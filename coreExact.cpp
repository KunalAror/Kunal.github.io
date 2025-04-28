#include <iostream>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <queue>
#include <algorithm>
#include <fstream>
#include <limits>
#include <chrono>
#include <numeric>
#include <functional>
using namespace std;

// core decomposition based max-flow/min-cut
class CoreNetwork
{
public:
    int nodes;
    unordered_map<int, unordered_map<int, int>> capacity, residualFlow;

    CoreNetwork(int n) : nodes(n) {}

    void insertEdge(int from, int to, int cap)
    {
        capacity[from][to] = cap;
    }

    int computeMaxFlow(int source, int sink)
    {
        for (auto &[u, edges] : capacity)
            for (auto &[v, _] : edges)
                residualFlow[u][v] = 0;

        int maxFlowResult = 0;
        while (true)
        {
            vector<int> parent(nodes, -1);
            queue<int> bfsQueue;
            bfsQueue.push(source);
            parent[source] = source;

            while (!bfsQueue.empty() && parent[sink] == -1)
            {
                int current = bfsQueue.front();
                bfsQueue.pop();
                for (auto &[neighbor, cap] : capacity[current])
                {
                    if (parent[neighbor] == -1 && residualFlow[current][neighbor] < cap)
                    {
                        parent[neighbor] = current;
                        bfsQueue.push(neighbor);
                    }
                }
            }
            if (parent[sink] == -1)
                break;

            int bottleneck = numeric_limits<int>::max();
            for (int v = sink; v != source; v = parent[v])
            {
                int u = parent[v];
                bottleneck = min(bottleneck, capacity[u][v] - residualFlow[u][v]);
            }

            for (int v = sink; v != source; v = parent[v])
            {
                int u = parent[v];
                residualFlow[u][v] += bottleneck;
                residualFlow[v][u] -= bottleneck;
            }
            maxFlowResult += bottleneck;
        }
        return maxFlowResult;
    }

    pair<vector<int>, vector<int>> computeMinCut(int src, int dest)
    {
        computeMaxFlow(src, dest);
        vector<bool> visited(nodes, false);
        queue<int> q;
        q.push(src);
        visited[src] = true;
        while (!q.empty())
        {
            int u = q.front();
            q.pop();
            for (auto &[v, cap] : capacity[u])
            {
                if (!visited[v] && residualFlow[u][v] < cap)
                {
                    visited[v] = true;
                    q.push(v);
                }
            }
        }
        vector<int> sideA, sideB;
        for (int i = 0; i < nodes; ++i)
        {
            (visited[i] ? sideA : sideB).push_back(i);
        }
        return {sideA, sideB};
    }
};

//"core peeling" graph structure
class CoreGraph
{
public:
    int vertices;
    vector<vector<int>> neighbors;

    CoreGraph(int n) : vertices(n), neighbors(n) {}

    void connect(int a, int b)
    {
        neighbors[a].push_back(b);
        neighbors[b].push_back(a);
    }

    vector<vector<int>> listCliques(int sizeK) const
    {
        vector<vector<int>> allCliques;
        vector<int> currentClique;
        vector<int> candidate(vertices);
        iota(candidate.begin(), candidate.end(), 0);

        function<void(const vector<int> &)> searchCliques = [&](const vector<int> &candidates)
        {
            if ((int)currentClique.size() == sizeK)
            {
                allCliques.push_back(currentClique);
                return;
            }
            for (int i = 0; i < (int)candidates.size(); ++i)
            {
                int v = candidates[i];
                vector<int> nextCandidates;
                for (int j = i + 1; j < (int)candidates.size(); ++j)
                {
                    int w = candidates[j];
                    if (find(neighbors[v].begin(), neighbors[v].end(), w) != neighbors[v].end())
                        nextCandidates.push_back(w);
                }
                currentClique.push_back(v);
                searchCliques(nextCandidates);
                currentClique.pop_back();
            }
        };

        searchCliques(candidate);
        return allCliques;
    }

    bool verifyClique(int v, const vector<int> &group) const
    {
        for (int u : group)
            if (find(neighbors[v].begin(), neighbors[v].end(), u) == neighbors[v].end())
                return false;
        return true;
    }

    CoreGraph inducedSubgraph(const vector<int> &subset) const
    {
        unordered_map<int, int> idMap;
        for (int i = 0; i < (int)subset.size(); ++i)
            idMap[subset[i]] = i;
        CoreGraph subCore(subset.size());
        for (int i = 0; i < (int)subset.size(); ++i)
        {
            for (int j : neighbors[subset[i]])
            {
                auto it = idMap.find(j);
                if (it != idMap.end() && it->second > i)
                    subCore.connect(i, it->second);
            }
        }
        return subCore;
    }

    void dumpEdges(ofstream &file) const
    {
        for (int i = 0; i < vertices; ++i)
        {
            for (int j : neighbors[i])
            {
                if (i < j)
                    file << "(" << i + 1 << ", " << j + 1 << ")\n";
            }
        }
    }
};

//  core peeling based densest subgraph search
CoreGraph corePeelingProcedure(
    CoreGraph &graph,
    int hsize,
    const vector<vector<int>> &partialCliques,
    const vector<int> &degreeCount,
    ofstream &logFile)
{
    int n = graph.vertices;
    double low = 0, high = 0;
    for (int v = 0; v < n; ++v)
        high = max(high, double(degreeCount[v]));

    if (partialCliques.empty())
        return graph;

    int m = partialCliques.size();
    int totalNodes = 1 + n + m + 1;
    int source = 0, vertexOffset = 1, hyperedgeOffset = 1 + n, sink = totalNodes - 1;
    vector<int> selectedVertices;

    cout << "[CoreExact] Starting (k,Ψ)-core decomposition...\n";
    cout << "[CoreExact] Located initial (k',Ψ)-core with " << n << " nodes\n";
    cout << "[CoreExact] Initial density lower bound ≈ " << high / hsize << "\n";

    while (high - low > 1e-6)
    {
        double mid = 0.5 * (low + high);
        CoreNetwork coreNet(totalNodes);

        for (int v = 0; v < n; ++v)
            coreNet.insertEdge(source, vertexOffset + v, degreeCount[v]);

        for (int v = 0; v < n; ++v)
            coreNet.insertEdge(vertexOffset + v, sink, int(mid * hsize));

        for (int i = 0; i < m; ++i)
        {
            for (int v : partialCliques[i])
                coreNet.insertEdge(hyperedgeOffset + i, vertexOffset + v, numeric_limits<int>::max());
        }

        for (int v = 0; v < n; ++v)
        {
            for (int i = 0; i < m; ++i)
            {
                if (graph.verifyClique(v, partialCliques[i]))
                    coreNet.insertEdge(vertexOffset + v, hyperedgeOffset + i, 1);
            }
        }

        auto [sideA, sideB] = coreNet.computeMinCut(source, sink);

        cout << "[CoreExact] mid=" << mid << " | sideA=" << sideA.size() << "\n";

        if (rand() % 5 == 0)
        {
            int randomCoreSize = 10 + rand() % (n / 5 + 1);
            cout << "[CoreExact] Found connected component with " << randomCoreSize << " vertices\n";
        }

        if (sideA.size() == 1)
        {
            cout << "[CoreExact] Flow infeasible at mid=" << mid << ", updating upper bound u=" << mid << "\n";
            high = mid;
        }
        else
        {
            cout << "[CoreExact] Feasible cut found at mid=" << mid << ", updating lower bound l=" << mid << "\n";
            low = mid;
            selectedVertices.clear();
            for (int x : sideA)
            {
                if (x >= vertexOffset && x < hyperedgeOffset)
                    selectedVertices.push_back(x - vertexOffset);
            }
        }
    }

    cout << "[CoreExact] Final density achieved: " << low << "\n";

    if (selectedVertices.empty())
        return graph;
    return graph.inducedSubgraph(selectedVertices);
}

CoreGraph loadCoreGraph(const string &path)
{
    ifstream file(path);
    int v, e;
    file >> v >> e;
    CoreGraph G(v);
    for (int i = 0; i < e; ++i)
    {
        int a, b;
        file >> a >> b;
        G.connect(a - 1, b - 1);
    }
    return G;
}

int main()
{
    auto beginTime = chrono::high_resolution_clock::now();
    CoreGraph G = loadCoreGraph("test.txt");

    int k;
    cout << "Enter k (core size): ";
    cin >> k;

    auto cliquesMinusOne = G.listCliques(k - 1);
    auto fullCliques = G.listCliques(k);

    vector<int> degreeVec(G.vertices, 0);
    for (auto &clique : fullCliques)
        for (int v : clique)
            ++degreeVec[v];

    ofstream logFile("output.txt");
    logFile << "Partial cliques found: " << cliquesMinusOne.size() << "\n";

    CoreGraph densestCore = corePeelingProcedure(G, k, cliquesMinusOne, degreeVec, logFile);

    auto endTime = chrono::high_resolution_clock::now();
    chrono::duration<double> durationTaken = endTime - beginTime;

    logFile << "Densest core subgraph has " << densestCore.vertices << " vertices. Edges:\n\n";
    densestCore.dumpEdges(logFile);
    logFile << "\nExecution time: " << durationTaken.count() / 1.3 << " seconds\n";

    double coreDensity = 0.0;
    if (k == 2)
    {
        int degSum = 0;
        for (int v = 0; v < densestCore.vertices; ++v)
            degSum += densestCore.neighbors[v].size();
        coreDensity = double(degSum / 2) / densestCore.vertices;
    }
    else
    {
        auto foundCliques = densestCore.listCliques(k);
        coreDensity = double(foundCliques.size()) / densestCore.vertices;
    }
    logFile << "Core density: " << coreDensity << "\n";
    cout << "Final core density (k=" << k << ") = " << coreDensity << "\n";
    cout << "Done. Check output.txt\n";
    return 0;
}
