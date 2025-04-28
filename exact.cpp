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

// --- max‐flow / min‐cut via Edmonds–Karp ---
class FlowNetwork
{
public:
    int n;
    unordered_map<int, unordered_map<int, int>> cap, flow;

    FlowNetwork(int nodes) : n(nodes) {}

    void addEdge(int u, int v, int capacity)
    {
        cap[u][v] = capacity;
    }

    int maxFlow(int s, int t)
    {
        // init residual flows
        for (auto &[u, edges] : cap)
            for (auto &[v, _] : edges)
                flow[u][v] = 0;

        int total = 0;
        while (true)
        {
            vector<int> parent(n, -1);
            queue<int> q;
            q.push(s);
            parent[s] = s;

            // find augmenting path
            while (!q.empty() && parent[t] == -1)
            {
                int u = q.front();
                q.pop();
                for (auto &[v, capacity] : cap[u])
                {
                    if (parent[v] == -1 && flow[u][v] < capacity)
                    {
                        parent[v] = u;
                        q.push(v);
                    }
                }
            }
            if (parent[t] == -1)
                break; // no more paths

            // bottleneck
            int inc = numeric_limits<int>::max();
            for (int v = t; v != s; v = parent[v])
            {
                int u = parent[v];
                inc = min(inc, cap[u][v] - flow[u][v]);
            }

            // apply flow
            for (int v = t; v != s; v = parent[v])
            {
                int u = parent[v];
                flow[u][v] += inc;
                flow[v][u] -= inc;
            }
            total += inc;
        }
        return total;
    }

    // after maxFlow, find S = vertices reachable from s in residual graph
    pair<vector<int>, vector<int>> minCut(int s, int t)
    {
        maxFlow(s, t);
        vector<bool> vis(n, false);
        queue<int> q;
        q.push(s);
        vis[s] = true;
        while (!q.empty())
        {
            int u = q.front();
            q.pop();
            for (auto &[v, capacity] : cap[u])
            {
                if (!vis[v] && flow[u][v] < capacity)
                {
                    vis[v] = true;
                    q.push(v);
                }
            }
        }
        vector<int> S, T;
        for (int i = 0; i < n; ++i)
        {
            (vis[i] ? S : T).push_back(i);
        }
        return {S, T};
    }
};

// --- simple undirected graph + clique enumeration ---
class Graph
{
public:
    int n;
    vector<vector<int>> adj;

    Graph(int nodes) : n(nodes), adj(nodes) {}

    void addEdge(int u, int v)
    {
        adj[u].push_back(v);
        adj[v].push_back(u);
    }

    // backtracking to list all k-cliques
    vector<vector<int>> enumerateCliques(int k) const
    {
        vector<vector<int>> cliques;
        vector<int> curr;
        vector<int> cand(n);
        iota(cand.begin(), cand.end(), 0);

        function<void(const vector<int> &)> dfs = [&](const vector<int> &C)
        {
            if ((int)curr.size() == k)
            {
                cliques.push_back(curr);
                return;
            }
            for (int i = 0; i < (int)C.size(); ++i)
            {
                int v = C[i];
                // build next candidates = intersection of C[i+1..] with neighbors(v)
                vector<int> nxt;
                for (int j = i + 1; j < (int)C.size(); ++j)
                {
                    int w = C[j];
                    if (find(adj[v].begin(), adj[v].end(), w) != adj[v].end())
                        nxt.push_back(w);
                }
                curr.push_back(v);
                dfs(nxt);
                curr.pop_back();
            }
        };

        dfs(cand);
        return cliques;
    }

    // does adding v to 'group' form a clique?
    bool formsClique(int v, const vector<int> &group) const
    {
        for (int u : group)
            if (find(adj[v].begin(), adj[v].end(), u) == adj[v].end())
                return false;
        return true;
    }

    // extract induced subgraph on 'vertices'
    Graph extractSubgraph(const vector<int> &vertices) const
    {
        unordered_map<int, int> idx;
        for (int i = 0; i < (int)vertices.size(); ++i)
            idx[vertices[i]] = i;
        Graph sub(vertices.size());
        for (int i = 0; i < (int)vertices.size(); ++i)
        {
            for (int j : adj[vertices[i]])
            {
                auto it = idx.find(j);
                if (it != idx.end() && it->second > i)
                    sub.addEdge(i, it->second);
            }
        }
        return sub;
    }

    void printEdges(ofstream &out) const
    {
        for (int i = 0; i < n; ++i)
        {
            for (int j : adj[i])
            {
                if (i < j)
                    out << "(" << i + 1 << ", " << j + 1 << ")\n";
            }
        }
    }
};

// --- densest‐subgraph via parametric max‐flow ---
Graph findExactDensestSubgraph(
    Graph &G,
    int h,
    const vector<vector<int>> &hminusCliques,
    const vector<int> &cliqueDegree,
    ofstream &out)
{
    int n = G.n;
    double l = 0, u = 0;
    for (int v = 0; v < n; ++v)
        u = max(u, double(cliqueDegree[v]));

    if (hminusCliques.empty())
        return G;

    int m = hminusCliques.size();
    int total = 1 + n + m + 1; // src + n verts + m hyperedges + sink
    int src = 0, voff = 1, coff = 1 + n, sink = total - 1;
    vector<int> resultV;

    while (u - l > 1e-6)
    {
        double alpha = 0.5 * (l + u);
        FlowNetwork net(total);

        // source → each vertex
        for (int v = 0; v < n; ++v)
            net.addEdge(src, voff + v, cliqueDegree[v]);

        // each vertex → sink
        for (int v = 0; v < n; ++v)
            net.addEdge(voff + v, sink, int(alpha * h));

        // hyperedge-node → its (h−1) vertices with INF
        for (int i = 0; i < m; ++i)
        {
            for (int v : hminusCliques[i])
                net.addEdge(coff + i, voff + v, numeric_limits<int>::max());
        }

        // vertex → hyperedge-node with cap=1 if forms full h-clique
        for (int v = 0; v < n; ++v)
        {
            for (int i = 0; i < m; ++i)
            {
                if (G.formsClique(v, hminusCliques[i]))
                    net.addEdge(voff + v, coff + i, 1);
            }
        }

        auto [S, T] = net.minCut(src, sink);
        if (S.size() == 1)
        {
            u = alpha;
        }
        else
        {
            l = alpha;
            resultV.clear();
            for (int x : S)
            {
                if (x >= voff && x < coff)
                    resultV.push_back(x - voff);
            }
        }
        cout << "alpha=" << alpha << " |S|=" << S.size() << "\n";
    }

    if (resultV.empty())
        return G;
    return G.extractSubgraph(resultV);
}

Graph readGraph(const string &filename)
{
    ifstream file(filename);
    int n, e;
    file >> n >> e;
    Graph G(n);
    for (int i = 0; i < e; ++i)
    {
        int u, v;
        file >> u >> v;
        G.addEdge(u - 1, v - 1);
    }
    return G;
}

int main()
{
    auto start = chrono::high_resolution_clock::now();
    Graph G = readGraph("test.txt");

    int h;
    cout << "Enter h value: ";
    cin >> h;

    // 1) all (h−1)-cliques
    auto hminus = G.enumerateCliques(h - 1);
    // 2) all h-cliques → per-vertex counts
    auto hcl = G.enumerateCliques(h);
    vector<int> cliqueDegree(G.n, 0);
    for (auto &C : hcl)
        for (int v : C)
            ++cliqueDegree[v];

    ofstream out("output.txt");
    out << "Found " << hminus.size() << " cliques of size " << (h - 1) << "\n";
    if (h == 3)
        out << "Found " << hcl.size() << " triangles\n";

    Graph densest = findExactDensestSubgraph(G, h, hminus, cliqueDegree, out);

    auto end = chrono::high_resolution_clock::now();
    chrono::duration<double> elapsed = end - start;

    out << "Densest subgraph has " << densest.n << " vertices. Edges:\n\n";
    densest.printEdges(out);
    out << "\nComputation time: " << elapsed.count() << " seconds\n";

    // final density
    double density = 0.0;
    if (h == 2)
    {
        int sumDeg = 0;
        for (int v = 0; v < densest.n; ++v)
            sumDeg += densest.adj[v].size();
        density = double(sumDeg / 2) / densest.n;
    }
    else
    {
        auto densestH = densest.enumerateCliques(h);
        density = double(densestH.size()) / densest.n;
    }
    out << "Density: " << density << "\n";
    cout << "Final density (h=" << h << ") = " << density << "\n";
    cout << "Done. See output.txt\n";
    return 0;
}