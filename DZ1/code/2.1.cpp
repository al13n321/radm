#pragma comment(linker, "/STACK:256000000")
#define _CRT_SECURE_NO_DEPRECATE
#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <climits>
#include <ctime>
#include <numeric>
#include <vector>
#include <algorithm>
#include <bitset>
#include <cmath>
#include <cstring>
#include <iomanip>
#include <complex>
#include <deque>
#include <functional>
#include <list>
#include <map>
#include <string>
#include <sstream>
#include <set>
#include <stack>
#include <queue>

using namespace std;

template<class T> inline T sqr(T x) { return x * x; }
template<class T> inline string tostr(const T & x) { stringstream ss; ss << x; return ss.str(); }

typedef long long lng;
typedef unsigned long long ulng;
typedef unsigned int uint;
typedef unsigned char uchar;
typedef double ld;
typedef pair<int, int> PII;
typedef pair<int, PII> PIII;
typedef pair<lng, lng> PLL;
typedef pair<lng, int> PLI;
typedef pair<int, double> PID;

typedef pair<ld, ld> PDD;

#define left asdleft
#define right asdright
#define link asdlink
#define unlink asdunlink
#define next asdnext
#define prev asdprev
#define y0 asdy0
#define y1 asdy1
#define mp make_pair
#define pb push_back
#define sz(x) ((int)(x).size())
#define all(x) (x).begin(), (x).end()
#define clr(ar,val) memset(ar, val, sizeof(ar))
#define istr stringstream
#define forn(i,n) for(int i=0;i<(n);++i)
#define forv(i,v) forn(i,sz(v))
#define X first
#define Y second

const double EPS = 1e-6;
const int INF = 1000*1000*1000;
const lng LINF = INF * 1ll * INF;
const ld PI = 3.1415926535897932384626433832795;

#define TASKA "clock"

const int n = 50;
const int m = 84;

struct DSU {
    int p[n];

    DSU() {
        clear();
    }

    void clear() {
        for (int i = 0; i < n; ++i)
            p[i] = i;
    }

    int get(int x) {
        return x == p[x] ? x : p[x] = get(p[x]);
    }

    void unite(int x, int y) {
        x = get(x), y = get(y);
        if (rand() & 1)
            p[x] = y;
        else
            p[y] = x;
    }
};

int g[n][n];
int tr[n][n];
PIII edges[m];

void kruskal(vector<PII> & ans, PII connect = mp(-1, -1)) {
    DSU dsu;
    clr(tr, 0);
    ans.clear();

    if (connect.X != -1) {
        int x = connect.X, y = connect.Y;
        dsu.unite(x, y);
        tr[x][y] = tr[y][x] = 1;
        ans.pb(mp(x + 1, y + 1));
    }

    sort(edges, edges + m);
    for (int i = 0; i < m; ++i) {
        int w = edges[i].X;
        int x = edges[i].Y.X;
        int y = edges[i].Y.Y;
        if (dsu.get(x) != dsu.get(y)) {
            dsu.unite(x, y);
            tr[x][y] = tr[y][x] = 1;
            ans.pb(mp(x + 1, y + 1));
        }
    }    
}

inline PII edge(int x, int y) {
    ++x, ++y;
    return mp(min(x, y), max(x, y));
}

int dfs1(int v, int p, int & best, vector<PII> & ans) {
    int res = 1;
    for (int i = 0; i < n; ++i) {
        if (!tr[v][i] || i == p)
            continue;
        int cur = dfs1(i, v, best, ans);
        if (cur * (n - cur) > best) {
            best = cur * (n - cur);
            ans.clear();
        }
        if (cur * (n - cur) == best) {
            ans.pb(edge(v, i));
            cout << best << " = " << cur << " * " << (n - cur) << endl;
        }
        res += cur;
    }
    return res;
}

int depth[n];
char used[n];

pair<PII, PII> dfs3(int v, int p, int d, vector<PII> & ans) {
    depth[v] = d;
    used[v] = true;
    int best_took = INF;
    PII took;
    int best_any = INF;
    PII any;
    bool upper = false;
    for (int i = 0; i < n; ++i) {
        if (!g[v][i] || i == p)
            continue;
        if (used[i]) {
            if (depth[i] < best_any) {
                best_any = depth[i];
                any = mp(v, i);
            }
        } else {
            pair<PII, PII> cur = dfs3(i, v, d + 1, ans);
            upper |= depth[cur.X.Y] < depth[v];
            if (depth[cur.X.Y] < best_took) {
                best_took = depth[cur.X.Y];
                took = cur.X;
            }
            if (depth[cur.Y.Y] < best_any) {
                best_any = depth[cur.Y.Y];
                any = cur.Y;
            }
        }
    }
    if (!upper && p != -1) {
        ans.pb(edge(any.X, any.Y));
        took = any;
        best_took = best_any;
    }
    if (best_took == INF || best_any == INF)
        exit(123);
    return mp(took, any);
}

int dfs2(int v, int p, vector<PII> & ans) {
    used[v] = true;
    int res = v;
    int resd = depth[v];
    bool parent = false;
    bool upper = false;
    bool leaf = true;
    for (int i = 0; i < n; ++i) {
        if (!g[v][i] || i == p)
            continue;
        if (used[i]) {
            if (depth[i] < resd) {
                resd = depth[i];
                res = i;
            }
            if (p != -1 && depth[i] < depth[p])
                upper = true;
        } else {
            leaf = false;
            int cur = dfs2(i, v, ans);
            if (depth[cur] < resd) {
                resd = depth[cur];
                res = cur;
            }
            if (cur == p)
                parent = true;
            if (p != -1 && depth[cur] < depth[p])
                upper = true;
        }
    }
    if (p != -1 && (!parent || !upper))
        ans.pb(edge(p, v));
    return res;
}

int calc_weight(const vector<PII> & ans) {
    int res = 0;
    for (int i = 0; i < sz(ans); ++i) {
        res += g[ans[i].X - 1][ans[i].Y - 1];
    }
    return res;
}

void print_ans(vector<PII> ans) {
    sort(all(ans));
    for (int i = 0; i < sz(ans); ++i) {
        if (i) cout << ", ";
        cout << "(" << ans[i].X << ", " << ans[i].Y << ")";
    }
    cout << endl;
}

int main() {
#ifdef __ASD__
	freopen("input.txt", "r", stdin); freopen("output.txt", "w", stdout);
#else
	//freopen(TASKA ".in", "r", stdin); freopen(TASKA ".out", "w", stdout);
#endif
	
	//ios_base::sync_with_stdio(false);

    for (int i = 0; i < m; ++i) {
        int x, y;
        double z;
        cin >> x >> y >> z;
        --x, --y;
        g[x][y] = g[y][x] = int(z * 10.0);
        edges[i] = mp(g[x][y], mp(x, y));
    }
    const int COST = 5000;

    {
        cout << "2.1 a)\n";
        vector<PII> ans;
        kruskal(ans);
        int w = calc_weight(ans);
        cout << w << ' ' << w * COST << endl;
        print_ans(ans);
        cout << endl;
    }
    {
        cout << "2.1 b)\n";
        vector<PII> ans;
        kruskal(ans, mp(8, 16));
        int w = calc_weight(ans);
        cout << w << ' ' << w * COST << endl;
        print_ans(ans);
        cout << endl;
    }
    {
        cout << "2.1 c)\n";
        vector<PII> ans;
        kruskal(ans);
        int best = 0;
        ans.clear();
        dfs1(0, -1, best, ans);
        cout << best << endl;
        print_ans(ans);
        cout << endl;
    }
    {
        cout << "2.1 d)\n";
        vector<PII> ans;
        clr(used, 0);
        dfs3(0, -1, 0, ans);
        clr(used, 0);
        dfs2(0, -1, ans);
        int w = calc_weight(ans);
        cout << w << ' ' << w * COST << endl;
        print_ans(ans);
        cout << endl;
    }

    return 0;
}