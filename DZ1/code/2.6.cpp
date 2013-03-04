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
typedef pair<double, PII> PDII;
typedef pair<lng, lng> PLL;
typedef pair<lng, int> PLI;
typedef pair<int, double> PID;
typedef pair<double, int> PDI;

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

const int n = 19;

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

int m = 0;
double g[n][n];
PDII edges[n * n];
bool del[n][n];
PII a[n];

inline double dist(PII a, PII b) {
    return _hypot(a.X - b.X, a.Y - b.Y);
}

inline int get_label(int x) {
    if (x < 13) return x + 'A';
    if (x < 17) return x - 13 + '1';
    return x - 17 + 'X';
}

inline PII edge(int x, int y) {
    if (x > y) swap(x, y);
    int a = get_label(x);
    int b = get_label(y);
    return mp(a, b);
}

double kruskal(vector<PII> & ans, vector<PII> add = vector<PII>(), vector<int> unite = vector<int>()) {
    DSU dsu;

    for (int i = 1; i < sz(unite); ++i) {
        int x = unite[0];
        int y = unite[i];
        dsu.unite(x, y);
    }

    ans.clear();
    double res = 0.0;

    for (int i = 0; i < sz(add); ++i) {
        int x = add[i].X;
        int y = add[i].Y;
        res += g[x][y];
        dsu.unite(x, y);
        ans.pb(edge(x, y));
    }

    static PDII edges[n * n];
    memcpy(edges, ::edges, sizeof edges);
    sort(edges, edges + m);
    for (int i = 0; i < m && sz(ans) < n - 1; ++i) {
        double w = edges[i].X;
        int x = edges[i].Y.X;
        int y = edges[i].Y.Y;
        if (del[x][y])
            continue;
        if (dsu.get(x) != dsu.get(y)) {
            res += w;
            dsu.unite(x, y);
            ans.pb(edge(x, y));
        }
    }    
    return res;
}

void print_ans(vector<PII> ans) {
    sort(all(ans));
    for (int i = 0; i < sz(ans); ++i) {
        if (i) cout << ", ";
        cout << "(" << char(ans[i].X) << ",~" << char(ans[i].Y) << ")";
    }
    cout << endl;
}

void print_ids(vector<int> ids) {
    for (int i = 0; i < sz(ids); ++i) {
        if (i) cout << ", ";
        cout << "(" << edges[ids[i]].Y.X + 1 << ",~" << edges[ids[i]].Y.Y + 1 << ")";
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

    for (int i = 0; i < n; ++i) {
        int x, y;
        cin >> x >> y;
        a[i] = mp(x, y);
    }
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            g[i][j] = dist(a[i], a[j]);
        }
    }

    const int COST = 10000;
    double ans_2_6_a;
    {
        cout << "2.6 a)\n";
        m = 0;
        for (int i = 0; i < 13; ++i) {
            for (int j = i + 1; j < 13; ++j) {
                edges[m++] = mp(g[i][j], mp(i, j));
            }
        }
        vector<PII> ans;
        double w = ans_2_6_a = kruskal(ans);
        printf("%.15lf %.15lf\n", w, w * COST);
        print_ans(ans);
        cout << endl;
    }

    {
        cout << "2.6 b)\n";
        m = 0;
        for (int i = 0; i < n - 2; ++i) {
            for (int j = i + 1; j < n - 2; ++j) {
                edges[m++] = mp(g[i][j], mp(i, j));
            }
        }
        vector<PII> ans;
        vector<int> unite;
        unite.pb(13); unite.pb(14); unite.pb(15); unite.pb(16);
        double w = kruskal(ans, vector<PII>(), unite);
        printf("%.15lf %.15lf\n", w, w * COST);
        printf("%.15lf\n", (ans_2_6_a - w) * COST);
        print_ans(ans);
        cout << endl;
    }

    {
        cout << "2.6 d)\n";
        m = 0;
        for (int i = 0; i < n; ++i) {
            for (int j = i + 1; j < n; ++j) {
                edges[m++] = mp(g[i][j], mp(i, j));
            }
        }
        vector<PII> ans;
        vector<int> unite;
        unite.pb(13); unite.pb(14); unite.pb(15); unite.pb(16);
        double w = kruskal(ans, vector<PII>(), unite);
        printf("%.15lf %.15lf\n", w, w * COST);
        printf("%.15lf\n", w * COST - 50000);
        printf("%.15lf\n", w * COST - 50000 + 23500);
        printf("%.15lf\n", w * COST - 50000 + 7500 * 4);
        print_ans(ans);
        cout << endl;
    }

    return 0;
}