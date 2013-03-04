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

const int n = 46;
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

double g[n][n];
int c[n][n];
int e[n][n];
int tr[n][n];
PDII edges[m];
bool del[n][n];
bool need[n][n];
int lt[n][n];
int ut[n][n];
bool discounted[n][n];

inline PII edge(int x, int y) {
    ++x, ++y;
    return mp(min(x, y), max(x, y));
}

double kruskal(vector<PII> & ans, vector<PII> add = vector<PII>()) {
    DSU dsu;
    ans.clear();
    clr(tr, 0);

    double res = 0.0;
    for (int i = 0; i < sz(add); ++i) {
        int x = add[i].X;
        int y = add[i].Y;
        res += g[x][y];
        tr[x][y] = tr[y][x] = 1;
        dsu.unite(x, y);
        ans.pb(edge(x, y));
    }
    static PDII edges[m];
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
            tr[x][y] = tr[y][x] = 1;
            dsu.unite(x, y);
            ans.pb(mp(x + 1, y + 1));
        }
    }    
    return res;
}

double calc_weight(const vector<PII> & ans) {
    double res = 0;
    for (int i = 0; i < sz(ans); ++i) {
        res += g[ans[i].X - 1][ans[i].Y - 1];
    }
    return res;
}

void print_ans(vector<PII> ans) {
    sort(all(ans));
    for (int i = 0; i < sz(ans); ++i) {
        if (i) cout << ", ";
        cout << "(" << ans[i].X << ",~" << ans[i].Y << ")";
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

double apply_discount(double discount, vector<PII> & ans, vector<int> & ids) {
    vector<PII> add;
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            if (need[i][j])
                add.pb(mp(i, j));
        }
    }
    double best = 1e20;
    int IT = 0;
    forn(i1,m) {
        if (e[edges[i1].Y.X][edges[i1].Y.Y] * discount < lt[edges[i1].Y.X][edges[i1].Y.Y] || del[edges[i1].Y.X][edges[i1].Y.Y] || need[edges[i1].Y.X][edges[i1].Y.Y])
            continue;
        forn(i2,i1) {
            if (e[edges[i2].Y.X][edges[i2].Y.Y] * discount < lt[edges[i2].Y.X][edges[i2].Y.Y] || del[edges[i2].Y.X][edges[i2].Y.Y] || need[edges[i2].Y.X][edges[i2].Y.Y])
                continue;
            forn(i3,i2) {
                if (e[edges[i3].Y.X][edges[i3].Y.Y] * discount < lt[edges[i3].Y.X][edges[i3].Y.Y] || del[edges[i3].Y.X][edges[i3].Y.Y] || need[edges[i3].Y.X][edges[i3].Y.Y])
                    continue;
                forn(i4,i3) {
                    if (e[edges[i4].Y.X][edges[i4].Y.Y] * discount < lt[edges[i4].Y.X][edges[i4].Y.Y] || del[edges[i4].Y.X][edges[i4].Y.Y] || need[edges[i4].Y.X][edges[i4].Y.Y])
                        continue;
                    forn(i5,i4) {
                        if (e[edges[i5].Y.X][edges[i5].Y.Y] * discount < lt[edges[i5].Y.X][edges[i5].Y.Y] || del[edges[i5].Y.X][edges[i5].Y.Y] || need[edges[i4].Y.X][edges[i4].Y.Y])
                            continue;
                        
                        if (++IT % 100000 == 0)
                            cerr << IT << endl;

                        edges[i1].X -= e[edges[i1].Y.X][edges[i1].Y.Y] * discount;
                        edges[i2].X -= e[edges[i2].Y.X][edges[i2].Y.Y] * discount;
                        edges[i3].X -= e[edges[i3].Y.X][edges[i3].Y.Y] * discount;
                        edges[i4].X -= e[edges[i4].Y.X][edges[i4].Y.Y] * discount;
                        edges[i5].X -= e[edges[i5].Y.X][edges[i5].Y.Y] * discount;

                        vector<PII> res;
                        double w = kruskal(res, add);
                        if (w < best) {
                            best = w, ans = res;
                            ids.clear();
                            ids.pb(i1); ids.pb(i2); ids.pb(i3); ids.pb(i4); ids.pb(i5);
                        }

                        edges[i1].X += e[edges[i1].Y.X][edges[i1].Y.Y] * discount;
                        edges[i2].X += e[edges[i2].Y.X][edges[i2].Y.Y] * discount;
                        edges[i3].X += e[edges[i3].Y.X][edges[i3].Y.Y] * discount;
                        edges[i4].X += e[edges[i4].Y.X][edges[i4].Y.Y] * discount;
                        edges[i5].X += e[edges[i5].Y.X][edges[i5].Y.Y] * discount;
                    }
                }
            }
        }
    }
    std::cerr << IT << std::endl;
    return best;
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
        int cc, ec;
        cin >> x >> y >> cc >> ec;
        --x, --y;
        c[x][y] = c[y][x] = cc;
        e[x][y] = e[y][x] = ec;
        g[x][y] = g[y][x] = cc + ec;
        edges[i] = mp(g[x][y], mp(x, y));
    }

    int sum = 0;
    for (int i = 0; i < n - 1; ++i) {
        int x, y, z;
        scanf("\n(%d,%d)\n%d\n", &x, &y, &z);
        --x, --y;
        assert(g[x][y] == z);
        sum += z;
    }
    cout << sum << endl;

    { /// upper tolerances
        clr(ut, 127);
        vector<PII> ans;
        kruskal(ans);
        double w = calc_weight(ans);
        clr(del, 0);
        vector<PII> tmp;
        for (int i = 0; i < sz(ans); ++i) {
            int x = ans[i].X - 1;
            int y = ans[i].Y - 1;
            del[x][y] = del[y][x] = true;
            kruskal(tmp);
            double nw = calc_weight(tmp);
            ut[x][y] = ut[y][x] = int(nw - w + 0.5);
            del[x][y] = del[y][x] = false;
        }
    }

    { /// lower tolerances
        clr(lt, 128);
        vector<PII> ans;
        kruskal(ans);
        double w = calc_weight(ans);
        int save[n][n];
        memcpy(save, tr, sizeof save);
        vector<PII> tmp, add;
        for (int i = 0; i < m; ++i) {
            int x = edges[i].Y.X;
            int y = edges[i].Y.Y;
            if (save[x][y])
                continue;
            add.pb(mp(x, y));
            kruskal(tmp, add);
            double nw = calc_weight(tmp);
            lt[x][y] = lt[y][x] = int(nw - w + 0.5);
            add.pop_back();
        }
    }

    const int COST = 1000;

    {
        cout << "2.2 a)\n";
        vector<PII> ans;
        kruskal(ans);
        double w = calc_weight(ans);
        cout << setprecision(0) << fixed << w << ' ' << w * COST << endl;
        print_ans(ans);
        cout << endl;
    }

    {
        cout << "2.2 b)\n";
        vector<PII> ans;
        vector<int> ids;
        double w = apply_discount(0.15, ans, ids);
        printf("%.4lf %.4lf\n", w, w * COST);
        print_ids(ids);
        print_ans(ans);

        w = apply_discount(0.125, ans, ids);
        printf("%.15lf\n", 0.125); //(old_w - 9500) * 15 / (old_w - w)
        printf("%.4lf %.4lf\n", w, w * COST);        
        print_ids(ids);
        print_ans(ans);
        cout << endl;
    }

    {
        cout << "2.2 c)\n";
        del[4][12] = del[12][4] = true;
        vector<PII> ans;
        kruskal(ans);
        double w = calc_weight(ans);
        cout << setprecision(0) << fixed << w << ' ' << w * COST << endl;
        print_ans(ans);
        cout << ut[5 - 1][13 - 1] << "\n\n";
        del[4][12] = del[12][4] = false;
    }

    {
        cout << "2.2 d)\n";
        del[24 - 1][26 - 1] = del[26 - 1][24 - 1] = true;
        del[31 - 1][39 - 1] = del[39 - 1][31 - 1] = true;
        vector<PII> ans, add;
        add.pb(mp(6 - 1, 9 - 1));
        add.pb(mp(15 - 1, 17 - 1));
        kruskal(ans, add);
        double w = calc_weight(ans);
        cout << setprecision(0) << fixed << w << ' ' << w * COST << endl;
        print_ans(ans);

        g[6 - 1][9 - 1] = g[9 - 1][6 - 1] -= e[6 - 1][9 - 1] * 0.1;
        g[15 - 1][17 - 1] = g[17 - 1][15 - 1] -= e[15 - 1][17 - 1] * 0.1;
        need[6 - 1][9 - 1] = need[9 - 1][6 - 1] = true;
        need[15 - 1][17 - 1] = need[17 - 1][15 - 1] = true;
        for (int i = 0; i < m; ++i) {
            int x = edges[i].Y.X;
            int y = edges[i].Y.Y;
            edges[i].X = g[x][y];
        }
        vector<int> ids;
        clr(lt, 128);
        w = apply_discount(0.15, ans, ids);
        cout << setprecision(4) << fixed << w << ' ' << w * COST << endl;
        print_ids(ids);
        print_ans(ans);
    }

    return 0;
}