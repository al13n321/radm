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

struct graph {
    static const int MAXN = 20;
    int n;
    int cost[MAXN][MAXN];
    int xy[MAXN], yx[MAXN];
    int lx[MAXN], ly[MAXN];
    int slack[MAXN], slackx[MAXN];
    bool S[MAXN], T[MAXN];
    int p[MAXN];

    void update_labels() {
        int delta = INF;
        for (int y = 0; y < n; ++y)
            if (!T[y])
                delta = min(delta, slack[y]);
        for (int y = 0; y < n; ++y)
            if (!T[y])
                slack[y] -= delta;
            else
                ly[y] += delta;
        for (int x = 0; x < n; ++x)
            if (S[x])
                lx[x] -= delta;
    }

    void add_to_tree(int x, int px) {
        S[x] = true;
        p[x] = px;
        for (int y = 0; y < n; ++y)
            if (slack[y] > lx[x] + ly[y] - cost[x][y]) {
                slack[y] = lx[x] + ly[y] - cost[x][y];
                slackx[y] = x;
            }
    }

    void augment() {
        static int q[MAXN];
        int l = 0, r = 0, x, y;
        for (x = 0; x < n; ++x)
            if (xy[x] == -1)
                break;
        for (y = 0; y < n; ++y) {
            slack[y] = lx[x] + ly[y] - cost[x][y];
            slackx[y] = x;
        }
        S[x] = true;
        q[r++] = x;
        for (;;) {
            while (l < r) {
                x = q[l++];
                for (y = 0; y < n; ++y) {
                    if (lx[x] + ly[y] == cost[x][y] && !T[y]) {
                        if (yx[y] == -1) break;
                        T[y] = true;
                        add_to_tree(yx[y], x);
                        q[r++] = yx[y];
                    }
                }
                if (y < n) break;
            }
            if (y < n) break;
            update_labels();
            for (y = 0; y < n; ++y) {
                if (!T[y] && !slack[y]) {
                    if (yx[y] == -1) {
                        x = slackx[y];
                        break;
                    } else {
                        T[y] = true;
                        if (!S[yx[y]]) {
                            add_to_tree(yx[y], slackx[y]);
                            q[r++] = yx[y];
                        }
                    }
                }
            }
            if (y < n) break;
        }
        for (int py; x != -1; x = p[x], y = py) {
            py = xy[x];
            xy[x] = y;
            yx[y] = x;
        }
    }

    int hungarian() {
        memset(lx, 128, sizeof lx);
        memset(ly, 0, sizeof ly);
        for (int x = 0; x < n; ++x) {
            for (int y = 0; y < n; ++y) {
                cost[x][y] *= -1;
                lx[x] = max(lx[x], cost[x][y]);
            }
        }
        memset(xy, -1, sizeof xy);
        memset(yx, -1, sizeof yx);
        for (int it = 0; it < n; ++it) {
            memset(S, 0, sizeof S);
            memset(T, 0, sizeof T);
            memset(p, -1, sizeof p);
            augment();
        }
        for (int x = 0; x < n; ++x) {
            for (int y = 0; y < n; ++y) {
                cost[x][y] *= -1;
            }
        }
        int res = 0;
        for (int x = 0; x < n; ++x) {
            if (cost[x][xy[x]] < INF)
                res += cost[x][xy[x]];
        }
        return res;
    }

    int greedy_yx() {
        clr(S, 0);
        clr(xy, -1);
        clr(yx, -1);
        int res = 0;
        for (int y = 0; y < n; ++y) {
            int best = -1;
            for (int x = 0; x < n; ++x) {
                if (!S[x] && (best == -1 || cost[best][y] > cost[x][y]))
                    best = x;
            }
            xy[best] = y;
            yx[y] = best;
            res += cost[best][y];
            S[best] = true;
        }
        return res;
    }

    int greedy() {
        clr(S, 0);
        clr(T, 0);
        clr(xy, -1);
        clr(yx, -1);
        int res = 0;
        for (int it = 0; it < n; ++it) {
            int bestx = -1, besty = -1;
            for (int x = 0; x < n; ++x) {
                if (S[x]) continue;
                for (int y = 0; y < n; ++y) {
                    if (T[y]) continue;
                    if (bestx == -1 || cost[bestx][besty] > cost[x][y])
                        bestx = x, besty = y;
                }
            }
            S[bestx] = T[besty] = true;
            xy[bestx] = besty;
            yx[besty] = bestx;
            if (cost[bestx][besty] < INF)
                res += cost[bestx][besty];
        }
        return res;
    }

    void print_assignment_yx() {
        printf("Customer & Technician & Repairing time \\\\ \\hline\n");
        for (int i = 0; i < n; ++i) {
            printf("%d & %d & %d \\\\\n", i + 1, yx[i] + 1, cost[yx[i]][i]);
        }
        printf("\\hline\n");
    }

    void print_assignment_xy() {
        printf("Technician & Customer & Repairing time \\\\ \\hline\n");
        for (int i = 0; i < n; ++i) {
            printf("%d & %d & %d \\\\\n", i + 1, xy[i] + 1, cost[i][xy[i]]);
        }
        printf("\\hline\n");
    }

    void print_cost_matrix() {
        printf("\\backslashbox{Technicians}{Customers}");
        for (int i = 0; i < n; ++i) {
            printf(" & %d", i + 1);
        }
        printf("\\\\\\hline\n");
        for (int i = 0; i < n; ++i) {
            printf("%d", i + 1); 
            for (int j = 0; j < n; ++j) {
                if (cost[i][j] < INF)
                    printf(" & %d ", cost[i][j]);
                else
                    printf(" & $\\infty$ ");
            }
            printf("\\\\ \\hline\n");
        }
        printf("\\hline\n");
    }
};

const int TECHNICIANS = 15;
const int CUSTOMERS = 20;
const int CATEGORIES = 10;

graph g;
int cost[TECHNICIANS][CATEGORIES];
int category[CUSTOMERS];

int main() {
#ifdef __ASD__
	freopen("input.txt", "r", stdin); freopen("output.txt", "w", stdout);
#else
	//freopen(TASKA ".in", "r", stdin); freopen(TASKA ".out", "w", stdout);
#endif
	
	//ios_base::sync_with_stdio(false);
    for (int i = 0; i < CUSTOMERS; ++i) {
        int x, y;
        cin >> x >> y;
        --x, --y;
        category[x] = y;
    }
    for (int i = 0; i < TECHNICIANS; ++i) {
        for (int j = 0; j < CATEGORIES; ++j) {
            cin >> cost[i][j];
        }
    }

    {
        cout << "4.1 a)\n";
        g.n = TECHNICIANS;
        for (int i = 0; i < g.n; ++i) {
            for (int j = 0; j < g.n; ++j) {
                g.cost[i][j] = cost[i][category[j]];
            }
        }
        int res = g.greedy_yx();
        cout << res << endl;
        g.print_assignment_yx();
        g.print_cost_matrix();
        res = g.hungarian();
        cout << res << endl;
        g.print_assignment_yx();
        cout << endl;
    }

    {
        cout << "4.1 b)\n";
        g.n = CUSTOMERS;
        for (int i = 0; i < g.n; ++i) {
            for (int j = 0; j < g.n; ++j) {
                if (i < TECHNICIANS)
                    g.cost[i][j] = cost[i][category[j]];
                else
                    g.cost[i][j] = INF;
            }
        }
        int res = g.greedy();
        cout << res << endl;
        g.print_assignment_xy();
        g.print_cost_matrix();
        res = g.hungarian();
        cout << res << endl;
        g.print_assignment_xy();
        cout << endl;
    }

    {
        cout << "4.1 d)\n";
        g.n = CUSTOMERS;
        for (int i = 0; i < g.n; ++i) {
            for (int j = 0; j < g.n; ++j) {
                if (i < TECHNICIANS)
                    g.cost[i][j] = cost[i][category[j]];
                else
                    g.cost[i][j] = INF;
            }
        }
        int val = -1;
        int x = 2 - 1, y = 14 - 1;
        for (g.cost[x][y] = 0; g.cost[x][y] <= 200; ++g.cost[x][y]) {
            cout << g.hungarian();
            cout << " " << g.cost[x][y] << " " << g.xy[x] + 1 << "; ";
            if (val == -1 && g.xy[x] != y)
                val = g.cost[x][y];
        }
        cout << endl;
        cout << val << ' ' << g.xy[x] + 1 << endl;
        cout << endl;
    }

    {
        cout << "4.1 e)\n";
        g.n = TECHNICIANS;
        for (int i = 0; i < g.n; ++i) {
            for (int j = 0; j < g.n; ++j) {
                g.cost[i][j] = cost[i][category[j]];
            }
        }
        memcpy(g.cost[2 - 1], g.cost[8 - 1], sizeof g.cost[2 - 1]);
        //g.print_cost_matrix();
        int res = g.hungarian();
        cout << res << endl;
        // replace 2 by 8
        g.print_assignment_yx();
        cout << endl;
    }

    {
        cout << "4.1 f)\n";
        g.n = CUSTOMERS;
        for (int i = 0; i < g.n; ++i) {
            for (int j = 0; j < g.n; ++j) {
                if (i < TECHNICIANS && j != 4 - 1)
                    g.cost[i][j] = cost[i][category[j]];
                else
                    g.cost[i][j] = INF;
            }
        }
        //g.print_cost_matrix();
        int res = g.hungarian();
        cout << res << endl;
        g.print_assignment_xy();
        cout << endl;
    }

    return 0;
}