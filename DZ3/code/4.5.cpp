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

const double EPS = 1e-7;
const int INF = 1000*1000*1000;
const lng LINF = INF * 1ll * INF;
const ld PI = 3.1415926535897932384626433832795;

#define TASKA "clock"

struct graph {
    static const int MAXN = 10;
    int n;
    double cost[MAXN][MAXN];
    int xy[MAXN], yx[MAXN];
    double lx[MAXN], ly[MAXN];
    double slack[MAXN];
    int slackx[MAXN];
    bool S[MAXN], T[MAXN];
    int p[MAXN];

    void update_labels() {
        double delta = 1e20;
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
                    if (fabs(lx[x] + ly[y] - cost[x][y]) < EPS && !T[y]) {
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

    double hungarian() {
        memset(lx, 128, sizeof lx);
        memset(ly, 0, sizeof ly);
        for (int x = 0; x < n; ++x) {
            for (int y = 0; y < n; ++y) {
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
        double res = 0;
        for (int x = 0; x < n; ++x) {
            if (- INF < cost[x][xy[x]] && cost[x][xy[x]] < INF)
                res += cost[x][xy[x]];
        }
        return res;
    }

    double greedy() {
        clr(S, 0);
        clr(T, 0);
        clr(xy, -1);
        clr(yx, -1);
        double res = 0;
        for (int it = 0; it < n; ++it) {
            int bestx = -1, besty = -1;
            for (int x = 0; x < n; ++x) {
                if (S[x]) continue;
                for (int y = 0; y < n; ++y) {
                    if (T[y]) continue;
                    if (bestx == -1 || cost[bestx][besty] < cost[x][y])
                        bestx = x, besty = y;
                }
            }
            S[bestx] = T[besty] = true;
            xy[bestx] = besty;
            yx[besty] = bestx;
            if (- INF < cost[bestx][besty] && cost[bestx][besty] < INF)
                res += cost[bestx][besty];
        }
        return res;
    }
};

const int n = 10;

graph g;
string phones[n];
string products[n];
int inc[n][n];
int phone_cost[n];
int product_cost[n];

void print_cost_matrix() {
    printf("Prod.\\textbackslash GT");
    for (int i = 0; i < g.n; ++i) {
        printf(" & %s", phones[i].substr(3).c_str());
    }
    printf("\\\\\\hline\n");
    for (int i = 0; i < n; ++i) {
        printf("%s", products[i].c_str()); 
        for (int j = 0; j < n; ++j) {
            if (g.cost[i][j] < INF)
                printf(" & %.2lf ", g.cost[i][j] / 100.0);
            else
                printf(" & $\\infty$ ");
        }
        printf("\\\\ \\hline\n");
    }
    printf("\n");
}

void print_assignment_yx() {
    printf("Cell phone type & Other product & Price (including short-term increase) \\\\ \\hline\n");
    for (int i = 0; i < g.n; ++i) {
        printf("%s & %s & %.2lf \\\\\n", phones[i].c_str(), products[g.yx[i]].c_str(), g.cost[g.yx[i]][i] / 100.0);
    }
    printf("\\hline\n");
}

int main() {
#ifdef __ASD__
	freopen("input.txt", "r", stdin); freopen("output.txt", "w", stdout);
#else
	//freopen(TASKA ".in", "r", stdin); freopen(TASKA ".out", "w", stdout);
#endif
	
	//ios_base::sync_with_stdio(false);
    for (string s; getline(cin, s); ) {
        stringstream ssin(s);
        for (int i = 0; i < n; ++i) {
            string t;
            ssin >> t;
            phones[i] = "GT " + t;
        }
        break;
    }
    for (int i = 0; i < n; ++i) {
        string s;
        getline(cin, s);
        for (int j = 0; ; ++j) {
            if (s[j] == '&') {
                s = s.substr(j + 1);
                break;
            }
            products[i] += s[j];
        }
        stringstream ssin(s);
        for (int j = 0; j < n; ++j) {
            ssin >> inc[i][j];
        }
    }
    for (int i = 0; i < n; ++i) {
        int buy, sell;
        cin >> buy >> sell;
        phone_cost[i] = sell - buy;
    }
    for (int i = 0; i < n; ++i) {
        int buy, sell;
        cin >> buy >> sell;
        product_cost[i] = sell - buy;
    }

    g.n = n;

    {
        cout << "4.5 b)\n";
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) {
                g.cost[i][j] = (phone_cost[j] + product_cost[i]) * (100 + inc[i][j]);
            }
        }
        double res = g.greedy();
        printf("%.2lf\n", res / 100.0);
        print_assignment_yx();
        cout << endl;
    }

    {
        cout << "4.5 c)\n";
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) {
                g.cost[i][j] = (phone_cost[j] + product_cost[i]) * (100 + inc[i][j]);
            }
        }
        print_cost_matrix();
        double res = g.hungarian();
        printf("%.2lf\n", res / 100.0);
        print_assignment_yx();
        cout << endl;
    }

    {
        cout << "4.5 a)\n";
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) {
                g.cost[i][j] = (phone_cost[j] + product_cost[i]) * (100 + inc[i][j]);
            }
        }
        int y = find(phones, phones + n, "GT I") - phones;
        int x = find(products, products + n, "Extra Li-Ion Battery") - products;
        for (int val = inc[x][y]; val <= 100; ++val) {
            g.cost[x][y] = (phone_cost[y] + product_cost[x]) * (100 + val);
            double res = g.hungarian();
            printf("%d & %.2lf & %s \\\\\n", val, res / 100.0, products[g.yx[y]].c_str());
            if (g.yx[y] == x)
                break;
        }
        double l = inc[x][y], r = 100.0;
        for (int it = 0; it < 100; ++it) {
            double m = (l + r) / 2.0;
            g.cost[x][y] = (phone_cost[y] + product_cost[x]) * (100 + m);
            g.hungarian();
            if (g.yx[y] == x)
                r = m;
            else
                l = m;
        }
        printf("%.10lf\n", (l + r) / 2.0);
        cout << endl;
    }
    
    {
        cout << "4.5 d)\n";
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) {
                g.cost[i][j] = (phone_cost[j] + product_cost[i]) * (100 + inc[i][j]);
            }
        }
        int y = find(phones, phones + n, "GT IV") - phones;
        int x = find(products, products + n, "Call bundle (400 min.)") - products;
        for (int val = 0; val <= inc[x][y] + 10; ++val) {
            g.cost[x][y] = (phone_cost[y] + product_cost[x]) * (100 + val);
            double res = g.hungarian();
            printf("%d & %.2lf & %s \\\\\n", val, res / 100.0, products[g.yx[y]].c_str());
            printf("%.2lf ", res / 100.0);
            if (g.yx[y] == x)
                break;
        }
        cout << endl;
        double l = 0.0, r = 100.0;
        for (int it = 0; it < 100; ++it) {
            double m = (l + r) / 2.0;
            g.cost[x][y] = (phone_cost[y] + product_cost[x]) * (100 + m);
            g.hungarian();
            if (g.yx[y] == x)
                r = m;
            else
                l = m;
        }
        printf("%.10lf\n", (l + r) / 2.0);
        cout << endl;
    }

    {
        cout << "4.5 e)\n";
        int x = find(products, products + n, "Extra Li-Ion Battery") - products;
        assert(x == 5 - 1);
        for (int i = 0; i < n; ++i)
            cin >> inc[x][i];
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < n; ++j) {
                g.cost[i][j] = (phone_cost[j] + product_cost[i]) * (100 + inc[i][j]);
            }
        }
        print_cost_matrix();
        double res = g.hungarian();
        printf("%.2lf\n", res / 100.0);
        print_assignment_yx();
        cout << endl;
    }

    return 0;
}