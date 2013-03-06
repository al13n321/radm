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
    static const int MAXN = 128;
    int n;
    int cost[MAXN][MAXN];
    int xy[MAXN], yx[MAXN];
    lng lx[MAXN], ly[MAXN];
    lng slack[MAXN];
    int slackx[MAXN];
    bool S[MAXN], T[MAXN];
    int p[MAXN];

    void update_labels() {
        lng delta = LINF;
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

    int hungarian(int mult = -1) {
        memset(lx, 128, sizeof lx);
        memset(ly, 0, sizeof ly);
        for (int x = 0; x < n; ++x) {
            for (int y = 0; y < n; ++y) {
                cost[x][y] *= mult;
                lx[x] = max(lx[x], (lng)cost[x][y]);
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
                cost[x][y] *= mult;
            }
        }
        int res = 0;
        for (int x = 0; x < n; ++x) {
            if (- 100 < cost[x][xy[x]] && cost[x][xy[x]] < 100)
                res += cost[x][xy[x]];
        }
        return res;
    }

    int greedy_a() {
        clr(S, 0);
        clr(T, 0);
        clr(xy, -1);
        clr(yx, -1);
        int res = 0;
        for (int i = 0; i < n; ++i) {
            int any = -1;
            for (int j = 0; j < n; ++j) {
                if (!T[j] && cost[i][j] == 0) {
                    any = j;
                    break;
                }
            }
            if (any == -1)
                continue;
            S[i] = T[any] = true;
            xy[i] = any;
            yx[any] = i;
            res += cost[i][any];
        }
        for (int i = 0; i < n; ++i) {
            if (S[i])
                continue;
            int any = find(T, T + n, false) - T;
            S[i] = T[any] = true;
            xy[i] = any;
            yx[any] = i;
            res += cost[i][any];
        }
        return res;
    }

    int greedy_b() {
        clr(S, 0);
        clr(T, 0);
        clr(xy, -1);
        clr(yx, -1);
        int res = 0;
        for (int it = 0; it < n; ++it) {
            int best = -1;
            int cnt = INF;
            int mt = -1;
            for (int i = 0; i < n; ++i) {
                if (S[i]) continue;
                int cur = 0;
                int any = -1;
                for (int j = 0; j < n; ++j) {
                    if (!T[j] && cost[i][j] == 0)
                        ++cur, any = j;
                }
                if (cur && cur < cnt)
                    cnt = cur, best = i, mt = any;
            }
            if (best == -1) {
                best = find(S, S + n, false) - S;
            }
            if (mt == -1) {
                mt = find(T, T + n, false) - T;
            }
            res += cost[best][mt];
            xy[best] = mt;
            yx[mt] = best;
            T[mt] = true;
            S[best] = true;
        }
        return res;
    }

    void print_cost_matrix() {
        printf("Emp.\\textbackslash Subtasks.");
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

const int EMPLOYEES = 40;
const int TASKS = 8;
const int SUBTASKS = 80;

graph g;
int subtasks[TASKS];
int first_subtask[TASKS];
int doable[EMPLOYEES][TASKS];
int task_id[SUBTASKS + EMPLOYEES];
int cost[EMPLOYEES][TASKS];

void print(int i, int x = -1) {
    if (x == -1) {
        printf("%d & %d, %d & %d ", i + 1,
            task_id[g.xy[2 * i]] + 1, task_id[g.xy[2 * i + 1]] + 1,
            g.cost[2 * i][g.xy[2 * i]] + g.cost[2 * i + 1][g.xy[2 * i + 1]]);
    } else {
        printf("%d & %d, %d, %d & %d ", i + 1,
            task_id[g.xy[2 * i]] + 1, task_id[g.xy[2 * i + 1]] + 1, task_id[g.xy[x]] + 1,
            g.cost[2 * i][g.xy[2 * i]] + g.cost[2 * i + 1][g.xy[2 * i + 1]] + g.cost[x][g.xy[x]]);
    }
}

void print_assignment_xy(string sub = "Non-doable", vector<int> xs = vector<int>(), vector<int> pos = vector<int>()) {
    printf("Employee & Tasks & %s subtasks & Employee & Tasks & %s subtasks \\\\ \\hline\n",
        sub.c_str(), sub.c_str());
    for (int i = 0; i < EMPLOYEES / 2; ++i) {
        int k;
        k = find(all(xs), i) - xs.begin();
        print(i, k == sz(xs) ? -1 : pos[k]);
        printf("& ");
        int j = i + EMPLOYEES / 2;
        k = find(all(xs), j) - xs.begin();
        print(j, k == sz(xs) ? -1 : pos[k]);
        printf("\\\\\n");
    }
    printf("\\hline\n");
}

void print3(int i) {
    bool first = true;
    int sum = 0;
    for (int j = 0; j < 3; ++j) {
        int x = g.xy[3 * i + j];
        if (task_id[x] != -1) {
            if (!first) printf(", ");
            first = false;
            sum += g.cost[3 * i + j][x];
            printf("%d", task_id[x] + 1);
        }
    }
    if (first)
        printf("- & -");
    else
        printf(" & %d", sum);
}

void print_assignment_xy3(string sub = "Non-doable") {
    printf("Employee & Tasks & %s subtasks & Employee & Tasks & %s subtasks \\\\ \\hline\n",
        sub.c_str(), sub.c_str());
    for (int i = 0; i < EMPLOYEES / 2; ++i) {
        printf("%d & ", i + 1);
        print3(i);
        printf(" & ");
        int j = i + EMPLOYEES / 2;
        printf("%d & ", j + 1);
        print3(j);
        printf(" \\\\\n");
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
    for (int i = 0, j = 0; i < TASKS; ++i) {
        int sub, days;
        cin >> sub >> days;
        subtasks[i] = sub * days;
        first_subtask[i] = j;
        for (int it = subtasks[i]; it--; )
            task_id[j++] = i;
    }
    for (int i = 0; i < EMPLOYEES; ++i) {
        int x, t;
        cin >> x >> t;
        --x;
        assert(t == -2);
        for (; (cin >> t) && t != -2; ) {
            if (t != -1) {
                --t;
                doable[x][t] = true;
            }
        }
    }
    for (int i = 0; i < EMPLOYEES; ++i) {
        int x;
        cin >> x;
        --x;
        for (int j = 0; j < TASKS; ++j)
            cin >> cost[x][j];
    }

    {
        cout << "4.3 a)\n";
        g.n = SUBTASKS;
        for (int i = 0; i < EMPLOYEES; ++i) {
            for (int j = 0; j < SUBTASKS; ++j) {
                g.cost[2 * i][j] = g.cost[2 * i + 1][j] = !doable[i][task_id[j]];
            }
        }
        int res = g.greedy_a();
        cout << res << endl;
        print_assignment_xy();
        cout << endl;
    }

    {
        cout << "4.3 b)\n";
        g.n = SUBTASKS;
        for (int i = 0; i < EMPLOYEES; ++i) {
            for (int j = 0; j < SUBTASKS; ++j) {
                g.cost[2 * i][j] = g.cost[2 * i + 1][j] = !doable[i][task_id[j]];
            }
        }
        int res = g.greedy_b();
        cout << res << endl;
        print_assignment_xy();
        cout << endl;
    }

    {
        cout << "4.3 c)\n";
        g.n = SUBTASKS;
        for (int i = 0; i < EMPLOYEES; ++i) {
            for (int j = 0; j < SUBTASKS; ++j) {
                g.cost[2 * i][j] = g.cost[2 * i + 1][j] = !doable[i][task_id[j]];
            }
        }
        int res = g.hungarian();
        cout << res << endl;
        print_assignment_xy();
        cout << endl;
    }

    {
        cout << "4.3 d)\n";
        g.n = SUBTASKS;
        for (int i = 0; i < EMPLOYEES; ++i) {
            for (int j = 0; j < SUBTASKS; ++j) {
                g.cost[2 * i][j] = g.cost[2 * i + 1][j] = cost[i][task_id[j]];
            }
        }
        int res = g.hungarian(+1);
        cout << res << endl;
        print_assignment_xy("Sum of preferences of");
        cout << endl;
    }

    {
        cout << "4.3 e)\n";
        g.n = SUBTASKS + 2;
        task_id[SUBTASKS] = task_id[SUBTASKS + 1] = 4 - 1;
        for (int i = 0; i < EMPLOYEES; ++i) {
            for (int j = 0; j < SUBTASKS + 2; ++j) {
                g.cost[2 * i][j] = g.cost[2 * i + 1][j] = cost[i][task_id[j]];
            }
        }
        int res = - INF;
        vector<int> xs;
        for (int i = 0; i < EMPLOYEES; ++i) {
            for (int j = i + 1; j < EMPLOYEES; ++j) {
                memcpy(g.cost[g.n - 2], g.cost[2 * i], sizeof g.cost[g.n - 2]);
                memcpy(g.cost[g.n - 1], g.cost[2 * j], sizeof g.cost[g.n - 1]);
                int cur = g.hungarian(+1);
                if (cur > res) {
                    xs.clear();
                    xs.pb(i), xs.pb(j);
                    res = cur;
                }
            }
        }
        cout << res << endl;
        cout << xs[0] + 1 << ' ' << xs[1] + 1 << endl;
        vector<int> pos;
        pos.pb(g.n - 2), pos.pb(g.n - 1);
        print_assignment_xy("Sum of preferences of", xs, pos);
        cout << endl;
    }

    {
        cout << "4.3 g)\n";
        g.n = EMPLOYEES * 3;
        vector<int> xs, pos;
        pos.pb(15 - 1), pos.pb(29 - 1), pos.pb(35 - 1);
        for (int i = 0; i < EMPLOYEES; ++i) {
            for (int j = 0; j < SUBTASKS; ++j) {
                if (count(all(pos), i) == 0)
                    g.cost[3 * i][j] = g.cost[3 * i + 1][j] = g.cost[3 * i + 2][j] = cost[i][task_id[j]];
                else
                    g.cost[3 * i][j] = g.cost[3 * i + 1][j] = g.cost[3 * i + 2][j] = - INF;
            }
            for (int j = SUBTASKS; j < g.n; ++j) {
                task_id[j] = -1;
                g.cost[3 * i][j] = g.cost[3 * i + 1][j] = g.cost[3 * i + 2][j] = j - SUBTASKS == i ? - INF / 100000 : - INF;
            }
        }
        int res = g.hungarian(+1);        
        cout << res << endl;
        print_assignment_xy3("Sum of preferences of");
        cout << endl;
    }

    {
        cout << "4.3 h)\n";
        g.n = SUBTASKS;
        for (int i = 0; i < EMPLOYEES; ++i) {
            for (int j = 0; j < SUBTASKS; ++j) {
                g.cost[2 * i][j] = g.cost[2 * i + 1][j] = cost[i][task_id[j]];
            }
        }
        int x = 2 - 1;
        int y = 6 - 1;
        for (int val = 1; val <= 10; ++val) {
            for (int j = first_subtask[y]; j < first_subtask[y] + subtasks[y]; ++j) {
                g.cost[2 * x][j] = g.cost[2 * x + 1][j] = val;
            }
            int res = g.hungarian(+1);
            printf("%d & %d & %d, %d \\\\\n", val, res, task_id[g.xy[2 * x]] + 1, task_id[g.xy[2 * x + 1]] + 1);
        }
        cout << endl;
    }

    return 0;
}