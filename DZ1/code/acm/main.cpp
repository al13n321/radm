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

const double EPS = 1e-10;
const int INF = 1000*1000*1000;
const lng LINF = INF * 1ll * INF;
const ld PI = 3.1415926535897932384626433832795;

typedef vector<vector<lng> > graph;

int n;

graph read_graph(){
	int m;
	cin>>m;
	graph gr(n, vector<lng>(n, LINF));
	forn(i,m){
		int a,b;
		string s;
		cin>>a>>b>>s;
		--a;--b;
		if(sz(s) != 3 || !isdigit(s[0]) || !isdigit(s[2]) || s[1] != '.' || a < 0 || b <= a || b >= n)
			exit(55);
		lng w=(s[0]-'0')*10 + s[2]-'0';
		if(gr[a][b] != LINF)
			exit(44);
		gr[a][b] = gr[b][a] = w;
	}
	return gr;
}

void print_diff(graph a, graph b){
	forn(i,n){
		forn(j,i){
			if((a[i][j]==LINF) != (b[i][j]==LINF)){
				cout<<j<<' '<<i<<endl;
			}
		}
	}
}

typedef vector<vector<PLL> > floyd;

floyd do_floyd(graph gr){
	floyd res(n,vector<PLL>(n, mp(LINF, 0)));
	forn(i,n){
		forn(j,n){
			res[i][j]=mp(gr[i][j],j);
		}
		res[i][i]=mp(0, -1);
	}
	forn(k,n){
		forn(i,n){
			forn(j,n){
				if(res[i][k].X != LINF && res[k][j].X != LINF && res[i][k].X+res[k][j].X < res[i][j].X)
					res[i][j]=mp(res[i][k].X+res[k][j].X,res[i][k].Y);
			}
		}
	}
	forn(i,n){
		if(res[i][i].X<0){
			cout<<"negative cycle through "<<i+1<<endl;
			int v=i;
			forn(qqq,15){
				if(v==-1)
					break;
				cout<<v+1<<' ';
				v=res[v][i].Y;
			}
			exit(31);
		}
	}
	return res;
}

typedef vector<int> path;

path get_path(floyd f, int from, int to){
	path res;
	int v=from;
	while(v != to){
		res.pb(v);
		v=f[v][to].Y;
	}
	res.pb(v);
	return res;
}

lng path_weight(graph gr, path p){
	lng r=0;
	forn(i,sz(p)-1){
		lng t=gr[p[i]][p[i+1]];
		if(t==LINF)
			exit(64);
		r+=t;
	}
	return r;
}

path read_path(){
	path res;
	while(true){
		int v;
		cin>>v;
		if(!v)
			break;
		--v;
		if(v<0 || v>=n)
			exit(91);
		res.pb(v);
	}
	return res;
}

void print_path(graph gr, path p, bool tex=false){
	if(tex)
		cout<<"$ ";
	forv(i,p){
		if(tex && i)
			cout<<"\\rightarrow ";
		cout<<p[i]+1<<' ';
	}
	if(tex)
		cout<<"$";
	lng len=0;
	forn(i,sz(p)-1){
		lng t=gr[p[i]][p[i+1]];
		if(t==LINF)
			exit(36);
		len+=t;
	}
	cout<<"  (length "<<len<<")"<<endl;
}

void open_files(string name){
	freopen((name + "_in.txt").c_str(), "r", stdin);
	freopen((name + "_out.txt").c_str(), "w", stdout);
}

void do_11_14(){
	n=50;
	open_files("11_14");
	
	graph gr=read_graph();
	floyd fl=do_floyd(gr);
	
	int m;
	cin>>m;
	forn(qqq,2){
		if(qqq==0)
			cout<<"Slava:"<<endl;
		else
			cout<<"Mike:"<<endl;
		forn(i,m){
			path p=read_path();
			path q=get_path(fl, p[0], p.back());
			cout<<"your path: ";
			print_path(gr, p);
			cout<<"shortest: ";
			print_path(gr, q);
		}
		cout<<endl;
	}
	
	graph gr0=gr;
	
	cout<<endl<<"1.4:"<<endl<<endl;
	cin>>m;
	forn(q,m){
		path p;
		p=read_path();
		forn(i,sz(p)-1){
			int a=p[i];
			int b=p[i+1];
			if(gr[b][a]==LINF)
				exit(90);
			gr[b][a]=LINF;
		}
	}
	
	graph gr1=gr;
	
	cin>>m;
	forn(q,m){
		int a,b,c;
		cin>>a>>b>>c;
		--a;--b;
		if(a<0||a>=n||b<0||b>=n)
			exit(5);
		gr[a][b]-=c;
	}
	
	int from,to;
	cin>>from>>to;
	--from;--to;
	
	fl=do_floyd(gr);
	path p=get_path(fl, from, to);
	cout<<"(a) ";
	print_path(gr, p);
	
	cin>>m;
	forn(q,m){
		int a,b,c;
		cin>>a>>b>>c;
		--a;--b;
		if(a<0||a>=n||b<0||b>=n)
			exit(5);
		gr[a][b]-=c;
	}
	
	cout<<"(b), (c) ";
	print_path(gr, read_path());
	
	int from2,to2;
	cin>>from2>>to2;
	--from2;--to2;
	
	fl=do_floyd(gr1);
	cout<<"(d):"<<endl;
	path p1=get_path(fl, from, to);
	print_path(gr, p1);
	forn(i,sz(p1)-1){
		int a=p1[i];
		int b=p1[i+1];
		gr[a][b]=gr0[a][b];
	}
	path p2=get_path(fl, from2, to2);
	print_path(gr, p2);
}

bool on_path(path p, int a, int b){
	forn(i,sz(p)-1){
		if((p[i]==a && p[i+1]==b) || (p[i]==b && p[i+1]==a))
			return true;
	}
	return false;
}

pair<lng,path> shortest_path_through(graph gr, floyd fl, int from, int to, vector<PII> edges){
	int m=sz(edges);
	sort(all(edges));
	pair<lng,path> res=mp(LINF,path());
	do{
		forn(msk, 1<<m){
			path p;
			forn(i,m+1){
				int v1=i?((msk&(1<<(i-1)))?edges[i-1].X:edges[i-1].Y):from;
				int v2=i<m?((msk&(1<<i))?edges[i].Y:edges[i].X):to;
				path t=get_path(fl, v1, v2);
				p.insert(p.end(), all(t));
			}
			lng r=path_weight(gr, p);
			res=min(res,mp(r,p));
		}
	}while(next_permutation(all(edges)));
	return res;
}

lng lower_tolerance(graph gr, floyd f, int from, int to, int a, int b){
	return shortest_path_through(gr, f, from, to, vector<PII>(1, mp(a,b))).X - f[from][to].X;
}

lng upper_tolerance(graph gr, int from, int to, int a, int b){
	floyd f1=do_floyd(gr);
	gr[a][b]=gr[b][a]=LINF;
	floyd f2=do_floyd(gr);
	return f2[from][to].X-f1[from][to].X;
}

vector<path> three_paths(graph gr, int from, int to, vector<PII> edges){
	floyd f0=do_floyd(gr);
	pair<lng,path> p0=shortest_path_through(gr, f0, from, to, edges);
	pair<lng,path> p1(LINF,path());
	forn(i,sz(p0.Y)-1){
		int a=p0.Y[i];
		int b=p0.Y[i+1];
		if(count(all(edges),mp(a,b)) || count(all(edges),mp(b,a)))
			continue;
		graph gr1=gr;
		gr1[a][b]=gr1[b][a]=LINF;
		floyd f=do_floyd(gr1);
		pair<lng,path> p=shortest_path_through(gr1, f, from, to, edges);
		p1=min(p1,p);
	}
	pair<lng,path> p2(LINF,path());
	forn(i,sz(p0.Y)-1){
		int a0=p0.Y[i];
		int b0=p0.Y[i+1];
		if(count(all(edges),mp(a0,b0)) || count(all(edges),mp(b0,a0)))
			continue;
		forn(j,sz(p1.Y)-1){
			int a1=p1.Y[j];
			int b1=p1.Y[j+1];
			if(count(all(edges),mp(a1,b1)) || count(all(edges),mp(b1,a1)))
				continue;
			graph gr1=gr;
			gr1[a0][b0]=gr1[b0][a0]=gr1[a1][b1]=gr1[b1][a1]=LINF;
			floyd f=do_floyd(gr1);
			pair<lng,path> p=shortest_path_through(gr1, f, from, to, edges);
			p2=min(p2,p);
		}
	}
	vector<path> res;
	res.pb(p0.Y);
	res.pb(p1.Y);
	res.pb(p2.Y);
	return res;
}

void do_12(){
	n=50;
	open_files("12");
	
	graph gr=read_graph();
	floyd fl=do_floyd(gr);
	
	int m;
	cin>>m;
	forn(qqq,m){
		path p=read_path();
		int from=p[0];
		int to=p.back();
		p=get_path(fl, from, to);
		
		cout<<"(a) shortest path: ";
		print_path(gr, p, true);
		
		int a=8-1;
		int b=10-1;
		if(on_path(p, a, b)){
			cout<<"(b) 8-10 range: $ [-\\infty, "<<gr[a][b]+upper_tolerance(gr, from, to, a, b)<<"] $"<<endl;
		}else{
			cout<<"(b) 8-10 range: $ ["<<gr[a][b]-lower_tolerance(gr, fl, from, to, a, b)<<", +\\infty] $"<<endl;
		}
		
		cout<<"(d) upper tolerances:"<<endl;
		lng min_t=LINF;
		int zero_i=-1;
		forn(i,sz(p)-1){
			lng t=upper_tolerance(gr, from, to, p[i], p[i+1]);
			min_t=min(min_t,t);
			if(t==0)
				zero_i=i;
			if(t<0)
				exit(29);
			cout<<p[i]+1<<'-'<<p[i+1]+1<<": "<<t<<endl;
		}
		cout<<"min tolerance: "<<min_t<<"; path "<<(min_t?"":"not ")<<"unique"<<endl;
		if(min_t==0){
			cout<<"alternative path:"<<endl;
			int a=p[zero_i];
			int b=p[zero_i+1];
			graph gr2=gr;
			gr2[a][b]=gr2[b][a]=LINF;
			floyd f2=do_floyd(gr2);
			path p2=get_path(f2, from, to);
			print_path(gr, p2, true);
		}
		cout<<endl;
	}
	
	{
		int from=8-1;
		int to=31-1;
		vector<path> ps=three_paths(gr, from, to, vector<PII>());
		cout<<"(f) paths:"<<endl;
		forn(q,2){
			print_path(gr, ps[q], true);
		}
		cout<<"upper tolerances:"<<endl;
		forn(i,sz(ps[0])-1){
			lng t=upper_tolerance(gr, from, to, ps[0][i], ps[0][i+1]);
			if(t<0)
				exit(27);
			cout<<ps[0][i]+1<<'-'<<ps[0][i+1]+1<<": "<<t<<endl;
		}
		cout<<endl;
	}
	
	cout<<"(g):"<<endl;
	cin>>m;
	forn(qqq,m){
		int from,to;
		cin>>from>>to;
		--from;--to;
		vector<PII> inc;
		while(true){
			int a,b;
			cin>>a;
			if(!a)
				break;
			cin>>b;
			--a;--b;
			inc.pb(mp(a,b));
		}
		vector<path> ps=three_paths(gr, from, to, inc);
		string s;
		cin>>s;
		cout<<from+1<<" to "<<to+1<<":"<<endl;
		forn(q,s=="+"?3:1){
			print_path(gr, ps[q], true);
		}
	}
}

void print_13(graph gr, int n, int mx){
	floyd f=do_floyd(gr);
	pair<lng,path> res(LINF,path());
	forn(j,mx+1){
		if(f[0][n*(mx+1)+j].X!=LINF)
			res=min(res,mp(f[0][n*(mx+1)+j].X,get_path(f,0,n*(mx+1)+j)));
	}
	
	print_path(gr, res.Y, false);
	
	vector<int> ans(n,0);
	forn(i,sz(res.Y)-1){
		int v1=res.Y[i];
		int v2=res.Y[i+1];
		if(v1/(mx+1)==v2/(mx+1))
			continue;
		ans[v1/(mx+1)]=v1%(mx+1);
	}
	
	cout<<endl;
	forn(i,n){
		cout<<ans[i]<<" & ";
	}
	cout<<endl<<endl;
}

void do_13() {
	open_files("13");
	
	int n;
	cin>>n;
	int mx=0;
	vector<int> src(n);
	forn(i,n){
		cin>>src[i];
		mx=max(mx,src[i]);
	}
	int N=(n+1)*(mx+1);
	graph gr(N,vector<lng>(N,LINF));
	forn(i,n){
		forn(j,mx){
			gr[i*(mx+1)+j][i*(mx+1)+j+1]=8000;
			gr[i*(mx+1)+j+1][i*(mx+1)+j]=24000;
		}
		forn(j,mx+1){
			if(j>=src[i])
				gr[i*(mx+1)+j][(i+1)*(mx+1)+j]=(32000-1)*max(0,j-src[i]);
		}
	}
	
	::n=N;
	print_13(gr, n, mx);
	
	const int is[2]={2,5};
	forn(ii,2){
		int i=is[ii];
		for(int j=src[i]+1;j<=mx;++j){
			gr[i*(mx+1)+j][(i+1)*(mx+1)+j]=LINF;
		}
	}
	
	print_13(gr, n, mx);
}

int main() {

	//do_11_14();
	//do_12();
	do_13();

	return 0;
}
