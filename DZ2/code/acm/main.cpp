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

struct edge{
	int to,back,cap,cost,flo;
	edge(int to,int back,int cap,int cost,int flo):to(to),back(back),cap(cap),cost(cost),flo(flo){}
};

struct graph{
	vector<vector<edge> > gr;
	int n;
	int S,T;
	
	void init(int nn){
		n=nn;
		gr.clear();
		gr.resize(n);
	}
	
	void add_edge(int from,int to,int cap,int cost){
		edge e1(to,sz(gr[to]),cap,cost,0);
		edge e2(from,sz(gr[from]),0,-cost,0);
		gr[from].pb(e1);
		gr[to].pb(e2);
	}
	
	PII augment(){
		vector<pair<PII,int> > dist(n,mp(mp(INF,0),-1));
		dist[S]=mp(mp(0,INF),-1);
		bool changed=true;
		forn(qqq,n){
			changed=false;
			forn(v,n){
				if(dist[v].X.X==INF)
					continue;
				forv(i,gr[v]){
					edge e=gr[v][i];
					if(e.flo>e.cap)
						exit(66);
					if(e.flo==e.cap)
						continue;
					pair<PII,int> t = mp(mp(dist[v].X.X+e.cost, min(dist[v].X.Y,e.cap-e.flo)), e.back);
					if(t.X.X<dist[e.to].X.X){
						dist[e.to]=t;
						changed=true;
					}
				}
			}
			if(!changed)
				break;
		}
		if(changed)
			exit(55);
		if(dist[T].X.X==INF)
			return mp(0,0);
		
		int mn=dist[T].X.Y;
		int v=T;
		int res=0;
		while(v!=S){
			edge &e2=gr[v][dist[v].Y];
			v=e2.to;
			edge &e1=gr[v][e2.back];
			e1.flo+=mn;
			e2.flo-=mn;
			res+=e1.cost*mn;
		}
		return mp(mn,res);
	}
	
	PII min_cost_max_flow(){
		PII res(0,0);
		while(true){
			PII t=augment();
			if(!t.X)
				break;
			res.X+=t.X;
			res.Y+=t.Y;
		}
		return res;
	}
	
	void read(){
		string s;
		cin>>s;
		if(s!="network")
			exit(44);
		int m;
		cin>>n>>m;
		cin>>s;
		if(s!="vertices")
			exit(44);
		n+=2;
		S=0;
		T=n-1;
		init(n);
		for(int i=1;i<=n-2;++i){
			int c;
			cin>>c;
			if(c<0)
				add_edge(i,T,-c,0);
			if(c>0)
				add_edge(S,i,c,0);
		}
		cin>>s;
		if(s!="edges")
			exit(44);
		forn(i,m){
			int a,b,c;
			cin>>a>>b>>c;
			add_edge(a,b,INF,c);
		}
		cin>>s;
		if(s!="end")
			exit(44);
	}
	
	void read2(){
		string s;
		cin>>s;
		if(s!="network")
			exit(44);
		int m;
		cin>>n>>m;
		init(n);
		S=0;
		T=n-1;
		cin>>s;
		if(s!="edges")
			exit(44);
		forn(i,m){
			int a,b;
			cin>>a>>b;
			add_edge(a,b,1,0);
		}
		cin>>s;
		if(s!="end")
			exit(44);
	}
	
	void write_as_paths(map<int,string> name_map = (map<int,string>())){
		cout<<"paths:"<<endl;
		while(true){
			int v=S;
			vector<PII> path;
			int mn=INF;
			while(v!=T){
				int i=0;
				while(i<sz(gr[v]) && gr[v][i].flo<=0)
					++i;
				if(i==sz(gr[v])){
					if(v==S)
						break;
					else
						exit(12);
				}
				path.pb(mp(v,i));
				edge &e=gr[v][i];
				mn=min(mn,e.flo);
				v=e.to;
			}
			if(v==S)
				break;
			int sum=0;
			forv(q,path){
				edge &e1=gr[path[q].X][path[q].Y];
				e1.flo-=mn;
				sum+=e1.cost*mn;
			}
			
			cout<<"$ ";
			for(int i=1;i<sz(path);++i){
				if(i>1)
					cout<<" \\rightarrow ";
				int v=path[i].X;
				if (name_map.count(v))
					cout<<name_map[v];
				else
					cout<<v;
			}
			cout<<" $ & "<<mn<<" & \\texteuro "<<sum<<"\\\\ \\hline"<<endl;
		}
		cout<<endl;
	}
	
	void write_as_edges(PII flow, bool assert_tree=false, bool assert_saturated_sink=true){
		cout<<"flow: "<<flow.X<<", cost: "<<flow.Y<<", edges:"<<endl;
		vector<int> cnt_in(n,0);
		bool sink_ok=true;
		forn(v,n){
			if(v==S)
				continue;
			forv(i,gr[v]){
				const edge &e=gr[v][i];
				if(e.to==T && assert_saturated_sink && e.flo!=e.cap)
					sink_ok=false;
				if(e.to==T || e.flo<=0)
					continue;
				cout<<"$ "<<v<<" \\rightarrow "<<e.to<<" $ : "<<e.flo<<endl;
				++cnt_in[e.to];
			}
		}
		if(!sink_ok)
			cout<<"sink not saturated!"<<endl;
		forn(i,n){
			if(assert_tree && cnt_in[i]>1){
				cout<<"duplicate "<<i<<endl;
			}
		}
		cout<<endl;
	}
	
	void write_mincut(){
		vector<bool> reach(n,false);
		reach[S]=true;
		vector<int> st;
		st.pb(S);
		while(!st.empty()){
			int v=st.back();
			st.pop_back();
			forv(i,gr[v]){
				if(gr[v][i].flo<gr[v][i].cap && !reach[gr[v][i].to]){
					reach[gr[v][i].to]=true;
					st.pb(gr[v][i].to);
				}
			}
		}
		cout<<"cut:"<<endl;
		forn(v,n){
			forv(i,gr[v]){
				edge e=gr[v][i];
				if(e.cap>0 && reach[v] && !reach[e.to])
					cout<<v<<" --- "<<e.to<<endl;
			}
		}
		cout<<endl;
	}
	
	void make_bidirectional(){
		vector<pair<PII,int> > es;
		forn(v,n){
			if(v==S || v==T)
				continue;
			forv(i,gr[v]){
				edge e=gr[v][i];
				if(e.to==T || !e.cap)
					continue;
				es.pb(mp(mp(v,e.to),e.cost));
			}
		}
		forv(i,es){
			int a=es[i].X.X;
			int b=es[i].X.Y;
			int c=es[i].Y;
			add_edge(b,a,INF,c);
		}
	}
	
	void increase_capacity_from_source(){
		forv(i,gr[S]){
			gr[S][i].cap=INF;
		}
	}
	
	void write_flow_from_source(){
		cout<<"flows from source:"<<endl;
		forv(i,gr[S]){
			cout<<gr[S][i].flo<<' ';
		}
		cout<<endl<<"residuals from source:"<<endl;
		forv(i,gr[S]){
			cout<<gr[S][i].cap-gr[S][i].flo<<' ';
		}
		cout<<endl<<endl;
	}
	
	int flow_through(int from, int to){
		forv(i,gr[from]){
			if(gr[from][i].to==to)
				return gr[from][i].flo;
		}
		exit(32);
	}
	
	void set_capacity(int from, int to, int cap){
		forv(i,gr[from]){
			if(gr[from][i].to==to){
				gr[from][i].cap=cap;
				return;
			}
		}
		exit(34);
	}
	
	void reverse_edge(int from, int to){
		forv(i,gr[from]){
			if(gr[from][i].to==to){
				edge &e1=gr[from][i];
				edge &e2=gr[to][e1.back];
				swap(e1.cap,e2.cap);
				swap(e1.cost,e2.cost);
				return;
			}
		}
		exit(34);
	}
};

int upper_tolerance(graph gr0, int from, int to){
	graph gr=gr0;
	PII flow0=gr.min_cost_max_flow();
	int f=gr.flow_through(from, to);
	if(!f)
		return INF;
	gr=gr0;
	gr.set_capacity(from, to, f-1);
	PII flow1=gr.min_cost_max_flow();
	if(flow0.X!=flow1.X)
		return -1;
	return flow1.Y-flow0.Y;
}

void open_files(string s){
	freopen((s+"_in.txt").c_str(),"r",stdin);
	freopen((s+"_out.txt").c_str(),"w",stdout);
}

void do_31(){
	open_files("31");
	
	graph gr0;
	gr0.read();
	
	graph gr=gr0;
	cout<<"(a)"<<endl;
	gr.write_as_edges(gr.min_cost_max_flow());
	gr.write_flow_from_source();
	gr.write_as_paths();
	
	string s;
	cin>>s;
	if(s!="edge_queries")
		exit(10);
	int c;
	cin>>c;
	cout<<"(b)"<<endl;
	forn(i,c){
		int from,to;
		cin>>from>>to;
		int t=upper_tolerance(gr0, from, to);
		cout<<"$ "<<from<<" \\rightarrow "<<to<<" $ & "<<t<<"\\\\ \\hline"<<endl;
	}
	cout<<endl;
	
	gr=gr0;
	gr.reverse_edge(33, 34);
	cout<<"(c)"<<endl;
	gr.write_as_edges(gr.min_cost_max_flow());
	gr.write_as_paths();
}

void do_32(){
	open_files("32");
	
	map<int,string> name_map;
	name_map[45]='A';
	name_map[46]='B';
	name_map[47]='C';
	name_map[48]='D';
	name_map[49]='E';
	name_map[50]='F';
	
	graph gr0;
	gr0.read();
	
	graph gr=gr0;
	cout<<"(a)"<<endl;
	gr.write_as_edges(gr.min_cost_max_flow());
	gr.write_as_paths(name_map);
	
	cout<<"(c)"<<endl;
	gr=gr0;
	gr.increase_capacity_from_source();
	gr.write_as_edges(gr.min_cost_max_flow(), true);
	gr.write_flow_from_source();
	gr.write_as_paths(name_map);
	
	gr=gr0;
	gr.make_bidirectional();
	cout<<"(?)"<<endl;
	gr.write_as_edges(gr.min_cost_max_flow());
	gr.write_as_paths(name_map);
}

void do_36(){
	open_files("36");
	
	graph gr0;
	gr0.read2();
	
	graph gr=gr0;
	gr.min_cost_max_flow();
	gr.write_mincut();
	
	gr=gr0;
	gr.reverse_edge(32, 25);
	gr.min_cost_max_flow();
	gr.write_mincut();
}

int main() {

	do_31();
	do_32();
	do_36();

	return 0;
}
