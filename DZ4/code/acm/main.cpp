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

struct graph{
	int n;
	vector<vector<int> > gr0;
	vector<vector<PII> > gr;
	vector<vector<PII> > dp;
	
	void copy_gr(){
		gr.resize(n,vector<PII>(n));
		forn(i,n){
			forn(j,n){
				gr[i][j]=mp(gr0[i][j],i);
			}
		}
	}
	
	void read_list(){
		cin>>n;
		gr0.resize(n,vector<int>(n,INF));
		int m;
		cin>>m;
		forn(i,n){
			gr0[i][i]=0;
		}
		forn(i,m){
			char a,b;
			int c;
			cin>>a>>b>>c;
			a-='A';
			b-='A';
			if(gr0[a][b]!=INF)
				exit(32);
			gr0[a][b]=c;
		}
		forn(i,n){
			forn(j,i){
				if(gr0[i][j]!=gr0[j][i])
					exit(5);
			}
		}
		copy_gr();
	}
	
	void read_table(){
		cin>>n;
		gr0.resize(n,vector<int>(n,INF));
		forn(i,n){
			forn(j,n){
				cin>>gr0[i][j];
			}
		}
		copy_gr();
	}
	
	void floyd(){
		forn(k,n){
			forn(i,n){
				forn(j,n){
					if(gr[i][k].X+gr[k][j].X<gr[i][j].X)
						gr[i][j]=mp(gr[i][k].X+gr[k][j].X,gr[k][j].Y);
				}
			}
		}
	}
	
	void do_dp(bool cycle=true,int from=-1){
		dp.resize(1<<n,vector<PII>(n,mp(INF,-1)));
		if(cycle){
			dp[0][0]=mp(0,-1);
		} else {
			forn(i,n){
				if(from==-1 || i==from)
					dp[1<<i][i]=mp(0,-1);
			}
		}
		forn(msk,1<<n){
			forn(v,n){
				if(dp[msk][v].X==INF)
					continue;
				forn(k,n){
					if(msk&(1<<k))
						continue;
					int t=dp[msk][v].X+gr[v][k].X;
					int msk2=msk|(1<<k);
					if(t<dp[msk2][k].X){
						dp[msk2][k]=mp(t,v);
					}
				}
			}
		}
	}
	
	vector<int> get_path(int from, int to){
		vector<int> res;
		while(to!=from){
			res.pb(to);
			to=gr[from][to].Y;
		}
		res.pb(to);
		reverse(all(res));
		return res;
	}
	
	vector<int> full_path(vector<int> p){
		vector<int> res;
		forn(i,sz(p)-1){
			vector<int> t=get_path(p[i],p[i+1]);
			t.pop_back();
			res.insert(res.end(),all(t));
		}
		res.pb(p.back());
		return res;
	}
	
	int path_weight(vector<int> p){
		int r=0;
		forn(i,sz(p)-1){
			if(gr0[p[i]][p[i+1]]==INF || p[i]==p[i+1])
				exit(66);
			r+=gr0[p[i]][p[i+1]];
		}
		return r;
	}
	
	vector<int> path_from_dp(int msk, int v){
		if(dp[msk][v].X==INF)
			exit(55);
		int s=dp[msk][v].X;
		vector<int> res;
		while(msk){
			if(!(msk&(1<<v)))
				exit(66);
			int p=dp[msk][v].Y;
			res.pb(v);
			msk^=1<<v;
			v=p;
		}
		if(v != -1 && (res.empty() || v!=res.back()))
			res.pb(v);
		reverse(all(res));
		if(path_weight(full_path(res))!=s)
			exit(4);
		return res;
	}
	
	vector<int> min_path_from_dp(int from=-1){
		int mn=INF;
		vector<int> res;
		forn(v,n){
			if(from != -1 && v==from)
				continue;
			vector<int> p=path_from_dp((1<<n)-1,v);
			int w=path_weight(p);
			if (w<mn){
				mn=w;
				res=p;
			}
		}
		return res;
	}
	
	vector<int> nearest_insertion_route(int v0){
		vector<int> res(1,v0);
		int s=0;
		while(sz(res)<n){
			pair<int,PII> best(INF,mp(-1,-1));
			forn(v,n){
				bool ok=true;
				pair<int,PII> sub=best;
				forv(j,res){
					int a=res[j];
					int b=res[(j+1)%sz(res)];
					ok &= a!=v;
					int t=gr[a][v].X+gr[v][b].X-gr[a][b].X;
					sub=min(sub,mp(t,mp(v,j)));
				}
				if(ok)
					best=sub;
			}
			if(best.X==INF)
				exit(23);
			res.insert(res.begin()+best.Y.Y+1,best.Y.X);
			s+=best.X;
		}
		res.pb(res[0]);
		if(path_weight(full_path(res))!=s)
			exit(9);
		return res;
	}
	
	vector<int> nearest_neighbour_path(int v0){
		vector<int> res(1,v0);
		vector<bool> was(n,false);
		was[v0]=true;
		while(sz(res)<n){
			PII mn(INF,INF);
			forn(v,n){
				if(!was[v])
					mn=min(mn, mp(gr0[res.back()][v],v));
			}
			int v=mn.Y;
			res.pb(v);
			was[v]=true;
		}
		return res;
	}
	
	vector<int> two_opt_cycle(vector<int> p){
		int v0=p[0];
		p.pop_back();
		while(true){
			p.pb(p[0]);
			int s=path_weight(full_path(p));
			p.pop_back();
			bool found=false;
			forn(q,sz(p)){
				for(int i=0;i+2<=sz(p);++i){
					for(int j=i+2;j<=sz(p);++j){
						reverse(p.begin()+i,p.begin()+j);
						p.pb(p[0]);
						int t=path_weight(full_path(p));
						p.pop_back();
						if(t<s){
							found=true;
							s=t;
						}else{
							reverse(p.begin()+i,p.begin()+j);
						}
					}
				}
				rotate(p.begin(),p.begin()+1,p.end());
			}
			if(!found)
				break;
		}
		while(p[0]!=v0)
			rotate(p.begin(),p.begin()+1,p.end());
		p.pb(p[0]);
		return p;
	}
	
	void two_cycles(int limit, vector<int> &p1, vector<int> &p2){
		int mn=INF;
		forn(msk1,1<<n){
			if(!(msk1&1))
				continue;
			int msk2=((1<<n)-1)^msk1;
			msk2|=1;
			int w1=dp[msk1][0].X;
			int w2=dp[msk2][0].X;
			if(w1>limit || w2>limit)
				continue;
			if(w1+w2<mn){
				mn=w1+w2;
				p1=path_from_dp(msk1, 0);
				p2=path_from_dp(msk2, 0);
				if(w1!=path_weight(full_path(p1)) || w2!=path_weight(full_path(p2)))
					exit(30);
			}
		}
	}
	
	void two_paths(int limit, vector<int> &p1, vector<int> &p2){
		int mn=INF;
		forn(msk1,1<<n){
			if(msk1&1)
				continue;
			int msk2=((1<<n)-1)^msk1;
			msk2&=~1;
			forn(v1,n){
				if(!(msk1&(1<<v1)))
					continue;
				forn(v2,n){
					if(!(msk2&(1<<v2)))
						continue;
					int w1=dp[msk1][v1].X;
					int w2=dp[msk2][v2].X;
					if(w1>limit || w2>limit)
						continue;
					if(w1+w2<mn){
						mn=w1+w2;
						p1=path_from_dp(msk1, v1);
						p2=path_from_dp(msk2, v2);
						if(w1!=path_weight(full_path(p1)) || w2!=path_weight(full_path(p2)))
							exit(30);
					}
				}
			}
		}
	}
	
	void euler(int v,vector<vector<int> > &cnt,vector<int> &res){
		forn(i,n){
			while(cnt[v][i]){
				--cnt[v][i];
				--cnt[i][v];
				euler(i,cnt,res);
			}
		}
		res.pb(v);
	}
	
	vector<int> min_edge_covering_cycle(){
		vector<vector<int> > gr2(n,vector<int>(n,0));
		int msk0=0;
		int dist0=0;
		forn(i,n){
			forn(j,i){
				if(gr0[i][j]!=INF){
					gr2[i][j]=gr2[j][i]=1;
					msk0^=(1<<i)^(1<<j);
					dist0+=gr0[i][j];
				}
			}
		}
		vector<int> dist(1<<n,INF);
		vector<bool> done(1<<n,false);
		vector<PII> last(1<<n);
		dist[msk0]=dist0;
		priority_queue<pair<int,int> > qu;
		qu.push(mp(-dist[msk0],msk0));
		while(!qu.empty()){
			int msk;
			do{
				msk=qu.top().Y;
				qu.pop();
			}while(!qu.empty() && done[msk]);
			if(done[msk])
				break;
			done[msk]=true;
			forn(i,n){
				forn(j,i){
					int w=gr0[i][j];
					if(w==INF)
						continue;
					int msk2=msk^(1<<i)^(1<<j);
					if(dist[msk]+w<dist[msk2]){
						dist[msk2]=dist[msk]+w;
						last[msk2]=mp(i,j);
						qu.push(mp(-dist[msk2],msk2));
					}
				}
			}
		}
		
		if (!done[0])
			exit(100);
		
		int msk=0;
		while(msk!=msk0){
			int a=last[msk].X;
			int b=last[msk].Y;
			++gr2[a][b];
			++gr2[b][a];
			msk^=(1<<a)^(1<<b);
		}
		
		vector<int> res;
		euler(0,gr2,res);
		
		if (path_weight(res) != dist[0])
			exit(91);
		
		return res;
	}
	
	vector<int> min_edge_covering_cycles_optional(vector<PII> opt){
		vector<vector<int> > gr1=gr0;
		vector<int> res;
		int mn=INF;
		forn(msk,1<<sz(opt)){
			forn(i,2){
				if(msk&(1<<i)){
					gr0[opt[i].X][opt[i].Y]=gr0[opt[i].Y][opt[i].X]=INF;
				}
			}
			vector<int> t=min_edge_covering_cycle();
			int w=path_weight(t);
			if(w<mn){
				mn=w;
				res=t;
			}
			gr0=gr1;
		}
		return res;
	}
};

vector<string> read_names(int n){
	vector<string> res(n);
	forn(i,n){
		cin>>res[i];
	}
	return res;
}

void print_path(vector<int> p,graph gr,double add_cost,double cost_coef,bool wei=true,vector<string> names=vector<string>()){
	forv(i,p){
		if (i)
			cout<<" \\rightarrow ";
		string s(1,(char)('A'+p[i]));
		if (sz(names))
			s = names[p[i]];
		cout<<s;
	}
	cout<<endl;
	if(wei){
		int c=gr.path_weight(p);
		cout<<"weight: "<<c<<endl;
		if (add_cost != 0 || cost_coef != 0)
			cout<<"cost: \\texteuro "<<add_cost + c*cost_coef<<endl;
	}
}

vector<int> read_path(){
	int n;
	cin>>n;
	vector<int> res;
	forn(i,n){
		char a;
		cin>>a;
		a-='A';
		res.pb(a);
	}
	return res;
}

void open_files(string s){
	freopen((s+"_in.txt").c_str(),"r",stdin);
	freopen((s+"_out.txt").c_str(),"w",stdout);
}

void do_61(){
	open_files("61");
	
	graph gr;
	gr.read_table();
	vector<string> names = read_names(gr.n);
	
	cout<<"(b)"<<endl;
	vector<int> p=gr.nearest_neighbour_path(0);
	print_path(p,gr,18000/500.*60,1,true,names);
	
	cout<<"(c)"<<endl;
	gr.do_dp(false);
	vector<int> bp=gr.min_path_from_dp();
	print_path(bp,gr,18000/500.*60,1,true,names);
	
	cout<<"(d)"<<endl;
	graph gr2;
	gr2.read_table();
	vector<string> names2 = read_names(gr2.n);
	gr2.do_dp(false,1);
	vector<int> p2=gr2.min_path_from_dp(1);
	print_path(p2,gr2,18000/500.*60,1,true,names2);
}

void do_65(){
	open_files("65");
	
	graph gr;
	gr.read_list();
	gr.floyd();
	gr.do_dp();
	
	cout<<"(a)"<<endl;
	vector<int> p=gr.nearest_insertion_route(0);
	print_path(gr.full_path(p), gr, 2000, .75*40);
	print_path(p, gr, 0, 0, false);
	
	cout<<endl<<"(b)"<<endl;
	print_path(gr.full_path(gr.path_from_dp((1<<gr.n)-1, 0)), gr, 2000, .75*40);
	
	cout<<endl<<"(c)"<<endl;
	vector<int> p1=read_path();
	vector<int> p2=read_path();
	print_path(p1, gr, 1050, .7*40);
	print_path(p2, gr, 1050, .7*40);
	cout<<"sum: \\texteuro "<<1050*2+.7*40*(gr.path_weight(p1)+gr.path_weight(p2))<<endl;
	
	cout<<endl<<"(d)"<<endl;
	vector<int> tp1=gr.full_path(gr.two_opt_cycle(p1));
	vector<int> tp2=gr.full_path(gr.two_opt_cycle(p2));
	print_path(tp1, gr, 1050, .7*40);
	print_path(tp2, gr, 1050, .7*40);
	cout<<"sum: \\texteuro "<<1050*2+.7*40*(gr.path_weight(tp1)+gr.path_weight(tp2))<<endl;
	
	cout<<endl<<"(e)"<<endl;
	gr.two_cycles(100, p1, p2);
	p1=gr.full_path(p1);
	p2=gr.full_path(p2);
	print_path(p1, gr, 1050, .7*40);
	print_path(p2, gr, 1050, .7*40);
	cout<<"sum: \\texteuro "<<1050*2+.7*40*(gr.path_weight(p1)+gr.path_weight(p2))<<endl;
	
	cout<<endl<<"(f)"<<endl;
	gr.two_paths(100, p1, p2);
	p1=gr.full_path(p1);
	p2=gr.full_path(p2);
	print_path(p1, gr, 1050, .7*40);
	print_path(p2, gr, 1050, .7*40);
	cout<<"sum: \\texteuro "<<1050*2+.7*40*(gr.path_weight(p1)+gr.path_weight(p2))<<endl;
}

void do_66(){
	open_files("66");
	
	graph gr;
	gr.read_list();
	
	cout<<"(a)"<<endl;
	vector<int> p1=gr.min_edge_covering_cycle();
	print_path(p1,gr,0,.01);
	
	cout<<"(b)"<<endl;
	vector<PII> opt;
	opt.pb(mp('A'-'A','D'-'A'));
	opt.pb(mp('G'-'A','H'-'A'));
	vector<int> p2=gr.min_edge_covering_cycles_optional(opt);
	print_path(p2,gr,0,.01);
	
	cout<<"(c)"<<endl;
	gr.gr0['B'-'A']['H'-'A']=gr.gr0['H'-'A']['B'-'A']=50;
	vector<int> p3=gr.min_edge_covering_cycle();
	print_path(p3,gr,0,.01);
	
	cout<<"(d)"<<endl;
	vector<int> p4=gr.min_edge_covering_cycles_optional(opt);
	print_path(p4,gr,0,.01);
}

int main() {

	//do_61();
	//do_65();
	do_66();

	return 0;
}
