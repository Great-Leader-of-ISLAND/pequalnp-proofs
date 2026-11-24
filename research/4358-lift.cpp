// Original bounded constructive search for L-meta-4358. No completeness claim for the whole gap.
// Build on a standard runner: c++ -std=c++17 -O2 4358-lift.cpp -o lift4358
// ./lift4358 --self-test ; timeout -k 1s 108s ./lift4358 97 435824 witness4358.json
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <random>
#include <set>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
using Word=uint32_t;
using Full=__uint128_t;
using Clock=chrono::steady_clock;
struct Gate {int a=0,b=0;bool andOp=false;};
using Net=array<Gate,11>;
struct Circuit {Net g{};int size=0,out=0;};
const int E[8][2]={{0,1},{1,2},{0,4},{1,5},{2,6},{3,5},{4,6},{3,6}};
bool truth(int row,bool promoted=false){
    if(promoted && (row&9)) return true;
    for(auto &e:E) if((row>>e[0]&1)&&(row>>e[1]&1)) return true;
    return false;
}
template<class W> W gate(const Gate& g,W a,W b){return g.andOp?a&b:a|b;}
struct Tests {
    vector<int> pos,neg;
    array<Word,7> raw{};Word target=0;
    Tests(bool six=false,bool modified=false){
        for(int r=0;r<128;++r){
            if(six&&(r&4)) continue;
            bool f=truth(r,modified),extreme=true;
            for(int i=0;i<7;++i) if((!six||i!=2)&&bool(r>>i&1)==f&&truth(r^(1<<i),modified)==f) extreme=false;
            if(extreme && (!modified||!f||r==1||r==8)) (f?pos:neg).push_back(r);
        }
        vector<int> rows=pos;rows.insert(rows.end(),neg.begin(),neg.end());
        if(rows.size()>=32) abort();
        for(int j=0;j<(int)rows.size();++j) for(int i=0;i<7;++i) if(rows[j]>>i&1)raw[i]|=Word(1)<<j;
        target=(Word(1)<<pos.size())-1;
    }
};
Tests seven,six(true),prom(false,true);
array<Full,7> raw128{};
Full all128=~Full(0),goal128=0,up128=0;
array<uint64_t,7> raw64{};
int pc(uint32_t a){return __builtin_popcount(a);}
template<class W> W eval(const Circuit &c,const array<W,7>&raw,uint32_t repl=0,W one=~W(0)){
    array<W,18>w{};copy(raw.begin(),raw.end(),w.begin());
    for(int i=0;i<c.size;++i){auto g=c.g[i];
        W a=(repl>>(2*i)&1)?one:w[g.a],b=(repl>>(2*i+1)&1)?one:w[g.b];
        w[7+i]=gate(g,a,b);
    }
    return w[c.out];
}
int columns(const Circuit &c){
    array<uint64_t,18>w{};copy(raw64.begin(),raw64.end(),w.begin());
    uint64_t keep[11];int n=0;
    for(int i=0;i<c.size;++i){auto g=c.g[i];auto z=w[7+i]=gate(g,w[g.a],w[g.b]);
        if(z==0||z==~uint64_t(0)||find(raw64.begin(),raw64.end(),z)!=raw64.end()||find(keep,keep+n,z)!=keep+n)continue;
        keep[n++]=z;
    }
    return n;
}
int readers(const Circuit &c){int n=0;for(int i=0;i<c.size;++i){auto g=c.g[i];n+=!g.andOp&&(g.a==2||g.b==2);}return n;}
uint64_t mix(uint64_t z){z^=z>>30;z*=0xbf58476d1ce4e5b9ULL;z^=z>>27;z*=0x94d049bb133111ebULL;return z^(z>>31);}
uint64_t fingerprint(const Circuit& c){
    array<uint64_t,18>w;for(int i=0;i<7;++i)w[i]=mix(i+1);
    for(int i=0;i<c.size;++i){auto g=c.g[i];auto a=w[g.a],b=w[g.b];
        if(b<a)swap(a,b);w[7+i]=mix(a^mix(b+(g.andOp?57991:36731)));
    }
    return w[c.out];
}
Clock::time_point ending;mt19937 rng;string outpath;
bool expired(){return Clock::now()>=ending;}
uint64_t tested=0,originals=0,promTrials=0,baseNodes=0,mutants=0;
unordered_set<uint64_t> seen;
vector<Circuit> repairPool;
bool won=false;
void save(const Circuit& c,uint32_t repl,int s,int t){
    if(c.size!=11||readers(c)>1||columns(c)<8||eval(c,raw128)!=goal128||eval(c,raw128,repl)!=up128)abort();
    for(int i=0;i<11;++i)for(int p=0;p<2;++p)if(repl>>(2*i+p)&1){
        auto g=c.g[i];int a=p?g.b:g.a;if(a!=s&&a!=t)abort();
    }
    ofstream f(outpath+".tmp");if(!f)abort();
    f<<"{\"source_pair\":["<<s<<","<<t<<"],\"gates\":[";
    for(int i=0;i<11;++i){auto g=c.g[i];if(i)f<<",";f<<"["<<int(g.andOp)<<","<<g.a<<","<<g.b<<"]";}
    f<<"],\"x4_shifted_gates\":[";
    for(int i=0;i<11;++i){auto g=c.g[i];if(i)f<<",";f<<"["<<int(g.andOp)<<","<<((repl>>(2*i)&1)?0:g.a+1)<<","<<((repl>>(2*i+1)&1)?0:g.b+1)<<"]";}
    f<<"],\"output\":"<<c.out<<",\"shifted_output\":"<<c.out+1<<",\"changed_pin_mask\":"<<repl
     <<",\"or_readers_of_2\":"<<readers(c)<<",\"fresh_cofactor_columns\":"<<columns(c)<<"}\n";f.close();
    if(!f||rename((outpath+".tmp").c_str(),outpath.c_str()))abort();
    won=true;cout<<"COUNTEREXAMPLE FULL 128-ROW REPLAY "<<outpath<<endl;
}
bool promotion(const Circuit& c,bool exportResult){
    array<uint32_t,18>pins{};
    for(int i=0;i<c.size;++i){auto g=c.g[i];pins[g.a]|=1u<<(2*i);pins[g.b]|=1u<<(2*i+1);}
    for(int s=0;s<c.out;++s)for(int t=s;t<c.out;++t){
        auto mask=pins[s]|pins[t];if(!pins[s]||!pins[t])continue;
        // Maximal promotion must pass both singleton rows by monotonicity in redirections.
        if((eval(c,prom.raw,mask)&3)!=3)continue;
        for(uint32_t m=mask;m;m=(m-1)&mask){
            ++promTrials;
            if((m&pins[s])&&(m&pins[t])&&eval(c,prom.raw,m)==prom.target){
                if(eval(c,raw128,m)!=up128)abort();
                if(exportResult)save(c,m,s,t);
                return true;
            }
        }
    }
    return false;
}
void consider(const Circuit&c){
    ++tested;if(readers(c)>1||eval(c,seven.raw)!=seven.target)return;
    auto h=fingerprint(c);if(seen.count(h))return;
    if(seen.size()<200000)seen.insert(h);
    if(columns(c)<8)return;
    if(eval(c,raw128)!=goal128)abort(); // independent full-function validation
    ++originals;if(repairPool.size()<1400)repairPool.push_back(c);promotion(c,true);
}
// Make all live gates physical in DFS postorder, permit arbitrary temporary labels, reject cycles.
bool physical(const Net& g,int root,int size,Circuit &out){
    int status[18]{},perm[18]{};out.size=0;
    auto visit=[&](auto&&v,int id)->bool{
        if(id<7){perm[id]=id;return true;}
        if(status[id]==2)return true;
        if(status[id]==1)return false;
        status[id]=1;auto u=g[id-7];
        if(!v(v,u.a)||!v(v,u.b))return false;
        perm[id]=7+out.size;out.g[out.size++]={perm[u.a],perm[u.b],u.andOp};
        status[id]=2;return true;
    };
    if(!visit(visit,root)||out.size!=size)return false;
    out.out=perm[root];return true;
}
vector<Circuit> bases;
set<string>basekeys;
string baseKey(const Circuit& c){
    array<string,18>sig;
    for(int i=0;i<7;++i)sig[i]=string(1,char('a'+i));
    for(int i=0;i<c.size;++i){auto g=c.g[i];auto a=sig[g.a],b=sig[g.b];
        if(b<a)swap(a,b);
        sig[7+i]=string(1,g.andOp?'&':'|')+'('+a+','+b+')';
    }
    return sig[c.out];
}
void addBase(const Circuit&c){
    if(c.size!=8||eval(c,six.raw)!=six.target||columns(c)!=8)return;
    if(basekeys.insert(baseKey(c)).second)bases.push_back(c);
}
vector<Circuit> stars(bool sixOnly){
    vector<Circuit> result;int edges=sixOnly?6:8;
    vector<pair<int,int>> es;for(auto&e:E)if(!sixOnly||(e[0]!=2&&e[1]!=2))es.push_back({e[0],e[1]});
    for(int mask=0;mask<(1<<edges);++mask){vector<vector<int>>own(7);
        for(int j=0;j<edges;++j){auto [a,b]=es[j];if(mask>>j&1)swap(a,b);own[a].push_back(b);}
        vector<int> centers;for(int i=0;i<7;++i)if(!own[i].empty())centers.push_back(i);
        if(centers.size()!=(sixOnly?3u:4u))continue;
        // Several orderings expose different internal pair ORs and final OR branch groupings.
        for(int rep=0;rep<(sixOnly?12:6);++rep){shuffle(centers.begin(),centers.end(),rng);Circuit c;
            auto add=[&](int a,int b,bool k){int id=7+c.size;c.g[c.size++]={a,b,k};return id;};
            vector<int>terms;
            for(int v:centers){auto ns=own[v];shuffle(ns.begin(),ns.end(),rng);int w=ns[0];
                for(int i=1;i<(int)ns.size();++i)w=add(w,ns[i],false);
                terms.push_back(add(v,w,true));
            }
            shuffle(terms.begin(),terms.end(),rng);
            while(terms.size()>1){int a=terms.back();terms.pop_back();int b=terms.back();terms.pop_back();
                int z=add(a,b,false);terms.insert(terms.begin()+int(rng()%(terms.size()+1)),z);}
            c.out=terms[0];result.push_back(c);
        }
    }return result;
}
uint64_t coverage(Word w){
    uint64_t a=0;int p=six.pos.size(),n=six.neg.size();
    for(int i=0;i<p;++i)if(w>>i&1)for(int j=0;j<n;++j)if(!(w>>(p+j)&1))a|=uint64_t(1)<<(i*n+j);
    return a;
}
int cycle6[6]={0,1,5,3,6,4};
long long shapeCount=0,placements=0,matching=0;
bool diamonds(Clock::time_point stop){
    const int count=1<<(six.pos.size()+six.neg.size());
    vector<uint64_t> cv(count);for(int i=0;i<count;++i)cv[i]=coverage(i);
    auto all=cv[six.target]; array<Word,18> sig{};copy(six.raw.begin(),six.raw.end(),sig.begin());
    for(int distance=1;distance<=3;++distance)
    for(int pref=1;pref<=6;++pref)for(int u=0;u<=6;++u)for(int v=max(1,u);v<=6;++v){
        int tail=7-pref-u-v;if(tail<0)continue;
        ++shapeCount;
        array<int,6> perm={0,1,3,4,5,6};
        do{
            if((placements++&127)==0&&Clock::now()>=stop)return false;
            int pi=0;Circuit c;
            auto create=[&](int a,int b){int id=7+c.size;c.g[c.size++]={a,b,false};return id;};
            int branch=create(0,cycle6[distance]);
            for(int j=1;j<pref;++j)branch=create(branch,perm[pi++]);
            int left=branch,right=branch;
            for(int j=0;j<u;++j)left=create(left,perm[pi++]);
            for(int j=0;j<v;++j)right=create(right,perm[pi++]);
            int root=create(left,right);
            for(int j=0;j<tail;++j)root=create(root,perm[pi++]);
            c.out=root;if(c.size!=8||pi!=6)abort();
            uint64_t staticCover[8]{};unsigned live[8]{};
            for(int i=0;i<8;++i){
                for(int k=i+1;k<8;++k)for(int w:{c.g[k].a,c.g[k].b}){
                    if(w<7)staticCover[i]|=cv[sig[w]];else if(w<=7+i)live[i]|=1u<<w;
                }
                if(i==7)live[i]|=1u<<c.out;
            }
            auto visit=[&](auto&&go,int i)->void{
                ++baseNodes;auto&g=c.g[i];auto a=sig[g.a],b=sig[g.b];
                for(int op=0;op<2;++op){
                    auto z=op?(a&b):(a|b);
                    if(!z||z==Word(count-1)||find(sig.begin(),sig.begin()+7+i,z)!=sig.begin()+7+i)continue;
                    g.andOp=op;sig[7+i]=z;
                    uint64_t cov=staticCover[i];
                    for(unsigned m=live[i];m;m&=m-1)cov|=cv[sig[__builtin_ctz(m)]];
                    if(cov!=all)continue;
                    if(i<7){go(go,i+1);continue;}
                    if(z!=six.target)continue;
                    ++matching;
                    for(int sign:{-1,1})for(int shift=0;shift<6;++shift){
                        int move[7]={};for(int j=0;j<6;++j)move[cycle6[j]]=cycle6[(shift+sign*j+6)%6];
                        auto q=c;for(int k=0;k<8;++k){
                            if(q.g[k].a<7)q.g[k].a=move[q.g[k].a];
                            if(q.g[k].b<7)q.g[k].b=move[q.g[k].b];
                        }addBase(q);
                    }
                }
            };
            visit(visit,0);
        }while(next_permutation(perm.begin(),perm.end()));
    }
    return true;
}
struct LiftJob {uint8_t b,t,w,kind;};
void lift(const Circuit&c,const LiftJob job){
    // C6 gate IDs 7..14. R=15, P=16, Q=17. All P versions have cofactor zero.
    int b=job.b,t=job.t,w=job.w; Net g=c.g;
    g[8]={job.kind==0?2:16,b,false};g[9]={2,w,true};g[10]={16,t,false};
    // Choose any occurrences of B/T to lift to R/Q, including in the other new gates or final output.
    struct Opt{int *dst;int orig;bool r,q;};
    array<Opt,24> opts;int n=0,root=c.out;
    auto pin=[&](int& x,int owner){bool r=x==b&&owner!=15,q=x==t&&owner!=17;
        if(r||q)opts[n++]={&x,x,r,q};};
    for(int i=0;i<11;++i){pin(g[i].a,i+7);pin(g[i].b,i+7);}pin(root,-1);
    auto rec=[&](auto&&go,int k,bool usedR,bool usedQ)->void{
        if(won)return;
        if(k==n){if(!usedR||!usedQ)return;Circuit d;if(physical(g,root,11,d))consider(d);return;}
        auto a=opts[k];go(go,k+1,usedR,usedQ);
        if(a.r){*a.dst=15;go(go,k+1,true,usedQ);}
        if(a.q){*a.dst=17;go(go,k+1,usedR,true);}
        *a.dst=a.orig;
    };
    rec(rec,0,false,false);
}
void shuffleTopo(Circuit&c){
    int perm[18];for(int i=0;i<7;++i)perm[i]=i;for(int i=7;i<18;++i)perm[i]=-1;
    Net g{};for(int k=0;k<c.size;++k){int choices[11],n=0;
        for(int i=0;i<c.size;++i){auto u=c.g[i];if(perm[7+i]<0&&perm[u.a]>=0&&perm[u.b]>=0)choices[n++]=i;}
        int i=choices[rng()%n];auto u=c.g[i];perm[7+i]=7+k;g[k]={perm[u.a],perm[u.b],u.andOp};
    }
    c.g=g;c.out=perm[c.out];
}
void mutantSweep(Circuit c){
    shuffleTopo(c);int a=rng()%10,b=a+1+rng()%(10-a);
    int amax=a+7,bmax=b+7;
    for(int rep=0;rep<12&&!won;++rep){
        int u=rng()%amax,v=rng()%amax;if(u==v)continue;c.g[a]={u,v,bool(rng()%2)};
        for(int j=0;j<bmax&&!won;++j)for(int k=j+1;k<bmax&&!won;++k)for(int op=0;op<2&&!won;++op){
            c.g[b]={j,k,bool(op)};++mutants;
            if(eval(c,seven.raw)!=seven.target||readers(c)>1)continue;
            Circuit d;if(physical(c.g,c.out,11,d))consider(d);
        }
    }
}
int main(int argc,char**argv){
    bool small=argc>1&&string(argv[1])=="--self-test";
    int sec=small?0:(argc>1?atoi(argv[1]):96);
    if(!small&&(sec<1||sec>104))return 2;
    unsigned seed=small?435824:(argc>2?strtoul(argv[2],nullptr,10):435824);
    outpath=argc>3?argv[3]:"witness4358.json";
    if(!small&&ifstream(outpath)){cerr<<"Witness path already exists, refusing overwrite\n";return 2;}
    rng.seed(seed);for(int r=0;r<128;++r){Full bit=Full(1)<<r;
        if(truth(r))goal128|=bit;if(truth(r,true))up128|=bit;
        for(int i=0;i<7;++i)if(r>>i&1)raw128[i]|=bit;
        if(!(r&4)){int j=(r&3)|((r>>3)<<2);for(int i=0;i<7;++i)if(r>>i&1)raw64[i]|=uint64_t(1)<<j;}
    }
    if(seven.pos.size()!=8||prom.pos!=vector<int>{1,8}||prom.neg.size()!=4)abort();
    auto seeds=stars(false);for(auto&c:stars(true))addBase(c);
    vector<Circuit> valid;bool hardPositive=false;
    for(auto&c:seeds){
        if(eval(c,raw128)!=goal128)abort();
        if(readers(c)<=1)valid.push_back(c);
        if(!hardPositive&&readers(c)>=2&&columns(c)>=8&&promotion(c,false))hardPositive=true;
    }
    if(!hardPositive||bases.empty()||valid.empty())abort();
    cout<<"seed "<<seed<<" original rows "<<seven.pos.size()<<"+"<<seven.neg.size()
        <<" promotion "<<prom.pos.size()<<"+"<<prom.neg.size()<<" C6 seed skeletons "<<bases.size()
        <<" qualifying two-OR positive control PASS"<<endl;
    if(small){cout<<"SELF-TEST ONLY, no search or artifact"<<endl;return 0;}
    auto start=Clock::now();ending=start+chrono::seconds(sec);
    bool exact=diamonds(start+chrono::milliseconds(min(14000,sec*165)));
    cout<<"C6 diamond sweep "<<(exact?"complete":"timeout, partial")<<" shape-distance combinations "<<shapeCount
        <<" placements "<<placements<<" algebra prefixes "<<baseNodes<<" matching representatives "<<matching
        <<" distinct labeled C6 circuits incl six control formulas "<<bases.size()<<endl;
    vector<LiftJob> jobs;for(int b=0;b<15;++b)for(int t=0;t<15;++t)for(int w=0;w<15;++w)
        if(b!=2&&t!=2&&w!=2)for(int k=0;k<2;++k)jobs.push_back({(uint8_t)b,(uint8_t)t,(uint8_t)w,(uint8_t)k});
    for(auto&c:bases)shuffleTopo(c);shuffle(jobs.begin(),jobs.end(),rng);
    size_t calls=0;auto liftStop=start+chrono::milliseconds(sec*710);
    for(auto j:jobs){for(auto&c:bases){
        if(Clock::now()>=liftStop||won)break;
        lift(c,j);++calls;
    }if(Clock::now()>=liftStop||won)break;}
    cout<<"C6 skeletons "<<bases.size()<<" frontier visits "<<baseNodes<<" graft templates "<<calls
        <<" complete original circuits "<<originals<<endl;
    while(!expired()&&!won){
        if(!repairPool.empty()&&rng()%4)mutantSweep(repairPool[rng()%repairPool.size()]);
        else mutantSweep(valid[rng()%valid.size()]);
    }
    cout<<(won?"WITNESS":"NO WITNESS IN BOUNDED SEARCH")<<" admissible unique originals "<<originals
        <<" graph checks "<<tested<<" simultaneous two-gate rewrites "<<mutants<<" promotion trials "<<promTrials
        <<" seconds "<<chrono::duration<double>(Clock::now()-start).count()<<endl;
}
