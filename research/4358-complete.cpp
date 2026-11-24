// Complete bounded monotone 11-gate DAG check for the exact L-meta-4358 hypotheses.
// Compile with c++ -O2 -std=c++17. Run: check4358 --self-test
// check4358 SECONDS [FIRST_ROOT [PAST_ROOT [WITNESS_JSON]]]. UNKNOWN never means exhaustion.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
using Word=uint16_t;
using Mask=uint64_t;
using PinMask=uint32_t;
using Clock=std::chrono::steady_clock;
constexpr int gateCount=11,rawCount=7;
constexpr Word goal=(1u<<8)-1,ones=(1u<<15)-1;
constexpr Mask kwAll=(Mask(1)<<56)-1;
constexpr int edges[][2]={{0,1},{1,2},{0,4},{1,5},{2,6},{3,5},{4,6},{3,6}};
constexpr int maxneg[]={13,26,28,37,52,66,97};
constexpr int liftedRows[]={1,8,96,66,18,52};
using Full=__uint128_t;
bool graph(int x){for(auto &e:edges)if((x>>e[0]&1)&&(x>>e[1]&1))return true;return false;}
int pop(Mask x){return __builtin_popcountll(x);}
int bit(Mask x){return __builtin_ctzll(x);}
struct State{
    std::array<Word,13> w{};uint8_t n=0,k=0,quota=1;
    bool operator==(const State &t)const{return n==t.n&&k==t.k&&quota==t.quota&&std::equal(w.begin(),w.begin()+n,t.w.begin());}
};
struct Hash{
    size_t operator()(const State&s)const{size_t h=(s.k*31u+s.n)*31u+s.quota;
        for(int i=0;i<s.n;++i)h=(h^s.w[i])*1099511628211ULL;return h;}
};
struct Gate{bool isOr;int a,b;};
struct Move{State next;Word a,b,z;bool isOr;uint32_t key;};
struct Stats{
    Mask oracle=0,hit=0,formula=0,actual=0,terminal=0,eight=0,tests=0;
    Mask orderPruned=0,stale=0,slicePruned=0,oraclePruned=0;
}stats;
std::array<Mask,1<<15> sep{};
std::array<Word,18> kw{};
std::array<Mask,18> sliced{};
std::array<uint8_t,7> liftRaw{};
std::array<Gate,11> gates{};
std::array<uint32_t,11> seq{};
std::array<int,1<<15> wireId{};
std::unordered_map<State,bool,Hash> memo;
Clock::time_point deadline,start;
struct Limit{};
Mask pulses=0;bool found=false;int witnessP=-1,witnessQ=-1;PinMask witnessMask=0;
std::string witnessPath;
void tick(){if((++pulses&2047u)==0&&Clock::now()>=deadline)throw Limit{};}

void init(){
    int rows[15]{};
    for(int i=0;i<8;++i)rows[i]=(1<<edges[i][0])|(1<<edges[i][1]);
    for(int i=0;i<7;++i)rows[8+i]=maxneg[i];
    for(unsigned w=0;w<sep.size();++w){unsigned missing=(~w>>8)&127;
        for(int i=0;i<8;++i)if(w>>i&1)sep[w]|=Mask(missing)<<(7*i);}
    wireId.fill(-1);
    for(int j=0;j<7;++j){for(int i=0;i<15;++i)kw[j]|=Word(rows[i]>>j&1)<<i;
        for(int i=0;i<64;++i){int row=(i&3)|((i&~3)<<1);sliced[j]|=Mask(row>>j&1)<<i;}
        for(int i=0;i<6;++i)liftRaw[j]|=(liftedRows[i]>>j&1)<<i;wireId[kw[j]]=j;}
}

// At zero slack the suffix is read-once in its live variables. If two variables
// own unique KW cells in a common positive row, their LCA must be AND. A common
// negative column forces OR. A simultaneous connected component is impossible.
bool formulaConflict(const State&s){
    Mask seen=0,multi=0;
    for(int i=0;i<s.n;++i){Mask v=sep[s.w[i]];multi|=seen&v;seen|=v;}
    std::array<unsigned,13> pos{},neg{},red{},blue{};
    for(int i=0;i<s.n;++i){
        Mask u=sep[s.w[i]]&~multi;
        while(u){int j=bit(u);pos[i]|=1u<<(j/7);neg[i]|=1u<<(j%7);u&=u-1;}
        for(int j=0;j<i;++j){
            if(pos[i]&pos[j]){red[i]|=1u<<j;red[j]|=1u<<i;}
            if(neg[i]&neg[j]){blue[i]|=1u<<j;blue[j]|=1u<<i;}
        }
        if(red[i]&blue[i])return true;
    }
    auto component=[](unsigned m,const auto&adj){
        unsigned q=m&-m,seen=0;while(q){int i=__builtin_ctz(q);q&=q-1;seen|=1u<<i;q|=adj[i]&m&~seen;}return seen;};
    std::array<unsigned,26> stack{};int top=0;stack[top++]=(1u<<s.n)-1;
    while(top){unsigned m=stack[--top];if(!(m&(m-1)))continue;
        unsigned c=component(m,red);if(c==m)c=component(m,blue);
        if(c==m)return true;stack[top++]=c;stack[top++]=m^c;}
    return false;
}
template<class Visit> bool children(const State&s,Visit visit){
    if(!s.k)return false;
    for(int i=0;i<s.n;++i)for(int j=i+1;j<s.n;++j){
        Word a=s.w[i],b=s.w[j];Mask restCover=0;
        for(int l=0;l<s.n;++l)if(l!=i&&l!=j)restCover|=sep[s.w[l]];
        for(int op=0;op<2;++op){
            bool pay=op&&(a==kw[2]||b==kw[2]);if(pay&&!s.quota)continue;
            Word z=op?(a|b):(a&b);
            if(!z||z==ones||std::binary_search(s.w.begin(),s.w.begin()+s.n,z))continue;
            for(int keep=0;keep<4;++keep){
                int width=s.n-1+(keep&1)+(keep>>1);
                if(width>s.k)continue;
                Mask cover=restCover|sep[z];if(keep&1)cover|=sep[a];if(keep&2)cover|=sep[b];if(cover!=kwAll)continue;
                Move m{};m.next.n=width;m.next.k=s.k-1;m.next.quota=s.quota-pay;
                m.a=a;m.b=b;m.z=z;m.isOr=op;m.key=(uint32_t(op)<<30)|(uint32_t(a)<<15)|b;
                int n=0;for(int l=0;l<s.n;++l)if((l!=i&&l!=j)||(l==i&&(keep&1))||(l==j&&(keep&2)))m.next.w[n++]=s.w[l];
                auto ins=std::lower_bound(m.next.w.begin(),m.next.w.begin()+n,z);
                std::move_backward(ins,m.next.w.begin()+n,m.next.w.begin()+n+1);*ins=z;
                if(visit(m))return true;
            }
        }
    }
    return false;
}
bool viable(const State&s){
    tick();++stats.oracle;
    if(std::binary_search(s.w.begin(),s.w.begin()+s.n,goal))return s.n==1&&s.k==0;
    if(!s.k||s.n>s.k+1)return false;
    auto old=memo.find(s);if(old!=memo.end()){++stats.hit;return old->second;}
    bool yes=false;
    if(s.n==s.k+1&&formulaConflict(s))++stats.formula;
    else yes=children(s,[](const Move&m){return viable(m.next);});
    // Bounded storage only affects runtime, never the set of explored branches.
    if(memo.size()<1000000)memo.emplace(s,yes);
    return yes;
}
uint8_t lifted(const Gate* gs,PinMask pins){
    std::array<uint8_t,18> w{};std::copy(liftRaw.begin(),liftRaw.end(),w.begin());
    for(int j=0;j<11;++j){auto g=gs[j];auto a=(pins>>(2*j)&1)?63:w[g.a];auto b=(pins>>(2*j+1)&1)?63:w[g.b];
        w[7+j]=g.isOr?(a|b):(a&b);}
    return w[17];
}
bool testLift(const Gate*gs){
    std::array<PinMask,17> uses{};
    for(int j=0;j<11;++j){uses[gs[j].a]|=1u<<(2*j);uses[gs[j].b]|=1u<<(2*j+1);}
    auto tryPins=[&](PinMask pins,int p,int q){++stats.tests;
        if(lifted(gs,pins)!=3)return false;witnessP=p;witnessQ=q;witnessMask=pins;return true;};
    if(tryPins(0,0,0))return true;
    for(int p=0;p<17;++p)for(PinMask a=uses[p];a;a=(a-1)&uses[p]){
        if(tryPins(a,p,p))return true;
        for(int q=p+1;q<17;++q)for(PinMask b=uses[q];b;b=(b-1)&uses[q])
            if(tryPins(a|b,p,q))return true;
    }
    return false;
}
bool validateFull(const Gate*gs,PinMask mask,int pc,int qc,bool needLift){
    if(pc<0||qc<0)return false;
    for(int i=0;i<128;++i){
        bool a[18]{},b[18]{};for(int j=0;j<7;++j)a[j]=b[j]=(i>>j)&1;
        for(int j=0;j<11;++j){auto g=gs[j];
            if(g.a<0||g.b<0||g.a>=7+j||g.b>=7+j)return false;
            bool pa=mask>>(2*j)&1,pb=mask>>(2*j+1)&1;
            if((pa&&g.a!=pc&&g.a!=qc)||(pb&&g.b!=pc&&g.b!=qc))return false;
            a[7+j]=g.isOr?(a[g.a]||a[g.b]):(a[g.a]&&a[g.b]);
            b[7+j]=g.isOr?((pa||b[g.a])||(pb||b[g.b])):((pa||b[g.a])&&(pb||b[g.b]));}
        if(a[17]!=graph(i))return false;
        if(needLift&&b[17]!=(graph(i)||bool(i&9)))return false;
    }return true;
}
void save(){
    if(!validateFull(gates.data(),witnessMask,witnessP,witnessQ,true))throw std::logic_error("full witness disagrees");
    if(witnessPath.empty())return;
    int readers=0,fresh=0;
    for(int j=0;j<11;++j){
        auto g=gates[j];readers+=g.isOr&&(g.a==2||g.b==2);
        auto z=sliced[7+j];if(z&&z!=~Mask(0)&&std::find(sliced.begin(),sliced.begin()+7+j,z)==sliced.begin()+7+j)++fresh;
    }
    if(readers>1||fresh<8)throw std::logic_error("physical bounds disagree");
    std::ofstream f(witnessPath);f<<"{\"gates\":[";
    for(int j=0;j<11;++j){if(j)f<<',';auto g=gates[j];f<<'['<<(!g.isOr)<<','<<g.a<<','<<g.b<<']';}
    f<<"],\"x4_shifted_gates\":[";
    for(int j=0;j<11;++j){if(j)f<<',';auto g=gates[j];
        f<<'['<<(!g.isOr)<<','<<((witnessMask>>(2*j)&1)?0:g.a+1)<<','<<((witnessMask>>(2*j+1)&1)?0:g.b+1)<<']';}
    f<<"],\"output\":17,\"shifted_output\":18,\"source_pair\":["<<witnessP<<','<<witnessQ<<"],\"changed_pin_mask\":"<<witnessMask
     <<",\"or_readers_of_2\":"<<readers<<",\"fresh_cofactor_columns\":"<<fresh<<"}\n";
}
bool follow(const Move&m,int depth,int novel){
    tick();if(wireId[m.z]>=0){++stats.stale;return false;}
    int a=wireId[m.a],b=wireId[m.b];if(a<0||b<0)throw std::logic_error("lost physical wire");
    // Kahn's ordered topological listing of this actual circuit picks the least available gate key.
    // A smaller later gate whose physical parents already existed cannot follow a larger earlier gate.
    for(int i=std::max(0,std::max(a,b)-6);i<depth;++i)if(seq[i]>m.key){++stats.orderPruned;return false;}
    Mask z=m.isOr?(sliced[a]|sliced[b]):(sliced[a]&sliced[b]);
    bool isNew=z&&z!=~Mask(0)&&std::find(sliced.begin(),sliced.begin()+7+depth,z)==sliced.begin()+7+depth;
    novel+=isNew;
    if(novel+m.next.k<8){++stats.slicePruned;return false;}
    if(!viable(m.next)){++stats.oraclePruned;return false;}
    ++stats.actual;int id=7+depth;gates[depth]={m.isOr,a,b};seq[depth]=m.key;
    kw[id]=m.z;sliced[id]=z;wireId[m.z]=id;
    if(!m.next.k){++stats.terminal;if(novel>=8){++stats.eight;
        if(!validateFull(gates.data(),0,0,0,false))throw std::logic_error("incorrect original terminal");
        if(testLift(gates.data())){save();found=true;}}}
    else children(m.next,[&](const Move&c){return follow(c,depth+1,novel);});
    wireId[m.z]=-1;return found;
}
State root(){
    State s{};s.n=7;s.k=11;s.quota=1;std::copy(kw.begin(),kw.begin()+7,s.w.begin());std::sort(s.w.begin(),s.w.begin()+7);return s;
}
void selfTest(){
    int neg=0;for(int i=0;i<128;++i)if(!graph(i)){bool maximal=true;for(int j=0;j<7;++j)if(!(i>>j&1)&&!graph(i|(1<<j)))maximal=false;
       if(maximal){if(std::find(maxneg,maxneg+7,i)==maxneg+7)throw std::logic_error("KW list");++neg;}}
    if(neg!=7||sep[goal]!=kwAll)throw std::logic_error("invalid KW header");
    std::array<Gate,11> pos={{{true,1,4},{false,0,7},{true,5,6},{false,3,9},{true,2,5},{false,1,11},{true,2,4},{false,6,13},{true,8,10},{true,12,14},{true,15,16}}};
    std::array<Gate,11> no={{{true,1,4},{false,0,7},{true,1,3},{false,5,9},{true,3,4},{false,6,11},{true,1,6},{false,2,13},{true,8,10},{true,12,14},{true,15,16}}};
    if(!validateFull(pos.data(),0,0,0,false)||!testLift(pos.data())||!validateFull(pos.data(),witnessMask,witnessP,witnessQ,true))throw std::logic_error("positive lift");
    if(!validateFull(no.data(),0,0,0,false)||testLift(no.data()))throw std::logic_error("negative lift");
    int branches=0;children(root(),[&](const Move&m){if(m.next.k!=10)throw std::logic_error("root accounting");++branches;return false;});
    std::cout<<"SELF_TEST_PASS KW=8x7 full positive/negative lift controls; root transitions="<<branches<<"\n";
}
int main(int argc,char**argv){
    init();
    if(argc>1&&std::string(argv[1])=="--self-test"){selfTest();return 0;}
    int seconds=argc>1?std::atoi(argv[1]):110,lo=argc>2?std::atoi(argv[2]):0,hi=argc>3?std::atoi(argv[3]):100000;
    if(argc>4)witnessPath=argv[4];
    if(seconds<=0||lo<0||hi<=lo)return 2;
    start=Clock::now();deadline=start+std::chrono::seconds(seconds);int roots=0,done=0,active=-1;bool timeout=false;
    try{children(root(),[&](const Move&m){int ix=roots++;if(ix<lo||ix>=hi)return false;
       active=ix;bool hit=follow(m,0,0);if(!hit)++done;return hit;});}catch(const Limit&){timeout=true;}
    std::cout<<(found?"WITNESS":timeout?"UNKNOWN":"EXHAUSTED_RANGE")<<" lower="<<lo<<" upper="<<hi<<" completed_root_buckets="<<done
      <<" root_transitions_seen="<<roots<<" last_active="<<active<<" oracle_calls="<<stats.oracle<<" oracle_memo="<<memo.size()
      <<" memo_hits="<<stats.hit<<" cotree_prune="<<stats.formula<<" viable_physical_prefixes="<<stats.actual<<" canonical_prune="<<stats.orderPruned
      <<" repeated_prune="<<stats.stale<<" slice_prune="<<stats.slicePruned<<" dead_child_prune="<<stats.oraclePruned
      <<" qualifying_dags="<<stats.eight<<" six_row_pin_trials="<<stats.tests
      <<" seconds="<<std::chrono::duration<double>(Clock::now()-start).count()<<std::endl;
    if(found){std::cout<<"forced_source_colors="<<witnessP<<','<<witnessQ<<" pin_mask="<<witnessMask<<"\n";return 0;}
    return timeout?3:0;
}
