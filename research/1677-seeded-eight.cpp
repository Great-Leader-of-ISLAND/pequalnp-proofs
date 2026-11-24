// Bounded, exact lower-bound search on a finite restriction of G minus vertex 6.
// Eight raw vertices and the additional OR(x2,x5) are free. Each step is a
// binary AND/OR or a paid unary NOT. The project has already shown that even
// with free wire complements this eight-vertex target costs 12 binary gates.
// Thus after the prescribed OR at most one paid NOT fits in 13 physical gates.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>
using Word=uint32_t;
constexpr std::array<std::array<int,2>,10> edges={{{0,1},{1,2},{2,3},{3,4},{0,4},{0,5},{2,6},{3,7},{5,6},{5,7}}};
bool target(int row) {
    for(auto e:edges) if((row>>e[0])&(row>>e[1])&1) return true;
    return false;
}
using Clock=std::chrono::steady_clock;
struct State {
    std::array<Word,14> wires{};
    unsigned n=0, budget=0, neg=0;
    void add(Word w) {if(n>=wires.size())throw std::logic_error("bank overflow");wires[n++]=w;}
    void sort() {std::sort(wires.begin(),wires.begin()+n);}
    bool has(Word w) const {return std::binary_search(wires.begin(),wires.begin()+n,w);}
    bool operator==(const State& s)const {
        return n==s.n && budget==s.budget && neg==s.neg && std::equal(wires.begin(),wires.begin()+n,s.wires.begin());
    }
};
struct Hash {
    size_t operator()(const State& s)const{
        size_t h=257*s.n+61*s.budget+s.neg;
        for(unsigned i=0;i<s.n;++i)h=(h^s.wires[i])*1099511628211ULL;
        return h;
    }
};
struct Gate{char op;Word a,b,z;};
std::vector<int> samples;
std::vector<Gate> path,answer;
unsigned posCount,negCount;
Word totalMask,goalBits;
std::vector<Word> fwd,rev;
std::unordered_set<State,Hash> dead;
Clock::time_point beginTime;
uint64_t visited=0;
double seconds;
double elapsed(){return std::chrono::duration<double>(Clock::now()-beginTime).count();}
void initialize() {
    for(bool positive:{true,false}){
        for(int row=0;row<256;++row){
            if(target(row)!=positive)continue;
            bool boundary=true;
            for(int pin=0;pin<8;++pin)
                if(bool((row>>pin)&1)==positive && target(row^(1<<pin))==positive)boundary=false;
            if(boundary)samples.push_back(row);
        }
        if(positive)posCount=samples.size();
    }
    negCount=samples.size()-posCount;
    if(posCount!=10||negCount!=9)throw std::logic_error("boundary mismatch");
    totalMask=(Word(1)<<samples.size())-1;goalBits=(1u<<posCount)-1;
    // A table entry is the mask of negative rows not yet distinguished from
    // a specified positive row. Keep negCount-bit masks, not truth-table hashes.
    fwd.resize(totalMask+1);rev.resize(totalMask+1);
    for(Word w=0;w<=totalMask;++w){
        rev[w]=w>>posCount;fwd[w]=(~rev[w])&((1u<<negCount)-1);
    }
}
bool consistent(const State& s) {
    if(s.n>s.budget+1)return false;
    Word negRows=(1u<<negCount)-1;
    Word mustBeOne=0,mustBeZero=0;
    std::array<Word,10> reverse{};
    for(unsigned p=0;p<posCount;++p){
        Word up=negRows,down=negRows;
        for(unsigned i=0;i<s.n;++i){
            Word w=s.wires[i];
            if((w>>p)&1) up&=~fwd[w];else down&=~rev[w];
        }
        if(!up) {reverse[p]=down;continue;}
        if(!s.neg || (up&down))return false;
        mustBeOne |= up;mustBeZero|=1u<<p;reverse[p]=down;
    }
    if(s.neg){
        // If the downstream NOT is necessary for (positive p, negative q),
        // its monotone input must be 0 at p, 1 at q. Every cross demand is
        // possible only when q is not below p in this bank's coordinate order.
        for(unsigned p=0;p<posCount;++p)
            if((mustBeZero>>p&1) && (reverse[p]&mustBeOne))return false;
        // At least one inversion is necessary, so it cannot help reduce the
        // number of live signals. A binary step reduces that number by at most 1.
        if(mustBeOne && s.n>s.budget)return false;
    }
    return true;
}
template<typename F> bool children(const State& s,F visit) {
    if(!s.budget)return false;
    auto emit=[&](unsigned i,unsigned j,Word z,char op,bool unary) {
        if(z==0||z==totalMask||s.has(z))return false;
        State base;base.budget=s.budget-1;base.neg=s.neg-unsigned(unary);
        for(unsigned t=0;t<s.n;++t)if(t!=i&&t!=j)base.add(s.wires[t]);
        base.add(z);
        for(unsigned retain=0;retain<(unary?2u:4u);++retain){
            State t=base;
            if(retain&1)t.add(s.wires[i]);
            if(retain&2)t.add(s.wires[j]);
            t.sort();
            if(!consistent(t))continue;
            Gate g{op,s.wires[i],s.wires[j],z};
            if(visit(t,g))return true;
        }
        return false;
    };
    for(unsigned i=0;i<s.n;++i){
        if(s.neg && emit(i,i,totalMask^s.wires[i],'!',true))return true;
        for(unsigned j=i+1;j<s.n;++j){
            if(emit(i,j,s.wires[i]&s.wires[j],'&',false)||emit(i,j,s.wires[i]|s.wires[j],'|',false))return true;
        }
    }
    return false;
}
bool search(const State&s){
    if(((++visited)&1023)==0 && elapsed()>seconds)throw std::runtime_error("bounded run");
    if(s.has(goalBits)){answer=path;return true;}
    if(!s.budget||dead.count(s))return false;
    bool result=children(s,[&](const State&t,Gate g){
        path.push_back(g);bool hit=search(t);path.pop_back();return hit;
    });
    if(!result&&dead.size()<150000)dead.insert(s);
    return result;
}
std::vector<Word> rawColumns(){
    std::vector<Word> raw;
    for(int i=0;i<8;++i){
        Word w=0;
        for(unsigned j=0;j<samples.size();++j)w|=Word((samples[j]>>i)&1)<<j;
        raw.push_back(w);
    }
    return raw;
}
bool control(bool signedInput){
    std::vector<Word> values=rawColumns();
    if(signedInput)values[1]^=totalMask;
    struct Physical{char op;unsigned a,b;};
    std::vector<Physical> gates;
    auto step=[&](char op,unsigned a,unsigned b){
        gates.push_back({op,a,b});
        Word av=values[a],bv=values[b];
        values.push_back(op=='!'?(av^totalMask):op=='&'?(av&bv):(av|bv));
        return unsigned(values.size()-1);
    };
    unsigned one=signedInput?step('!',1,1):1;
    unsigned s0=step('&',0,step('|',step('|',one,4),5));
    unsigned s3=step('&',3,step('|',step('|',2,4),7));
    unsigned s2=step('&',2,step('|',one,6));
    unsigned s5=step('&',5,step('|',6,7));
    unsigned final=step('|',step('|',s0,s3),step('|',s2,s5));
    if(values[final]!=goalBits||gates.size()!=13+unsigned(signedInput))return false;
    for(int row=0;row<256;++row){
        std::vector<bool> vals;
        for(int i=0;i<8;++i)vals.push_back(bool((row>>i)&1)^(signedInput&&i==1));
        for(auto g:gates){
            bool a=vals[g.a],b=vals[g.b];
            vals.push_back(g.op=='!'?!a:(g.op=='&'?(a&&b):(a||b)));
        }
        if(vals[final]!=target(row))return false;
    }
    std::vector<State> states(gates.size()+1);
    uint32_t bank=1u<<final;
    for(int stage=gates.size();stage>=0;--stage){
        State& q=states[stage];q.budget=gates.size()-stage;q.neg=signedInput&&stage==0;
        for(unsigned i=0;i<8+gates.size();++i)if((bank>>i)&1)q.add(values[i]);
        q.sort();if(!consistent(q))return false;
        if(stage){
            unsigned z=7+stage;
            if(!(bank>>z&1))return false;
            auto g=gates[stage-1];
            bank=(bank^(1u<<z))|(1u<<g.a)|(1u<<g.b);
        }
    }
    for(unsigned i=0;i<gates.size();++i)
        if(!children(states[i],[&](const State& t,Gate){return t==states[i+1];}))return false;
    return true;
}
int main(int argc,char**argv){
    if(argc==2 && std::string(argv[1])=="--control"){
        initialize();
        if(!control(false)||!control(true))return 1;
        std::puts("CONTROL PASS: 13 positive-gate and 14 one-inversion paths, all 256 rows and all 27 steps");return 0;
    }
    if(argc!=5){std::fprintf(stderr,"usage: seeded-eight neg-budget lo hi seconds\n");return 2;}
    unsigned allowed=std::strtoul(argv[1],nullptr,10);
    int lo=std::atoi(argv[2]),hi=std::atoi(argv[3]);
    seconds=std::atof(argv[4]);if(allowed>1||lo<0||hi<=lo||seconds<=0||seconds>120)return 2;
    initialize();
    std::vector<Word> raw=rawColumns();
    raw.push_back(raw[2]|raw[5]);
    int bucket=0,masks=0;beginTime=Clock::now();
    try{
        for(unsigned m=1;m<(1u<<9);++m){
            State initial;initial.budget=12;initial.neg=allowed;
            for(unsigned j=0;j<9;++j)if(m>>j&1)initial.add(raw[j]);
            initial.sort();
            if(!consistent(initial))continue;
            ++masks;
            bool hit=children(initial,[&](const State&t,Gate g){
                int index=bucket++;if(index<lo||index>=hi)return false;
                path={g};return search(t);
            });
            if(hit){
                std::printf("SAMPLE_WITNESS sourceMask=%u bucket=%d len=%zu\n",m,bucket-1,answer.size());
                for(auto g:answer)std::printf("%c %u %u %u\n",g.op,g.a,g.b,g.z);
                return 0;
            }
        }
    }catch(const std::runtime_error& e){
        std::printf("UNKNOWN neg=%u range=[%d,%d) nextBucket=%d visited=%llu sec=%.2f\n",allowed,lo,hi,bucket,(unsigned long long)visited,elapsed());return 0;
    }
    std::printf("EXHAUSTED neg=%u range=[%d,%d) totalBuckets=%d possibleBanks=%d visited=%llu sec=%.2f\n",allowed,lo,hi,bucket,masks,(unsigned long long)visited,elapsed());
}
