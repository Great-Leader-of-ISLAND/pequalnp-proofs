// Exact, resumable refinement of the cost-six one-bank scan.
// Build in the same directory as the unchanged 3004-fixed-bank.cpp.
#define main bank_reference_main
#include "3004-fixed-bank.cpp"
#undef main
#include <memory>

struct RowTable { array<U,58> toFalse{}, fromTrue{}; };
struct Context { unsigned r, freeEdges; U negTrue; };

struct Six : Game {
    int cap, maxSeconds;
    unsigned rows[58]{};
    vector<pair<unsigned,U>> newTrue[58],newFalse[58];
    vector<unique_ptr<RowTable>> projected;
    unsigned long long supportDead=0,projectionDead=0;
    vector<unsigned> pending;
    chrono::steady_clock::time_point began;

    Six(int sec): Game(sec), cap(k+1), maxSeconds(sec), projected(1<<14), began(chrono::steady_clock::now()) {
        if(k!=6) abort();
        for(int i=0;i<21;i++) rows[i]=E[i];
        for(int i=0;i<37;i++) rows[i+21]=N[i];
        for(int a=0;a<58;a++) {
            U plus[14]{},minus[14]{};
            for(int b=0;b<58;b++) {
                unsigned d=rows[a]&~rows[b], rev=rows[b]&~rows[a];
                if(d && !(d&(d-1))) plus[first(d)]|=U(1)<<b;
                if(rev && !(rev&(rev-1))) minus[first(rev)]|=U(1)<<b;
            }
            for(int v=0;v<14;v++) {
                if(plus[v])newTrue[a].push_back({1u<<v,plus[v]});
                if(minus[v])newFalse[a].push_back({1u<<v,minus[v]});
            }
        }
    }
    static unsigned forcedBy(const vector<pair<unsigned,U>>& queries,U opposite) {
        unsigned f=0;
        for(auto [v,mask]:queries)if(mask&opposite)f|=v;
        return f;
    }
    const RowTable& table(unsigned support) {
        if(!projected[support]) {
            auto t=make_unique<RowTable>();
            for(int a=0;a<58;a++)for(int b=0;b<58;b++)
                if(!(rows[a]&~rows[b]&support)) {
                    t->toFalse[a]|=U(1)<<b;
                    t->fromTrue[b]|=U(1)<<a;
                }
            projected[support]=move(t);
        }
        return *projected[support];
    }
    bool compatible(unsigned f,U on,U off,int last,bool turnOn,bool wasLocked) {
        const auto &t=table(f);
        if(wasLocked && last>=0)
            return turnOn ? !(off&t.toFalse[last]) : !(on&t.fromTrue[last]);
        for(U a=on;a;a&=a-1)if(off&t.toFalse[__builtin_ctzll(a)])return false;
        return true;
    }
    void walk(U on,U off,unsigned freeBits,unsigned f,bool testL,bool testH,
              int last=-1,bool turnOn=false,bool wasLocked=false) {
        if(timed)return;
        nodes++;
        if(!(nodes&4095) && chrono::duration<double>(chrono::steady_clock::now()-began).count()>maxSeconds) {
            timed=true;
            return;
        }
        int used=pop(f);
        if(used>cap) {supportDead++;return;}
        bool locked=used==cap;
        if(locked && !compatible(f,on,off,last,turnOn,wasLocked)){projectionDead++;return;}
        unsigned p=unsigned(on&ALLP),high=p|freeBits;
        if(!high||p==ALLP)return;
        if(testH&&!suffixOK(high)){sufDead++;return;}
        if(testL&&bankRank(p)>cap){bankDead++;return;}
        if(!freeBits) {pending.push_back(p);return;}
        unsigned v=freeBits&-freeBits,rem=freeBits^v;
        int e=first(v);
        walk(on|v,off,rem,f|forcedBy(newTrue[e],off),true,false,e,true,locked);
        walk(on,off|v,rem,f|forcedBy(newFalse[e],on),false,true,e,false,locked);
    }
    void scan(int lo,int hi) {
        vector<Context> all;
        Context c;
        while(cin>>c.r>>c.freeEdges>>c.negTrue)all.push_back(c);
        int total=int(all.size());
        if(lo<0||lo>total||hi<lo)abort();
        hi=min(hi,total);
        cout<<"ORBIT_UNIVERSE "<<k<<" "<<total<<" range=["<<lo<<","<<hi<<")"<<endl;
        int j=lo;
        for(;j<hi;j++) {
            auto [r,em,negs]=all[j];
            R=int(r);bad=negs;usable={0};
            if(!bad||pop(r)>25-k)abort();
            for(unsigned i=0;i<14;i++)if(!(sup[1u<<i]&~bad))usable.push_back(inc[i]);
            U on=(bad<<21)|(ALLP^em), off=(ALLN^bad)<<21;
            unsigned f=0;
            for(U a=on;a;a&=a-1)f|=forcedBy(newTrue[__builtin_ctzll(a)],off);
            pending.clear();
            walk(on,off,em,f,true,true);
            if(timed)break;
            for(auto v:pending)cout<<"CTX "<<j<<" REMAIN "<<R<<" "<<v<<" "<<bad<<"\n";
            leaves+=pending.size();
        }
        cout<<"CTX_RANGE "<<lo<<" "<<j<<" requested_end="<<hi<<" universe="<<total<<endl;
        cout<<"BANK_CHUNK "<<k<<" "<<(timed?"INCOMPLETE":"COMPLETE")<<" orbits_finished="<<(j-lo)
            <<" visited="<<nodes<<" bank_pruned="<<bankDead<<" suffix_pruned="<<sufDead
            <<" forced_pruned="<<supportDead<<" projected_pruned="<<projectionDead
            <<" remaining="<<leaves<<endl;
    }
};
int main(int argc,char**argv) {
    auto g=make_unique<Six>(argc>3?atoi(argv[3]):100);
    g->scan(argc>1?atoi(argv[1]):0,argc>2?atoi(argv[2]):100000000);
}
