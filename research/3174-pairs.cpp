// Bounded search for the nine-input edge function with a supplied OR and inverted pin.
// Each two-zero restriction listed below leaves the same seven-input theta graph.
// Its proved lower bound is 11 binary gates even with arbitrary free inversions.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <string>
using Bits=uint64_t;
using Clock=std::chrono::steady_clock;
constexpr int cuts[][2]={{0,4},{1,6},{2,7},{3,4},{4,6},{4,7},{5,7},{6,7},{6,8}};
constexpr int edges[][2]={{0,1},{1,2},{2,3},{3,4},{0,4},{0,5},{1,6},{2,7},{3,8},{5,7},{6,8},{5,8}};
bool target(int x){for(auto& e:edges)if((x>>e[0])&(x>>e[1])&1)return true;return false;}
std::array<std::array<Bits,8>,9> region{};
bool useAlias=false;
struct Signal {
  Bits bits=0;uint16_t zero=0,one=0;
  std::array<Bits,8> truth{};
  bool operator<(const Signal& b)const{return bits!=b.bits?bits<b.bits:truth<b.truth;}
  bool fixed()const{return std::all_of(truth.begin(),truth.end(),[](auto x){return x==0;})||std::all_of(truth.begin(),truth.end(),[](auto x){return x==~Bits(0);});}
  bool operator==(const Signal& b)const{return bits==b.bits && zero==b.zero && one==b.one && truth==b.truth;}
};
using Loss=std::array<uint8_t,9>;
struct Frontier{
  std::array<Signal,16> data{};Loss saved{};int n=0,k=0;
  void add(Signal s){data[n++]=s;}
  bool operator==(const Frontier& t)const{return n==t.n&&k==t.k&&saved==t.saved&&std::equal(data.begin(),data.begin()+n,t.data.begin());}
};
struct Hash{size_t operator()(const Frontier& s)const{size_t h=s.n+71*s.k;for(auto v:s.saved)h=257*h+v;
 for(int i=0;i<s.n;++i){auto a=s.data[i];h=(h^a.bits)*1099511628211ULL;h=(h^(a.zero+1024u*a.one))*1099511628211ULL;}return h;}};
struct Cover{std::array<Bits,5>w{};void merge(const Cover& c){for(int i=0;i<5;++i)w[i]|=c.w[i];}bool operator==(const Cover& c)const{return w==c.w;}};
int pos,neg,cap,seconds;Bits wanted,full;
Cover all;std::unordered_map<Bits,Cover> memoCover;
std::unordered_set<Frontier,Hash> dead;
long long visits,cutPrunes,kwPrunes;Clock::time_point start;
double elapsed(){return std::chrono::duration<double>(Clock::now()-start).count();}
Cover cover(Bits x){
 if(auto it=memoCover.find(x);it!=memoCover.end())return it->second;
 Cover c;for(int i=0;i<pos;++i)if(x>>i&1)for(int j=0;j<neg;++j)if(!(x>>(pos+j)&1)){
 int z=i*neg+j;c.w[z/64]|=Bits(1)<<(z%64);}
 if(memoCover.size()<100000)memoCover.emplace(x,c);return c;
}
Signal combine(bool join,Signal a,Signal b){
 Signal v;
 if(join){v={a.bits|b.bits,uint16_t(a.zero&b.zero),uint16_t(a.one|b.one)};}
 else{v={a.bits&b.bits,uint16_t(a.zero|b.zero),uint16_t(a.one&b.one)};}
 for(int t=0;t<8;++t)v.truth[t]=join?(a.truth[t]|b.truth[t]):(a.truth[t]&b.truth[t]);
 v.zero=v.one=0;
 for(int c=0;c<9;++c){bool z=true,o=true;
  for(int t=0;t<8;++t){Bits r=region[c][t];if(v.truth[t]&r)z=false;if((~v.truth[t])&r)o=false;}
  if(z)v.zero|=1U<<c;if(o)v.one|=1U<<c;
 }return v;
}
bool spend(Loss& v,Signal a,Signal b){
 auto free=a.zero|a.one|b.zero|b.one;
 for(int i=0;i<9;++i)if(free>>i&1)if(++v[i]>cap)return false;
 return true;
}
bool tightConflict(const Frontier& s,const std::array<Cover,16>& covers){
 Cover hit,shared;uint16_t red[16]{},blue[16]{};uint32_t rows[16]{},cols[16]{};
 for(int i=0;i<s.n;++i)for(int t=0;t<5;++t){shared.w[t]|=hit.w[t]&covers[i].w[t];hit.w[t]|=covers[i].w[t];}
 for(int i=0;i<s.n;++i){
  for(int t=0;t<5;++t){auto v=covers[i].w[t]&~shared.w[t];while(v){
   int z=t*64+__builtin_ctzll(v);v&=v-1;rows[i]|=1U<<(z/neg);cols[i]|=1U<<(z%neg);}}
  for(int j=0;j<i;++j){if(rows[i]&rows[j]){red[i]|=1U<<j;red[j]|=1U<<i;}
   if(cols[i]&cols[j]){blue[i]|=1U<<j;blue[j]|=1U<<i;}if(red[i]&blue[i])return true;}
 }

 return false;
}
bool noCotree=false, rawOnly=false, noCoverage=false;std::array<Bits,8> goalTruth{};
bool search(const Frontier& s);
long long runwayPrunes=0;
bool residual_budget(const Frontier& state){
 for(int cut=0;cut<9;++cut){
  unsigned fixed=0;
  for(int i=0;i<state.n;++i)
   if((state.data[i].zero|state.data[i].one)>>cut&1)++fixed;
  if(state.saved[cut]+fixed>cap)return false;
 }
 return true;
}
template<class Test> bool moves(const Frontier& s, Test accept){
 if(!residual_budget(s)){++runwayPrunes;return false;}
 std::array<Cover,16> covers{};for(int i=0;i<s.n;++i)covers[i]=cover(s.data[i].bits);
 if(!noCotree&&s.n==s.k+1&&tightConflict(s,covers)){++kwPrunes;return false;}
 for(int i=0;i<s.n;++i)for(int j=i+1;j<s.n;++j){
  Signal a=s.data[i],b=s.data[j];Frontier rest;rest.k=s.k-1;rest.saved=s.saved;

  Cover others;for(int v=0;v<s.n;++v)if(v!=i&&v!=j){rest.add(s.data[v]);others.merge(covers[v]);}
  for(bool join:{false,true}){
   auto z=combine(join,a,b);if(rawOnly)z.zero=z.one=0;
   if(z.fixed()||std::binary_search(s.data.begin(),s.data.begin()+s.n,z))continue;
   Frontier charged=rest;
   if(!spend(charged.saved,a,b)){++cutPrunes;continue;}
   if(useAlias){
    for(int c=0;c<9;++c)if(!((a.zero|b.zero|a.one|b.one)>>c&1)){
     bool left=true,right=true;
     for(int t=0;t<8;++t){auto r=region[c][t];if((a.truth[t]^z.truth[t])&r)left=false;if((b.truth[t]^z.truth[t])&r)right=false;}
     if(left||right||((z.zero|z.one)>>c&1))++charged.saved[c];
    }
   }
   Cover with=others;with.merge(cover(z.bits));
   for(int m=0;m<4;++m){
    if(rest.n+1+(m&1)+(m>>1)>s.k)continue;
    auto cc=with;if(m&1)cc.merge(covers[i]);if(m&2)cc.merge(covers[j]);if(!noCoverage&&!(cc==all))continue;
    Frontier t=charged;t.add(z);if(m&1)t.add(a);if(m&2)t.add(b);std::sort(t.data.begin(),t.data.begin()+t.n);
    if(accept(t))return true;
   }
  }
 }
 return false;
}
bool search(const Frontier& s){
 if((++visits&255)==0&&elapsed()>seconds)throw 1;
 // A correctly cone-pruned circuit always ends in a singleton output.
 if(s.n==1&&s.data[0].truth==goalTruth)return true;
 if(!s.k||s.n>s.k+1||dead.count(s))return false;
 if(!residual_budget(s)){++runwayPrunes;return false;}
 std::array<Cover,16> local{};for(int i=0;i<s.n;++i)local[i]=cover(s.data[i].bits);
 if(!noCotree&&s.n==s.k+1&&tightConflict(s,local)){++kwPrunes;return false;}
 if(moves(s,search))return true;
 if(dead.size()<14000)dead.insert(s);return false;
}

int control(){
 struct G{bool join;int a,b;};
 const G trace[]={{1,0,6},{0,1,11},{1,1,3},{1,13,7},{0,2,14},{0,4,10},{1,0,7},{0,5,17},{1,3,6},{1,19,5},{0,8,20},{1,12,15},{1,16,18},{1,22,23},{1,24,21}};
 std::array<Signal,26> signals{};Loss lost{};cap=5;
 for(int i=0;i<9;++i)for(int z=0;z<9;++z)if(i==cuts[z][0]||i==cuts[z][1])signals[i].zero|=1U<<z;
 signals[9].one=signals[0].zero;
 signals[10]=combine(true,signals[0],signals[3]);if(!spend(lost,signals[0],signals[3]))return 3;
 for(int g=0;g<15;++g){
  auto x=trace[g];signals[11+g]=combine(x.join,signals[x.a],signals[x.b]);
  if(!spend(lost,signals[x.a],signals[x.b]))return 4;
 }
 for(int x=0;x<512;++x){
  bool vals[26]{};for(int i=0;i<9;++i)vals[i]=x>>i&1;
  vals[9]=!vals[0];vals[10]=vals[0]||vals[3];
  for(int g=0;g<15;++g){auto t=trace[g];vals[11+g]=t.join?(vals[t.a]||vals[t.b]):(vals[t.a]&&vals[t.b]);}
  if(vals[25]!=target(x))return 5;
  for(int j=0;j<9;++j)if(!vals[cuts[j][0]]&&!vals[cuts[j][1]])for(int i=0;i<26;++i){
   if((signals[i].zero>>j&1)&&vals[i])return 6;
   if((signals[i].one>>j&1)&&!vals[i])return 7;
  }
 }
 std::printf("CONTROL 512 inputs, 9 theta restrictions, 26 wires; certified gate losses");
 for(int c:lost)std::printf(" %d",c);std::puts("");return 0;
}

int replay(const std::vector<Signal>& raw){
 struct Gate{bool join;int a,b;};const Gate shape[]={{1,9,6},{0,1,10},{1,3,7},{0,2,12},{1,3,0},{0,4,14},{1,0,7},{1,16,8},{0,5,17},{1,3,6},{0,8,19},{1,11,13},{1,21,15},{1,22,18},{1,23,20}};
 std::array<Signal,25> pool{};std::copy(raw.begin(),raw.begin()+10,pool.begin());
 std::array<Loss,16> losses{};cap=5;
 if(!spend(losses[0],pool[0],pool[2]))return 8;
 for(int k=0;k<15;++k){
  auto g=shape[k];pool[10+k]=combine(g.join,pool[g.a],pool[g.b]);
  losses[k+1]=losses[k];if(!spend(losses[k+1],pool[g.a],pool[g.b]))return 9;
 }
 if(pool[24].bits!=wanted)return 10;
 unsigned active=1U<<24;std::array<Frontier,16> trace;
 for(int k=15;k>=0;--k){
  auto& q=trace[k];q.k=15-k;q.saved=losses[k];
  for(int i=0;i<25;++i)if(active>>i&1)q.add(pool[i]);
  std::sort(q.data.begin(),q.data.begin()+q.n);
  if(k){auto g=shape[k-1];active&=~(1U<<(9+k));active|=1U<<g.a;active|=1U<<g.b;}
 }
 for(int k=0;k<15;++k)if(!moves(trace[k],[&](const Frontier& t){return t==trace[k+1];})){
  std::printf("REPLAY failed at gate %d\n",k);return 11;}
 std::puts("REPLAY accepted all 15 transitions with the actual OR(0,2) seed, all nine loss limits and the tight-width obstruction.");
 return 0;
}
int main(int argc,char** argv){
 for(int c=0;c<9;++c)for(int r=0;r<512;++r)if(!(r>>cuts[c][0]&1)&&!(r>>cuts[c][1]&1))region[c][r/64]|=Bits(1)<<(r%64);
 if(argc!=6)return 2;
 int leftVertex=atoi(argv[4]),rightVertex=atoi(argv[5]);
 if(leftVertex<0||leftVertex>=9||rightVertex<0||rightVertex>=9||leftVertex==rightVertex)return 2;
 for(int v=0;v<9;++v){
  bool necessary=false;
  for(int lo=0;lo<512;++lo){
   int hi=lo|(1<<v);
   int seedMask=(1<<leftVertex)|(1<<rightVertex);
   if(!target(lo)&&target(hi)&&bool(lo&seedMask)==bool(hi&seedMask))necessary=true;
  }
  if(!necessary)return 6;
 }
 std::string variant=argv[3];
 noCotree=variant=="plain"||variant=="rawplain";rawOnly=variant=="raw"||variant=="rawplain";
 useAlias=(variant=="alias"||variant=="aliasplain");if(variant=="aliasplain")noCotree=true;
 noCoverage=variant=="bare";if(noCoverage)noCotree=true;
 int pivot=atoi(argv[1]);seconds=atoi(argv[2]);if((pivot!=0&&pivot!=-1)||seconds<1||seconds>40)return 2;
 std::vector<int> yes,no;
 for(int r=0;r<512;++r){bool y=target(r),extreme=true;for(int j=0;j<9;++j){
  bool fixed=pivot==j || (pivot==9&&(j==0||j==2));
  if(!fixed&&bool((r>>j)&1)==y&&target(r^(1<<j))==y)extreme=false;
 }if(extreme)(y?yes:no).push_back(r);}
 pos=yes.size();neg=no.size();auto rows=yes;rows.insert(rows.end(),no.begin(),no.end());
 if(rows.size()>=64||pos>=32||neg>=32||pos*neg>320)return 2;
 wanted=(Bits(1)<<pos)-1;full=(Bits(1)<<rows.size())-1;all=cover(wanted);
 for(int r=0;r<512;++r)if(target(r))goalTruth[r/64]|=Bits(1)<<(r%64);
 std::vector<Signal> raw;
 for(int j=0;j<9;++j){Signal a;for(int r=0;r<(int)rows.size();++r)if(rows[r]>>j&1)a.bits|=Bits(1)<<r;
  for(int z=0;z<9;++z)if(cuts[z][0]==j||cuts[z][1]==j)a.zero|=1U<<z;
  for(int x=0;x<512;++x)if(x>>j&1)a.truth[x/64]|=Bits(1)<<(x%64);
  raw.push_back(a);}
 auto seed=combine(true,raw[leftVertex],raw[rightVertex]);raw.push_back(seed);
 if(pivot>=0){auto a=raw[pivot];Signal b{a.bits^full,a.one,a.zero};for(int t=0;t<8;++t)b.truth[t]=~a.truth[t];raw.push_back(b);}
 if(variant=="replay")return 2;
 cap=3;Loss initial{};if(!spend(initial,raw[leftVertex],raw[rightVertex]))return 3;
 int roots=0;start=Clock::now();const char* result="EXHAUSTED";
 try{for(unsigned mask=1;mask<(1U<<raw.size());++mask){
  // Each missing raw is detected by a target-changing row pair keeping OR(0,2) fixed.
  if((mask&511)!=511)continue;
  if(!(mask&(1U<<9))&&!(pivot==9&&(mask&(1U<<10))))continue;
  if(pivot>=0&&!(mask&(1U<<10)))continue; // ordinary case is run separately
  Cover cc;Frontier q;q.k=13;q.saved=initial;
  for(int i=0;i<(int)raw.size();++i)if(mask>>i&1){q.add(raw[i]);cc.merge(cover(raw[i].bits));}
  if(!noCoverage&&!(cc==all))continue;
  ++roots;std::sort(q.data.begin(),q.data.begin()+q.n);
  if(search(q)){result="FOUND_BOUNDARY";break;}
 }}catch(int){result="UNKNOWN";}
 std::printf("variant=%s memo=%zu residual_prunes=%lld ",variant.c_str(),dead.size(),runwayPrunes);
 std::printf("OR(%d,%d) ",leftVertex,rightVertex);
 std::printf("nine cuts pivot=%d rows=%zu roots=%d %s visits=%lld cut_prunes=%lld cotree_prunes=%lld sec=%.3f\n",pivot,rows.size(),roots,result,visits,cutPrunes,kwPrunes,elapsed());
}
