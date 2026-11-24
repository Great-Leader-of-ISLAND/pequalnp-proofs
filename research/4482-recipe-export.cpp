// Exact live-frontier search for L-meta-4482. No third-party dependencies.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <cstdio>
#include <string>
#include <unordered_map>
#include <vector>
using namespace std;
using U=uint64_t; using Word=array<U,8>;
static constexpr int ed[12][2]={{0,1},{1,2},{2,3},{3,4},{4,0},{0,5},{1,6},{2,7},{3,8},{5,7},{6,8},{8,5}};
static int pop(int x){return __builtin_popcount(unsigned(x));}
static bool label(int x){for(auto &e:ed)if((x>>e[0]&x>>e[1])&1)return true;return false;}
// Six final slots, no remaining fanout. Each block of current wires must
// supply one monotone observed bit separating every pair lost outside it.
struct TightBlocks4482 {
  struct Edge {unsigned p,n,diff;};
  std::vector<Edge> edges;
  std::vector<signed char> allowed,parts;
  std::vector<unsigned> positive;
  std::vector<unsigned> negatives;
  int width;
  TightBlocks4482(const std::array<unsigned,512>& codes,int w,
      const std::vector<std::pair<int,int>>& pairs):allowed(1<<w,-1),parts(7*(1<<w),-1),
      positive(1<<w),width(w) {
    edges.reserve(pairs.size());negatives.reserve(pairs.size());
    for(auto [lo,hi]:pairs) {
      unsigned n=codes[lo],p=codes[hi];
      // Every supplied pair is comparable in the raw cube.
      if(n&~p)std::abort();
      edges.push_back({p,n,p^n});
    }
  }
  bool good(unsigned B) {
    if(allowed[B]>=0)return bool(allowed[B]);
    negatives.clear();
    for(auto e:edges)if(!(e.diff&~B)){
      positive[e.p&B]=B;
      negatives.push_back(e.n&B);
    }
    for(unsigned n:negatives){
      unsigned u=n;
      for(;;) {
        if(positive[u]==B){allowed[B]=0;return false;}
        if(!u)break;
        u=(u-1)&n;
      }
    }
    allowed[B]=1;return true;
  }

  int anchor() {
    unsigned N=1U<<width;std::vector<unsigned> options;
    for(unsigned a=0;a<N;a++)if(__builtin_popcount(a)==7)options.push_back(a);
    for(unsigned b=1;b<N&&!options.empty();b++){
      int n=__builtin_popcount(b);
      if(n<2||n>width-5||!good(b))continue;
      options.erase(std::remove_if(options.begin(),options.end(),[&](unsigned a){
        unsigned x=a&b;return x&&(x&(x-1));}),options.end());
    }
    return options.empty()?-1:int(options.front());
  }
  using Mask=std::array<uint64_t,5>;
  static bool blank(const Mask& a){return !(a[0]|a[1]|a[2]|a[3]|a[4]);}
  static int least(const Mask& a){for(int j=0;j<5;j++)if(a[j])return 64*j+__builtin_ctzll(a[j]);return -1;}
  struct Mark {Mask p{},n{};};
  static bool pick(const std::vector<Mark>& marks,unsigned in,Mask p,Mask n,int& e,int& f,int& nodes){
    nodes++;
    if(blank(p)||blank(n))return false;
    if(!in){e=least(p);f=least(n);return true;}
    unsigned l=in&-in;const Mark& v=marks[__builtin_ctz(l)]; Mask lo,hi,upper;
    for(int k=0;k<5;k++){lo[k]=p[k]&~v.p[k];hi[k]=p[k]&v.p[k];upper[k]=n[k]&v.n[k];}
    return pick(marks,in^l,lo,n,e,f,nodes)||pick(marks,in^l,hi,upper,e,f,nodes);
  }
  std::pair<int,int> implicit(unsigned core){
    unsigned limit=1U<<width; std::vector<unsigned> pending;
    for(unsigned b=0;b<limit;b++)if(__builtin_popcount(b)<=width-5&&__builtin_popcount(b&core)>=2)pending.push_back(b);
    std::vector<Mark> marks(width);Mask all{};int rounds=0,nodes=0;
    for(unsigned i=0;i<edges.size();i++){
      auto edge=edges[i];uint64_t g=1ULL<<(i%64);all[i/64]|=g;
      for(int w=0;w<width;w++){if(edge.p>>w&1)marks[w].p[i/64]|=g;if(edge.n>>w&1)marks[w].n[i/64]|=g;}
    }
    while(!pending.empty()){
      unsigned b=pending.front();Mask excl=all;
      for(int w=0;w<width;w++)if(!(b>>w&1))for(int j=0;j<5;j++)excl[j]&=~(marks[w].p[j]^marks[w].n[j]);
      int e,f;if(!pick(marks,b,excl,excl,e,f,nodes))return {-1,nodes};
      unsigned need=edges[e].diff|edges[f].diff,absent=edges[e].p&~edges[f].n;
      if((need&~b)||(absent&b))std::abort();
      pending.erase(std::remove_if(pending.begin(),pending.end(),
        [&](unsigned x){return !(need&~x)&&!(absent&x);}),pending.end());rounds++;
    }
    return {rounds,nodes};
  }
  bool partition(unsigned pool,int slots){
    if(__builtin_popcount(pool)==slots)return true; // physical singleton wires separate their own pairs
    if(slots==1)return good(pool);
    const int i=slots*(1<<width)+pool;
    if(parts[i]>=0)return bool(parts[i]);
    unsigned pivot=pool&-pool, rest=pool^pivot;
    // Enumerate all blocks containing the least remaining wire, not assuming
    // upward or downward closure of block feasibility.
    for(unsigned other=rest;;other=(other-1)&rest) {
      unsigned keep=rest^other;
      if(__builtin_popcount(keep)>=slots-1&&good(other|pivot)&&partition(keep,slots-1)) {
        parts[i]=1;return true;
      }
      if(!other)break;
    }
    parts[i]=0;return false;
  }
};

struct Hash {template<class T> size_t operator()(const T& a)const {U h=0x9e3779b97f4a7c15ULL;for(auto q:a){h^=U(q)+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);}return h;}};
struct Atom {int id,wire;}; struct Gate {bool op;int a,b;}; // op=true means OR
static constexpr int perms[12][9]={{0,1,2,3,4,5,6,7,8},{3,8,5,0,4,2,6,7,1},{0,5,8,3,4,1,7,6,2},{3,2,1,0,4,8,7,6,5},{1,0,5,8,6,2,4,7,3},{8,3,2,1,6,5,4,7,0},{1,2,3,8,6,0,7,4,5},{8,5,0,1,6,3,7,4,2},{2,3,8,5,7,1,4,6,0},{5,0,1,2,7,8,4,6,3},{2,1,0,5,7,3,6,4,8},{5,8,3,2,7,0,6,4,1}};
struct Search {
 vector<int> allowed; array<array<int,512>,12> maps{};vector<array<int,12>> symids;
 vector<int> rows; vector<pair<int,int>> pairs; int missedA=-1,missedB=-1;
 int A,cap,M,m=0,seed,limitDepth;bool seeded,connected,stop=false,found=false;
 std::array<unsigned,16> deadAt{},sampled{},wins{},maxRound{},sumRound{},sumNodes{};
 std::ofstream records,recipes;
 std::unordered_map<Word,unsigned,Hash> derived;
 std::array<Word,9> inputs{};
 unsigned derive(const Word& w,char op,unsigned a,unsigned b){
   auto [it,fresh]=derived.emplace(w,unsigned(derived.size()));
   if(fresh){recipes<<op<<" "<<it->second<<" "<<a;if(op!='R')recipes<<" "<<b;recipes<<'\n';}
   return it->second;
 }
 void recipeRoots(){
   recipes<<"H 1 "<<seeded<<"\n";
   for(unsigned i=0;i<9;i++){
     for(unsigned r=0;r<512;r++)if((r>>i)&1)inputs[i][r>>6]|=1ULL<<(r&63);
     if(derive(inputs[i],'R',i,0)!=i)std::abort();
   }
 }
 void recipeGate(int g){
   std::array<Word,18> bank{};std::array<unsigned,18> ids{};
   for(int i=0;i<9;i++){bank[i]=inputs[perms[g][i]];ids[i]=derived.at(bank[i]);}
   if(seeded){
     for(int j=0;j<8;j++)bank[9][j]=bank[0][j]|bank[2][j];
     ids[9]=derive(bank[9],'O',ids[0],ids[2]);
   }
   unsigned out=10;
   for(auto step:path){
     if(out>=18||step.a<0||step.b<0||unsigned(step.a)>=out||unsigned(step.b)>=out||
       (!seeded&&(step.a==9||step.b==9)))std::abort();
     for(int j=0;j<8;j++)bank[out][j]=step.op?(bank[step.a][j]|bank[step.b][j]):(bank[step.a][j]&bank[step.b][j]);
     ids[out]=derive(bank[out],step.op?'O':'A',ids[step.a],ids[step.b]);out++;
   }
 }

 std::unordered_map<Word,unsigned,Hash> exportIds;
 std::string dest;
 unsigned noAnchor=0,certified=0,maxFuel=0;
 // Words in the file are sorted as unsigned 512-bit natural numbers.
 static bool lessWord(const Word& a,const Word& b) {
   return std::lexicographical_compare(a.rbegin(),a.rend(),b.rbegin(),b.rend());
 }
 unsigned recordWord(const Word& w) {
   auto [it,fresh]=exportIds.emplace(w,unsigned(exportIds.size()));
   if(fresh){
     recipes<<"M "<<it->second<<" "<<derived.at(w)<<'\n';
     records<<"W "<<it->second<<" "<<std::hex<<std::setfill('0');
     for(int l=7;l>=0;l--)records<<std::setw(16)<<w[l];
     records<<std::dec<<'\n';
   }
   return it->second;
 }
 void recordState(const std::vector<Atom>& k) {
   std::vector<int> best;int transporter=-1;
   auto less=[&](int a,int b){return lessWord(data[a],data[b]);};
   for(int g:allowed) {
     std::vector<int> view;
     for(auto a:k){int id=symids.at(a.id)[g];if(id<0)std::abort();view.push_back(id);}
     std::sort(view.begin(),view.end(),less);
     if(best.empty()||std::lexicographical_compare(view.begin(),view.end(),best.begin(),best.end(),less)){
       best=std::move(view);transporter=g;
     }
   }
   recipeGate(transporter);
   const int n=int(best.size());std::array<unsigned,512> codes{};
   for(int row:rows)for(int i=0;i<n;i++)
     codes[row]|=unsigned((data[best[i]][row>>6]>>(row&63))&1)<<i;
   TightBlocks4482 pack(codes,n,pairs);int anchor=pack.anchor(),rounds=0;
   if(anchor>=0){
     auto result=pack.implicit(unsigned(anchor));rounds=result.first;
     if(rounds<0)std::abort();
     certified++;maxFuel=std::max(maxFuel,unsigned(rounds));
   }else noAnchor++;
   std::vector<unsigned> ids;for(auto id:best)ids.push_back(recordWord(data[id]));
   records<<"S "<<n<<" "<<anchor<<" "<<rounds;
   for(auto id:ids)records<<" "<<id;
   records<<'\n';
   if(!records)std::abort();
 }
 U tightChecks=0,tightReject=0,descended=0; U limit,expanded=0,visited=0,pruned=0;double seconds;chrono::steady_clock::time_point start;
 vector<int> names,types;vector<Word> data;vector<int> support;unordered_map<Word,int,Hash> ids;
 unordered_map<vector<int>,unsigned char,Hash> memo;vector<Gate> path,answer;vector<int> outs;
 Search(int mask,bool use,int depth,U lim,double sec,bool conn):A(mask),cap(pop(mask)-3),seed(-1),limitDepth(depth),seeded(use),connected(conn),limit(lim),seconds(sec),start(chrono::steady_clock::now()){
  for(int g=0;g<12;g++){
    if(seeded&&!((perms[g][0]==0&&perms[g][2]==2)||(perms[g][0]==2&&perms[g][2]==0)))continue;
    allowed.push_back(g);
    for(int r=0;r<512;r++)for(int i=0;i<9;i++)if(r>>i&1)maps[g][r]|=1<<perms[g][i];
  }
  for(int i=0;i<9;i++)if(A>>i&1)names.push_back(i);
  m=names.size();M=1<<m;types.resize(M);unordered_map<string,int> ct;
  for(int a=0;a<M;a++){
   int r=0;for(int j=0;j<m;j++)if(a>>j&1)r|=1<<names[j];
   string key;for(int b=0;b<512;b++)if(!(A&b))key+=char(label(r|b));
   auto it=ct.emplace(key,int(ct.size()));types[a]=it.first->second;
  }
 }
 int intern(const Word& w){
  auto it=ids.find(w);if(it!=ids.end())return it->second;
  int id=data.size(),s=0;ids.emplace(w,id);data.push_back(w);
  for(int i=0;i<m;i++)for(int a=0;a<M;a++)if(!(a>>i&1)&&(((w[a>>6]>>(a&63))^(w[(a^(1<<i))>>6]>>((a^(1<<i))&63)))&1)){
   s|=1<<i;break;
  }
  support.push_back(s);return id;
 }
 struct Conf {array<unsigned,16> zero{},one{},swap{};bool ok=true;};
 Conf conflicts(const vector<Atom>& k)const{
  Conf c;unsigned n=k.size(),all=(1U<<n)-1;
  array<unsigned,512> codes{};
  for(int r:rows)for(unsigned i=0;i<n;i++)codes[r]|=((data[k[i].id][r>>6]>>(r&63))&1ULL)<<i;
  for(auto [a,b]:pairs){
    unsigned p=codes[a],q=codes[b],diff=p^q;
    if(!diff){c.ok=false;return c;}
    unsigned i=__builtin_ctz(diff),other=diff&(diff-1);
    if(!other){c.zero[i]|=(~p)&all;c.one[i]|=p;}
    else if(!(other&(other-1)) && (p&diff) && (q&diff)){
      unsigned j=__builtin_ctz(other);c.swap[i]|=1U<<j;c.swap[j]|=1U<<i;
    }
  }
  return c;
 }
 bool done(const vector<Atom>& k,int rem,int parts){
  if(int(k.size())>cap||(connected&&parts!=1))return false;
  answer=path;outs.clear();
  for(int i=0;i<9;i++)if(!(A>>i&1))outs.push_back(i);
  // The abstract separation theorem permits every live port, including the seed.
  // Accepting a relaxed terminal still requires all 512 table rows to agree.
  for(auto a:k)outs.push_back(a.wire);
  int witness[64][2];for(auto &pair:witness)pair[0]=pair[1]=-1;
  int best=1000;
  for(int r=0;r<512;r++){
    int w[32]{};for(int i=0;i<9;i++)w[i]=r>>i&1;w[9]=w[0]|w[2];
    int g=10;for(auto z:answer){w[g++]=z.op?(w[z.a]|w[z.b]):(w[z.a]&w[z.b]);}
    int sig=0;for(unsigned j=0;j<outs.size();j++)sig|=w[outs[j]]<<j;
    int sign=label(r);auto &old=witness[sig][sign];
    if(old<0||pop(r)<pop(old))old=r;
    int other=witness[sig][!sign];if(other<0)continue;
    int extra=(find(rows.begin(),rows.end(),r)==rows.end())+(find(rows.begin(),rows.end(),other)==rows.end());
    int cost=extra*16+pop(r^other);if(cost<best){best=cost;missedA=r;missedB=other;}
  }
  found=true;return true;
 }
 bool dfs(vector<Atom> k,array<int,9> comp,int parts,int rem){
  visited++;if(found||stop)return found;
  if(int(k.size())>cap+rem||(connected&&parts-1>rem)){pruned++;return false;}
  if(done(k,rem,parts))return true;if(!rem)return false;
  sort(k.begin(),k.end(),[](Atom a,Atom b){return a.id<b.id;});
  vector<int> key;
  for(int g:allowed){
    vector<int> view;
    for(auto a:k){
      while(int(symids.size())<=a.id){array<int,12> v;v.fill(-1);symids.push_back(v);}
      int id=symids[a.id][g];
      if(id<0){
        Word u{},src=data[a.id];
        for(int r=0;r<512;r++)if((src[r>>6]>>(r&63))&1){int v=maps[g][r];u[v>>6]|=1ULL<<(v&63);}
        id=intern(u);symids[a.id][g]=id;
      }
      view.push_back(id);
    }
    sort(view.begin(),view.end());
    if(key.empty()||view<key)key=view;
  }
  if(connected){key.push_back(-1);for(int i=0;i<m;i++)key.push_back(comp[i]);}
  auto it=memo.find(key);if(it!=memo.end()&&it->second>=rem)return false;
  memo[key]=rem;
  if((limit&&expanded>=limit)||((expanded&255)==0&&seconds>0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>=seconds)){stop=true;return false;}
  expanded++;
  if(int(k.size())==6+rem){
    tightChecks++;
    std::array<unsigned,512> codes{};
    for(int r:rows)for(unsigned j=0;j<k.size();j++)
      codes[r]|=unsigned((data[k[j].id][r>>6]>>(r&63))&1)<<j;
    TightBlocks4482 price(codes,int(k.size()),pairs);
    if(!price.partition((1U<<k.size())-1,6)){
      tightReject++;recordState(k);return false;
    }
  }
  descended++;

  int n=k.size();auto cf=conflicts(k);if(!cf.ok){cerr<<"internal frontier failure\n";abort();}
  for(int drop: {3,1,2,0}){int newSize=n+1-pop(drop);if(newSize>cap+rem-1)continue;
   for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){
    int ca=comp[__builtin_ctz(unsigned(support[k[i].id]))],cb=comp[__builtin_ctz(unsigned(support[k[j].id]))];
    int pnext=parts-(ca!=cb);if(connected&&pnext-1>rem-1)continue;
    if(drop==3&&(cf.swap[i]>>j&1))continue;
    auto cc=comp;if(ca!=cb){int a=min(ca,cb),b=max(ca,cb);for(int x=0;x<m;x++)if(cc[x]==b)cc[x]=a;}
    for(int op:{0,1}){const auto& bad=op?cf.one:cf.zero;
     if(((drop&1)&&(bad[i]>>j&1))||((drop&2)&&(bad[j]>>i&1)))continue;
     Word w{};for(int h=0;h<(M+63)/64;h++)w[h]=op?(data[k[i].id][h]|data[k[j].id][h]):(data[k[i].id][h]&data[k[j].id][h]);
     int id=intern(w);if(!support[id])continue;
     if(any_of(k.begin(),k.end(),[&](Atom a){return a.id==id;}))continue;
     vector<Atom> next;for(int l=0;l<n;l++)if(!((l==i&&(drop&1))||(l==j&&(drop&2))))next.push_back(k[l]);
     int out=10+path.size();next.push_back({id,out});path.push_back({bool(op),k[i].wire,k[j].wire});
     if(dfs(next,cc,pnext,rem-1))return true;path.pop_back();if(stop)return false;
    }
   }
  }
  return false;
 }
 void run(){
  if(m<6||m>9||limitDepth>7||limitDepth<0||(seeded&&(A&5)!=5)){cerr<<"invalid mask/seed/depth\n";exit(2);}
  vector<Atom> k;array<int,9> cc{};for(int j=0;j<m;j++){Word w{};for(int a=0;a<M;a++)if(a>>j&1)w[a>>6]|=1ULL<<(a&63);k.push_back({intern(w),names[j]});cc[j]=j;}
  int parts=m;
  if(seeded){int a=find(names.begin(),names.end(),0)-names.begin(),b=find(names.begin(),names.end(),2)-names.begin();Word w{};for(int h=0;h<8;h++)w[h]=data[k[a].id][h]|data[k[b].id][h];seed=intern(w);k.push_back({seed,9});cc[b]=cc[a];parts--;}
  for(int j=0;j<m;j++){auto s=k;s.erase(s.begin()+j);if(conflicts(s).ok){cerr<<"a raw input is not independently required; unsupported root\n";exit(3);}}
  dfs(k,cc,parts,limitDepth);
  cout<<(found?"ROW_CANDIDATE":stop?"UNKNOWN":"EXHAUSTED")<<" A="<<A<<" seed="<<seeded<<" gates="<<limitDepth<<" conn="<<connected<<" tightChecks="<<tightChecks<<" tightReject="<<tightReject<<" descended="<<descended<<" states="<<expanded<<" visits="<<visited<<" words="<<data.size()<<" sec="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<'\n';
  if(found){for(auto g:answer)cout<<(g.op?"OR ":"AND ")<<g.a<<' '<<g.b<<'\n';cout<<"observed";for(int w:outs)cout<<' '<<w;cout<<" (selected labels verified)\n";}
 }
};
// Exact positive control for the generalized nine-gate problem, assembled independently
// from three stars, a two-neighbor OR, two additional raw probes, and two outside raws.
static void positive_control(){
 Search s(463,true,9,0,0,true);
 vector<Atom> k;
 for(int j=0;j<s.m;j++){Word w{};for(int a=0;a<s.M;a++)if(a>>j&1)w[a>>6]|=1ULL<<(a&63);k.push_back({s.intern(w),s.names[j]});}
 Word init{};for(int h=0;h<8;h++)init[h]=s.data[k[0].id][h]|s.data[k[2].id][h];
 k.push_back({s.intern(init),9});
 vector<Gate> gates={{1,7,8},{1,9,6},{0,1,11},{1,3,7},{0,2,13},{1,3,6},{0,8,15},{1,12,14},{1,17,16}};
 const vector<int> observed={0,3,10,18};
 for(unsigned g=0;g<gates.size();g++){
  auto x=gates[g];int a=-1,b=-1;
  for(int z=0;z<int(k.size());z++){if(k[z].wire==x.a)a=z;if(k[z].wire==x.b)b=z;}
  if(a<0||b<0||a==b)abort();
  auto live_after=[&](int w){if(find(observed.begin(),observed.end(),w)!=observed.end())return true;
   for(unsigned q=g+1;q<gates.size();q++)if(gates[q].a==w||gates[q].b==w)return true;return false;};
  bool da=!live_after(x.a),db=!live_after(x.b);
  auto cf=s.conflicts(k);const auto& bad=x.op?cf.one:cf.zero;
  if(!cf.ok||(da&&(bad[a]>>b&1))||(db&&(bad[b]>>a&1))||(da&&db&&(cf.swap[a]>>b&1)))abort();
  Word w{};for(int h=0;h<8;h++)w[h]=x.op?(s.data[k[a].id][h]|s.data[k[b].id][h]):(s.data[k[a].id][h]&s.data[k[b].id][h]);
  int id=s.intern(w);vector<Atom> next;for(int z=0;z<int(k.size());z++)if(!(z==a&&da)&&!(z==b&&db))next.push_back(k[z]);
  next.push_back({id,int(10+g)});k=next;s.path.push_back(x);
 }
 if(!s.conflicts(k).ok||!s.done(k,0,1))abort();
 cout<<"CONTROL nine suffix gates, six observations, all nine live transitions and 512 full inputs verified\n";
}
int main(int argc,char**argv){
  if(argc!=3||(std::string(argv[1])!="0"&&std::string(argv[1])!="1")){
    std::cerr<<"usage: export4482 {0|1} output.tsv\n";return 2;
  }
  int seed=std::stoi(argv[1]);std::string out=argv[2];
  if(std::ifstream(out).good()||std::ifstream(out+".part").good()||std::ifstream(out+".recipes").good()||std::ifstream(out+".recipes.part").good()){
    std::cerr<<"output already exists\n";return 2;
  }
  Search s(511,seed,7,400000,180,false);
  for(int lo=0;lo<512;lo++)if(!label(lo))for(int j=0;j<9;j++)
    if(!(lo>>j&1)&&label(lo|(1<<j)))s.pairs.emplace_back(lo,lo|(1<<j));
  if(s.pairs.size()!=258)std::abort();
  for(auto [lo,hi]:s.pairs){s.rows.push_back(lo);s.rows.push_back(hi);}
  std::sort(s.rows.begin(),s.rows.end());
  s.rows.erase(std::unique(s.rows.begin(),s.rows.end()),s.rows.end());
  s.records.open(out+".part");if(!s.records)return 2;
  s.recipes.open(out+".recipes.part");if(!s.recipes)return 2;
  s.recipeRoots();
  s.records<<"H 1 "<<seed<<" 258\n";s.run();
  s.records<<"E "<<s.tightReject<<" "<<s.exportIds.size()<<" "<<s.certified<<" "<<s.noAnchor<<" "<<s.maxFuel<<"\n";
  s.recipes<<"E "<<s.derived.size()<<" "<<s.exportIds.size()<<"\n";s.recipes.close();
  std::cout<<"RECIPE nodes="<<s.derived.size()<<" mapped="<<s.exportIds.size()<<"\n";
  s.records.close();
  bool complete=!s.stop&&!s.found&&s.tightReject==(seed?9445U:2713U);
  std::cout<<"TABLE complete="<<complete<<" states="<<s.tightReject<<" words="<<s.exportIds.size()
    <<" certified="<<s.certified<<" misses="<<s.noAnchor<<" maxFuel="<<s.maxFuel<<"\n";
  if(!complete||!s.records||!s.recipes)return 3;
  if(std::rename((out+".part").c_str(),out.c_str()))return 4;
  if(std::rename((out+".recipes.part").c_str(),(out+".recipes").c_str()))return 4;
  return s.noAnchor?5:0;
}
