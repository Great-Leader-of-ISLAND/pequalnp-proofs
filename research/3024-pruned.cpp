#include <string>
// Exact live-frontier search for the nine-vertex graph on boundary rows.
// Enumerate all sufficient initial subsets, including those which omit a free input.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using Word=uint32_t;
struct Cover {uint64_t b[4]{};};
Cover operator|(Cover a,Cover b){for(int i=0;i<4;++i)a.b[i]|=b.b[i];return a;}
bool operator==(Cover a,Cover b){return a.b[0]==b.b[0]&&a.b[1]==b.b[1]&&a.b[2]==b.b[2]&&a.b[3]==b.b[3];}
const int edges[][2]={{0,1},{1,2},{2,3},{3,4},{0,4},{0,5},{1,6},{2,7},{3,8},{5,7},{6,8},{5,8}};
bool goal(int r){for(auto&e:edges)if((r>>e[0])&(r>>e[1])&1)return true;return false;}
struct State {
  std::array<Word,17>w{}; uint8_t n=0,k=0;
  void add(Word a){w[n++]=a;}
  bool operator==(const State&t) const {return n==t.n&&k==t.k&&std::equal(w.begin(),w.begin()+n,t.w.begin());}
};
struct Hash{size_t operator()(const State&s)const{size_t h=s.k+257*s.n;for(int i=0;i<s.n;i++)h=(h^s.w[i])*1099511628211ULL;return h;}};
int npos,nneg;Word expected,ones;Cover all;
std::unordered_map<Word,Cover> cmap;
std::unordered_set<State,Hash> dead;
size_t memoryCap=180000;long long count=0;std::chrono::steady_clock::time_point start;double secs;
double elapsed(){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();}
Cover cover(Word w){
 if(auto it=cmap.find(w);it!=cmap.end())return it->second;
 Cover v;
 for(int i=0;i<npos;++i)if((w>>i)&1)for(int j=0;j<nneg;++j)if(!((w>>(npos+j))&1)){int z=i*nneg+j;v.b[z/64]|=1ULL<<(z%64);}
 if(cmap.size()<30000)cmap.emplace(w,v);return v;
}
template<class F> bool children(const State&s,F f){
 Cover cache[17];for(int i=0;i<s.n;++i)cache[i]=cover(s.w[i]);
 for(int i=0;i<s.n;++i)for(int j=i+1;j<s.n;++j){
  State r;r.k=s.k-1;Cover rest;
  for(int t=0;t<s.n;++t)if(t!=i&&t!=j){rest=rest|cache[t];r.add(s.w[t]);}
  Word a=s.w[i],b=s.w[j];
  for(auto z:{a&b,a|b}){
   if(z==0||z==ones||std::binary_search(s.w.begin(),s.w.begin()+s.n,z))continue;
   Cover cov=rest|cover(z);
   for(int m=0;m<4;++m){
    if(r.n+1+(m&1)+(m>>1)>s.k)continue;
    Cover c=cov;if(m&1)c=c|cache[i];if(m&2)c=c|cache[j];if(!(c==all))continue;
    State t=r;t.add(z);if(m&1)t.add(a);if(m&2)t.add(b);std::sort(t.w.begin(),t.w.begin()+t.n);
    if(f(t))return true;
   }
  }
 }
 return false;
}
bool rectangle_conflict(const State&s){
  Cover hit,twice;Cover c[17];
  for(int i=0;i<s.n;++i){
    c[i]=cover(s.w[i]);
    for(int k=0;k<4;++k){twice.b[k]|=hit.b[k]&c[i].b[k];hit.b[k]|=c[i].b[k];}
  }
  uint32_t P[17]{},N[17]{};uint16_t red[17]{},blue[17]{};
  for(int i=0;i<s.n;++i){
    for(int k=0;k<4;++k){auto v=c[i].b[k]&~twice.b[k];while(v){int b=__builtin_ctzll(v)+64*k;v&=v-1;P[i]|=1<<(b/nneg);N[i]|=1<<(b%nneg);}}
    for(int j=0;j<i;++j){
      if(P[i]&P[j]){red[i]|=1<<j;red[j]|=1<<i;}
      if(N[i]&N[j]){blue[i]|=1<<j;blue[j]|=1<<i;}
      if((red[i]&blue[i])!=0)return true;
    }
  }
  auto component=[](uint16_t keep,const uint16_t *g){
    uint16_t seen=0,todo=keep&-keep;
    while(todo){uint16_t v=todo&-todo;todo^=v;seen|=v;todo|=(keep & g[__builtin_ctz(v)] & ~seen);}
    return seen;
  };
  uint16_t stack[32]{};int top=0;stack[top++]=(1<<s.n)-1;
  while(top){auto mask=stack[--top];if((mask&(mask-1))==0)continue;
    uint16_t left=component(mask,red);if(left==mask)left=component(mask,blue);
    if(left==mask)return true;
    stack[top++]=left;stack[top++]=mask^left;
  }
  return false;
}
bool dfs(const State&s){
 if((++count&255)==0&&elapsed()>secs)throw 1;
 if(std::binary_search(s.w.begin(),s.w.begin()+s.n,expected))return true;
 if(!s.k||s.n>s.k+1||dead.count(s))return false;
 if(s.n==s.k+1 && rectangle_conflict(s))return false;
 if(children(s,dfs))return true;
 if(dead.size()<memoryCap)dead.insert(s);return false;
}


int seeded_control(const std::vector<int>& rows) {
 struct Gate {bool join; int a,b;};
 // Nine raw bits, an unused complement at wire nine, then OR(0,3).
 const Gate gates[]={{1,0,6},{0,1,11},{1,1,3},{1,13,7},{0,2,14},{0,4,10},{1,0,7},{0,5,17},{1,3,6},{1,19,5},{0,8,20},{1,12,15},{1,16,18},{1,22,23},{1,24,21}};
 std::array<Word,26> word{};
 for(int r=0;r<512;++r) {
  std::array<bool,26> value{};for(int i=0;i<9;++i)value[i]=(r>>i)&1;
  value[9]=!value[0];value[10]=value[0]||value[3];
  for(int k=0;k<15;++k){auto g=gates[k];value[11+k]=g.join?(value[g.a]||value[g.b]):(value[g.a]&&value[g.b]);}
  if(value[25]!=goal(r))return 7;
  auto it=std::find(rows.begin(),rows.end(),r);
  if(it!=rows.end())for(int i=0;i<26;++i)if(value[i])word[i]|=1U<<(it-rows.begin());
 }
 unsigned active=1U<<25;std::array<State,16> trace;
 for(int k=15;k>=0;--k) {
  State t;t.k=15-k;for(int i=0;i<26;++i)if((active>>i)&1)t.add(word[i]);
  std::sort(t.w.begin(),t.w.begin()+t.n);trace[k]=t;
  if(k){auto g=gates[k-1];active &= ~(1U<<(10+k));active |= (1U<<g.a)|(1U<<g.b);}
 }
 for(int k=0;k<15;++k)if(!children(trace[k],[&](const State& t){return t==trace[k+1];}))return 8;
 puts("Positive control: 512 truth rows and all 15 forward live-cone transitions reproduced.");return 0;
}
int main(int argc,char **argv){
 if(argc!=7)return 2;
 int inverted=atoi(argv[1]), a=atoi(argv[2]), b=atoi(argv[3]), budget=atoi(argv[4]);
 int marked=(inverted>=0&&inverted<9)?inverted:-1;
 secs=atof(argv[5]); int bucket=atoi(argv[6]);
 if((inverted < -1 || inverted > 9)||a<0||a>8||b<0||b>8||budget<1||budget>16||secs<0||secs>30)return 2;
 memoryCap=200000;
 std::vector<int> pos,neg;
 for(int r=0;r<512;++r){
   bool y=goal(r),good=true;
   for(int j=0;j<9;++j)if(j!=marked&&bool(r>>j&1)==y&&goal(r^(1<<j))==y)good=false;
   if(good)(y?pos:neg).push_back(r);
 }
 std::vector<int> rows=pos;rows.insert(rows.end(),neg.begin(),neg.end());
 npos=pos.size();nneg=neg.size();if(rows.size()>32||npos*nneg>256)return 3;
 expected=(1U<<npos)-1; ones=rows.size()==32?~0U:(1U<<rows.size())-1; all=cover(expected);
 if(std::string(argv[6])=="control") return seeded_control(rows);
 std::vector<Word> full;
 for(int i=0;i<9;++i){Word z=0;for(size_t j=0;j<rows.size();++j)if(rows[j]>>i&1)z|=1U<<j;full.push_back(z);}
 Word seeded=full[a]|full[b];full.push_back(seeded);
 Word negword=inverted<0?0:(ones^full[inverted]);
 if(inverted>=0)full.push_back(negword);
 std::sort(full.begin(),full.end());full.erase(std::unique(full.begin(),full.end()),full.end());
 printf("rows=%zu pos=%d neg=%d pivot=%d budget=%d\n",rows.size(),npos,nneg,inverted,budget);
 int ix=0;start=std::chrono::steady_clock::now();
 for(unsigned subset=1;subset<(1U<<full.size());++subset){
   State q;q.k=budget;Cover cc;for(size_t i=0;i<full.size();++i)if((subset>>i)&1){q.add(full[i]);cc=cc|cover(full[i]);}
   if(!(cc==all))continue;
   // A 13-binary-gate implementation with only raw literals contradicts the checked signed lower bound 14.
   auto has=[&](Word v){return std::binary_search(q.w.begin(),q.w.begin()+q.n,v);};
   if(!has(seeded) && !(inverted==9 && has(negword)))continue;
   // The case without the free negative literal is run separately at pivot=-1.
   if(inverted>=0 && !has(negword))continue;
   if(bucket==-2){printf("root=%d wires=%d mask=%x\n",ix++,q.n,subset);continue;}
   if(bucket>=0&&bucket!=ix++){continue;}
   try{bool hit=dfs(q);printf("%s root=%x wires=%d budget=%d visits=%lld sec=%.3f\n",hit?"FOUND":"EXHAUSTED",subset,q.n,budget,count,elapsed());if(hit)return 10;}
   catch(int){printf("UNKNOWN root=%x visits=%lld sec=%.3f\n",subset,count,elapsed());return 0;}
 }
}
