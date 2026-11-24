#include <string>
// Exact forward live-frontier enumeration for the monotone (zero paid NOT) branch of L-meta-3143.
// Arguments: free input (0 or 1), include free negative (0/1), budget seconds, first bucket, past last.
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
struct Cover {uint64_t b[3]{};};
Cover operator|(Cover a,Cover b){for(int i=0;i<3;++i)a.b[i]|=b.b[i];return a;}
bool operator==(Cover a,Cover b){return a.b[0]==b.b[0]&&a.b[1]==b.b[1]&&a.b[2]==b.b[2];}
const int sevenEdges[][2]={{0,1},{1,2},{0,4},{1,5},{2,6},{3,5},{4,6},{3,6}};
const int eightEdges[][2]={{0,1},{1,2},{2,3},{0,4},{1,5},{2,6},{3,7},{4,6},{5,7},{4,7}};
int nvars;
bool goal(int r){const int (*es)[2]=nvars==8?eightEdges:sevenEdges;for(int i=0;i<(nvars==8?10:8);++i)if((r>>es[i][0])&(r>>es[i][1])&1)return true;return false;}
struct State {
  std::array<Word,11>w{}; uint8_t n=0,k=0;
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
 if(cmap.size()<120000)cmap.emplace(w,v);return v;
}
template<class F> bool children(const State&s,F f){
 Cover cache[12];for(int i=0;i<s.n;++i)cache[i]=cover(s.w[i]);
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
  Cover hit,twice;Cover c[12];
  for(int i=0;i<s.n;++i){
    c[i]=cover(s.w[i]);
    for(int k=0;k<3;++k){twice.b[k]|=hit.b[k]&c[i].b[k];hit.b[k]|=c[i].b[k];}
  }
  uint16_t P[12]{},N[12]{},red[12]{},blue[12]{};
  for(int i=0;i<s.n;++i){
    for(int k=0;k<3;++k){auto v=c[i].b[k]&~twice.b[k];while(v){int b=__builtin_ctzll(v)+64*k;v&=v-1;P[i]|=1<<(b/nneg);N[i]|=1<<(b%nneg);}}
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
  uint16_t stack[24]{};int top=0;stack[top++]=(1<<s.n)-1;
  while(top){auto mask=stack[--top];if((mask&(mask-1))==0)continue;
    uint16_t left=component(mask,red);if(left==mask)left=component(mask,blue);
    if(left==mask)return true;
    stack[top++]=left;stack[top++]=mask^left;
  }
  return false;
}
long long stat[16][16]{};
bool dfs(const State&s){
 if((++count&255)==0&&elapsed()>secs)throw 1;
 if(s.n==1&&s.w[0]==expected)return true;
 if(!s.k||s.n>s.k+1||dead.count(s))return false;
 if(s.n==s.k+1&&rectangle_conflict(s))return false;
 ++stat[s.k][s.k+1-s.n];
 if(children(s,dfs))return true;
 if(dead.size()<memoryCap)dead.insert(s);return false;
}

int main(int argc,char**argv){
 if(argc!=4){std::fprintf(stderr,"usage: seven-signed | seven-small | eight-ordinary  state-table.txt  seconds\n");return 2;}
 std::string mode=argv[1]; if(mode!="seven-signed"&&mode!="seven-small"&&mode!="eight-ordinary")return 2;
 nvars=mode=="eight-ordinary"?8:7;int p=nvars==7?1:-1;bool include=mode=="seven-signed";secs=atof(argv[3]);if(secs<=0||secs>90)return 2;
 memoryCap=700000;std::vector<int> pos,neg,rows;
 for(int r=0;r<(1<<nvars);++r){bool y=goal(r),good=true;for(int i=0;i<nvars;++i)if(i!=p&&bool(r>>i&1)==y&&goal(r^(1<<i))==y)good=false;if(good)(y?pos:neg).push_back(r);}
 rows=pos;rows.insert(rows.end(),neg.begin(),neg.end());npos=pos.size();nneg=neg.size();if(rows.size()>=32||npos*nneg>192)return 3;
 expected=(1U<<npos)-1;ones=(1U<<rows.size())-1;all=cover(expected);State q;q.k=nvars==8?12:include?11:10;
 for(int i=0;i<nvars;++i){Word z=0;for(int a=0;a<(int)rows.size();++a)if(rows[a]>>i&1)z|=1U<<a;q.add(z);if(i==p&&include)q.add(ones^z);}
 std::sort(q.w.begin(),q.w.begin()+q.n);start=std::chrono::steady_clock::now();
 try{if(dfs(q)){std::puts("FOUND");return 4;}}catch(int){std::puts("UNKNOWN");return 5;}
 if(dead.size()==memoryCap){std::puts("TABLE_CAP");return 6;}
 std::vector<State> nodes(dead.begin(),dead.end());
 std::sort(nodes.begin(),nodes.end(),[](auto&a,auto&b){if(a.k!=b.k)return a.k>b.k;if(a.n!=b.n)return a.n<b.n;return a.w<b.w;});
 FILE*f=std::fopen(argv[2],"w");if(!f)return 7;
 std::fprintf(f,"# %s pos",mode.c_str());for(int r:pos)std::fprintf(f," %d",r);std::fprintf(f," neg");for(int r:neg)std::fprintf(f," %d",r);std::fprintf(f,"\n");
 for(auto&s:nodes){std::fprintf(f,"%u",s.k);for(int i=0;i<s.n;++i)std::fprintf(f," %x",s.w[i]);std::fprintf(f,"\n");}
 std::fclose(f);std::printf("EXHAUSTED mode=%s states=%zu children=%lld seconds=%.3f\n",mode.c_str(),dead.size(),count,elapsed());
}
