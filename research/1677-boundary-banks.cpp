// Unit checks and an exact bounded search for normalized monotone H-prefixes.
// Only the false⇒true edge contrast on ten minimal positives and nine maximal
// negatives is used. A timeout never certifies the unsearched suffix.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <stdexcept>
#include <string>
#include <vector>
using W=uint32_t;
constexpr W P=(1u<<10)-1, N=((1u<<9)-1)<<10;
constexpr int edges[][2]={{0,1},{1,2},{2,3},{3,4},{0,4},{0,5},{2,6},{3,7},{5,6},{5,7}};
bool independent(int row){for(auto e:edges)if(row>>e[0]&row>>e[1]&1)return false;return true;}
std::array<W,8> raws{};
using Clock=std::chrono::steady_clock;
Clock::time_point start;double seconds;int k,limit,lo,hi;
uint64_t calls=0,terminals=0;
std::array<W,24> bank{};
struct G{int i,j;bool mul;};
std::array<G,14> path;
bool dominated(W a,W z){return !(z&~a&P) && !(a&~z&N);}
void init(){
 std::vector<int> rows;
 for(auto e:edges)rows.push_back(1<<e[0]|1<<e[1]);
 for(int r=0;r<256;++r)if(independent(r)){
  bool maximal=true;
  for(int i=0;i<8;++i)if(!(r>>i&1)&&independent(r|(1<<i)))maximal=false;
  if(maximal)rows.push_back(r);
 }
 if(rows.size()!=19)throw std::logic_error("wrong antichain");
 for(int i=0;i<8;++i){
  for(unsigned j=0;j<rows.size();++j)raws[i]|=W((rows[j]>>i)&1)<<j;
  bank[i]=raws[i];
 }
 bank[8]=raws[2]|raws[5];
}
bool cover(W todo,int left,const std::vector<W>& stars){
 if(!todo)return true;
 if(!left)return false;
 int best=10000;W chosen=0;
 for(W rem=todo;rem;rem&=rem-1){
  W bit=rem&-rem;int count=0;for(auto s:stars)count+=(s&bit)!=0;
  if(count<best){chosen=bit;best=count;}
 }
 if(!best)return false;
 for(W s:stars)if((s&chosen)&&cover(todo&~s,left-1,stars))return true;
 return false;
}
std::vector<W> safe_pairs(int n){
 std::vector<W> s;
 for(int i=0;i<n;++i)for(int j=0;j<i;++j){W a=bank[i]&bank[j];if(a&&!(a&N))s.push_back(a);}
 std::sort(s.begin(),s.end());s.erase(std::unique(s.begin(),s.end()),s.end());return s;
}
bool dfs(int n,int count){
 if(((++calls)&1023)==0 && std::chrono::duration<double>(Clock::now()-start).count()>seconds)throw std::runtime_error("UNKNOWN");
 int left=limit-(n-8);
 if(left<0||count+left<2)return false;
 auto safe=safe_pairs(n);
 if(!left){
  ++terminals;if(!cover(P,k,safe))return false;
  std::printf("FOUND k=%d;",k);
  for(int t=9;t<n;++t)std::printf(" %d%c%d",path[t-9].i,path[t-9].mul?'&':'|',path[t-9].j);
  std::puts("");return true;
 }
 int id=0;
 // Skip duplicate realizations only within this particular parent state.
 std::vector<std::pair<W,bool>> tried;
 for(int i=0;i<n;++i)for(int j=i+1;j<n;++j,++id){
  if(n==9&&(id<lo||id>=hi))continue;
  for(bool mul:{true,false}){
   if(count+left-1+int(mul)<2)continue;
   W z=mul?bank[i]&bank[j]:bank[i]|bank[j];
   if(!(z&P)||!(z&N))continue;
   if(std::any_of(bank.begin(),bank.begin()+n,[=](W a){return dominated(a,z);}))continue;
   if(mul&&((z&P & ((z&P)-1))==0||std::any_of(safe.begin(),safe.end(),[=](W a){return dominated(a,z);})))continue;
   auto tag=std::make_pair(z,mul);
   if(std::find(tried.begin(),tried.end(),tag)!=tried.end())continue;
   tried.push_back(tag);bank[n]=z;path[n-9]={i,j,mul};if(dfs(n+1,count+mul))return true;
  }
 }return false;
}
int main(int argc,char**argv){
 init();
 if(argc==2&&std::string(argv[1])=="--control"){
  if(cover(P,9,safe_pairs(8))||!cover(P,10,safe_pairs(8)))return 1;
  int n=8;
  for(auto t:std::array<std::array<int,3>,4>{{{1,4,5},{1,6,-1},{2,4,7},{6,7,-1}}}){
   W w=raws[t[0]];for(int i=1;i<3&&t[i]>=0;++i){w|=raws[t[i]];bank[n++]=w;}
  }
  if(n!=14||!cover(P,4,safe_pairs(n)))return 1;
  std::puts("CONTROL PASS: exact bank cover checks and a 13-gate four-star implementation.");return 0;
 }
 if(argc!=5)return 2;
 k=std::atoi(argv[1]);lo=std::atoi(argv[2]);hi=std::atoi(argv[3]);seconds=std::atof(argv[4]);limit=14-2*k;
 if(k<1||k>6||lo<0||hi>36||lo>=hi||seconds<=0||seconds>120)return 2;
 start=Clock::now();const char* verdict="EXHAUSTED";
 try{if(dfs(9,0))verdict="FOUND";}catch(const std::runtime_error&){verdict="UNKNOWN";}
 std::printf("%s normalized k=%d roots=[%d,%d) calls=%llu terminals=%llu seconds=%.4f\n",verdict,k,lo,hi,
 (unsigned long long)calls,(unsigned long long)terminals,std::chrono::duration<double>(Clock::now()-start).count());
}
