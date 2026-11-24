// Check both ends of an interval of bank columns on Heawood extremal inputs.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;
using U=uint64_t;
const unsigned ALLV=(1u<<14)-1, ALLP=(1u<<21)-1;
const U ALLN=(U(1)<<37)-1;
static int pop(U q){return __builtin_popcountll(q);}
static unsigned first(unsigned q){return __builtin_ctz(q);}
struct Game {
 int k,R; unsigned E[21],N[37],x[21],y[21],adj[14]{},inc[14]{};
 array<U,1<<14> sup{},avo{};U uniqueCell[14][21]{},bad=0;
 vector<pair<unsigned,unsigned>> paths;vector<unsigned> usable;
 unsigned long long nodes=0,leaves=0,bankDead=0,sufDead=0;bool timed=false;
 chrono::steady_clock::time_point start=chrono::steady_clock::now();int seconds;
 Game(int lim):seconds(lim){
   cin>>k;for(auto &v:E)cin>>v;for(auto &v:N)cin>>v;
   for(unsigned e=0;e<21;e++){
     x[e]=first(E[e]);y[e]=first(E[e]&(E[e]-1));
     unsigned a=x[e],b=y[e];adj[a]|=1u<<b;adj[b]|=1u<<a;
     inc[a]|=1u<<e;inc[b]|=1u<<e;
     for(int c=0;c<37;c++)for(unsigned i:{a,b})if((E[e]&~N[c])==(1u<<i))uniqueCell[i][e]|=U(1)<<c;
   }
   for(unsigned m=0;m<=ALLV;m++)for(int j=0;j<37;j++){
     if((N[j]&m)==m)sup[m]|=U(1)<<j;
     if(!(N[j]&m))avo[m]|=U(1)<<j;
   }
   for(unsigned e=0;e<21;e++)for(int i=0;i<21;i++)for(int j=0;j<21;j++){
     if(i==int(e)||j==int(e)||!(E[i]&(1u<<x[e]))||!(E[j]&(1u<<y[e])))continue;
     unsigned vs=E[e]|E[i]|E[j];if(pop(vs)==4)paths.push_back({(1u<<e)|(1u<<i)|(1u<<j),vs});
   }
   if(paths.size()!=84)abort();
 }
 int matching(unsigned edges,unsigned verts=ALLV)const{
   unsigned nb[7]{};int mates[7];fill(begin(mates),end(mates),-1);
   for(unsigned t=edges;t;t&=t-1){int e=first(t);if((verts&E[e])==E[e])nb[x[e]]|=1u<<(y[e]-7);}
   auto find=[&](auto &self,int a,unsigned &seen)->bool{
     for(unsigned q=nb[a];q;q&=q-1){int v=first(q);if(seen>>v&1)continue;
       seen|=1u<<v;if(mates[v]<0||self(self,mates[v],seen)){mates[v]=a;return true;}}
     return false;
   };
   int m=0;for(int i=0;i<7;i++){unsigned seen=0;if(find(find,i,seen))m++;}return m;
 }
 int bankRank(unsigned p)const{
   unsigned ng[14]{},wins[14]{},good=0,forced=0;bool base[14],essential[14]{};
   U zeros=ALLN^bad;
   for(unsigned t=p;t;t&=t-1){int e=first(t);unsigned a=x[e],b=y[e];ng[a]|=1u<<b;ng[b]|=1u<<a;
      for(unsigned i:{a,b})if(zeros&uniqueCell[i][e])essential[i]=true;}
   for(int i=0;i<14;i++)base[i]=bool(zeros&sup[ng[i]]&avo[1u<<i]);
   for(unsigned t=p;t;t&=t-1){
     int e=first(t);unsigned a=x[e],b=y[e];
     if((pop(ng[a])==1&&!base[a])||(pop(ng[b])==1&&!base[b]))continue;
     if(zeros&sup[(ng[a]|ng[b])&~E[e]]&avo[E[e]]){good|=1u<<e;wins[a]++;wins[b]++;}
   }
   for(int i=0;i<14;i++)if((!wins[i]&&essential[i])||(wins[i]<unsigned(pop(ng[i]))&&base[i]))forced|=1u<<i;
   return pop(good)+pop(forced)+matching(good,ALLV^forced);
 }
 bool canHit(const vector<unsigned>& sets,unsigned take,int budget)const{
   unsigned shortSet=0;for(auto s:sets)if(!(s&take)&&(!shortSet||pop(s)<pop(shortSet)))shortSet=s;
   if(!shortSet)return true;if(!budget)return false;
   for(unsigned r=shortSet&unsigned(R);r;r&=r-1)if(canHit(sets,take|(r&-r),budget-1))return true;
   return false;
 }
 bool suffixOK(unsigned p)const{
   for(unsigned e:usable){unsigned t=p&~e;int n=pop(t);if(n<=k&&n+matching(t)<=k)return false;}
   unsigned rows[14]{},good=0,forced=0,degs[14]{};U cols[14]{};vector<unsigned> hit;
   for(unsigned e=0;e<21;e++){
     for(unsigned i:{x[e],y[e]}){U cs=uniqueCell[i][e];if(p>>e&1)cs&=bad;
       if(cs){rows[i]|=1u<<e;cols[i]|=cs;}}
     if(!(p&(inc[x[e]]|inc[y[e]]))||(bad&sup[(adj[x[e]]|adj[y[e]])^E[e]])){good|=1u<<e;degs[x[e]]++;degs[y[e]]++;}
   }
   for(int i=0;i<14;i++){
     if(rows[i]&&!(R>>i&1))return false;
     if((!degs[i]&&rows[i])||(degs[i]<3&&(!(p&inc[i])||(bad&sup[adj[i]]))))forced|=1u<<i;
   }
   if(pop(good)+pop(forced)+matching(good,ALLV^forced)>25-k || 28-pop(p)-matching(p)>25-k)return false;
   for(unsigned e=0;e<21;e++)if((rows[x[e]]&rows[y[e]])&&(cols[x[e]]&cols[y[e]]))hit.push_back(E[e]);
   for(auto [es,vs]:paths)if(!(es&p))hit.push_back(vs);
   return canHit(hit,0,25-k-pop(R));
 }
 void dfs(unsigned p,unsigned freeBits,bool testL,bool testH){
   if(timed)return;nodes++;
   if(!(nodes&16383)&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>seconds){timed=true;return;}
   unsigned maxP=p|freeBits;if(!maxP||p==ALLP)return;
   if(testH&&!suffixOK(maxP)){sufDead++;return;}
   if(testL&&bankRank(p)>k+1){bankDead++;return;}
   if(!freeBits){if(leaves<4)cout<<"REMAIN "<<R<<" "<<p<<" "<<bad<<endl;leaves++;return;}
   unsigned v=freeBits&-freeBits;
   dfs(p|v,freeBits^v,true,false);dfs(p,freeBits^v,false,true);
 }
 void run(){unsigned em;int count=0;while(cin>>R>>em>>bad){
    if(!bad||pop(R)>25-k)abort();usable={0};for(unsigned i=0;i<14;i++)if(!(sup[1u<<i]&~bad))usable.push_back(inc[i]);
    dfs(ALLP^em,em,true,true);if(timed)break;count++;}
   cout<<"BANK_COMPILED "<<k<<" "<<(timed?"INCOMPLETE":"COMPLETE")<<" orbits_finished="<<count
       <<" visited="<<nodes<<" bank_pruned="<<bankDead<<" suffix_pruned="<<sufDead<<" remaining="<<leaves<<endl;
 }
};
int main(int argc,char**argv){Game game(argc>1?atoi(argv[1]):60);game.run();}
