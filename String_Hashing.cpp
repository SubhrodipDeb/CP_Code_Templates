#pragma GCC optimize("O3,unroll-loops")

#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

#define fastio() ios_base::sync_with_stdio(false);cin.tie(NULL);cout.tie(NULL)
#define MOD 1000000007
#define MOD1 998244353
#define INF 1e18
#define nline "\n"
#define pb push_back
#define ppb pop_back
#define mp make_pair
#define ff first
#define ss second
#define PI 3.141592653589793238462
#define set_bits __builtin_popcountll
#define sz(x) ((int)(x).size())
#define all(x) (x).begin(), (x).end()

#ifndef SDEB
#define debug(x) cerr << #x<<" "; _print(x); cerr << endl;
#else
#define debug(x);
#endif

typedef long long ll;
typedef unsigned long long ull;
typedef long double lld;

typedef tree<pair<ll, ll>, null_type, less<pair<ll, ll>>, rb_tree_tag, tree_order_statistics_node_update > pbds; // find_by_order, order_of_key

void _print(ll t) {cerr << t;}
void _print(int t) {cerr << t;}
void _print(string t) {cerr << t;}
void _print(char t) {cerr << t;}
void _print(lld t) {cerr << t;}
void _print(double t) {cerr << t;}
void _print(ull t) {cerr << t;}

template <class T, class V> void _print(pair <T, V> p);
template <class T> void _print(vector <T> v);
template <class T> void _print(set <T> v);
template <class T, class V> void _print(map <T, V> v);
template <class T> void _print(multiset <T> v);
template <class T, class V> void _print(pair <T, V> p) {cerr << "{"; _print(p.ff); cerr << ","; _print(p.ss); cerr << "}";}
template <class T> void _print(vector <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T> void _print(set <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T> void _print(multiset <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T, class V> void _print(map <T, V> v) {cerr << "[ "; for (auto i : v) {_print(i); cerr << " ";} cerr << "]";}
void _print(pbds v) {cerr << "[ "; for (auto i : v) {_print(i); cerr << " ";} cerr << "]";}



mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
/*---------------------------------------------------------------------------------------------------------------------------*/
ll gcd(ll a, ll b) {if (b > a) {return gcd(b, a);} if (b == 0) {return a;} return gcd(b, a % b);}
ll expo(ll a, ll b, ll mod) {ll res = 1; while (b > 0) {if (b & 1)res = (res * a) % mod; a = (a * a) % mod; b = b >> 1;} return res;}
void extendgcd(ll a, ll b, ll*v) {if (b == 0) {v[0] = 1; v[1] = 0; v[2] = a; return ;} extendgcd(b, a % b, v); ll x = v[1]; v[1] = v[0] - v[1] * (a / b); v[0] = x; return;} //pass an arry of size1 3
ll mminv(ll a, ll b) {ll arr[3]; extendgcd(a, b, arr); return arr[0];} //for non prime b
ll mminvprime(ll a, ll b) {return expo(a, b - 2, b);}
bool revsort(ll a, ll b) {return a > b;}
ll combination(ll n, ll r, ll m, ll *fact, ll *ifact) {ll val1 = fact[n]; ll val2 = ifact[n - r]; ll val3 = ifact[r]; return (((val1 * val2) % m) * val3) % m;}
void google(int t) {cout << "Case #" << t << ": ";}
vector<ll> sieve(int n) {int*arr = new int[n + 1](); vector<ll> vect; for (int i = 2; i <= n; i++)if (arr[i] == 0) {vect.push_back(i); for (int j = 2 * i; j <= n; j += i)arr[j] = 1;} return vect;}
ll mod_add(ll a, ll b, ll m) {a = a % m; b = b % m; return (((a + b) % m) + m) % m;}
ll mod_mul(ll a, ll b, ll m) {a = a % m; b = b % m; return (((a * b) % m) + m) % m;}
ll mod_sub(ll a, ll b, ll m) {a = a % m; b = b % m; return (((a - b) % m) + m) % m;}
ll mod_div(ll a, ll b, ll m) {a = a % m; b = b % m; return (mod_mul(a, mminvprime(b, m), m) + m) % m;}  //only for prime m
ll phin(ll n) {ll number = n; if (n % 2 == 0) {number /= 2; while (n % 2 == 0) n /= 2;} for (ll i = 3; i <= sqrt(n); i += 2) {if (n % i == 0) {while (n % i == 0)n /= i; number = (number / i * (i - 1));}} if (n > 1)number = (number / n * (n - 1)) ; return number;} //O(sqrt(N))
ll getRandomNumber(ll l, ll r) {return uniform_int_distribution<ll>(l, r)(rng);} 
/*--------------------------------------------------------------------------------------------------------------------------*/

class DisJointSet{
vector<int> rank,parent,size;
public:
DisJointSet(int n){
rank.resize(n+1,0);
parent.resize(n+1,0);
size.resize(n+1,0);
for(int i=0;i<n;i++){
parent[i]=i;
}
}
 int findUPar(int node){
if(node==parent[node]) return node;
 else return parent[node]=findUPar(parent[node]);
}
void union_by_rank(int u,int v){
int ultimate_parent_u=findUPar(u);
int ultimate_parent_v=findUPar(v);
if(ultimate_parent_u==ultimate_parent_v) return;
else if(rank[ultimate_parent_u]<rank[ultimate_parent_v]){
parent[ultimate_parent_u]=ultimate_parent_v;
}
else if(rank[ultimate_parent_v]<rank[ultimate_parent_u]){
 parent[ultimate_parent_v]=ultimate_parent_u;
}
else{
 parent[ultimate_parent_v]=ultimate_parent_u;
 rank[ultimate_parent_u]++;
}
}
void union_by_size(int u,int v){
int ultimate_parent_u=findUPar(u);
int ultimate_parent_v=findUPar(v);
if(ultimate_parent_u==ultimate_parent_v) return;
if(size[ultimate_parent_u]<size[ultimate_parent_v]){
 parent[ultimate_parent_u]=ultimate_parent_v;
size[ultimate_parent_v]+=size[ultimate_parent_u];
}
else{
 parent[ultimate_parent_v]=ultimate_parent_u;
size[ultimate_parent_u]+=size[ultimate_parent_v];
}
}
};
/*------------------------------------------------------------------------------------------*/
//iNTERACTIVE PROBLEMS
struct Interactor{
    int hiddenNumber;
    int queriesTillNow;
    int limitQueries;
    bool printInteraction;
    Interactor(){
        hiddenNumber = getRandomNumber(1, 100);
        queriesTillNow = 0;
        limitQueries = 10;
        printInteraction = false;
    }
    void checkTotalQueries(){
        if(queriesTillNow >= limitQueries){
            cout << "Made more than limit queries for " << hiddenNumber << endl;
        }
        assert(queriesTillNow < limitQueries);        
    }
    char make_query(int x){
        checkTotalQueries();
        queriesTillNow++;
        
        if(printInteraction)
            cout << "? " << x << endl;
        if(x < hiddenNumber)
            return '<';
        if(x > hiddenNumber)
            return '>';
        return '=';
    }
    void isValidOutput(int x){
        if(x != hiddenNumber){
            cout << "Failed for " << hiddenNumber << endl; 
        }else{
            cout << "Passed for " << hiddenNumber << endl;
        }
    }
};

void query(int x){
    cout << "? " << x << endl;
}
 /*---------------------------------------------------------------------------------------------*/
ll m=1e9+7,p=30;
ll hash1(string s){
	ll n=s.size();
	ll hashSoFar=0;
	ll powerOfP=1;
	for(ll i=0;i<n;i++){
		ll character_value=s[i]-'a'+1;
		hashSoFar=(character_value*powerOfP+hashSoFar)%(m);
		powerOfP=(powerOfP*p)%m;
	}
	return hashSoFar;
}
void solve() {
   string s;
   cin>>s;
   ll completeHash=hash1(s);
   cout<<completeHash<<endl;
}
int main() {
#ifndef SDEB
    
    freopen("error.txt", "w", stderr);
#endif
   fastio();
    int t;
    cin>>t;
    while(t--){
    solve();
    }
    
}
