#include <bits/stdc++.h>
using namespace std;

// ---------- BigInt (base 1e6) ----------
struct BigInt {
    static const uint32_t BASE = 1000000U;
    vector<uint32_t> d;
    int sign = 0;

    BigInt() : sign(0) {}
    BigInt(long long v) { *this = v; }

    BigInt& operator=(long long v) {
        d.clear();
        if (v == 0) { sign = 0; return *this; }
        if (v < 0) { sign = -1; v = -v; }
        else sign = +1;
        while (v) { d.push_back((uint32_t)(v % BASE)); v /= BASE; }
        return *this;
    }
    bool isZero() const { return sign == 0; }
    void trim() { while (!d.empty() && d.back() == 0) d.pop_back(); if (d.empty()) sign = 0; }

    friend BigInt operator+(const BigInt& a, const BigInt& b) {
        if (a.sign==0) return b; if (b.sign==0) return a;
        if (a.sign==b.sign) {
            BigInt c; c.sign=a.sign; unsigned long long carry=0ULL;
            size_t n=max(a.d.size(), b.d.size()); c.d.resize(n);
            for (size_t i=0;i<n;i++) {
                unsigned long long ai=(i<a.d.size()?a.d[i]:0);
                unsigned long long bi=(i<b.d.size()?b.d[i]:0);
                unsigned long long cur=ai+bi+carry;
                c.d[i]=(uint32_t)(cur%BASE); carry=cur/BASE;
            }
            if(carry) c.d.push_back((uint32_t)carry);
            c.trim(); return c;
        } else {
            BigInt bb=b; bb.sign*=-1; return a-bb;
        }
    }
    friend BigInt operator-(const BigInt& a, const BigInt& b) {
        if(b.sign==0) return a; if(a.sign==0){BigInt r=b; r.sign*=-1; return r;}
        if(a.sign!=b.sign){BigInt bb=b; bb.sign*=-1; return a+bb;}
        int cmp=cmpAbs(a,b); if(cmp==0) return BigInt(0);
        const BigInt *larg=&a,*small=&b; int s=a.sign;
        if(cmp<0){larg=&b; small=&a; s=-s;}
        BigInt c; c.sign=s; c.d.resize(larg->d.size());
        long long carry=0;
        for(size_t i=0;i<larg->d.size();i++){
            long long ai=larg->d[i];
            long long bi=(i<small->d.size()?small->d[i]:0);
            long long cur=ai-bi-carry;
            if(cur<0){cur+=BASE; carry=1;} else carry=0;
            c.d[i]=(uint32_t)cur;
        }
        c.trim(); return c;
    }
    static int cmpAbs(const BigInt&a,const BigInt&b){
        if(a.d.size()!=b.d.size()) return a.d.size()<b.d.size()?-1:1;
        for(int i=(int)a.d.size()-1;i>=0;i--)
            if(a.d[i]!=b.d[i]) return a.d[i]<b.d[i]?-1:1;
        return 0;
    }
    friend BigInt mulSmall(const BigInt&a,uint64_t m){
        if(a.isZero()||m==0) return BigInt(0);
        BigInt c; c.sign=a.sign; unsigned long long carry=0ULL;
        c.d.resize(a.d.size());
        for(size_t i=0;i<a.d.size();i++){
            unsigned long long cur=(unsigned long long)a.d[i]*m+carry;
            c.d[i]=(uint32_t)(cur%BASE); carry=cur/BASE;
        }
        while(carry){c.d.push_back((uint32_t)(carry%BASE)); carry/=BASE;}
        c.trim(); return c;
    }
    friend BigInt operator*(const BigInt&a,const BigInt&b){
        if(a.isZero()||b.isZero()) return BigInt(0);
        BigInt c; c.sign=a.sign*b.sign;
        c.d.assign(a.d.size()+b.d.size(),0);
        for(size_t i=0;i<a.d.size();i++){
            unsigned long long carry=0ULL; unsigned long long ai=a.d[i];
            for(size_t j=0;j<b.d.size()||carry;j++){
                unsigned long long cur=c.d[i+j]+ai*(j<b.d.size()?b.d[j]:0ULL)+carry;
                c.d[i+j]=(uint32_t)(cur%BASE); carry=cur/BASE;
            }
        }
        c.trim(); return c;
    }
    uint32_t divSmall(uint32_t v){
        unsigned long long rem=0ULL;
        for(int i=(int)d.size()-1;i>=0;i--){
            unsigned long long cur=d[i]+rem*BASE;
            uint32_t q=(uint32_t)(cur/v); uint32_t r=(uint32_t)(cur%v);
            d[i]=q; rem=r;
        }
        trim(); return (uint32_t)rem;
    }
    std::string toString() const{
        if(sign==0) return "0";
        BigInt tmp=*this; tmp.sign=+1; vector<uint32_t> parts;
        while(!tmp.isZero()) parts.push_back(tmp.divSmall(1000000U));
        std::string s=(sign<0?"-":"");
        for(int i=(int)parts.size()-1;i>=0;i--){
            std::string chunk=to_string(parts[i]);
            if(i!=(int)parts.size()-1) s+=string(6-(int)chunk.size(),'0');
            s+=chunk;
        }
        return s;
    }
};

// gcd
static long long igcd(long long a,long long b){ if(a<0)a=-a; if(b<0)b=-b; while(b){long long t=a%b;a=b;b=t;} return a; }

// Rational
struct Rational{
    BigInt num; long long den;
    Rational(long long v=0):num(v),den(1){} Rational(const BigInt&n,long long d):num(n),den(d){normalize();}
    void normalize(){ if(num.isZero()){den=1;return;} if(den<0){den=-den; num.sign=-num.sign;} }
    friend Rational operator+(const Rational&A,const Rational&B){
        if(A.num.isZero()) return B; if(B.num.isZero()) return A;
        long long ad=A.den, bd=B.den, g1=igcd(ad,bd);
        long long denL=(ad/g1)*bd;
        BigInt t1=mulSmall(A.num,(uint64_t)(bd/g1));
        BigInt t2=mulSmall(B.num,(uint64_t)(ad/g1));
        BigInt n=t1+t2; return Rational(n,denL);
    }
    friend Rational operator-(const Rational&A,const Rational&B){
        Rational negB=B; if(!negB.num.isZero()) negB.num.sign=-negB.num.sign; return A+negB;
    }
    friend Rational operator*(const Rational&A,const Rational&B){
        if(A.num.isZero()||B.num.isZero()) return Rational(0);
        BigInt n=A.num*B.num; long long d=A.den*B.den; return Rational(n,d);
    }
    friend Rational mulInt(const Rational&A,long long k){
        if(k==0||A.num.isZero()) return Rational(0);
        BigInt n=mulSmall(A.num,(uint64_t)(k<0?-k:k)); if(k<0&&!n.isZero()) n.sign=-n.sign;
        return Rational(n,A.den);
    }
};

// base-b parse
static int digitVal(char c){ if(c>='0'&&c<='9') return c-'0'; if(c>='a'&&c<='z') return 10+(c-'a'); if(c>='A'&&c<='Z') return 10+(c-'A'); return -1; }
static BigInt parseInBase(const string&s,int base){ BigInt val(0); for(char c:s){ int d=digitVal(c); val=mulSmall(val,base); BigInt addv(d); val=val+addv;} return val; }

// Lagrange interpolation
static vector<Rational> lagrange_coeffs(const vector<long long>&xs,const vector<BigInt>&ys){
    int m=(int)xs.size()-1; vector<Rational> coeffs(m+1,Rational(0));
    for(int i=0;i<=m;i++){
        long long xi=xs[i]; vector<BigInt> basis(1); basis[0]=BigInt(1); long long denom=1;
        for(int j=0;j<=m;j++) if(j!=i){
            long long xj=xs[j]; vector<BigInt> nxt(basis.size()+1,BigInt(0));
            for(size_t k=0;k<basis.size();k++){
                BigInt term=mulSmall(basis[k],(uint64_t)(xj<0?-xj:xj));
                if(xj>0&&!term.isZero()) term.sign=-term.sign;
                nxt[k]=nxt[k]+term; nxt[k+1]=nxt[k+1]+basis[k];
            }
            denom*=(xi-xj); basis.swap(nxt);
        }
        for(size_t k=0;k<basis.size();k++){ BigInt num=basis[k]*ys[i]; Rational term(num,denom); coeffs[k]=coeffs[k]+term; }
    }
    return coeffs;
}

// MAIN
int main(){
    ios::sync_with_stdio(false); cin.tie(nullptr);

    string js((istreambuf_iterator<char>(cin)), istreambuf_iterator<char>());
    regex re_n(R"RE("n"\s*:\s*(\d+))RE");
    regex re_k(R"RE("k"\s*:\s*(\d+))RE");
    smatch m; int n=-1,k=-1;
    if(regex_search(js,m,re_n)) n=stoi(m[1].str());
    if(regex_search(js,m,re_k)) k=stoi(m[1].str());

    regex re_e(R"REGEX("(\d+)"\s*:\s*\{\s*"base"\s*:\s*"([0-9A-Za-z]+)"\s*,\s*"value"\s*:\s*"([0-9A-Za-z]+)"\s*\})REGEX");
    vector<long long> xs; vector<int> bases; vector<string> vals;
    for(sregex_iterator it(js.begin(),js.end(),re_e),end; it!=end;++it){
        int x=stoi((*it)[1].str()); int b=stoi((*it)[2].str()); string v=(*it)[3].str();
        xs.push_back(x); bases.push_back(b); vals.push_back(v);
    }

    vector<pair<long long,BigInt>> pts;
    for(size_t i=0;i<xs.size();i++){ BigInt y=parseInBase(vals[i],bases[i]); pts.push_back({xs[i],y}); }
    sort(pts.begin(),pts.end());

    vector<long long> X; vector<BigInt> Y;
    for(int i=0;i<k;i++){ X.push_back(pts[i].first); Y.push_back(pts[i].second); }

    auto C=lagrange_coeffs(X,Y);

    // ✅ Only print constant term
    if(C[0].den==1) cout<<C[0].num.toString()<<"\n";
    else cout<<C[0].num.toString()<<"/"<<C[0].den<<"\n";

    return 0;
}
