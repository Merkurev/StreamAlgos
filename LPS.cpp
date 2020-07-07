#include <iostream>
#include <cstdio>
#include <vector>
#include <cstring>
#include <cmath>
#include <ctime>
#include <chrono>
#include <random>
using namespace std;

#ifdef LOCAL
    #define eprintf(...) fprintf(stderr, __VA_ARGS__)
#else
    #define eprintf(...) 42
#endif

mt19937_64 rng(chrono::steady_clock::now().time_since_epoch().count());
int64_t myRand(int64_t B) {
	return (uint64_t)rng() % B;
}

typedef unsigned __int128 uint128_t;

namespace Hash
{
    constexpr uint64_t p_pow = 61, p = (1ULL << 61) - 1;
   
    uint64_t mod(const uint128_t x)
    {
        uint64_t ans = (uint64_t) (x & p) + (uint64_t) (x >> p_pow);
        ans = (ans & p) + (ans >> p_pow);
        return (ans == p ? 0 : ans);
    }

    uint64_t mul(const uint64_t a, const uint64_t b)
    {
        return mod((uint128_t) a * b);
    }

    uint64_t fpow(const uint64_t x, const uint64_t n)
    {
        if (n == 0)
            return 1ULL;
        uint64_t a = fpow(x, n >> 1);
        a = mul(a, a);
        if (n & 1)
            a = mul(a, x);
        return a;
    }

    static uint64_t getInverse(const uint64_t x)
    {
        return fpow(x, p - 2);
    }

    struct Value
    {
        uint64_t x;

        Value() : x() {}

        Value(uint64_t _x) : x(_x) {}

        Value operator + (const Value &A) const
        {
            uint64_t ans = x + A.x;
            if (ans >= p)
                ans -= p;
            return Value(ans);
        }

        Value operator - (const Value &A) const
        {
            return Value((x < A.x) ? x + p - A.x : x - A.x);
        }

        Value operator * (const Value &A) const
        {
            return Value(mul(x, A.x));
        }

        bool operator == (const Value &A) const
        {
            return x == A.x;
        }
    };

    Value k, k_inv;
};

struct Frame
{
    long long i;
    Hash::Value FF, FR, ri_inv, ri;

    Frame() : i(), FF(), FR(), ri_inv(Hash::Value(1)), ri(Hash::Value(1)) {}

    Frame(long long _i, Hash::Value _FF, Hash::Value _FR, Hash::Value _ri_inv, Hash::Value _ri)
        : i(_i), FF(_FF), FR(_FR), ri_inv(_ri_inv), ri(_ri) {}

    pair <Hash::Value, Hash::Value> operator - (const Frame &A) const
    {
        Hash::Value ansF = (FF - A.FF) * A.ri_inv;
        Hash::Value ansR = FR - A.FR * A.ri_inv * ri;
        return make_pair(ansF, ansR);
    }

    Frame addItem(Hash::Value item)
    {
        return Frame(
                i + 1,
                FF + item * ri,
                FR * Hash::k + item,
                ri_inv * Hash::k_inv,
                ri * Hash::k
                );
    }
};

bool checkPalindrome(const Frame &A, const Frame &B)
{
    auto Hashes = B - A;
    //eprintf("[%lld, %lld) : ", A.i, B.i);
    //eprintf("%llu vs %llu\n", Hashes.first.x, Hashes.second.x);
    return Hashes.first == Hashes.second;
}

struct Answer
{
    long long pos, len;

    Answer() : pos(), len() {}
    
    Answer(long long _pos, long long _len) : pos(_pos), len(_len) {}

    bool operator < (const Answer &A) const
    {
        return len < A.len;;
    }

    bool operator > (const Answer &A) const
    {
        return len > A.len;
    }

    void print()
    {
        printf("pos = %lld, len = %lld\n", pos, len);
    }
};

struct ABasic
{
    long long tE;
    Answer ans;

    vector <Frame> SP;
    Frame I;

    ABasic(long long E) : tE(), ans(), I()
    {
        I.i = 1;
        tE = E / 2;
    }

    Answer addChar(long long i, uint64_t c)
    {
        if (i % tE == 0)
        {
            SP.push_back(I);
        }
        I = I.addItem(Hash::Value(c));
        for (const auto &v : SP)
            if (checkPalindrome(v, I))
            {
                Answer cur = Answer(v.i, i - v.i + 1);
                ans = max(ans, cur);
            }
        return ans;
    }
};

struct A
{
    long long tE;
    Answer ans;

    vector <Frame> SP;
    Frame I;
    long long sp;

    A(long long E) : tE(), ans(), I(), sp()
    {
        sp = -1;
        I.i = 1;
        tE = E / 2;
    }

    Answer addChar(long long i, uint64_t c)
    {
        if (i % tE == 0)
        {
            SP.push_back(I);
            if (i == tE)
                sp = 0;
        }
        I = I.addItem(Hash::Value(c));
        if (sp != -1)
        {
            sp++;
            while (sp > 0 && i - SP[sp].i + 1 <= ans.len)
                sp--;
            for (int it = 0; it <= min(1LL, sp); it++)
            {
                const auto &v = SP[sp - it];
                if (checkPalindrome(v, I))
                {
                    Answer cur = Answer(v.i, i - v.i + 1);
                    ans = max(ans, cur);
                }
            }
        }
        return ans;
    }
};

struct MBasic
{
    long long qe;
    Answer ans;

    vector <Frame> SP;
    Frame I;

    MBasic(double eps) : qe(), ans(), SP(), I()
    {
        I.i = 1;
        double _qe = log(2. / eps) / log(2);
        _qe = max(_qe, 1.);
        qe = (long long) (_qe + 1. - 1e-9);
    }

    long long ttl(long long x)
    {
        return 1LL << min(62LL, __builtin_ffsll(x) + 1 + qe);
    }

    Answer addChar(long long i, uint64_t c)
    {
        SP.push_back(I);
        vector <Frame> nSP;
        for (const auto &v : SP)
        {
            if (v.i + ttl(v.i) != i)
                nSP.push_back(v);
        }
        SP = nSP;
        I = I.addItem(Hash::Value(c));
        for (const auto &v : SP)
            if (checkPalindrome(v, I))
            {
                Answer cur = Answer(v.i, i - v.i + 1);
                ans = max(ans, cur);
            }
        return ans;
    }
};

template <class T>
struct LLNode
{
    LLNode *prev, *nxt;
    T value;

    LLNode() : prev(), nxt(), value() {}

    LLNode(T _value) : prev(), nxt(), value(_value) {}

    void linkTo(LLNode <T> *A)
    {
        nxt = A;
        if (A != NULL)
            A->prev = this;
    }

    ~ LLNode() = default;
};

struct M
{
    long long qe;
    Answer ans;

    LLNode <Frame> *SPhead;
    LLNode <Frame> *sp;
    vector <vector <LLNode <Frame> *>> QU;
    vector <int> quFirst, stopGrow;

    Frame I;

    M(double eps) : qe(), ans(), SPhead(), sp(), QU(), quFirst(), stopGrow(), I() 
    {
        I.i = 1;
        double _qe = log(2. / eps) / log(2);
        _qe = max(_qe, 1.);
        qe = (long long) (_qe + 1. - 1e-9);
    }
    
    long long ttl(long long x)
    {
        return 1LL << min(62LL, __builtin_ffsll(x) + 1 + qe);
    }

    Answer addChar(long long i, uint64_t c)
    {
        {
            auto cur = new LLNode <Frame> (I);
            cur->linkTo(SPhead);
            SPhead = cur;
        }
        if (i == 1)
            sp = SPhead;
        int beta = __builtin_ffsll(i) - 1;
        if ((int) QU.size() > beta)
        {
            auto v = QU[beta][quFirst[beta]];
            if (v->value.i + ttl(v->value.i) == i)
            {
                if (v == sp)
                    sp = sp->nxt;
                quFirst[beta]++;
                stopGrow[beta] = 1;
                if (quFirst[beta] == (int) QU[beta].size())
                    quFirst[beta] = 0;
                (v->prev)->linkTo(v->nxt);
                delete v;
            }
        }
        else
        {
            QU.push_back({});
            stopGrow.push_back(0);
            quFirst.push_back(0);
        }
        if (stopGrow[beta])
        {
            int pos = quFirst[beta] - 1;
            if (pos == -1)
                pos += (int) QU[beta].size();
            QU[beta][pos] = SPhead;
        }
        else
        {
            QU[beta].push_back(SPhead);
        }
        I = I.addItem(Hash::Value(c));
        if (sp->prev != NULL)
            sp = sp->prev;
        while (i - sp->value.i + 1 <= ans.len && sp->nxt != NULL)
            sp = sp->nxt;
        auto _sp = sp;
        for (int it = 0; it <= 2 && _sp != NULL; it++)
        {
            auto v = _sp->value;
            if (checkPalindrome(v, I))
            {
                Answer cur = Answer(v.i, i - v.i + 1);
                ans = max(ans, cur);
            }
            _sp = _sp->nxt;
        }

        return ans;
    }
};

const int LEN = (int) 1e8;
char s[LEN];

void solveA()
{
    int E;
    scanf("%d", &E);
    scanf("%s", s + 1);
    int n = strlen(s + 1);

    //ABasic algo = ABasic(E);
    A algo = A(E);

    for (int i = 1; i <= n; i++)
    {
        Answer ans = algo.addChar(i, s[i]);
        ans.print();
    }
}

void solveM()
{
    double eps;
    scanf("%lf", &eps);
    scanf("%s", s + 1);
    int n = strlen(s + 1);

    //MBasic algo = MBasic(eps);
    M algo = M(eps);

    for (long long i = 1; i <= (long long) 1e10; i++)
    {
        Answer ans = algo.addChar(i, s[i % n + 1]);
        if ((i & ((1LL << 20) - 1)) == 0)
        {
            printf("i = %lld : ", i);
            ans.print();
        }
    }
}

void init()
{
    Hash::k = myRand(Hash::p);
    Hash::k_inv = Hash::Value(Hash::getInverse(Hash::k.x));


    auto x = Hash::k * Hash::k_inv;
    if (x.x != 1ULL)
    {
        eprintf("initialization throw %llu != 1\n", x.x);
        throw;
    }

    {
        Hash::Value xx = Hash::Value('a');
        Frame empty = Frame();
        Frame one = empty.addItem(xx);
        eprintf("?%d?\n", checkPalindrome(empty, one));
    }
}

int main()
{
#ifdef LOCAL
    freopen("input.txt", "r", stdin);
//    freopen("output.txt", "w", stdout);
#endif

    init();
    solveM();

    return 0;
}
