#include <iostream>
#include <cmath>
#include <cstring>
#include <vector>
#include <cassert>
#include <thread>
#include <mutex>

using namespace std;

const unsigned maxn = 10;
using ull = unsigned long long;

struct LargeInteger
{
    ull n[maxn];

    friend void swap(LargeInteger& lhs, LargeInteger& rhs)
    {
        std::swap(lhs.n, rhs.n);
    }

    LargeInteger()
    {
        memset(n, 0, sizeof(ull) * maxn);
    }

    LargeInteger(ull c)
    {
        memset(n, 0, sizeof(ull) * maxn);
        n[0] = c;
    }
    
    LargeInteger(const string& s)
    {
        memset(n, 0, sizeof(ull) * maxn);
        for (auto c : s)
            *this = (*this << 3) + (*this << 1) + (c & 15);
    }

    LargeInteger& operator=(LargeInteger other)
    {
        swap(*this, other);
        return *this;
    }

    unsigned get_dixon_bound() const
    {
        unsigned i;
        for (i = (maxn << 6) - 1; !(n[i >> 6] >> (i & 63) & 1); i--);

        /*
            bound = math.floor(math.exp(math.sqrt(math.log(n) * math.log(math.log(n))) / 2))
            where n = 1 << i
        */
        return unsigned(exp(sqrt(i * log(2) * log(i * log(2))) * 0.5) + 1);
    }

    LargeInteger operator<<(unsigned shift) const
    {
        LargeInteger ret;
        if (shift >= maxn << 6) return ret;
        unsigned d = shift >> 6, l = shift & 63;
        if (l) {
            unsigned r = 64 - l;
            for (unsigned i = maxn - d - 1; i; i--)
                ret.n[i + d] = n[i] << l | n[i - 1] >> r;
            ret.n[d] = n[0] << l;
            return ret;
        }
        for (unsigned i = maxn - d - 1; ~i; i--)
            ret.n[i + d] = n[i];
        return ret;
    }

    LargeInteger operator>>(unsigned shift) const
    {
        LargeInteger ret;
        if (shift >= maxn << 6) return ret;
        unsigned d = shift >> 6, r = shift & 63;
        if (r) {
            unsigned l = 64 - r;
            for (unsigned i = d; i < maxn - 1; i++)
                ret.n[i - d] = n[i] >> r | n[i + 1] << l;
            ret.n[maxn - 1 - d] = n[maxn - 1] >> r;
            return ret;
        }
        for (unsigned i = d; i < maxn; i++)
            ret.n[i - d] = n[i];
        return ret;
    }

    friend LargeInteger operator+(LargeInteger lhs, ull rhs)
    { 
        lhs.n[0] += rhs;
        if (lhs.n[0] < rhs) {
            for (unsigned i = 1; i < maxn; i++) {
                lhs.n[i]++;
                if (lhs.n[i]) break;
            }
        }
        return lhs;
    }

    LargeInteger& operator+=(ull rhs)
    { 
        n[0] += rhs;
        if (n[0] < rhs) {
            for (unsigned i = 1; i < maxn; i++) {
                n[i]++;
                if (n[i]) break;
            }
        }
        return *this;
    }
    
    friend LargeInteger operator+(LargeInteger lhs, const LargeInteger& rhs)
    {
        bool car = 0;
        for (unsigned i = 0; i < maxn; i++) {
            lhs.n[i] += rhs.n[i] + car;
            car = car ? lhs.n[i] <= rhs.n[i] : lhs.n[i] < rhs.n[i];
        }
        return lhs;
    }

    friend LargeInteger operator-(LargeInteger lhs, const LargeInteger& rhs)
    {
        bool bor = 0;
        for (unsigned i = 0; i < maxn; i++) {
            ull lst = lhs.n[i];
            lhs.n[i] -= rhs.n[i] + bor;
            bor = bor ? lst <= lhs.n[i] : lst < lhs.n[i];
        }
        return lhs;
    }

    LargeInteger& operator-=(const LargeInteger& rhs)
    {
        bool bor = 0;
        for (unsigned i = 0; i < maxn; i++) {
            ull lst = n[i];
            n[i] -= rhs.n[i] + bor;
            bor = bor ? lst <= n[i] : lst < n[i];
        }
        return *this;
    }

    friend LargeInteger operator*(const LargeInteger& lhs, const LargeInteger& rhs)
    {
        LargeInteger ret;
        unsigned* p = (unsigned*)&lhs;
        unsigned* q = (unsigned*)&rhs;
        auto r = ret.n;
        unsigned k;
        for (k = 0; k < (maxn - 1) << 1; k++, r = (ull*)((unsigned*)r + 1))
            for (unsigned j = k; ~j; j--) {
                ull mul = (ull)p[j] * q[k - j];
                if ((*r += mul) < mul) ++*(r + 1);
            }
        for (unsigned j = k; ~j; j--)
            *r += (ull)p[j] * q[k - j];
        for (unsigned j = ++k; ~j; j--)
            *(unsigned*)(r + 1) += p[j] * q[k - j];
        return ret;
    }

    friend LargeInteger operator/(LargeInteger lhs, const LargeInteger& rhs)
    {
        if (lhs < rhs) return 0;
        LargeInteger cur, ret;
        unsigned i, j, e;
        ull t;
        for (i = maxn - 1; !lhs.n[i]; i--);
        for (j = i << 6, t = lhs.n[i] >> 1; t; j++, t >>= 1);
        for (i = maxn - 1; !rhs.n[i]; i--);
        for (e = i << 6, t = rhs.n[i] >> 1; t; e++, t >>= 1);
        for (j -= e; ~j; j--)
            if ((cur = rhs << j) <= lhs) {
                ret.n[j >> 6] |= 1ull << j;
                lhs -= cur;
            }
        return ret;
    }

    friend LargeInteger operator%(LargeInteger lhs, const LargeInteger& rhs)
    {
        if (lhs < rhs) return lhs;
        LargeInteger cur;
        unsigned i, j, e;
        ull t;
        for (i = maxn - 1; !lhs.n[i]; i--);
        for (j = i << 6, t = lhs.n[i] >> 1; t; j++, t >>= 1);
        for (i = maxn - 1; !rhs.n[i]; i--);
        for (e = i << 6, t = rhs.n[i] >> 1; t; e++, t >>= 1);
        for (j -= e; ~j; j--)
            if ((cur = rhs << j) <= lhs)
                lhs -= cur;
        return lhs;
    }

    friend bool operator<(const LargeInteger& lhs, const LargeInteger& rhs)
    {
        for (unsigned i = maxn - 1; ~i; i--)
            if (lhs.n[i] < rhs.n[i])
                return true;
            else if (lhs.n[i] > rhs.n[i])
                return false;
        return false;
    }

    friend bool operator<=(const LargeInteger& lhs, const LargeInteger& rhs)
    {
        for (unsigned i = maxn - 1; ~i; i--)
            if (lhs.n[i] < rhs.n[i])
                return true;
            else if (lhs.n[i] > rhs.n[i])
                return false;
        return true;
    }

    friend bool operator==(const LargeInteger& lhs, const LargeInteger& rhs)
    {
        return memcmp(lhs.n, rhs.n, sizeof(ull) * maxn) == 0;
    }

    friend ostream& operator<<(ostream& os, LargeInteger other)
    {
        char s[maxn * 20];
        char *p = s + maxn * 20 - 1;
        *p = '\0';
        LargeInteger b;
        ull *cur;
        char* q = (char*)&other;
        char* r = (char*)&b;
        int i;
        for (i = (maxn << 3) - 1; !q[i] && i > 7; i--);
        while (i > 7) {
            for (int j = i - 7; j > 0; j -= 7) {
                *(ull*)(r + j) |= *(cur = (ull*)(q + j)) / 10;
                *cur %= 10;
            }
            *(ull*)r |= *(cur = (ull*)q) / 10;
            *--p = *cur % 10 + '0';
            *cur = 0;
            swap(q, r);
            while (!q[i]) i--;
        }
        return os << *(ull*)q << p;
    }
};

/*
 * try to calculate ceil(sqrt(inp))
 */
LargeInteger sqrt_ceil(const LargeInteger& inp)
{
    LargeInteger lo(0);
    LargeInteger hi;
    hi.n[maxn / 2] = 1;
    while (lo + 1 < hi) { auto mid = (lo + hi) >> 1; inp <= mid * mid ? hi = mid : lo = mid; }
    return hi;
}

pair<LargeInteger, unsigned> unsigned_div_mod(LargeInteger inp, unsigned d)
{
    unsigned i, j, e;
    ull t;
    LargeInteger ret;
    for (i = maxn - 1; !inp.n[i] && i; i--);
    for (j = i << 6, t = inp.n[i] >> 1; t; j++, t >>= 1);
    for (e = 0; d >= 1 << e + 1; e++);
    if (j < e) return {0, inp.n[0]};
    for (j -= e; ~j; j--) {
        unsigned low = j & 63;
        unsigned idx = j >> 6;
        if (low < 32) {
            unsigned p = inp.n[idx] >> low;
            if (d <= p) {
                ret.n[idx] |= 1ULL << j;
                inp.n[idx] -= (ull)d << low;
            }
        }
        else {
            unsigned p = (unsigned)inp.n[idx + 1] << (64 - low) | inp.n[idx] >> low;
            if (d <= p) {
                ret.n[idx] |= 1ULL << j;
                p -= d;
                inp.n[idx] = inp.n[idx] & ((1ULL << low) - 1) | (ull)p << low;
                inp.n[idx + 1] = inp.n[idx + 1] & ~((1ULL << low - 32) - 1) | p >> (64 - low);
            }
        }
    }
    return {ret, inp.n[0]};
}

vector<unsigned> primes;

/*
 * calculate all primes in [1, bound]
 */
void init_primes(unsigned bound)
{
    vector<bool> del(bound + 1, 0);
    for (unsigned i = 2; i <= bound; i++) {
        if (!del[i]) primes.push_back(i);
        for (auto p : primes) {
            if (p > bound / i) break;
            del[p * i] = 1;
            if (i % p == 0) break;
        }
    }
}

bool  is_b_smooth(LargeInteger inp)
{
    for (unsigned i = 0; i < primes.size(); i++) {
        for ( ; ; ) {
            auto ret = unsigned_div_mod(inp, primes[i]);
            if (ret.second == 0) inp = ret.first;
            else break;
        }
    }
    for (unsigned i = 1; i < maxn; i++)
        if (inp.n[i]) return false;
    if (inp.n[0] != 1) return false;
    return true;
}

/*
 * input is guaranteed to be coprime and return a pair of <a, b> that a*b = input
 */

mutex mtx_gen;
vector<LargeInteger> generators;

void worker(const LargeInteger& inp, unsigned my_thread, unsigned tot_threads)
{
    LargeInteger cnt = sqrt_ceil(inp) + my_thread;

    while (generators.size() < primes.size() + 1) {
        LargeInteger mod = cnt * cnt % inp;
        if (is_b_smooth(mod)) {
            scoped_lock lck(mtx_gen);
            generators.push_back(mod);
        }
        cnt += tot_threads;
    }
}

void dixon_factorize(const LargeInteger& inp, unsigned num_threads)
{
    unsigned bound = inp.get_dixon_bound();
    init_primes(bound);
    generators.reserve(primes.size() + 1);

    vector<thread> threads(num_threads);
    for (unsigned i = 0; i < num_threads; i++)
        threads[i] = thread(worker, cref(inp), i, num_threads);
    for (auto& thd : threads) thd.join();
}

int main()
{
    cout << thread::hardware_concurrency() << endl;
    dixon_factorize(string("123434478345458574"), 1);
    return 0;
}

