// ptrank core: bit-parallel GF(2) linear algebra for the partial-transpose rank of the identity (d = 2).
//
// Conventions are EXACTLY those of src/ptrank/ptr.py (the Python reference):
//   an n x n matrix is n row bitmasks, bit j of row i is the entry [i][j];
//   Phi(X) = sum_r V_r X^T U_r,  (V X^T U)[i1,i2] = sum_{j1,j2} V[i1,j2] X[j1,j2] U[j1,i2];
//   the n^2 x n^2 matrix of Phi has row index i1*n+i2 and column index j1*n+j2;
//   cost = (R, rho, R+rho) with R = rank(B), B = sum_r vec(U_r) vec(V_r)^T, rho = rank(I + Phi).
// n <= 8, so every row of an n^2 x n^2 matrix is one uint64_t.
#pragma once
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

typedef uint64_t u64;
typedef unsigned __int128 u128;

static const int NMAX = 8;

struct Term {
    uint8_t V[NMAX];
    uint8_t U[NMAX];
};

static inline int popc(u64 x) { return __builtin_popcountll(x); }
static inline int par(u64 x) { return __builtin_parityll(x); }

// rank of cnt rows (destroys a)
static inline int rank_rows(u64* a, int cnt) {
    int rk = 0;
    for (int i = 0; i < cnt; i++) {
        u64 p = a[i];
        if (!p) continue;
        rk++;
        u64 low = p & (0 - p);
        for (int j = i + 1; j < cnt; j++) a[j] ^= p & (0 - (u64)((a[j] & low) != 0));
    }
    return rk;
}

// M = Phi (no identity added)
static inline void phi_rows(int n, const Term* t, int R, u64* M) {
    int N = n * n;
    for (int k = 0; k < N; k++) M[k] = 0;
    for (int r = 0; r < R; r++) {
        u64 W[NMAX];
        for (int i2 = 0; i2 < n; i2++) W[i2] = 0;
        for (int j1 = 0; j1 < n; j1++)
            for (int i2 = 0; i2 < n; i2++)
                if ((t[r].U[j1] >> i2) & 1) W[i2] ^= 1ull << (j1 * n);
        // row (i1,i2) ^= sum_{j1 : U[j1][i2]} V[i1] << (j1*n)  ==  W[i2] * V[i1]  (no carries: V[i1] < 2^n)
        for (int i1 = 0; i1 < n; i1++)
            for (int i2 = 0; i2 < n; i2++) M[i1 * n + i2] ^= W[i2] * (u64)t[r].V[i1];
    }
}

static inline int rho_of(int n, const Term* t, int R) {
    u64 M[64];
    phi_rows(n, t, R, M);
    int N = n * n;
    for (int k = 0; k < N; k++) M[k] ^= 1ull << k;
    return rank_rows(M, N);
}

// rank of B = sum_r vec(U_r) vec(V_r)^T
static inline int rankB_of(int n, const Term* t, int R) {
    u64 B[64];
    int N = n * n;
    for (int k = 0; k < N; k++) B[k] = 0;
    for (int r = 0; r < R; r++) {
        u64 vv = 0;
        for (int a = 0; a < n; a++) vv |= (u64)t[r].V[a] << (a * n);
        for (int a = 0; a < n; a++)
            for (int b = 0; b < n; b++)
                if ((t[r].U[a] >> b) & 1) B[a * n + b] ^= vv;
    }
    return rank_rows(B, N);
}

struct Cost {
    int R, rho, total;
};
static inline Cost cost_of(int n, const Term* t, int R) {
    Cost c;
    c.R = rankB_of(n, t, R);
    c.rho = rho_of(n, t, R);
    c.total = c.R + c.rho;
    return c;
}

// ---------------------------------------------------------------------------------------------------------
// RNG: splitmix64 seeding + xoshiro256**
struct Rng {
    u64 s[4];
    static u64 sm(u64& x) {
        u64 z = (x += 0x9e3779b97f4a7c15ull);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
        return z ^ (z >> 31);
    }
    explicit Rng(u64 seed = 1) {
        u64 x = seed;
        for (int i = 0; i < 4; i++) s[i] = sm(x);
    }
    static inline u64 rotl(u64 x, int k) { return (x << k) | (x >> (64 - k)); }
    inline u64 next() {
        u64 r = rotl(s[1] * 5, 7) * 9, t = s[1] << 17;
        s[2] ^= s[0];
        s[3] ^= s[1];
        s[1] ^= s[2];
        s[0] ^= s[3];
        s[2] ^= t;
        s[3] = rotl(s[3], 45);
        return r;
    }
    inline uint32_t below(uint32_t k) { return (uint32_t)(((next() >> 32) * (u64)k) >> 32); }
    inline double uni() { return (double)(next() >> 11) * (1.0 / 9007199254740992.0); }
};

// ---------------------------------------------------------------------------------------------------------
// small n x n matrix helpers (row bitmasks)
static inline void mat_ident(int n, uint8_t* A) {
    for (int i = 0; i < n; i++) A[i] = (uint8_t)(1u << i);
}
static inline void mat_mul(int n, const uint8_t* A, const uint8_t* B, uint8_t* C) {  // C = A B
    uint8_t out[NMAX];
    for (int i = 0; i < n; i++) {
        uint8_t r = 0, a = A[i];
        while (a) {
            int k = __builtin_ctz(a);
            a &= (uint8_t)(a - 1);
            r ^= B[k];
        }
        out[i] = r;
    }
    memcpy(C, out, n);
}
static inline void mat_transpose(int n, const uint8_t* A, uint8_t* C) {
    uint8_t out[NMAX];
    for (int i = 0; i < n; i++) {
        uint8_t r = 0;
        for (int j = 0; j < n; j++) r |= (uint8_t)(((A[j] >> i) & 1) << j);
        out[i] = r;
    }
    memcpy(C, out, n);
}
static inline int mat_rank(int n, const uint8_t* A) {
    u64 t[NMAX];
    for (int i = 0; i < n; i++) t[i] = A[i];
    return rank_rows(t, n);
}
// inverse; returns false if singular
static inline bool mat_inv(int n, const uint8_t* A, uint8_t* C) {
    uint16_t w[NMAX];
    for (int i = 0; i < n; i++) w[i] = (uint16_t)(A[i] | (1u << (n + i)));
    for (int c = 0; c < n; c++) {
        int p = -1;
        for (int i = c; i < n; i++)
            if ((w[i] >> c) & 1) {
                p = i;
                break;
            }
        if (p < 0) return false;
        std::swap(w[c], w[p]);
        for (int i = 0; i < n; i++)
            if (i != c && ((w[i] >> c) & 1)) w[i] ^= w[c];
    }
    for (int i = 0; i < n; i++) C[i] = (uint8_t)(w[i] >> n);
    return true;
}
static inline void mat_random_invertible(int n, Rng& g, uint8_t* A) {
    for (;;) {
        for (int i = 0; i < n; i++) A[i] = (uint8_t)(g.next() & ((1u << n) - 1));
        if (mat_rank(n, A) == n) return;
    }
}

// ---------------------------------------------------------------------------------------------------------
// JSON (our own witness format only)
struct Witness {
    int n = 0, R = -1, rho = -1, total = -1;
    std::vector<Term> terms;
    std::string note;
};

static inline std::string witness_json(int n, const std::vector<Term>& t, const std::string& extra = "") {
    Cost c = cost_of(n, t.data(), (int)t.size());
    std::string s = "{\"n\": " + std::to_string(n) + ", \"R\": " + std::to_string(c.R) + ", \"rho\": " +
                    std::to_string(c.rho) + ", \"total\": " + std::to_string(c.total) + ", \"terms\": [";
    for (size_t r = 0; r < t.size(); r++) {
        s += (r ? ", [[" : "[[");
        for (int i = 0; i < n; i++) s += (i ? ", " : "") + std::to_string((int)t[r].V[i]);
        s += "], [";
        for (int i = 0; i < n; i++) s += (i ? ", " : "") + std::to_string((int)t[r].U[i]);
        s += "]]";
    }
    s += "]";
    if (!extra.empty()) s += ", " + extra;
    s += "}";
    return s;
}

// parse {"n":..,"R":..,"rho":..,"total":..,"terms":[[[..],[..]],...]} ; tolerant of extra fields.
static inline bool parse_witness(const std::string& s, Witness& w, std::string& err) {
    auto find_int = [&](const char* key, int& out) -> bool {
        std::string k = std::string("\"") + key + "\"";
        size_t p = s.find(k);
        if (p == std::string::npos) return false;
        p = s.find(':', p);
        if (p == std::string::npos) return false;
        out = atoi(s.c_str() + p + 1);
        return true;
    };
    if (!find_int("n", w.n) || w.n < 1 || w.n > NMAX) {
        err = "missing or bad field n";
        return false;
    }
    find_int("R", w.R);
    find_int("rho", w.rho);
    find_int("total", w.total);
    size_t p = s.find("\"terms\"");
    if (p == std::string::npos) {
        err = "missing field terms";
        return false;
    }
    p = s.find('[', p);
    if (p == std::string::npos) {
        err = "bad terms";
        return false;
    }
    // collect all integers inside the balanced bracket expression starting at p
    int depth = 0;
    std::vector<long> nums;
    size_t i = p;
    for (; i < s.size(); i++) {
        char ch = s[i];
        if (ch == '[') depth++;
        else if (ch == ']') {
            depth--;
            if (depth == 0) break;
        } else if (ch >= '0' && ch <= '9') {
            long v = 0;
            while (i < s.size() && s[i] >= '0' && s[i] <= '9') v = v * 10 + (s[i++] - '0');
            i--;
            nums.push_back(v);
        } else if (ch == '-') {
            err = "negative number in terms";
            return false;
        }
    }
    if (depth != 0) {
        err = "unbalanced brackets in terms";
        return false;
    }
    int n = w.n;
    if (nums.size() % (2 * n) != 0) {
        err = "terms: number of integers is not a multiple of 2n";
        return false;
    }
    w.terms.clear();
    for (size_t k = 0; k < nums.size(); k += 2 * n) {
        Term t;
        memset(&t, 0, sizeof t);
        for (int j = 0; j < n; j++) {
            if (nums[k + j] >= (1 << n) || nums[k + n + j] >= (1 << n)) {
                err = "terms: row bitmask out of range";
                return false;
            }
            t.V[j] = (uint8_t)nums[k + j];
            t.U[j] = (uint8_t)nums[k + n + j];
        }
        w.terms.push_back(t);
    }
    return true;
}

static inline bool read_file(const char* path, std::string& out) {
    FILE* f = fopen(path, "rb");
    if (!f) return false;
    char buf[65536];
    size_t k;
    out.clear();
    while ((k = fread(buf, 1, sizeof buf, f)) > 0) out.append(buf, k);
    fclose(f);
    return true;
}

static inline void print_term_matrices(FILE* f, int n, const std::vector<Term>& t) {
    for (size_t r = 0; r < t.size(); r++) {
        fprintf(f, "  term %zu   V%*s U\n", r, n > 1 ? n : 1, "");
        for (int i = 0; i < n; i++) {
            fprintf(f, "    ");
            for (int j = 0; j < n; j++) fputc(((t[r].V[i] >> j) & 1) ? '1' : '.', f);
            fprintf(f, "   ");
            for (int j = 0; j < n; j++) fputc(((t[r].U[i] >> j) & 1) ? '1' : '.', f);
            fputc('\n', f);
        }
    }
}
