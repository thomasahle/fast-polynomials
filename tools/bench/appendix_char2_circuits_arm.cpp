// Timing of the four searched GF(2^64) circuits displayed in
// sections/appendix_polynomials.tex (degrees 7, 9, 11, 13), ARM NEON PMULL.
// Compile: clang++ -O3 -std=c++17 -march=armv8-a+crypto appendix_char2_circuits_arm.cpp -o appendix_char2_arm
#include <chrono>
#include <cstdio>
#include <vector>
#include <algorithm>
#include <random>
#include <iostream>
using namespace std;
#include "framework/multiplication_arm.h"
using namespace std;
typedef uint8x16_t V;
static inline V M(V a, V b) { return gf64_mult(a, b); }
static inline V X(V a, V b) { return xor128(a, b); }

// keys a[]
static inline V deg7(V x, const V* a) {
    V y = M(x, X(x, a[0]));
    V z = M(X(x, a[1]), X(y, a[2]));
    V s = X(X(x, y), z);
    V t = M(X(s, a[3]), s);
    V u = M(X(x, a[4]), X(X(y, t), a[5]));
    return X(u, a[6]);
}
static inline V deg9(V x, const V* a) {
    V y = M(x, x);
    V z = M(X(X(x, y), a[0]), X(x, a[1]));
    V t = M(X(z, a[2]), X(X(y, z), a[3]));
    V u = M(X(X(X(x, z), t), a[4]), X(X(X(x, y), z), a[5]));
    V v = M(X(x, a[6]), X(y, a[7]));
    return X(X(u, v), a[8]);
}
static inline V deg11(V x, const V* a) {
    V y = M(x, X(x, a[0]));
    V xy = X(x, y);
    V z = M(X(xy, a[1]), xy);
    V t = M(X(X(x, z), a[2]), X(z, a[3]));
    V u = M(X(t, a[4]), X(x, a[5]));
    V v = M(X(X(X(X(xy, z), t), u), a[6]), X(y, a[7]));
    V w = M(X(x, a[8]), X(X(X(y, z), t), a[9]));
    return X(X(X(z, v), w), a[10]);
}
static inline V deg13(V x, const V* a) {
    V y = M(x, x);
    V z = M(X(y, a[0]), X(X(x, y), a[1]));
    V t = M(X(X(x, z), a[2]), X(x, a[3]));
    V u = M(X(X(x, y), a[4]), X(X(x, t), a[5]));
    V v = M(X(X(y, z), a[6]), X(u, a[7]));
    V w = M(X(X(X(y, z), t), a[8]), X(X(x, u), a[9]));
    V s = M(X(X(X(X(X(x, z), u), v), w), a[10]), X(x, a[11]));
    return X(X(t, s), a[12]);
}

template <typename F>
static double time_ns(F f, const vector<V>& xs, const V* a, int reps) {
    vector<double> t;
    V acc = from64(0);
    for (int r = 0; r < reps; r++) {
        auto t0 = chrono::high_resolution_clock::now();
        for (const V& x : xs) acc = X(acc, f(x, a));
        auto t1 = chrono::high_resolution_clock::now();
        t.push_back(chrono::duration<double, nano>(t1 - t0).count() / xs.size());
    }
    if (lower64(acc) == 12345) printf("(unlikely)\n");   // keep acc live
    sort(t.begin(), t.end());
    return t[t.size() / 2];   // median over reps (first half of reps are effectively warmup)
}

int main() {
    const size_t N = 1000000; const int REPS = 41;
    mt19937_64 rng(42);
    vector<V> xs(N); for (auto& x : xs) x = from64(rng());
    V a[13]; for (auto& k : a) k = from64(rng());
    printf("Apple-silicon PMULL, %zu random inputs, median of %d reps, ns per evaluation\n", N, REPS);
    printf("degree  7 (4 products): %.2f ns\n", time_ns(deg7,  xs, a, REPS));
    printf("degree  9 (5 products): %.2f ns\n", time_ns(deg9,  xs, a, REPS));
    printf("degree 11 (6 products): %.2f ns\n", time_ns(deg11, xs, a, REPS));
    printf("degree 13 (7 products): %.2f ns\n", time_ns(deg13, xs, a, REPS));
}
