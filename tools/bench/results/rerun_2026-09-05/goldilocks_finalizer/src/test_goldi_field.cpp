// Prints 10^6 random (a, b) with a*b mod p, a+b mod p (b canonical), fold(a), plus edge cases.
// Inputs a, b drawn from splitmix64 (seed 12345): a arbitrary 64-bit, b = a' folded (canonical).
#include <cstdio>
#include "goldi_field.h"
int main() {
    uint64_t s = 12345;
    const uint64_t edges[] = {0, 1, 2, GL_EPS, GL_EPS + 1, (uint64_t)1 << 32, ((uint64_t)1 << 32) + 1, GL_P - 1, GL_P - 2, GL_P, GL_P + 1,
                              UINT64_C(0xFFFFFFFFFFFFFFFF), UINT64_C(0xFFFFFFFFFFFFFFFE), (uint64_t)1 << 63, ((uint64_t)1 << 63) - 1,
                              UINT64_C(0xFFFFFFFF00000000), UINT64_C(0x00000000FFFFFFFE), UINT64_C(0x8000000080000000)};
    const int NE = sizeof(edges) / sizeof(edges[0]);
    for (int i = 0; i < NE; i++)
        for (int j = 0; j < NE; j++) {
            uint64_t a = edges[i], b = gl_fold(edges[j]), c = edges[(i + j) % NE];
            printf("%016llx %016llx %016llx %016llx %016llx %016llx %016llx\n", (unsigned long long)a, (unsigned long long)b, (unsigned long long)c,
                   (unsigned long long)gl_mul(a, b), (unsigned long long)gl_add(a, b), (unsigned long long)gl_fold(a), (unsigned long long)gl_mul_add(a, b, c));
        }
    for (int i = 0; i < 1000000; i++) {
        uint64_t a = gl_splitmix64(&s), b = gl_fold(gl_splitmix64(&s));
        if ((i & 7) == 0) a |= UINT64_C(0xFFFFFFFF00000000);   // bias some a toward the top of the range (a >= p likely)
        if ((i & 7) == 1) a = gl_fold(a);
        uint64_t c = gl_splitmix64(&s);
        if ((i & 7) == 2) c = UINT64_C(0xFFFFFFFFFFFFFFFF);
        if ((i & 7) == 3) b = UINT64_C(0xFFFFFFFF00000000), a = UINT64_C(0xFFFFFFFFFFFFFFFF);   // max product
        printf("%016llx %016llx %016llx %016llx %016llx %016llx %016llx\n", (unsigned long long)a, (unsigned long long)b, (unsigned long long)c,
               (unsigned long long)gl_mul(a, b), (unsigned long long)gl_add(a, b), (unsigned long long)gl_fold(a), (unsigned long long)gl_mul_add(a, b, c));
    }
    // finalizer spot values (keys canonical) for the Python side
    uint64_t k[5], nk[5];
    for (int t = 0; t < 2000; t++) {
        for (int i = 0; i < 5; i++) { k[i] = gl_uniform(&s); nk[i] = GL_P - k[i]; }
        uint64_t x = gl_fold(gl_splitmix64(&s));
        printf("F %016llx %016llx %016llx %016llx %016llx %016llx %016llx %016llx\n", (unsigned long long)k[0], (unsigned long long)k[1],
               (unsigned long long)k[2], (unsigned long long)k[3], (unsigned long long)k[4], (unsigned long long)x,
               (unsigned long long)gl_fin_g4(k, nk, x), (unsigned long long)gl_fin_g5(k, nk, x));
    }
    return 0;
}
