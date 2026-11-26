/* Hepp bound of a primitive, logarithmically divergent graph (Panzer, arXiv:1908.09820).
 *
 *   H(G) = sum over orderings e_1..e_N of the edges of  prod_{k=1}^{N-1} 1/omega({e_1..e_k}),
 *   omega(S) = 2*rank(S) - |S|      (phi^4, D = 4; rank = #vertices touched minus #components).
 *
 * Input on stdin: "V N" followed by N lines "u v" (0-based vertices), the decompleted graph.
 * Usage: hepp_check float          -> H in floating point (long double)
 *        hepp_check p1 p2 ...      -> H mod each prime p_i (p_i < 2^31, p_i > max omega)
 * Output lines: "maxomega W", then "float H" or "mod p r".
 *
 * Algorithm (top-down over edge subsets):
 *   h(S) = 1 if |S| = N-1,   h(S) = sum_{e not in S} h(S+e) / omega(S+e) otherwise,   H = h(empty).
 * The rank is computed by flood fill on vertex bitmasks. The program refuses graphs that are not
 * primitive (omega(S) <= 0 for a proper nonempty S) or not log-divergent (omega(E) != 0). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int V, N, eu[40], ev[40];

static int rank_of(uint32_t S) {
    uint32_t nb[32] = {0}, touched = 0;
    for (int i = 0; i < N; i++)
        if (S >> i & 1) { nb[eu[i]] |= 1u << ev[i]; nb[ev[i]] |= 1u << eu[i]; touched |= (1u << eu[i]) | (1u << ev[i]); }
    int comps = 0; uint32_t left = touched;
    while (left) {
        uint32_t comp = left & -left, frontier = comp;
        while (frontier) {
            int v = __builtin_ctz(frontier); frontier &= frontier - 1;
            uint32_t add = nb[v] & ~comp; comp |= add; frontier |= add;
        }
        left &= ~comp; comps++;
    }
    return __builtin_popcount(touched) - comps;
}

static uint64_t powmod(uint64_t a, uint64_t e, uint64_t p) {
    uint64_t r = 1; a %= p;
    while (e) { if (e & 1) r = r * a % p; a = a * a % p; e >>= 1; }
    return r;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: hepp_check float | p1 p2 ...\n"); return 1; }
    if (scanf("%d %d", &V, &N) != 2 || V > 32 || N > 30 || N < 2) { fprintf(stderr, "bad header\n"); return 1; }
    for (int i = 0; i < N; i++)
        if (scanf("%d %d", &eu[i], &ev[i]) != 2 || eu[i] < 0 || ev[i] < 0 || eu[i] >= V || ev[i] >= V || eu[i] == ev[i]) {
            fprintf(stderr, "bad edge %d\n", i); return 1;
        }
    const uint32_t full = (N == 32) ? 0xffffffffu : ((1u << N) - 1);
    const uint64_t size = (uint64_t)full + 1;
    unsigned char *om = malloc(size);
    if (!om) { fprintf(stderr, "out of memory\n"); return 4; }
    int W = 0;
    for (uint64_t S = 0; S < size; S++) {
        int w = 2 * rank_of((uint32_t)S) - __builtin_popcount((uint32_t)S);
        if (S && S != full && w <= 0) { fprintf(stderr, "not primitive: omega(%llx)=%d\n", (unsigned long long)S, w); return 2; }
        if (S == full && w != 0) { fprintf(stderr, "not log-divergent: omega(E)=%d\n", w); return 3; }
        om[S] = (unsigned char)w; if (w > W) W = w;
    }
    printf("maxomega %d\n", W); fflush(stdout);

    if (!strcmp(argv[1], "float")) {
        long double *h = malloc(size * sizeof(long double));
        if (!h) { fprintf(stderr, "out of memory\n"); return 4; }
        for (int64_t S = (int64_t)full - 1; S >= 0; S--) {
            if (__builtin_popcount((uint32_t)S) == N - 1) { h[S] = 1.0L; continue; }
            long double s = 0; uint32_t T = full & ~(uint32_t)S;
            while (T) { uint32_t b = T & -T; T &= T - 1; s += h[S | b] / om[S | b]; }
            h[S] = s;
        }
        printf("float %.21Lg\n", h[0]);
        return 0;
    }
    uint32_t *h = malloc(size * sizeof(uint32_t));
    if (!h) { fprintf(stderr, "out of memory\n"); return 4; }
    for (int a = 1; a < argc; a++) {
        uint64_t p = strtoull(argv[a], 0, 10), inv[64];
        if (p <= (uint64_t)W || p >= (1ull << 31)) { fprintf(stderr, "prime out of range\n"); return 5; }
        for (int k = 1; k <= W; k++) inv[k] = powmod(k, p - 2, p);
        for (int64_t S = (int64_t)full - 1; S >= 0; S--) {
            if (__builtin_popcount((uint32_t)S) == N - 1) { h[S] = 1; continue; }
            uint64_t s = 0; uint32_t T = full & ~(uint32_t)S;
            while (T) { uint32_t b = T & -T; T &= T - 1; s = (s + (uint64_t)h[S | b] * inv[om[S | b]]) % p; }
            h[S] = (uint32_t)s;
        }
        printf("mod %llu %u\n", (unsigned long long)p, h[0]); fflush(stdout);
    }
    return 0;
}
