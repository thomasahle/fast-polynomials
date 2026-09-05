// Verification codes of the SMHasher3 experimental file through the shim, plus a cross-check of the
// backend selected here against the portable backend (compiled twice: default and CHG_FORCE_PORTABLE).
#include <cstdio>
#include <vector>
#include <cstring>
#include "chainhash_goldi_exp.cpp"
template <int BW, int K, int S, int FIN> static uint32_t vcode() {
    std::vector<uint8_t> key(256), hashes(256 * 8);
    for (int i = 0; i < 256; i++) {
        uintptr_t sp = chg_seed_init<BW, K, FIN>((seed_t)(256 - i));
        ChainHashG<BW, K, S, FIN, false>(key.data(), (size_t)i, (seed_t)sp, &hashes[8 * i]);
        key[i] = (uint8_t)i;
    }
    uintptr_t sp = chg_seed_init<BW, K, FIN>((seed_t)0);
    uint8_t total[8];
    ChainHashG<BW, K, S, FIN, false>(hashes.data(), hashes.size(), (seed_t)sp, total);
    return (uint32_t)total[0] | ((uint32_t)total[1] << 8) | ((uint32_t)total[2] << 16) | ((uint32_t)total[3] << 24);
}
int main() {
    printf("backend %s\n", CHG_IMPL_STR);
    printf("VCODE chainhash-256 (CHAR2, must be de1ab9f9) %08x\n", vcode<32, 5, 1, CHG_FIN_CHAR2>());
    printf("VCODE chainhash-1k (CHAR2, must be 32b4ee71) %08x\n", vcode<128, 5, 2, CHG_FIN_CHAR2>());
    printf("VCODE chainhash-g4-256 %08x\n", vcode<32, 5, 1, CHG_FIN_G4>());
    printf("VCODE chainhash-g5-256 %08x\n", vcode<32, 5, 1, CHG_FIN_G5>());
    printf("VCODE chainhash-g5-1k %08x\n", vcode<128, 5, 2, CHG_FIN_G5>());
    return 0;
}
