#pragma once
/* ------------------------------------------------------------------------
 * arm_neon_fix.h  --  ONLY correction applied to upstream HalftimeHash.
 *
 * The vendored halftime-hash.hpp is byte-for-byte identical to upstream
 * (jbapple/HalftimeHash, commit caf7924ceab4721f4e0cc33442b185558ba7f1c4,
 * 2022-05-28; sha256 7ef5dd48f54537b430f85bc1867b23a93551ab1c56415cfcef362d1651956cc3).
 *
 * That upstream header does NOT compile on AArch64/NEON: the 128-bit block
 * wrappers are defined with the "Sse2" suffix under
 *     #if __SSE2__ || defined(__ARM_NEON) ...
 * (as V2Sse2 / V3Sse2 / V4Sse2, backed by the NEON BlockWrapper128), but the
 * ARM specialization block calls SPECIALIZE_4(.,Neon), i.e. references the
 * never-defined identifiers V2Neon / V3Neon / V4Neon  ->  compile error.
 *
 * We fix this WITHOUT editing the verbatim header. The SPECIALIZE macro builds
 * the callee via the "##" paste operator (V##version##isa). A token produced by
 * "##" is rescanned for further macro replacement, so the three object-like
 * aliases below redirect the pasted V?Neon identifiers to the real,
 * NEON-backed V?Sse2 wrappers. This yields genuine NEON SIMD and reproduces the
 * official test vectors exactly (see selftest.cpp).
 *
 * On x86 the identifiers V2Neon/V3Neon/V4Neon never appear (the header takes an
 * AVX/SSE SPECIALIZE branch), so these macros are inert there. Include this
 * file BEFORE halftime-hash.hpp on every platform.
 * ---------------------------------------------------------------------- */
#if defined(__ARM_NEON) || defined(__ARM_NEON__)
#define V2Neon V2Sse2
#define V3Neon V3Sse2
#define V4Neon V4Sse2
#endif
