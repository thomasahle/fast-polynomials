#pragma once
#if defined(__x86_64__)
  #include <immintrin.h>
  static inline __m128i mm_bswap64(__m128i v) {
      return _mm_shuffle_epi8(v, _mm_set_epi8(8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7));
  }
#else
  #include <arm_neon.h>
#endif
