// AUTO-GENERATED from char2/decode_n13.py (transpiled; do not edit by hand).
export function decodeN13(c, F) {
  const M = (a,b) => F.mul(a,b), S = a => F.mul(a,a), Cu = a => F.mul(F.mul(a,a),a);
  const [c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12] = c;
  const a5 = c12
  const s = c11 ^ a5
  const a12 = c10 ^ M(a5, s) ^ a5 ^ 1n
  const a11 = s ^ a12
  const rest7_no_a9 = (
    ((((((((((M(a5, S(a11)) ^ M(a5, a11)) ^ M(a5, S(a12))) ^ a5) ^ Cu(a11)) ^ M(S(a11), a12)) ^ M(a11, S(a12))) ^ M(a11, a12)) ^ Cu(a12)) ^ S(a12)) ^ a12)
    )
  const a9 = c7 ^ rest7_no_a9
  const rest6_no_a8 = (
    ((((((((((((((M(a5, a9) ^ M(a5, Cu(a11))) ^ M(M(a5, S(a11)), a12)) ^ M(a5, S(a11))) ^ M(M(a5, a11), S(a12))) ^ M(M(a5, a11), a12)) ^ M(a5, a11)) ^ M(a5, Cu(a12))) ^ M(a5, a12)) ^ M(S(a11), a12)) ^ S(a11)) ^ M(a11, a12)) ^ a11) ^ Cu(a12)) ^ S(a12))
    )
  const a8 = c6 ^ rest6_no_a8
  const rest9_no_a10 = (
    (((((((M(a5, a11) ^ a5) ^ a8) ^ a9) ^ S(a11)) ^ M(a11, a12)) ^ S(a12)) ^ a12)
    )
  const a10 = c9 ^ rest9_no_a10
  const rest8_no_a1 = (
    (((((((((((((M(a5, a8) ^ M(a5, a9)) ^ M(a5, a10)) ^ M(a5, S(a11))) ^ M(M(a5, a11), a12)) ^ M(a5, a11)) ^ M(a5, S(a12))) ^ M(a5, a12)) ^ a5) ^ a8) ^ a9) ^ a10) ^ M(a11, a12)) ^ a12)
    )
  const a1 = c8 ^ rest8_no_a1
  const rest5_no_a7 = (
    (((((((((((((((((((((((((((a1 ^ M(a5, a8)) ^ M(a5, a10)) ^ M(a5, Cu(a11))) ^ M(a5, S(a11))) ^ M(M(a5, a11), S(a12))) ^ M(a5, a11)) ^ M(a8, a9)) ^ M(a8, a10)) ^ M(a8, S(a11))) ^ M(a8, a11)) ^ M(a8, S(a12))) ^ M(a8, a12)) ^ a8) ^ M(a9, a10)) ^ M(a9, S(a11))) ^ M(a9, S(a12))) ^ M(a10, S(a11))) ^ M(a10, a11)) ^ M(a10, S(a12))) ^ M(a10, a12)) ^ M(Cu(a11), a12)) ^ M(S(a11), S(a12))) ^ M(S(a11), a12)) ^ S(a11)) ^ M(a11, Cu(a12))) ^ M(a11, S(a12))) ^ M(a11, a12))
    )
  const a7 = c5 ^ rest5_no_a7
  const rest4_no_a3 = (
    (((((((((((((((((((((((((((((((((((((((((M(a1, a9) ^ M(a1, a10)) ^ M(a1, S(a11))) ^ M(a1, a11)) ^ M(a1, S(a12))) ^ M(a1, a12)) ^ M(a5, a7)) ^ M(M(a5, a8), a9)) ^ M(M(a5, a8), a10)) ^ M(M(a5, a8), S(a11))) ^ M(M(a5, a8), a11)) ^ M(M(a5, a8), S(a12))) ^ M(M(a5, a8), a12)) ^ M(M(a5, a9), a10)) ^ M(M(a5, a9), S(a11))) ^ M(M(a5, a9), S(a12))) ^ M(a5, a9)) ^ M(M(a5, a10), S(a11))) ^ M(M(a5, a10), a11)) ^ M(M(a5, a10), S(a12))) ^ M(M(a5, a10), a12)) ^ M(M(a5, Cu(a11)), a12)) ^ M(a5, Cu(a11))) ^ M(M(a5, S(a11)), S(a12))) ^ M(M(a5, S(a11)), a12)) ^ M(M(a5, a11), Cu(a12))) ^ M(M(a5, a11), a12)) ^ a5) ^ M(a8, S(a11))) ^ M(a8, S(a12))) ^ M(a8, a12)) ^ M(a9, S(a11))) ^ M(a9, a11)) ^ M(a9, S(a12))) ^ M(a9, a12)) ^ M(a10, S(a11))) ^ M(a10, a11)) ^ M(a10, S(a12))) ^ M(Cu(a11), a12)) ^ M(S(a11), a12)) ^ S(a11)) ^ M(a11, Cu(a12)))
    )
  const a3 = c4 ^ rest4_no_a3
  const rest3_no_a3a4 = (
    (((((((((((((((((((((((((((((((((((M(a1, a9) ^ M(a1, a10)) ^ M(a1, a11)) ^ a1) ^ M(a5, a7)) ^ M(M(a5, a8), a9)) ^ M(M(a5, a8), a10)) ^ M(M(a5, a8), a11)) ^ M(M(a5, a9), a10)) ^ M(M(a5, a10), a11)) ^ M(a5, Cu(a11))) ^ M(M(a5, S(a11)), S(a12))) ^ a5) ^ M(a7, a11)) ^ M(a7, a12)) ^ M(M(a8, a9), a11)) ^ M(M(a8, a9), a12)) ^ M(M(a8, a10), a11)) ^ M(M(a8, a10), a12)) ^ M(a8, a10)) ^ M(a8, S(a11))) ^ M(M(a8, a11), a12)) ^ M(a8, a11)) ^ M(M(a9, a10), a11)) ^ M(M(a9, a10), a12)) ^ M(a9, S(a11))) ^ M(a9, a11)) ^ M(a10, S(a11))) ^ M(M(a10, a11), a12)) ^ M(Cu(a11), S(a12))) ^ M(Cu(a11), a12)) ^ Cu(a11)) ^ M(S(a11), Cu(a12))) ^ M(S(a11), S(a12))) ^ a11) ^ a12)
    )
  const a4 = c3 ^ rest3_no_a3a4 ^ a3
  const rest1_no_a6 = (
    (((((((((((((((((((((((((M(a1, a3) ^ M(a1, a4)) ^ M(M(a1, a9), a11)) ^ M(M(a1, a10), a11)) ^ M(M(a5, a7), a11)) ^ M(M(M(a5, a8), a9), a11)) ^ M(M(M(a5, a8), a10), a11)) ^ M(M(M(a5, a9), a10), a11)) ^ M(M(a5, Cu(a11)), S(a12))) ^ M(a5, a11)) ^ M(a7, a8)) ^ M(M(a7, a11), a12)) ^ M(a7, a11)) ^ M(M(a8, a9), a10)) ^ M(M(M(a8, a9), a11), a12)) ^ M(M(a8, a9), a11)) ^ M(M(M(a8, a10), a11), a12)) ^ M(M(a8, a10), a11)) ^ M(M(a8, S(a11)), S(a12))) ^ M(M(M(a9, a10), a11), a12)) ^ M(M(a9, a10), a11)) ^ M(M(a9, S(a11)), S(a12))) ^ M(M(a10, S(a11)), S(a12))) ^ M(Cu(a11), Cu(a12))) ^ M(Cu(a11), S(a12))) ^ M(a11, a12))
    )
  const a6 = c1 ^ rest1_no_a6
  const rest2_no_a2 = (
    (((((((((((((((((((((((((((((((((((((((((((((M(a1, a3) ^ M(M(a1, a9), a11)) ^ M(M(a1, a9), a12)) ^ M(a1, a9)) ^ M(M(a1, a10), a11)) ^ M(M(a1, a10), a12)) ^ M(a1, S(a11))) ^ M(M(a1, a11), a12)) ^ a1) ^ M(a3, a4)) ^ M(M(a5, a7), a11)) ^ M(M(a5, a7), a12)) ^ M(a5, a7)) ^ M(M(M(a5, a8), a9), a11)) ^ M(M(M(a5, a8), a9), a12)) ^ M(M(a5, a8), a9)) ^ M(M(M(a5, a8), a10), a11)) ^ M(M(M(a5, a8), a10), a12)) ^ M(M(a5, a8), S(a11))) ^ M(M(M(a5, a8), a11), a12)) ^ M(M(M(a5, a9), a10), a11)) ^ M(M(M(a5, a9), a10), a12)) ^ M(M(a5, a9), a10)) ^ M(M(a5, a9), S(a11))) ^ M(M(a5, a10), S(a11))) ^ M(M(M(a5, a10), a11), a12)) ^ M(M(a5, Cu(a11)), S(a12))) ^ M(M(a5, Cu(a11)), a12)) ^ M(M(a5, S(a11)), Cu(a12))) ^ M(a5, a11)) ^ M(a5, a12)) ^ M(a7, a12)) ^ a7) ^ M(M(a8, a9), a12)) ^ M(a8, a9)) ^ M(M(a8, a10), a12)) ^ M(a8, S(a11))) ^ M(M(a8, a11), a12)) ^ M(M(a9, a10), a12)) ^ M(a9, S(a11))) ^ M(M(a9, a11), a12)) ^ M(a10, S(a11))) ^ M(Cu(a11), a12)) ^ M(S(a11), Cu(a12))) ^ M(S(a11), S(a12))) ^ a11)
    )
  const a2 = c2 ^ rest2_no_a2
  const rest0_no_a0 = (
    (((((((((((((((((((((((((((M(a1, a2) ^ M(M(a1, a3), a4)) ^ M(M(a1, a9), a10)) ^ M(M(M(a1, a9), a11), a12)) ^ M(M(M(a1, a10), a11), a12)) ^ M(M(a1, S(a11)), S(a12))) ^ M(a5, a6)) ^ M(M(a5, a7), a8)) ^ M(M(M(a5, a7), a11), a12)) ^ M(M(M(a5, a8), a9), a10)) ^ M(M(M(M(a5, a8), a9), a11), a12)) ^ M(M(M(M(a5, a8), a10), a11), a12)) ^ M(M(M(a5, a8), S(a11)), S(a12))) ^ M(M(M(M(a5, a9), a10), a11), a12)) ^ M(M(M(a5, a9), S(a11)), S(a12))) ^ M(M(M(a5, a10), S(a11)), S(a12))) ^ M(M(a5, Cu(a11)), Cu(a12))) ^ M(M(a5, a11), a12)) ^ M(a7, a8)) ^ M(M(a7, a11), a12)) ^ M(M(a8, a9), a10)) ^ M(M(M(a8, a9), a11), a12)) ^ M(M(M(a8, a10), a11), a12)) ^ M(M(a8, S(a11)), S(a12))) ^ M(M(M(a9, a10), a11), a12)) ^ M(M(a9, S(a11)), S(a12))) ^ M(M(a10, S(a11)), S(a12))) ^ M(Cu(a11), Cu(a12)))
    )
  const a0 = c0 ^ rest0_no_a0;
  return [a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12];
}
