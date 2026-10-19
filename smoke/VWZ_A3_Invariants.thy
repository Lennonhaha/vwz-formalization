(* SPDX-License-Identifier: Apache-2.0
   VWZ A3 smoke -- integer/natural-number invariants

   The purely arithmetic obligations of the v0 list: dimension relations
   (B1/B3), the |Z| size law (C4), the row-split identity (D3), the size
   relation between the target sets (D2), and serialization length positivity
   (F2/F3). These need no algebra library, so they form the positive control.

   Scope: TOOLCHAIN SMOKE ONLY; no security claim.
*)

theory VWZ_A3_Invariants
  imports Main
begin

(* B1: with n = 2k+2 and m = 2k+1, we get m = n - 1 *)
lemma B1_m_eq_n_minus_1: "(n::nat) = 2 * k + 2 ==> m = 2 * k + 1 ==> m = n - 1"
  by arith

(* B3: the challenge weight is positive *)
lemma B3_w_positive: "(w::nat) = k + 1 ==> w >= 1"
  by arith

(* C4 (i): the target set size is k+1 when |Z| = n - (k+1) *)
lemma C4_Z_eq_k_plus_1: "(n::nat) = 2 * k + 2 ==> Z = n - (k + 1) ==> Z = k + 1"
  by arith

(* C4 (ii): for k >= 1 the target set has at least two elements *)
lemma C4_Z_at_least_two: "1 <= (k::nat) ==> 2 * k + 2 - (k + 1) >= 2"
  by arith

(* D3: the row split adds up to m = 2k+1 *)
lemma D3_row_split_identity:
  "Z = (k::nat) + 1 ==> (a::nat) >= 1 ==> a <= Z ==> (k + 1) + (a - 1) + (Z - a) = 2 * k + 1"
  by arith

(* D2 (arithmetic rendering of the size relation): if |Za| = a+1, |Zb| = b+1,
   |Z| = k+1 and |Za| + |Zb| = |Z| + 1, then a + b = k. *)
lemma D2_size_relation:
  "(Za::nat) = a + 1 ==> (Zb::nat) = b + 1 ==> (Z::nat) = k + 1 ==> Za + Zb = Z + 1 ==> a + b = k"
  by arith

(* F2: the pk serialization length 1 + 2*n*m^2 is positive *)
lemma F2_pk_len_positive: "0 < 1 + 2 * (n::nat) * (m * m)"
  by simp

(* F3: the signature serialization length 1 + 4*m is positive *)
lemma F3_sig_len_positive: "0 < 1 + 4 * (m::nat)"
  by simp

end
