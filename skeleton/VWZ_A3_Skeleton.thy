(* SPDX-License-Identifier: Apache-2.0
   VWZ A3 smoke -- OBLIGATION SKELETON (inventory, all `sorry`)

   Every obligation of the v0 formalization plan is listed here exactly once,
   with a type-correct but unproved statement. The number of `sorry`s reported
   by the build is the quantified remaining work for the Isabelle leg.

   COUNT NOTE: this inventory has 8+8+6+8+4+3 = 37 items taken straight from the
   v0 tables (A1-A8, B1-B8, C1-C6, D1-D8, E1-E4, F1-F3), while the commit
   message of the v0 file says "32 proof obligations". The discrepancy is
   recorded as UNSETTLED in plans/vwz-a3-isabelle-windows_20261017.md; the
   inventory below follows the tables, not the commit message.

   Scope: TOOLCHAIN SMOKE ONLY; `sorry` means NOT proved; no security claim.
*)

theory VWZ_A3_Skeleton
  imports Main
begin

(* ---------- Layer A: algebraic structure (8) ---------- *)
lemma A1_field_add_commutative: "a + b = b + (a :: 'a :: comm_ring)" sorry
lemma A2_field_add_associative: "a + (b + c) = (a + b) + (c :: 'a :: comm_ring)" sorry
lemma A3_field_add_neutral: "a + 0 = (a :: 'a :: comm_ring)" sorry
lemma A4_field_mult_commutative: "a * b = b * (a :: 'a :: comm_ring)" sorry
lemma A5_field_distributive: "a * (b + c) = a * b + a * (c :: 'a :: comm_ring)" sorry
lemma A6_field_mult_zero: "a * 0 = (0 :: 'a :: comm_ring)" sorry
lemma A7_field_mult_inverse: "a ~= 0 ==> a * inverse a = (1 :: 'a :: field)" sorry
lemma A8_representatives_in_range: "0 < q ==> (a :: int) mod q < q" sorry

(* ---------- Layer B: key generation invariants (8) ---------- *)
lemma B1_dimensions: "n = 2 * (k :: nat) + 2 ==> m = 2 * k + 1 ==> m = n - 1" sorry
lemma B2_det_is_one: "det (mat :: int list) = 1" sorry
lemma B3_challenge_weight: "w = (k :: nat) + 1 ==> w >= 1" sorry
lemma B4_slice_entries_nonzero: "x1 (i :: nat) ~= 0" sorry
lemma B5_key_shape: "shape_ok (pk :: nat list)" sorry
lemma B6_keygen_deterministic: "kg (seed :: nat list) = kg seed" sorry
lemma B7_every_slice_rank_two: "rank2 (slice2 (seed :: nat list))" sorry
lemma B8_public_key_length: "length (pk :: nat list) = 1 + 2 * n * (m * m)" sorry

(* ---------- Layer C: hash to target (6) ---------- *)
lemma C1_hash_length: "length (hashv (s :: nat list)) = w" sorry
lemma C2_hash_nonempty: "hashv (s :: nat list) ~= []" sorry
lemma C3_sampling_unbiased: "unbiased (sampleBelow :: nat => nat => nat)" sorry
lemma C4_target_size: "Z = n - (k + 1) ==> Z = (k :: nat) + 1" sorry
lemma C5_target_deterministic: "target (s :: nat list) = target s" sorry
lemma C6_adaptation_zero_iff: "adapt (s :: nat list) (i :: nat) = 0 \<longleftrightarrow> t s i = 0" sorry

(* ---------- Layer D: signing correctness (8) ---------- *)
lemma D1_signature_correct: "sig_valid (s :: int list) (msg :: nat list)" sorry
lemma D2_target_sets_relation: "card (Z :: int set) = (k :: nat) + 1" sorry
lemma D3_row_split: "rows (Zx :: int set) = 1 + card (Za :: int set)" sorry
lemma D4_lifted_solution: "D4 (u :: int list)" sorry
lemma D5_lifted_solution_shape: "length (u :: int list) = n" sorry
lemma D6_lifted_solution_consistent: "D6 (u :: int list)" sorry
lemma D7_sign_deterministic: "sign2 (k, s) = sign2 (k, s)" sorry
lemma D8_always_signable_EMPIRICAL: "D8 (k :: nat) (msg :: nat list)" sorry

(* ---------- Layer E: verification completeness (4) ---------- *)
lemma E1_accepts_honest_signature: "E1 (pk :: nat list) (msg :: nat list) (sig :: nat list)" sorry
lemma E2_accepts_after_adaptation: "E2 (pk :: nat list) (msg :: nat list)" sorry
lemma E3_rejection_soundness_for_forgeries: "E3 (pk :: nat list) (msg :: nat list) (sig :: nat list)" sorry
lemma E4_accepts_well_formed: "E4 (pk :: nat list)" sorry

(* ---------- Layer F: serialization (3) ---------- *)
lemma F1_roundtrip: "deser (ser (b :: nat list)) = b" sorry
lemma F2_public_key_byte_length: "length (ser (b :: nat list)) = 1 + 2 * n * (m * m)" sorry
lemma F3_signature_byte_length: "length (serSig (b :: nat list)) = 1 + 4 * m" sorry

end
