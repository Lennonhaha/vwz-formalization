(* SPDX-License-Identifier: Apache-2.0
   VWZ A3 smoke -- Layer A (algebraic / structural layer)

   Scope: TOOLCHAIN SMOKE ONLY. The ring/field axioms are stated inside the
   Isabelle type-class contexts (comm_ring_1, field) so that no library import
   path has to be guessed. Instantiation to the concrete field F_q (q = 3329)
   is a follow-up: the defining theory is to be read off the installed
   distribution instead of being guessed here.

   No security claim is made by this file.
*)

theory VWZ_A3_Field
  imports Main
begin

context comm_ring_1
begin

(* A1: additive commutativity *)
lemma A1_add_comm: "a + b = b + a" by (simp add: add.commute)

(* A2: additive associativity *)
lemma A2_add_assoc: "a + (b + c) = (a + b) + c" by (simp add: add.assoc)

(* A3: additive neutral element *)
lemma A3_add_zero: "a + 0 = a" by simp

(* A4: multiplicative commutativity *)
lemma A4_mult_comm: "a * b = b * a" by (simp add: mult.commute)

(* A5: distributivity (left) *)
lemma A5_distrib_left: "a * (b + c) = a * b + a * c" by (simp add: algebra_simps)

(* A6: annihilation by zero *)
lemma A6_mult_zero: "a * 0 = 0" by simp

(* A7: multiplicative neutral element *)
lemma A7_mult_one: "a * 1 = a" by simp

end

context field
begin

(* A7b: inverse law on non-zero elements *)
lemma A7b_mult_inverse: "a ~= 0 ==> a * inverse a = 1" by simp

end

(* A8: reduced integer representatives stay in range *)
lemma A8_mod_range:
  fixes a q :: int
  assumes "0 < q"
  shows "a mod q < q" and "0 <= a mod q"
  using assms by (simp_all add: pos_mod_bound pos_mod_sign)

end
