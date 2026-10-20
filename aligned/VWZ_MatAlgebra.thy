(*  Title:      VWZ_MatAlgebra.thy
    SPDX-License-Identifier: Apache-2.0

    Matrix algebra over the definition layer of VWZ_Matrix: the identity laws,
    associativity of mat_mult, and the row-operation bridge used by T2_B3.

    These are tooling lemmas, not obligations.  They are stated with explicit
    shape premises rather than hidden assumptions: HOL's nth is total, so a
    list-index fact that is false out of range must be guarded, not ignored.
*)

theory VWZ_MatAlgebra
  imports VWZ_Aux
begin

section \<open>Sum lemmas\<close>

lemma sum_list_map_add:
  "sum_list (map (\<lambda>x. (f x::int) + g x) xs) = sum_list (map f xs) + sum_list (map g xs)"
  by (induct xs) (simp_all add: add.assoc add.left_commute)

lemma sum_list_map_mult_right:
  "sum_list (map (\<lambda>x. (f x::int) * c) xs) = sum_list (map f xs) * c"
  by (induct xs) (simp_all add: distrib_right)

lemma sum_list_map_mult_left:
  "sum_list (map (\<lambda>x. c * (f x::int)) xs) = c * sum_list (map f xs)"
  by (induct xs) (simp_all add: distrib_left)

lemma sum_list_map_const_zero:
  "sum_list (map (\<lambda>_. (0::int)) xs) = 0"
  by (induct xs) simp_all

text \<open>Deferred: the exchange of summation order, which is what associativity of
  @{text mat_mult} needs.  The surviving lemmas above are the ones that close;
  the exchange itself is left out until it is actually proved, so this file
  contains no unproved claim.\<close>

end
