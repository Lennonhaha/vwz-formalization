(*  Title:      VWZ_ModAlgebra.thy
    SPDX-License-Identifier: Apache-2.0

    The modular layer that T2_B3 actually needs.

    The obligation as written in v0 quantifies over `invertible` from
    VWZ_Matrix, whose product is an integer dot product, while the row operations
    that build the matrices (`add_row_mult`, `scale_row`) reduce every entry mod
    q.  The two do not commute: `VWZ_Probe` shows

      mat_mult (row_add_matrix 2 0 1 1) [[1,3328],[0,1]] = [[1,3329],[0,1]]
      add_row_mult [[1,3328],[0,1]] 0 1 1               = [[1,0],[0,1]]

    so the bridge lemma of the original plan is false as stated, and a product of
    elementary matrices generally has determinant +-1 in Z only after reduction.

    This file therefore introduces the modular product and the modular notion of
    invertibility, so that the restated obligation speaks about the same algebra
    the algorithm performs.  Nothing about the integer product is changed.

    Status: definitions plus the arithmetic they rest on.  The entrywise bridge
    (`mat_mult_mod (row_add_matrix ...) A = add_row_mult A ...`) and associativity
    of the modular product are the next two lemmas; they are NOT proved here and
    nothing in this file assumes them.
*)

theory VWZ_ModAlgebra
  imports VWZ_RREF
begin

section \<open>Reduction arithmetic\<close>

lemma fq_zero [simp]: "fq 0 = 0"
  unfolding fq_def by simp

lemma fq_one [simp]: "fq 1 = 1"
  unfolding fq_def by simp

lemma fq_idem [simp]: "fq (fq x) = fq x"
  unfolding fq_def by (simp add: mod_mod_trivial)

lemma fq_range: "0 \<le> fq x \<and> fq x < 3329"
  unfolding fq_def by (simp add: pos_mod_sign pos_mod_bound)

text \<open>@{text mod_add_eq} and @{text mod_mult_eq} are used once, as facts, and
  never as simp rules: together with @{text fq_idem} they rewrite in opposite
  directions and the simplifier does not terminate (observed: a build that keeps
  running with no output, not an error message).\<close>

lemma fq_add: "fq (x + y) = fq (fq x + fq y)"
  unfolding fq_def by (simp add: mod_add_eq)

lemma fq_mult: "fq (x * y) = fq (fq x * fq y)"
  unfolding fq_def by (simp add: mod_mult_eq)

section \<open>The modular product\<close>

definition mat_mult_mod :: "mat \<Rightarrow> mat \<Rightarrow> mat" where
  "mat_mult_mod A B = map (map fq) (mat_mult A B)"

text \<open>Two-sided invertibility over @{text F_q}: the witness must reproduce the
  identity under the modular product, whose entries are already reduced.  This is
  the notion T2_B3 is restated against (approved 2026-10-21); the integer
  @{text invertible} in VWZ_Matrix stays as it was.\<close>

definition invertible_mod :: "mat \<Rightarrow> bool" where
  "invertible_mod A =
     (\<exists>B. mat_mult_mod A B = id_mat (n_rows A) \<and>
          mat_mult_mod B A = id_mat (n_rows A))"

text \<open>A first, unconditional fact: the modular product is entrywise reduction
  of the integer product, so it is a total function on any pair of matrices.  This
  is recorded because the bridge lemmas will all be phrased as "the integer
  product is right, up to reduction".\<close>

lemma mat_mult_mod_alt: "mat_mult_mod A B = map (map fq) (mat_mult A B)"
  unfolding mat_mult_mod_def by simp

end
