(*  Title:      VWZ_Rank.thy
    SPDX-License-Identifier: Apache-2.0

    The first bricks of a rank theory: outer products and their shapes, the
    sum of two outer products, and the rank of the zero matrix.

    These are the pieces T2_B7 needs before any rank inequality can even be
    stated: the slice it talks about is a sum of two outer products, so the
    shape and entry lemmas here are what any later bound must consume.  The
    rank bounds themselves are NOT here -- see the closing note for exactly
    what they still need.
*)

theory VWZ_Rank
  imports VWZ_RREF
begin

section \<open>Outer products\<close>

text \<open>@{text "outer u v"} is the matrix with entry @{text "u ! i * v ! j"}.  It
  is written with a plain map so that its shape lemmas are rewriting rather
  than index arithmetic.\<close>

definition outer :: "vec \<Rightarrow> vec \<Rightarrow> mat" where
  "outer u v = map (\<lambda>a. map (\<lambda>b. a * b) v) u"

text \<open>The sum of two outer products, again entry-wise.  It is not spelled as a
  matrix addition because no such operation is needed anywhere else in the
  development; what T2_B7 needs is the entry formula, and this definition makes
  it a rewrite.\<close>

definition outer_sum2 :: "vec \<Rightarrow> vec \<Rightarrow> vec \<Rightarrow> vec \<Rightarrow> mat" where
  "outer_sum2 u v u' v' =
     map (\<lambda>i. map (\<lambda>j. u ! i * v ! j + u' ! i * v' ! j) [0..<length v]) [0..<length u]"

lemma n_rows_outer [simp]: "n_rows (outer u v) = length u"
  by (simp add: n_rows_def outer_def)

lemma n_cols_outer [simp]: "u \<noteq> [] \<Longrightarrow> n_cols (outer u v) = length v"
  by (simp add: n_cols_def outer_def)

lemma is_rect_outer [simp]: "is_rect (outer u v)"
  by (simp add: is_rect_def n_cols_def outer_def)

lemma entry_outer:
  "i < length u \<Longrightarrow> j < length v \<Longrightarrow> entry (outer u v) i j = u ! i * v ! j"
  by (simp add: entry_def outer_def)

lemma n_rows_outer_sum2 [simp]: "n_rows (outer_sum2 u v u' v') = length u"
  by (simp add: n_rows_def outer_sum2_def)

lemma n_cols_outer_sum2 [simp]:
  "u \<noteq> [] \<Longrightarrow> n_cols (outer_sum2 u v u' v') = length v"
  by (simp add: n_cols_def outer_sum2_def)

lemma is_rect_outer_sum2 [simp]: "is_rect (outer_sum2 u v u' v')"
  by (simp add: is_rect_def n_cols_def outer_sum2_def)

lemma entry_outer_sum2:
  "i < length u \<Longrightarrow> j < length v \<Longrightarrow>
     entry (outer_sum2 u v u' v') i j = u ! i * v ! j + u' ! i * v' ! j"
  by (simp add: entry_def outer_sum2_def)

section \<open>The zero matrix\<close>

text \<open>A zero matrix has rank zero.  This is the base case every rank argument
  needs, and it is genuinely a fact about @{text rref}: the reduction scans the
  columns, never finds a pivot, and returns the matrix it was given.\<close>

lemma fq_zero [simp]: "fq 0 = 0"
  by (simp add: fq_def)

lemma n_rows_zero_mat [simp]: "n_rows (zero_mat m n) = m"
  by (simp add: n_rows_def zero_mat_def)

lemma n_cols_zero_mat [simp]: "n_cols (zero_mat m n) = (if m = 0 then 0 else n)"
  by (simp add: n_cols_def zero_mat_def)

lemma entry_zero_mat [simp]:
  "i < m \<Longrightarrow> j < n \<Longrightarrow> entry (zero_mat m n) i j = 0"
  by (simp add: entry_def zero_mat_def)

lemma all_zero_row_replicate [simp]: "all_zero_row (replicate n 0)"
  by (simp add: all_zero_row_def)

lemma find_pivot_zero_mat:
  "c < n \<Longrightarrow> find_pivot_fuel f (zero_mat m n) r c = None"
proof (induct f arbitrary: r c)
  case 0
  then show ?case by simp
next
  case (Suc f)
  have cn: "c < n" using Suc.prems by simp
  show ?case
  proof (cases "r < m")
    case True
    have e0: "fq (entry (zero_mat m n) r c) = 0"
      using True cn by (simp add: entry_zero_mat)
    have piv: "find_pivot_fuel f (zero_mat m n) (r + 1) c = None"
      by (rule Suc.hyps) (rule cn)
    show ?thesis
      using True e0 piv by simp
  next
    case False
    then show ?thesis by simp
  qed
qed

lemma rref_zero_mat: "rref_fuel f r c (zero_mat m n) = zero_mat m n"
proof (induct f arbitrary: r c)
  case 0
  then show ?case by simp
next
  case (Suc f)
  show ?case
  proof cases
    assume rm: "r < m"
    show ?thesis
    proof cases
      assume cn: "c < n"
      have nr: "r < n_rows (zero_mat m n)" using rm by simp
      have nc: "c < n_cols (zero_mat m n)" using rm cn by (simp add: n_cols_zero_mat)
      have np: "find_pivot_fuel m (zero_mat m n) r c = None"
        by (rule find_pivot_zero_mat) (rule cn)
      have ih: "rref_fuel f r (c + 1) (zero_mat m n) = zero_mat m n"
        by (rule Suc.hyps)
      have step: "rref_fuel (Suc f) r c (zero_mat m n)
          = rref_fuel f r (c + 1) (zero_mat m n)"
        using nr nc np by (simp add: rref_fuel.simps split: option.split)
      also have "\<dots> = zero_mat m n" using ih .
      finally show ?thesis .
    next
      assume nc2: "\<not> c < n"
      show ?thesis using rm nc2 by (simp add: n_cols_zero_mat)
    qed
  next
    assume nrm: "\<not> r < m"
    show ?thesis using nrm by simp
  qed
qed

lemma rref_zero_mat_all [simp]: "rref (zero_mat m n) = zero_mat m n"
  using rref_zero_mat by (simp add: rref_def)

lemma mat_rank_zero_mat [simp]: "mat_rank (zero_mat m n) = 0"
proof -
  have r: "rref (zero_mat m n) = zero_mat m n" by simp
  have "mat_rank (zero_mat m n) = length (filter (\<lambda>r. \<not> all_zero_row r) (zero_mat m n))"
    using r by (simp add: mat_rank_def)
  also have "\<dots> = 0"
    by (simp add: zero_mat_def all_zero_row_def filter_replicate)
  finally show ?thesis .
qed

section \<open>What is still missing for T2_B7\<close>

text \<open>Nothing in this file bounds the rank of a sum of two outer products, and
  that is deliberate rather than an oversight.  The two lemmas the obligation
  needs are out of reach of the definitions in @{file VWZ_RREF.thy} alone,
  because @{text mat_rank} is defined as a count of nonzero rows of @{text rref}
  and no bridge from @{text rref} back to matrix invariants exists yet.  Precisely
  what is missing:

  \<^enum> @{text rref_step}: each of @{text swap_rows}, @{text scale_row} and
  @{text add_row_mult} is multiplication on the left by an invertible matrix.
  Needed to say anything about @{text A} after reducing it, including that
  reduction preserves the row space.
  \<^enum> @{text minors_invariant_under_row_ops}: if every @{text "2 x 2"} minor of
  a matrix vanishes, the same holds after a row swap, after scaling a row by a
  unit, and after adding a multiple of one row to another.  The top-left case
  is multilinearity of @{text det2}, which the obligation file already has;
  arbitrary index pairs need the general statement.
  \<^enum> @{text rank_le_one_imp_minors_vanish}: if @{text rref} has at most one
  nonzero row, every @{text "2 x 2"} minor of the reduced form vanishes.  This
  one is cheap once the reduced shape is characterised.
  \<^enum> combining the three gives @{text rank_ge_two_of_nonzero_minor}, while
  @{text rank_outer_sum_le_two} additionally needs the bound
  @{text "mat_rank (mat_mult A B) \<le> n_cols A"} -- that the rank is at most the
  number of pivot columns, which is again the reduced-shape characterisation.

  Writing these headers down without proofs would put four @{text sorry}s
  outside the obligation ledger, so they are recorded as a work list instead:
  the ledger stays exact at 56 lemmas and 7 sorry.\<close>

end
