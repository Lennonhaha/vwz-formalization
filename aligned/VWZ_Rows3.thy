(*  Title:      VWZ_Rows3.thy
    SPDX-License-Identifier: Apache-2.0

    Spec 6.4.1 -- the three-row system built by the trapdoor sampler.

    This file gives `rows3_of` a body.  The rows are exactly the ones the spec
    lists: one Vandermonde row in the secret lambda_c for every index of Za, and
    one row M3^T . vand(lambda_c[i]) for every index of Zb.  Nothing is invented
    here: `vand`, `matvec`, `transpose` and `mat` already exist, and the only
    choice made is to take the index sets as `nat set`, ordered by
    `sorted_list_of_set`, so that the result is a list and stays executable.

    The second half proves the dimension count of T2_D4.  It is stated against
    `nullity` (columns minus rank), not `dim_nullspace` (rows minus rank).
    That is not a convenience: for a (k+2) x (2k+1) system the row-count reading
    gives (k+2) - rank, which is at most k+2 and does not bound k-1 from below;
    the count that the security argument needs is (2k+1) - rank >= k-1, which is
    the column nullity.  The proof needs only that the rank never exceeds the
    number of rows, which follows from the reduction preserving the row count.
*)

theory VWZ_Rows3
  imports VWZ_Protocol VWZ_KeyGen VWZ_ModAlgebra
begin

section \<open>Spec 6.4.1 -- rows3\<close>

definition rows3_of :: "int list \<Rightarrow> mat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> mat" where
  "rows3_of lc M3 Za Zb =
     map (\<lambda>i. vand (lc ! i) (n_rows M3)) (sorted_list_of_set Za) @
     map (\<lambda>i. matvec (transpose M3) (vand (lc ! i) (n_cols M3)))
         (sorted_list_of_set Zb)"

text \<open>The row count is the size of the two index sets, with no overlap
  correction: the spec lets one index sit in both sets, and that index then
  contributes two rows.  This is the "+1" in @{text "|Za| + |Zb| = |Z| + 1"}.\<close>

lemma rows3_len: "length (rows3_of lc M3 Za Zb) = card Za + card Zb"
  by (simp add: rows3_of_def)

lemma n_cols_of_rows:
  assumes all: "\<forall>r \<in> set X. length r = m" and ne: "X \<noteq> []"
  shows "n_cols X = m"
proof -
  have "X ! 0 \<in> set X" using ne by simp
  hence "length (X ! 0) = m" using all by simp
  with ne show ?thesis by (simp add: n_cols_def)
qed

lemma rows3_n_cols:
  assumes h1: "n_rows M3 = m" and h2: "n_cols M3 = m"
      and hc: "0 < card Za + card Zb"
  shows "n_cols (rows3_of lc M3 Za Zb) = m"
proof (rule n_cols_of_rows)
  show "\<forall>r \<in> set (rows3_of lc M3 Za Zb). length r = m"
  proof
    fix r
    assume "r \<in> set (rows3_of lc M3 Za Zb)"
    hence "r \<in> set (map (\<lambda>i. vand (lc ! i) (n_rows M3)) (sorted_list_of_set Za)) \<or>
           r \<in> set (map (\<lambda>i. matvec (transpose M3) (vand (lc ! i) (n_cols M3)))
                          (sorted_list_of_set Zb))"
      by (simp add: rows3_of_def)
    thus "length r = m"
    proof
      assume "r \<in> set (map (\<lambda>i. vand (lc ! i) (n_rows M3)) (sorted_list_of_set Za))"
      then obtain i where "r = vand (lc ! i) (n_rows M3)" by auto
      thus ?thesis using h1 by (simp add: vand_def)
    next
      assume "r \<in> set (map (\<lambda>i. matvec (transpose M3) (vand (lc ! i) (n_cols M3)))
                        (sorted_list_of_set Zb))"
      then obtain i where "r = matvec (transpose M3) (vand (lc ! i) (n_cols M3))" by auto
      thus ?thesis using h2 by (simp add: matvec_def transpose_def)
    qed
  qed
  have len: "length (rows3_of lc M3 Za Zb) = card Za + card Zb"
    by (rule rows3_len)
  show "rows3_of lc M3 Za Zb \<noteq> []"
  proof
    assume "rows3_of lc M3 Za Zb = []"
    hence "length (rows3_of lc M3 Za Zb) = 0" by simp
    with len hc show False by simp
  qed
qed

section \<open>The rank of a matrix never exceeds its row count\<close>

lemma len_swap_rows [simp]: "length (swap_rows A i j) = length A"
  by (simp add: swap_rows_def)

lemma len_scale_row [simp]: "length (scale_row A i k) = length A"
  by (simp add: scale_row_def)

lemma len_add_row_mult [simp]: "length (add_row_mult A i j k) = length A"
  by (simp add: add_row_mult_def)

lemma foldl_len:
  assumes "\<And>B k. length (f B k) = length B"
  shows "length (foldl f A xs) = length A"
  using assms by (induct xs arbitrary: A) simp_all

lemma len_eliminate_col [simp]: "length (eliminate_col A r c) = length A"
  by (simp add: eliminate_col_def foldl_len)

lemma len_rref_fuel [simp]: "length (rref_fuel f r c A) = length A"
proof (induct f arbitrary: r c A)
  case 0
  then show ?case by simp
next
  case (Suc f)
  show ?case
  proof (cases "r < n_rows A \<and> c < n_cols A")
    case False
    then show ?thesis by (simp add: rref_fuel.simps False)
  next
    case True
    show ?thesis
    proof (cases "find_pivot_fuel (n_rows A) A r c")
      case None
      then show ?thesis using True by (simp add: rref_fuel.simps None Suc.hyps)
    next
      case (Some i)
      then show ?thesis using True by (simp add: rref_fuel.simps Some Let_def Suc.hyps)
    qed
  qed
qed

lemma len_rref [simp]: "length (rref A) = length A"
  unfolding rref_def by (rule len_rref_fuel)

lemma mat_rank_le_n_rows: "mat_rank A \<le> n_rows A"
proof -
  have h1: "length (filter (\<lambda>r. \<not> all_zero_row r) (rref A)) \<le> length (rref A)"
    by (rule length_filter_le)
  have h2: "length (rref A) = length A" by (rule len_rref)
  show ?thesis using h1 h2 by (simp add: mat_rank_def n_rows_def)
qed

section \<open>T2 :: D4 -- the dimension count, on the column nullity\<close>

text \<open>With @{text "m = 2k+1"} columns and @{text "k+2"} rows, the rank is at
  most @{text "k+2"}, so the nullity is at least @{text "2k+1 - (k+2) = k-1"}.
  The two side conditions are the spec's own: the two index sets cover the
  @{text "k+1"} zero positions with exactly one index counted twice, and the
  mixing matrix is square of order @{text "2k+1"}.\<close>

lemma rows3_dimension_count:
  assumes k2: "2 \<le> k"
      and hc: "card Za + card Zb = k + 2"
      and r1: "n_rows M3 = 2 * k + 1"
      and r2: "n_cols M3 = 2 * k + 1"
  shows "k - 1 \<le> nullity (rows3_of lc M3 Za Zb)"
proof -
  have nc: "n_cols (rows3_of lc M3 Za Zb) = 2 * k + 1"
  proof (rule rows3_n_cols)
    show "n_rows M3 = 2 * k + 1" by (rule r1)
    show "n_cols M3 = 2 * k + 1" by (rule r2)
    show "0 < card Za + card Zb" using hc by simp
  qed
  have nr: "n_rows (rows3_of lc M3 Za Zb) = k + 2"
    using hc by (simp add: n_rows_def rows3_len)
  have rk: "mat_rank (rows3_of lc M3 Za Zb) \<le> k + 2"
    using mat_rank_le_n_rows[of "rows3_of lc M3 Za Zb"] nr by simp
  have h: "k - 1 + mat_rank (rows3_of lc M3 Za Zb) \<le> 2 * k + 1"
  proof -
    have "k - 1 + mat_rank (rows3_of lc M3 Za Zb) \<le> k - 1 + (k + 2)"
      using rk by simp
    also have "\<dots> = 2 * k + 1" using k2 by presburger
    finally show ?thesis .
  qed
  show ?thesis using h nc by (simp add: nullity_def le_diff_conv)
qed

end
