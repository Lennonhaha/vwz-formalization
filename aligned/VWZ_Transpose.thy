(*  Title:      VWZ_Transpose.thy
    SPDX-License-Identifier: Apache-2.0

    The bilinear identity behind T2_D6: dotting with a transposed product.

        dot (matvec (transpose A) u) v  =  dot u (matvec A v)

    Left to right, the left side sums over the columns of A and the right side
    over its rows; the identity is a double-sum exchange (VWZ_MatAlgebra's
    swap_idx).  Nothing about the field is used, so this is an integer identity
    and it holds before any reduction.

    Why it matters: the u2 constraint at an index that is only in Za is
    "M2^T . vand(lambda_b[i]) dotted with u2 = 0", which is how the sampler
    writes it, while the obligation names the same number as the evalution
    P2b(lambda_b[i]) = dot (vand (lambda_b[i])) (M2 . u2).  These two are the
    two sides of this lemma.

    Everything is stated with explicit lengths, because the underlying `dot`
    truncates: it is sum_list over map2, so it silently ignores the tail of the
    longer argument.  The hypotheses below are the ones that make both sides
    well formed; without them the identity can fail on ragged input.
*)

theory VWZ_Transpose
  imports VWZ_ModAlgebra
begin

section \<open>Index form of @{text dot}, and the rows of a transpose\<close>

lemma dot_conv_idx:
  assumes "length u = n" "length v = n"
  shows "dot u v = sum_list (map (\<lambda>k. u ! k * v ! k) [0..<n])"
  unfolding dot_def using assms by (simp add: map2_conv_idx)

lemma sum_upt_cong:
  assumes "\<And>k. k < n \<Longrightarrow> f k = g k"
  shows "sum_list (map f [0..<n]) = sum_list (map g [0..<n])"
proof (rule arg_cong[where f=sum_list])
  show "map f [0..<n] = map g [0..<n]"
  proof (rule map_cong[OF refl])
    fix k
    assume "k \<in> set [0..<n]"
    then have "k < n" by simp
    with assms show "f k = g k" .
  qed
qed

lemma n_rows_transpose [simp]: "n_rows (transpose A) = n_cols A"
  by (simp add: n_rows_def transpose_def)

lemma transpose_nth:
  "j < n_cols A \<Longrightarrow> transpose A ! j = col_vec A j"
  unfolding transpose_def col_vec_def
  by (simp add: nth_map)

lemma matvec_nth:
  "i < n_rows A \<Longrightarrow> matvec A v ! i = dot (A ! i) v"
  by (simp add: matvec_def n_rows_def)

lemma matvec_transpose_nth:
  "j < n_cols A \<Longrightarrow> matvec (transpose A) u ! j = dot (col_vec A j) u"
  using transpose_nth[of j A] matvec_nth[of j "transpose A" u] by simp

lemma col_vec_nth:
  "i < length A \<Longrightarrow> col_vec A j ! i = A ! i ! j"
  by (simp add: col_vec_def nth_map)

section \<open>The exchange of the two sums\<close>

text \<open>The two sides, written out.  Both are sums of an inner sum times an
  entry; @{text swap_idx} exchanges them once the outer factor is pushed inside
  with @{text sum_list_map_mult_right} (left) and @{text
  sum_list_map_mult_left} (right).\<close>

lemma dot_matvec_transpose:
  assumes r: "is_rect A"
      and lu: "length u = n_rows A"
      and lv: "length v = n_cols A"
  shows "dot (matvec (transpose A) u) v = dot u (matvec A v)"
proof -
  let ?m = "n_rows A"
  let ?n = "n_cols A"
  have lenA: "length A = ?m" by (simp add: n_rows_def)
  have lenmv: "length (matvec (transpose A) u) = ?n"
    by (simp add: matvec_def transpose_def n_rows_def)
  have lenmv2: "length (matvec A v) = ?m"
    by (simp add: matvec_def n_rows_def)
  have lenrow: "\<And>i. i < ?m \<Longrightarrow> length (A ! i) = ?n"
  proof -
    fix i
    assume i: "i < ?m"
    have il: "i < length A" using i lenA by simp
    have "A ! i \<in> set A" using il by (rule nth_mem)
    with r show "length (A ! i) = ?n" by (simp add: is_rect_def)
  qed
  \<comment> \<open>left side, in column-major form\<close>
  have lhs1: "dot (matvec (transpose A) u) v
      = sum_list (map (\<lambda>j. matvec (transpose A) u ! j * v ! j) [0..<?n])"
    by (rule dot_conv_idx) (simp_all add: lenmv lv)
  have inner: "\<And>j. j < ?n \<Longrightarrow>
      matvec (transpose A) u ! j = sum_list (map (\<lambda>i. A ! i ! j * u ! i) [0..<?m])"
  proof -
    fix j
    assume j: "j < ?n"
    have "matvec (transpose A) u ! j = dot (col_vec A j) u"
      using j by (rule matvec_transpose_nth)
    also have "\<dots> = sum_list (map (\<lambda>k. col_vec A j ! k * u ! k) [0..<?m])"
      by (rule dot_conv_idx) (simp_all add: lu lenA col_vec_def)
    also have "\<dots> = sum_list (map (\<lambda>i. A ! i ! j * u ! i) [0..<?m])"
      by (rule sum_upt_cong) (simp add: col_vec_nth lenA)
    finally show "matvec (transpose A) u ! j
        = sum_list (map (\<lambda>i. A ! i ! j * u ! i) [0..<?m])" .
  qed
  have lhs2: "sum_list (map (\<lambda>j. matvec (transpose A) u ! j * v ! j) [0..<?n])
      = sum_list (map (\<lambda>j. (sum_list (map (\<lambda>i. A ! i ! j * u ! i) [0..<?m])) * v ! j) [0..<?n])"
    by (rule sum_upt_cong) (simp add: inner)
  \<comment> \<open>right side, in row-major form\<close>
  have rhs1: "dot u (matvec A v)
      = sum_list (map (\<lambda>i. u ! i * matvec A v ! i) [0..<?m])"
    by (rule dot_conv_idx) (simp_all add: lu lenmv2 lenA)
  have inner2: "\<And>i. i < ?m \<Longrightarrow>
      matvec A v ! i = sum_list (map (\<lambda>j. A ! i ! j * v ! j) [0..<?n])"
  proof -
    fix i
    assume i: "i < ?m"
    have "matvec A v ! i = dot (A ! i) v"
      using i by (simp add: matvec_nth n_rows_def)
    also have "\<dots> = sum_list (map (\<lambda>k. A ! i ! k * v ! k) [0..<?n])"
      by (rule dot_conv_idx) (simp_all add: lv lenrow[OF i])
    finally show "matvec A v ! i = sum_list (map (\<lambda>j. A ! i ! j * v ! j) [0..<?n])" .
  qed
  have rhs2: "sum_list (map (\<lambda>i. u ! i * matvec A v ! i) [0..<?m])
      = sum_list (map (\<lambda>i. u ! i * (sum_list (map (\<lambda>j. A ! i ! j * v ! j) [0..<?n]))) [0..<?m])"
    by (rule sum_upt_cong) (simp add: inner2)
  \<comment> \<open>push each outer factor inside its own inner sum\<close>
  have push_right: "\<And>j. j < ?n \<Longrightarrow>
      (sum_list (map (\<lambda>i. A ! i ! j * u ! i) [0..<?m])) * v ! j
      = sum_list (map (\<lambda>i. (A ! i ! j * u ! i) * v ! j) [0..<?m])"
    by (rule sum_list_map_mult_right[symmetric])
  have push_left: "\<And>i. i < ?m \<Longrightarrow>
      u ! i * (sum_list (map (\<lambda>j. A ! i ! j * v ! j) [0..<?n]))
      = sum_list (map (\<lambda>j. u ! i * (A ! i ! j * v ! j)) [0..<?n])"
    by (rule sum_list_map_mult_left[symmetric])
  have lhs3: "sum_list (map (\<lambda>j. (sum_list (map (\<lambda>i. A ! i ! j * u ! i) [0..<?m])) * v ! j) [0..<?n])
      = sum_list (map (\<lambda>j. sum_list (map (\<lambda>i. (A ! i ! j * u ! i) * v ! j) [0..<?m])) [0..<?n])"
    by (rule sum_upt_cong) (simp add: push_right)
  have rhs3: "sum_list (map (\<lambda>i. u ! i * (sum_list (map (\<lambda>j. A ! i ! j * v ! j) [0..<?n]))) [0..<?m])
      = sum_list (map (\<lambda>i. sum_list (map (\<lambda>j. u ! i * (A ! i ! j * v ! j)) [0..<?n])) [0..<?m])"
    by (rule sum_upt_cong) (simp add: push_left)
  \<comment> \<open>the two inner terms agree, and then the sums exchange\<close>
  have same_term: "\<And>i j. i < ?m \<Longrightarrow> j < ?n \<Longrightarrow>
      (A ! i ! j * u ! i) * v ! j = u ! i * (A ! i ! j * v ! j)"
    by (simp add: int_distrib mult.assoc mult.left_commute)
  have mid: "sum_list (map (\<lambda>j. sum_list (map (\<lambda>i. (A ! i ! j * u ! i) * v ! j) [0..<?m])) [0..<?n])
      = sum_list (map (\<lambda>i. sum_list (map (\<lambda>j. u ! i * (A ! i ! j * v ! j)) [0..<?n])) [0..<?m])"
  proof -
    have a: "sum_list (map (\<lambda>j. sum_list (map (\<lambda>i. (A ! i ! j * u ! i) * v ! j) [0..<?m])) [0..<?n])
        = sum_list (map (\<lambda>j. sum_list (map (\<lambda>i. u ! i * (A ! i ! j * v ! j)) [0..<?m])) [0..<?n])"
    proof (rule sum_upt_cong)
      fix j
      assume j: "j < ?n"
      show "sum_list (map (\<lambda>i. (A ! i ! j * u ! i) * v ! j) [0..<?m])
          = sum_list (map (\<lambda>i. u ! i * (A ! i ! j * v ! j)) [0..<?m])"
        by (rule sum_upt_cong) (simp add: same_term j)
    qed
    have b: "sum_list (map (\<lambda>j. sum_list (map (\<lambda>i. u ! i * (A ! i ! j * v ! j)) [0..<?m])) [0..<?n])
        = sum_list (map (\<lambda>i. sum_list (map (\<lambda>j. u ! i * (A ! i ! j * v ! j)) [0..<?n])) [0..<?m])"
      by (rule swap_idx)
    from a b show ?thesis by simp
  qed
  from lhs1 lhs2 lhs3 mid rhs3 rhs2 rhs1 show ?thesis by simp
qed

end
