(*  Title:      VWZ_MatAlgebra.thy
    SPDX-License-Identifier: Apache-2.0

    Matrix algebra over the definition layer of VWZ_Matrix: the identity laws,
    associativity of mat_mult, and the row-operation bridge used by T2_B3.

    These are tooling lemmas, not obligations.  They are stated with explicit
    shape premises rather than hidden assumptions: HOL's nth is total, so a
    list-index fact that is false out of range must be guarded, not ignored.

    Why this file exists at all: `invertible` is defined by a two-sided witness
    for `mat_mult`, so no argument about determinants can replace the algebra.
    T2_B3 needs "a row addition preserves invertibility", and that needs
    `(E * A) * (B * E\<inverse>) = E * (A * B) * E\<inverse>` -- i.e. associativity,
    i.e. an exchange of summation order.  That exchange is proved here.
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

text \<open>Exchange of summation order.  Induction is on the outer list only, so the
  inner index list stays fixed and no @{text arbitrary} clause is needed.

  Note for Isabelle2025-2: the induction hypothesis of a @{text list} case is
  available as @{text Cons.hyps}, not @{text Cons.IH}.  Using the latter gives
  "Undefined fact: Cons.IH" -- which is what blocked this lemma before.\<close>

lemma swap_idx:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> int"
  shows "sum_list (map (\<lambda>i. sum_list (map (\<lambda>j. f i j) ys)) xs)
       = sum_list (map (\<lambda>j. sum_list (map (\<lambda>i. f i j) xs)) ys)"
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons a as)
  have "sum_list (map (\<lambda>i. sum_list (map (\<lambda>j. f i j) ys)) (a # as))
        = sum_list (map (\<lambda>j. f a j) ys)
          + sum_list (map (\<lambda>i. sum_list (map (\<lambda>j. f i j) ys)) as)"
    by simp
  also have "... = sum_list (map (\<lambda>j. f a j) ys)
          + sum_list (map (\<lambda>j. sum_list (map (\<lambda>i. f i j) as)) ys)"
    using Cons.hyps by simp
  also have "... = sum_list (map (\<lambda>j. f a j + sum_list (map (\<lambda>i. f i j) as)) ys)"
    by (simp add: sum_list_map_add[symmetric])
  also have "... = sum_list (map (\<lambda>j. sum_list (map (\<lambda>i. f i j) (a # as))) ys)"
    by simp
  finally show ?case .
qed

section \<open>Index form of @{text dot} and of a product entry\<close>

text \<open>The library gives @{text map2_map_map} for two lists that are both images of
  the same index list; @{text map_nth} turns a list into that shape.  Combining
  them converts @{text map2} into a sum over an explicit index range.\<close>

lemma map2_conv_idx:
  assumes "length us = n" "length vs = n"
  shows "map2 f us vs = map (\<lambda>k. f (us ! k) (vs ! k)) [0..<n]"
proof -
  have u: "map ((!) us) [0..<n] = us" using assms(1)[symmetric] map_nth[of us] by simp
  have v: "map ((!) vs) [0..<n] = vs" using assms(2)[symmetric] map_nth[of vs] by simp
  have "map2 f us vs =
        map2 f (map ((!) us) [0..<n]) (map ((!) vs) [0..<n])"
    using u v by simp
  also have "... = map (\<lambda>k. f (us ! k) (vs ! k)) [0..<n]"
    by (rule map2_map_map)
  finally show ?thesis .
qed

lemma entry_mult:
  assumes "i < n_rows A" "j < n_cols B" "n_cols A = n_rows B" "is_rect A"
  shows "entry (mat_mult A B) i j
       = sum_list (map (\<lambda>k. entry A i k * entry B k j) [0..<n_cols A])"
proof -
  have hrow: "length (A ! i) = n_cols A"
    using assms unfolding is_rect_def n_rows_def by simp
  have hB: "length B = n_rows B" by (simp add: n_rows_def)
  have hlen: "length (map (\<lambda>r. r ! j) B) = n_cols A"
    using hB assms by simp
  have "entry (mat_mult A B) i j = dot (row_vec A i) (col_vec B j)"
    using assms by (simp add: entry_def mat_mult_def row_vec_def col_vec_def nth_map)
  also have "... = sum_list (map2 (*) (A ! i) (map (\<lambda>r. r ! j) B))"
    by (simp add: dot_def col_vec_def row_vec_def)
  also have "... = sum_list (map (\<lambda>k. (A ! i) ! k * (map (\<lambda>r. r ! j) B) ! k)
                                  [0..<n_cols A])"
    using map2_conv_idx[of "A ! i" "n_cols A" "map (\<lambda>r. r ! j) B" "(*)"] hrow hlen
    by simp
  also have "... = sum_list (map (\<lambda>k. (A ! i) ! k * (B ! k) ! j) [0..<n_cols A])"
  proof -
    have cong: "map (\<lambda>k. (A ! i) ! k * (map (\<lambda>r. r ! j) B) ! k) [0..<n_cols A]
              = map (\<lambda>k. (A ! i) ! k * (B ! k) ! j) [0..<n_cols A]"
    proof (intro map_cong refl)
      fix k
      assume "k \<in> set [0..<n_cols A]"
      then have "k < n_cols A" by simp
      with hB assms have "k < length B" by simp
      then have h1: "(map (\<lambda>r. r ! j) B) ! k = (B ! k) ! j"
        by (metis nth_map)
      from h1 show "(A ! i) ! k * (map (\<lambda>r. r ! j) B) ! k
               = (A ! i) ! k * (B ! k) ! j" by simp
    qed
    from cong show ?thesis by (simp only: cong)
  qed
  also have "... = sum_list (map (\<lambda>k. entry A i k * entry B k j) [0..<n_cols A])"
    by (simp add: entry_def)
  finally show ?thesis .
qed

section \<open>Shape of a product\<close>

lemma n_rows_mat_mult: "n_rows (mat_mult A B) = n_rows A"
  by (simp add: mat_mult_def n_rows_def)

lemma n_cols_mat_mult:
  assumes "n_rows A > 0"
  shows "n_cols (mat_mult A B) = n_cols B"
proof -
  have ne: "mat_mult A B \<noteq> []" using assms by (simp add: mat_mult_def)
  have "mat_mult A B ! 0 = map (\<lambda>j. dot (row_vec A 0) (col_vec B j)) [0..<n_cols B]"
    using assms by (simp add: mat_mult_def)
  then show ?thesis using ne by (simp add: n_cols_def)
qed

lemma is_rect_mat_mult:
  assumes "n_rows A > 0"
  shows "is_rect (mat_mult A B)"
proof -
  have h: "n_cols (mat_mult A B) = n_cols B"
    by (rule n_cols_mat_mult[OF assms])
  show ?thesis using assms h by (simp add: is_rect_def mat_mult_def)
qed

lemma row_mult_len:
  assumes "i < n_rows A"
  shows "length (mat_mult A B ! i) = n_cols B"
proof -
  have "mat_mult A B ! i = map (\<lambda>j. dot (row_vec A i) (col_vec B j)) [0..<n_cols B]"
    using assms by (simp add: mat_mult_def)
  then show ?thesis by simp
qed

section \<open>Associativity\<close>

text \<open>Square case only: that is the shape T2_B3 needs, and it keeps the side
  conditions finite.  The proof is entrywise; the only non-trivial step is
  @{text swap_idx}.\<close>

lemma entry_assoc:
  assumes rA: "is_rect A" and rB: "is_rect B" and rC: "is_rect C"
    and nA: "n_rows A = m" and cA: "n_cols A = m"
    and nB: "n_rows B = m" and cB: "n_cols B = m"
    and nC: "n_rows C = m" and cC: "n_cols C = m"
    and m0: "0 < m" and i: "i < m" and j: "j < m"
  shows "entry (mat_mult (mat_mult A B) C) i j
       = entry (mat_mult A (mat_mult B C)) i j"
proof -
  have ABr: "n_rows (mat_mult A B) = m"
    using nA by (simp add: mat_mult_def n_rows_def)
  have ABc: "n_cols (mat_mult A B) = m"
    using m0 nA cB by (simp add: n_cols_mat_mult)
  have ABrect: "is_rect (mat_mult A B)"
    using m0 nA by (simp add: is_rect_mat_mult)
  have BCr: "n_rows (mat_mult B C) = m"
    using nB by (simp add: mat_mult_def n_rows_def)
  have BCc: "n_cols (mat_mult B C) = m"
    using m0 nB cC by (simp add: n_cols_mat_mult)
  have BCrect: "is_rect (mat_mult B C)"
    using m0 nB by (simp add: is_rect_mat_mult)

  have innerAB: "\<And>k. k < m \<Longrightarrow> entry (mat_mult A B) i k
      = sum_list (map (\<lambda>l. entry A i l * entry B l k) [0..<m])"
  proof -
    fix k
    assume km: "k < m"
    show "entry (mat_mult A B) i k
        = sum_list (map (\<lambda>l. entry A i l * entry B l k) [0..<m])"
      using entry_mult[of i A k B] rA nA cA cB nB km i by simp
  qed

  have innerBC: "\<And>l. l < m \<Longrightarrow> entry (mat_mult B C) l j
      = sum_list (map (\<lambda>k. entry B l k * entry C k j) [0..<m])"
  proof -
    fix l
    assume lm: "l < m"
    show "entry (mat_mult B C) l j
        = sum_list (map (\<lambda>k. entry B l k * entry C k j) [0..<m])"
      using entry_mult[of l B j C] rB nB cB cC nC lm j by simp
  qed

  have L0: "entry (mat_mult (mat_mult A B) C) i j
      = sum_list (map (\<lambda>k. entry (mat_mult A B) i k * entry C k j) [0..<m])"
    using entry_mult[of i "mat_mult A B" j C] ABr ABc ABrect nC cC i j by simp

  have Lsub: "map (\<lambda>k. entry (mat_mult A B) i k * entry C k j) [0..<m]
      = map (\<lambda>k. sum_list (map (\<lambda>l. entry A i l * entry B l k) [0..<m])
              * entry C k j) [0..<m]"
  proof (intro map_cong refl)
    fix k
    assume "k \<in> set [0..<m]"
    then have km: "k < m" by simp
    show "entry (mat_mult A B) i k * entry C k j
        = sum_list (map (\<lambda>l. entry A i l * entry B l k) [0..<m]) * entry C k j"
      using innerAB[OF km] by simp
  qed

  have L: "entry (mat_mult (mat_mult A B) C) i j
      = sum_list (map (\<lambda>k. sum_list (map (\<lambda>l. entry A i l * entry B l k) [0..<m])
                            * entry C k j) [0..<m])"
    using L0 Lsub by (simp only: Lsub)

  have L2: "sum_list (map (\<lambda>k. sum_list (map (\<lambda>l. entry A i l * entry B l k) [0..<m])
                            * entry C k j) [0..<m])
      = sum_list (map (\<lambda>k. sum_list (map (\<lambda>l. (entry A i l * entry B l k) * entry C k j)
                            [0..<m])) [0..<m])"
    by (simp add: sum_list_map_mult_right[symmetric])

  have L3: "sum_list (map (\<lambda>k. sum_list (map (\<lambda>l. (entry A i l * entry B l k) * entry C k j)
                            [0..<m])) [0..<m])
      = sum_list (map (\<lambda>l. sum_list (map (\<lambda>k. (entry A i l * entry B l k) * entry C k j)
                            [0..<m])) [0..<m])"
    by (rule swap_idx)

  have L4: "sum_list (map (\<lambda>l. sum_list (map (\<lambda>k. (entry A i l * entry B l k) * entry C k j)
                            [0..<m])) [0..<m])
      = sum_list (map (\<lambda>l. entry A i l * sum_list (map (\<lambda>k. entry B l k * entry C k j)
                            [0..<m])) [0..<m])"
    by (simp add: mult.assoc sum_list_map_mult_left[symmetric])

  have R0: "entry (mat_mult A (mat_mult B C)) i j
      = sum_list (map (\<lambda>l. entry A i l * entry (mat_mult B C) l j) [0..<m])"
    using entry_mult[of i A j "mat_mult B C"] rA nA cA BCr BCc i j by simp

  have Rsub: "map (\<lambda>l. entry A i l * entry (mat_mult B C) l j) [0..<m]
      = map (\<lambda>l. entry A i l * sum_list (map (\<lambda>k. entry B l k * entry C k j) [0..<m]))
            [0..<m]"
  proof (intro map_cong refl)
    fix l
    assume "l \<in> set [0..<m]"
    then have lm: "l < m" by simp
    show "entry A i l * entry (mat_mult B C) l j
        = entry A i l * sum_list (map (\<lambda>k. entry B l k * entry C k j) [0..<m])"
      using innerBC[OF lm] by simp
  qed

  have R: "entry (mat_mult A (mat_mult B C)) i j
      = sum_list (map (\<lambda>l. entry A i l * sum_list (map (\<lambda>k. entry B l k * entry C k j)
                            [0..<m])) [0..<m])"
    using R0 Rsub by (simp only: Rsub)

  from L L2 L3 L4 R show ?thesis by simp
qed

lemma mat_mult_assoc_square:
  assumes rA: "is_rect A" and rB: "is_rect B" and rC: "is_rect C"
    and nA: "n_rows A = m" and cA: "n_cols A = m"
    and nB: "n_rows B = m" and cB: "n_cols B = m"
    and nC: "n_rows C = m" and cC: "n_cols C = m"
    and m0: "0 < m"
  shows "mat_mult (mat_mult A B) C = mat_mult A (mat_mult B C)"
proof (rule nth_equalityI)
  show "length (mat_mult (mat_mult A B) C) = length (mat_mult A (mat_mult B C))"
    using nA nB by (simp add: mat_mult_def n_rows_def)
next
  fix i
  assume i: "i < length (mat_mult (mat_mult A B) C)"
  then have im: "i < m" using nA nB by (simp add: mat_mult_def n_rows_def)
  have BCc: "n_cols (mat_mult B C) = m"
    using m0 nB cC by (simp add: n_cols_mat_mult)
  show "mat_mult (mat_mult A B) C ! i = mat_mult A (mat_mult B C) ! i"
  proof (rule nth_equalityI)
    show "length (mat_mult (mat_mult A B) C ! i) = length (mat_mult A (mat_mult B C) ! i)"
    proof -
      have h1: "length (mat_mult (mat_mult A B) C ! i) = n_cols C"
        using row_mult_len[of i "mat_mult A B"] im nB nA by (simp add: n_rows_mat_mult)
      have h2: "length (mat_mult A (mat_mult B C) ! i) = n_cols (mat_mult B C)"
        using row_mult_len[of i A] im nA by (simp add: n_rows_def)
      from h1 h2 cC BCc show ?thesis by simp
    qed
  next
    fix j
    assume j: "j < length (mat_mult (mat_mult A B) C ! i)"
    then have jm: "j < m"
      using row_mult_len[of i "mat_mult A B"] im nB nA j cC by (simp add: mat_mult_def n_rows_def)
    have "mat_mult (mat_mult A B) C ! i ! j = entry (mat_mult (mat_mult A B) C) i j"
      by (simp add: entry_def)
    also have "... = entry (mat_mult A (mat_mult B C)) i j"
      by (rule entry_assoc[OF rA rB rC nA cA nB cB nC cC m0 im jm])
    also have "... = mat_mult A (mat_mult B C) ! i ! j"
      by (simp add: entry_def)
    finally show "mat_mult (mat_mult A B) C ! i ! j = mat_mult A (mat_mult B C) ! i ! j" .
  qed
qed

end
