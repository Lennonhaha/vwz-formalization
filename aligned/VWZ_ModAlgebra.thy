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
  imports VWZ_MatAlgebra VWZ_RREF
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

section \<open>Rows of an elementary matrix, and the two dot products\<close>

text \<open>These are the entry-level facts the bridge lemma needs.  They are stated for
  vectors of length @{text n} and indices below it; no matrix shape is assumed
  here beyond that.\<close>


lemma nth_row_add_matrix:
  assumes "r < m"
  shows "row_add_matrix m i j f ! r
       = map (\<lambda>c. if r = i \<and> c = j then f else (if r = c then 1 else 0)) [0..<m]"
  using assms unfolding row_add_matrix_def by (simp add: nth_map)

lemma row_add_matrix_len [simp]: "length (row_add_matrix m i j f) = m"
  unfolding row_add_matrix_def by simp

lemma row_add_matrix_row_len [simp]:
  assumes "r < m"
  shows "length (row_add_matrix m i j f ! r) = m"
  using nth_row_add_matrix[OF assms] by simp

lemma fq_reduced:
  assumes "0 \<le> (x::int)" and "x < 3329"
  shows "fq x = x"
  unfolding fq_def using assms by (simp add: mod_pos_pos_trivial)

lemma sum_sel_one:
  fixes y :: "int list"
  assumes "i < n"
  shows "sum_list (map (\<lambda>k. (if k = i then (1::int) else 0) * y ! k) [0..<n]) = y ! i"
proof -
  have map_eq: "map (\<lambda>k. (if k = i then (1::int) else 0) * y ! k) [0..<n]
              = map (\<lambda>k. if k = i then y ! i else 0) [0..<n]"
    by (rule map_cong[OF refl]) (auto split: if_splits)
  have step: "sum_list (map (\<lambda>k. if k = i then y ! i else 0) [0..<n]) = y ! i"
    by (simp add: aux_rref_sum_single[OF assms])
  have "sum_list (map (\<lambda>k. (if k = i then (1::int) else 0) * y ! k) [0..<n])
      = sum_list (map (\<lambda>k. if k = i then y ! i else 0) [0..<n])"
    using map_eq by (rule arg_cong[where f = sum_list])
  also have "\<dots> = y ! i" using step .
  finally show ?thesis .
qed

lemma sum_sel_scaled:
  fixes y :: "int list" and f :: int
  assumes "j < n"
  shows "sum_list (map (\<lambda>k. f * ((if k = j then (1::int) else 0) * y ! k)) [0..<n]) = f * y ! j"
proof -
  have "sum_list (map (\<lambda>k. f * ((if k = j then (1::int) else 0) * y ! k)) [0..<n])
      = f * sum_list (map (\<lambda>k. (if k = j then (1::int) else 0) * y ! k) [0..<n])"
    by (simp add: sum_list_map_mult_left)
  also have "\<dots> = f * y ! j" using sum_sel_one[OF assms] by simp
  finally show ?thesis .
qed

lemma map2_unit_row:
  fixes y :: "int list"
  assumes "r < n" and "length y = n"
  shows "map2 (*) (map (\<lambda>c. if c = r then (1::int) else 0) [0..<n]) y
       = map (\<lambda>k. (if k = r then (1::int) else 0) * y ! k) [0..<n]"
proof -
  let ?xs = "map (\<lambda>c. if c = r then (1::int) else 0) [0..<n]"
  have xlen: "length ?xs = n" by simp
  have conv: "map2 (*) ?xs y = map (\<lambda>k. ?xs ! k * y ! k) [0..<n]"
    using map2_conv_idx[OF xlen assms(2), of "(*)"] by simp
  have step: "map (\<lambda>k. ?xs ! k * y ! k) [0..<n]
      = map (\<lambda>k. (if k = r then (1::int) else 0) * y ! k) [0..<n]"
  proof (rule map_cong[OF refl])
    fix k
    assume "k \<in> set [0..<n]"
    hence kn: "k < n" by (simp add: set_upt)
    have "?xs ! k = (if k = r then (1::int) else 0)"
      by (simp add: nth_map kn nth_upt)
    thus "?xs ! k * y ! k = (if k = r then (1::int) else 0) * y ! k" by simp
  qed
  show ?thesis using conv step by (simp only: conv step)
qed

lemma dot_unit_row:
  fixes y :: "int list"
  assumes "r < n" and "length y = n"
  shows "dot (map (\<lambda>c. if c = r then (1::int) else 0) [0..<n]) y = y ! r"
proof -
  have m2: "map2 (*) (map (\<lambda>c. if c = r then (1::int) else 0) [0..<n]) y
          = map (\<lambda>k. (if k = r then (1::int) else 0) * y ! k) [0..<n]"
    using map2_unit_row[OF assms] .
  have "dot (map (\<lambda>c. if c = r then (1::int) else 0) [0..<n]) y
      = sum_list (map (\<lambda>k. (if k = r then (1::int) else 0) * y ! k) [0..<n])"
    unfolding dot_def using m2 by simp
  also have "\<dots> = y ! r" using sum_sel_one[OF assms(1)] by simp
  finally show ?thesis .
qed

lemma dot_sparse_two:
  fixes y :: "int list" and f :: int
  assumes i: "i < n" and j: "j < n" and ij: "i \<noteq> j" and len: "length y = n"
  shows "dot (map (\<lambda>c. if c = j then f else (if c = i then (1::int) else 0)) [0..<n]) y
       = y ! i + f * y ! j"
proof -
  let ?xs = "map (\<lambda>c. if c = j then f else (if c = i then (1::int) else 0)) [0..<n]"
  have xlen: "length ?xs = n" by simp
  have m2: "map2 (*) ?xs y = map (\<lambda>k. ?xs ! k * y ! k) [0..<n]"
    using map2_conv_idx[OF xlen len, of "(*)"] by simp
  have first: "map (\<lambda>k. ?xs ! k * y ! k) [0..<n]
      = map (\<lambda>k. (if k = i then (1::int) else 0) * y ! k
            + f * ((if k = j then (1::int) else 0) * y ! k)) [0..<n]"
  proof (rule map_cong[OF refl])
    fix k
    assume hyp: "k \<in> set [0..<n]"
    hence kn: "k < n" by (simp add: set_upt)
    have nth: "?xs ! k = (if k = j then f else (if k = i then (1::int) else 0))"
      by (simp add: nth_map kn nth_upt)
    show "?xs ! k * y ! k
        = (if k = i then (1::int) else 0) * y ! k
          + f * ((if k = j then (1::int) else 0) * y ! k)"
    proof (cases "k = j")
      case True
      with ij nth show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "k = i")
        case True
        with ij nth show ?thesis by simp
      next
        case False
        with nth show ?thesis by simp
      qed
    qed
  qed
  have sumsplit: "sum_list (map (\<lambda>k. (if k = i then (1::int) else 0) * y ! k
                          + f * ((if k = j then (1::int) else 0) * y ! k)) [0..<n])
      = y ! i + f * y ! j"
  proof -
    have "sum_list (map (\<lambda>k. (if k = i then (1::int) else 0) * y ! k
                            + f * ((if k = j then (1::int) else 0) * y ! k)) [0..<n])
        = sum_list (map (\<lambda>k. (if k = i then (1::int) else 0) * y ! k) [0..<n])
          + sum_list (map (\<lambda>k. f * ((if k = j then (1::int) else 0) * y ! k)) [0..<n])"
      by (simp add: sum_list_map_add)
    also have "\<dots> = y ! i + f * y ! j"
      using sum_sel_one[OF i] sum_sel_scaled[OF j] by simp
    finally show ?thesis .
  qed
  have "dot ?xs y = sum_list (map (\<lambda>k. ?xs ! k * y ! k) [0..<n])"
    unfolding dot_def using m2 by simp
  also have "\<dots> = sum_list (map (\<lambda>k. (if k = i then (1::int) else 0) * y ! k
                          + f * ((if k = j then (1::int) else 0) * y ! k)) [0..<n])"
    by (simp only: first)
  also have "\<dots> = y ! i + f * y ! j" using sumsplit .
  finally show ?thesis .
qed


lemma is_rect_rows:
  assumes "is_rect A" and "r < n_rows A"
  shows "length (A ! r) = n_cols A"
  using assms by (simp add: is_rect_def n_rows_def)

lemma mat_mult_mod_row_add:
  assumes im: "i < m" and jm: "j < m" and ij: "i \<noteq> j"
      and rows: "n_rows A = m"
      and rect: "is_rect A"
      and red: "\<forall>r \<in> set A. \<forall>x \<in> set r. 0 \<le> x \<and> x < 3329"
  shows "mat_mult_mod (row_add_matrix m i j f) A = add_row_mult A i j f"
proof -
  let ?E = "row_add_matrix m i j f"
  have Erows: "n_rows ?E = m" by (simp add: n_rows_def)
  have nA: "length A = m" using rows by (simp add: n_rows_def)
  have mpos: "m > 0" using im by simp
  have Arow: "\<And>r. r < m \<Longrightarrow> length (A ! r) = n_cols A"
    using rect nA is_rect_rows rows by simp
  have redrow: "\<And>r c. r < m \<Longrightarrow> c < n_cols A \<Longrightarrow> 0 \<le> A ! r ! c \<and> A ! r ! c < 3329"
  proof -
    fix r c assume rm: "r < m" and cm: "c < n_cols A"
    have "A ! r \<in> set A" using nA rm by (simp add: nth_mem)
    have "A ! r ! c \<in> set (A ! r)" using Arow[OF rm] cm by (simp add: nth_mem)
    with red \<open>A ! r \<in> set A\<close> show "0 \<le> A ! r ! c \<and> A ! r ! c < 3329" by auto
  qed
  have lenE: "length ?E = m" by simp
  have lenL: "length (mat_mult_mod ?E A) = m"
  proof -
    have h1: "length (mat_mult ?E A) = n_rows (mat_mult ?E A)"
      by (simp add: n_rows_def)
    also have "\<dots> = n_rows ?E" by (simp add: n_rows_mat_mult)
    also have "\<dots> = m" by (simp add: n_rows_def)
    finally have h2: "length (mat_mult ?E A) = m" .
    show ?thesis using h2 by (simp add: mat_mult_mod_def)
  qed
  have lenR: "length (add_row_mult A i j f) = m"
    by (simp add: add_row_mult_def nA)
  show ?thesis
  proof (rule list_eq_iff_nth_eq[THEN iffD2], rule conjI)
    show "length (mat_mult_mod ?E A) = length (add_row_mult A i j f)"
      using lenL lenR by simp
  next
    show "\<forall>r < length (mat_mult_mod ?E A).
            (mat_mult_mod ?E A) ! r = (add_row_mult A i j f) ! r"
    proof (rule allI, rule impI)
      fix r assume rlen: "r < length (mat_mult_mod ?E A)"
      hence rm: "r < m" using lenL by simp
      have rlen2: "r < length (mat_mult ?E A)" using rlen by (simp add: mat_mult_mod_def)
      have innerL: "length ((mat_mult_mod ?E A) ! r) = n_cols A"
      proof -
        have "length ((mat_mult_mod ?E A) ! r) = length ((mat_mult ?E A) ! r)"
          by (simp add: mat_mult_mod_def nth_map rlen2)
        also have "\<dots> = n_cols A" using row_mult_len[of r ?E A] rm Erows by simp
        finally show ?thesis .
      qed
      have innerR: "length ((add_row_mult A i j f) ! r) = n_cols A"
      proof (cases "r = i")
        case True
        have li: "length (A ! i) = n_cols A" using Arow[OF im] .
        have lj: "length (A ! j) = n_cols A" using Arow[OF jm] .
        show ?thesis using True li lj nA im by (simp add: add_row_mult_def)
      next
        case False
        show ?thesis using False Arow[OF rm] by (simp add: add_row_mult_def)
      qed
      show "(mat_mult_mod ?E A) ! r = (add_row_mult A i j f) ! r"
      proof (rule list_eq_iff_nth_eq[THEN iffD2], rule conjI)
        show "length ((mat_mult_mod ?E A) ! r) = length ((add_row_mult A i j f) ! r)"
          using innerL innerR by simp
      next
        show "\<forall>c < length ((mat_mult_mod ?E A) ! r).
                (mat_mult_mod ?E A) ! r ! c = (add_row_mult A i j f) ! r ! c"
        proof (rule allI, rule impI)
          fix c assume clen: "c < length ((mat_mult_mod ?E A) ! r)"
          hence cm: "c < n_cols A" using innerL by simp
          have lhs: "(mat_mult_mod ?E A) ! r ! c = fq (dot (?E ! r) (col_vec A c))"
          proof -
            have h1: "(mat_mult_mod ?E A) ! r = map fq ((mat_mult ?E A) ! r)"
              by (simp add: mat_mult_mod_def nth_map rlen2)
            have rE: "r < n_rows ?E" using rm Erows by simp
            have lr: "r < length [0..<n_rows ?E]" using rE by simp
            have h2: "(mat_mult ?E A) ! r = map (\<lambda>j. dot (row_vec ?E r) (col_vec A j)) [0..<n_cols A]"
              using nth_map[OF lr, of "\<lambda>ia. map (\<lambda>ja. dot (row_vec ?E ia) (col_vec A ja)) [0..<n_cols A]"]
              by (simp add: mat_mult_def nth_upt rE)
            have h3: "(\<lambda>j. dot (row_vec ?E r) (col_vec A j)) c = dot (?E ! r) (col_vec A c)"
              by (simp add: row_vec_def cm h2)
            show ?thesis using h1 h2 h3 innerL cm by simp
          qed
          show "(mat_mult_mod ?E A) ! r ! c = (add_row_mult A i j f) ! r ! c"
          proof (cases "r = i")
            case True
            have Erow: "?E ! i = map (\<lambda>c. if i = i \<and> c = j then f else (if i = c then 1 else 0)) [0..<m]"
              using nth_row_add_matrix[OF im] .
            have colr: "col_vec A c ! i = A ! i ! c" using nA im by (simp add: col_vec_def nth_map)
            have colj: "col_vec A c ! j = A ! j ! c" using nA jm by (simp add: col_vec_def nth_map)
            have dotv: "dot (?E ! i) (col_vec A c) = A ! i ! c + f * A ! j ! c"
            proof -
              have lenA: "length A = m" using nA .
              have "col_vec A c = map (\<lambda>r. r ! c) A" by (simp add: col_vec_def)
              hence cl: "length (col_vec A c) = m" using nA by simp
              have "?E ! i = map (\<lambda>c. if c = j then f else (if c = i then (1::int) else 0)) [0..<m]"
                using Erow ij by simp
              thus ?thesis using dot_sparse_two[OF im jm ij cl, of f] colr colj by simp
            qed
            have "add_row_mult A i j f ! i = map2 (\<lambda>x y. fq (x + f * y)) (A ! i) (A ! j)"
              by (simp add: add_row_mult_def nth_list_update im nA)
            have rhs: "(add_row_mult A i j f) ! i ! c = fq (A ! i ! c + f * A ! j ! c)"
            proof -
              have li: "length (A ! i) = n_cols A" using Arow[OF im] .
              have lj: "length (A ! j) = n_cols A" using Arow[OF jm] .
              have e: "(add_row_mult A i j f) ! i = map2 (\<lambda>x y. fq (x + f * y)) (A ! i) (A ! j)"
                by (simp add: add_row_mult_def nth_list_update nA im)
              have m2: "map2 (\<lambda>x y. fq (x + f * y)) (A ! i) (A ! j)
                  = map (\<lambda>k. fq ((A ! i) ! k + f * ((A ! j) ! k))) [0..<n_cols A]"
              proof -
                have "map2 (\<lambda>x y. fq (x + f * y)) (A ! i) (A ! j)
                    = map (\<lambda>k. (\<lambda>x y. fq (x + f * y)) ((A ! i) ! k) ((A ! j) ! k)) [0..<n_cols A]"
                  using map2_conv_idx[OF li lj, of "\<lambda>x y. fq (x + f * y)"] by simp
                thus ?thesis by simp
              qed
              show ?thesis using e m2 cm by (simp add: nth_map nth_upt)
            qed
            show ?thesis using True lhs dotv rhs by simp
          next
            case False
            have Erow: "?E ! r = map (\<lambda>cc. if cc = r then (1::int) else 0) [0..<m]"
            proof -
              have "?E ! r = map (\<lambda>cc. if r = i \<and> cc = j then f else (if r = cc then 1 else 0)) [0..<m]"
                using nth_row_add_matrix[OF rm] .
              thus ?thesis using False by simp
            qed
            have cl: "length (col_vec A c) = m" using nA by (simp add: col_vec_def)
            have dotv: "dot (?E ! r) (col_vec A c) = A ! r ! c"
            proof -
              have "col_vec A c ! r = A ! r ! c" using nA rm by (simp add: col_vec_def nth_map)
              thus ?thesis using Erow dot_unit_row[OF rm cl] by simp
            qed
            have redc: "0 \<le> A ! r ! c \<and> A ! r ! c < 3329" using redrow[OF rm cm] .
            have rhs: "(add_row_mult A i j f) ! r ! c = A ! r ! c"
            proof -
              have "(add_row_mult A i j f) ! r = A ! r"
                using False by (auto simp: add_row_mult_def nth_list_update_neq)
              thus ?thesis by simp
            qed
            have "fq (A ! r ! c) = A ! r ! c" using fq_reduced redc by simp
            thus ?thesis using lhs dotv rhs by simp
          qed
        qed
      qed
    qed
  qed
qed


section \<open>The inverse of an elementary matrix, in the integers and modulo q\<close>

lemma id_mat_nth:
  assumes r: "r < m" and c: "c < m"
  shows "(id_mat m) ! r ! c = (if r = c then 1 else 0)"
proof -
  have lr: "r < length [0..<m]" using r by simp
  have lc: "c < length [0..<m]" using c by simp
  have o: "(id_mat m) ! r = map (\<lambda>j. if r = j then (1::int) else 0) [0..<m]"
    using nth_map[OF lr, of "\<lambda>i. map (\<lambda>j. if i = j then (1::int) else 0) [0..<m]"] r
    by (simp add: id_mat_def nth_upt)
  have i: "(map (\<lambda>j. if r = j then (1::int) else 0) [0..<m]) ! c = (if r = c then 1 else 0)"
    using nth_map[OF lc, of "\<lambda>j. if r = j then (1::int) else 0"] c by (simp add: nth_upt)
  show ?thesis using o i by simp
qed

lemma id_mat_fq: "map (map fq) (id_mat m) = id_mat m"
  by (simp add: id_mat_def fq_zero fq_one split: if_split)

lemma entry_mat_mult_dot:
  assumes r: "r < n_rows A" and c: "c < n_cols B"
  shows "entry (mat_mult A B) r c = dot (row_vec A r) (col_vec B c)"
proof -
  have rA: "r < length A" using r by (simp add: n_rows_def)
  have lr: "r < length [0..<n_rows A]" using r by (simp add: n_rows_def)
  have outer: "(mat_mult A B) ! r
      = map (\<lambda>j. dot (row_vec A r) (col_vec B j)) [0..<n_cols B]"
    using nth_map[OF lr, of "\<lambda>ia. map (\<lambda>ja. dot (row_vec A ia) (col_vec B ja)) [0..<n_cols B]"]
    by (simp add: mat_mult_def n_rows_def nth_upt rA)
  have lc: "c < length [0..<n_cols B]" using c by simp
  have "(mat_mult A B) ! r ! c = dot (row_vec A r) (col_vec B c)"
    using outer nth_map[OF lc, of "\<lambda>j. dot (row_vec A r) (col_vec B j)"] c
    by (simp add: nth_upt)
  thus ?thesis by (simp add: entry_def)
qed

lemma row_add_matrix_int_inverse:
  assumes im: "i < m" and jm: "j < m" and ij: "i \<noteq> j"
  shows "mat_mult (row_add_matrix m i j f) (row_add_matrix m i j (-f)) = id_mat m"
proof -
  let ?E = "row_add_matrix m i j f"
  let ?F = "row_add_matrix m i j (-f)"
  have Erows: "length ?E = m" by simp
  have Frows: "length ?F = m" by simp
  have nE: "n_rows ?E = m" by (simp add: n_rows_def)
  have nF: "n_rows ?F = m" by (simp add: n_rows_def)
  have rowlen: "\<And>r. r < m \<Longrightarrow> length (?F ! r) = m" using row_add_matrix_row_len by simp
  have cF: "n_cols ?F = m"
  proof -
    have mne: "m \<noteq> 0" using im by simp
    have "?F \<noteq> []" using Frows mne by (metis list.size(3))
    hence "n_cols ?F = length (?F ! 0)" by (simp add: n_cols_def)
    also have "\<dots> = m" using rowlen[of 0] im by simp
    finally show ?thesis .
  qed
  have colLen: "\<And>c. length (col_vec ?F c) = m" using Frows by (simp add: col_vec_def)
  have lenL: "length (mat_mult ?E ?F) = m"
  proof -
    have "length (mat_mult ?E ?F) = n_rows (mat_mult ?E ?F)" by (simp add: n_rows_def)
    also have "\<dots> = n_rows ?E" by (simp add: n_rows_mat_mult)
    also have "\<dots> = m" using nE .
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule list_eq_iff_nth_eq[THEN iffD2], rule conjI)
    show "length (mat_mult ?E ?F) = length (id_mat m)"
      using lenL by (simp add: id_mat_def)
  next
    show "\<forall>r < length (mat_mult ?E ?F). (mat_mult ?E ?F) ! r = (id_mat m) ! r"
    proof (rule allI, rule impI)
      fix r assume rl: "r < length (mat_mult ?E ?F)"
      hence rm: "r < m" using lenL by simp
      have innerL: "length ((mat_mult ?E ?F) ! r) = m"
        using row_mult_len[of r ?E ?F] rm nE cF by simp
      have innerR: "length ((id_mat m) ! r) = m"
        by (simp add: id_mat_def rm)
      show "(mat_mult ?E ?F) ! r = (id_mat m) ! r"
      proof (rule list_eq_iff_nth_eq[THEN iffD2], rule conjI)
        show "length ((mat_mult ?E ?F) ! r) = length ((id_mat m) ! r)"
          using innerL innerR by simp
      next
        show "\<forall>c < length ((mat_mult ?E ?F) ! r).
                (mat_mult ?E ?F) ! r ! c = (id_mat m) ! r ! c"
        proof (rule allI, rule impI)
          fix c assume cl: "c < length ((mat_mult ?E ?F) ! r)"
          hence cm: "c < m" using innerL by simp
          have lhs: "(mat_mult ?E ?F) ! r ! c = dot (?E ! r) (col_vec ?F c)"
            using entry_mat_mult_dot[of r ?E c ?F] rm nE cF cm by (simp add: entry_def row_vec_def)
          have rhsId: "(id_mat m) ! r ! c = (if r = c then (1::int) else 0)"
            using id_mat_nth[OF rm cm] .
          show "(mat_mult ?E ?F) ! r ! c = (id_mat m) ! r ! c"
          proof (cases "r = i")
            case True
            have Er: "?E ! i = map (\<lambda>cc. if cc = j then f else (if cc = i then (1::int) else 0)) [0..<m]"
              using nth_row_add_matrix[OF im] ij by simp
            have dotv: "dot (?E ! i) (col_vec ?F c) = col_vec ?F c ! i + f * (col_vec ?F c ! j)"
              using dot_sparse_two[OF im jm ij colLen[of c], of f] Er by simp
            have ci: "col_vec ?F c ! i = (if c = j then -f else (if i = c then (1::int) else 0))"
            proof -
              have "col_vec ?F c ! i = ?F ! i ! c" using im Frows by (simp add: col_vec_def nth_map)
              also have "?F ! i = map (\<lambda>cc. if cc = j then -f else (if i = cc then (1::int) else 0)) [0..<m]"
                using nth_row_add_matrix[OF im] ij by simp
              hence "?F ! i ! c = (if c = j then -f else (if i = c then (1::int) else 0))"
                using cm by (simp add: nth_map nth_upt)
              finally show ?thesis .
            qed
            have cj: "col_vec ?F c ! j = (if c = j then (1::int) else 0)"
            proof -
              have "col_vec ?F c ! j = ?F ! j ! c" using jm Frows by (simp add: col_vec_def nth_map)
              also have "?F ! j = map (\<lambda>cc. if cc = j then (1::int) else 0) [0..<m]"
                using nth_row_add_matrix[OF jm] ij by simp
              hence "?F ! j ! c = (if c = j then (1::int) else 0)"
                using cm by (simp add: nth_map nth_upt)
              finally show ?thesis .
            qed
            have sum: "col_vec ?F c ! i + f * (col_vec ?F c ! j) = (if i = c then (1::int) else 0)"
            proof (cases "c = j")
              case True
              hence "i \<noteq> c" using ij by simp
              thus ?thesis using ci cj True by simp
            next
              case False
              thus ?thesis using ci cj by simp
            qed
            show ?thesis using True lhs dotv rhsId sum by simp
          next
            case False
            have Er: "?E ! r = map (\<lambda>cc. if cc = r then (1::int) else 0) [0..<m]"
              using nth_row_add_matrix[OF rm] False by simp
            have dotv: "dot (?E ! r) (col_vec ?F c) = col_vec ?F c ! r"
              using dot_unit_row[OF rm colLen[of c]] Er by simp
            have cr: "col_vec ?F c ! r = (if r = c then (1::int) else 0)"
            proof -
              have "col_vec ?F c ! r = ?F ! r ! c" using rm Frows by (simp add: col_vec_def nth_map)
              also have "?F ! r = map (\<lambda>cc. if cc = r then (1::int) else 0) [0..<m]"
                using nth_row_add_matrix[OF rm] False by simp
              hence "?F ! r ! c = (if r = c then (1::int) else 0)"
                using cm by (simp add: nth_map nth_upt)
              finally show ?thesis .
            qed
            show ?thesis using lhs dotv rhsId cr by simp
          qed
        qed
      qed
    qed
  qed
qed

lemma mat_mult_mod_elem_inverse:
  assumes im: "i < m" and jm: "j < m" and ij: "i \<noteq> j"
  shows "mat_mult_mod (row_add_matrix m i j f) (row_add_matrix m i j (-f)) = id_mat m"
  using row_add_matrix_int_inverse[OF im jm ij] id_mat_fq
  by (simp add: mat_mult_mod_def)



section \<open>Reduction is a ring congruence\<close>

text \<open>Two integers are \<open>q\<close>-congruent when they reduce to the same residue.  This is the
  relation that lets a matrix of already-reduced entries stand in for the integer matrix it
  came from; it is a congruence for \<open>+\<close> and \<open>*\<close>, which is what
  associativity of the modular product needs.  Every lemma below is applied by explicit
  @{text "simp only"} --- @{text fq_add} and @{text fq_idem} rewrite in opposite directions
  and must never meet inside the simplifier.\<close>

definition cong_q :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "cong_q x y = (fq x = fq y)"

lemma cong_q_refl [simp]: "cong_q x x" by (simp add: cong_q_def)
lemma cong_q_sym: "cong_q x y \<Longrightarrow> cong_q y x" by (simp add: cong_q_def)

lemma cong_q_fq [simp]: "cong_q (fq x) x"
  by (simp add: cong_q_def fq_idem)

lemma fq_cong_add:
  assumes "fq a = fq b" and "fq c = fq d"
  shows "fq (a + c) = fq (b + d)"
proof -
  have "fq (a + c) = fq (fq a + fq c)" by (rule fq_add)
  also have "\<dots> = fq (fq b + fq d)" using assms by simp
  also have "\<dots> = fq (b + d)" by (rule fq_add[symmetric])
  finally show ?thesis .
qed

lemma fq_cong_mult:
  assumes "fq a = fq b" and "fq c = fq d"
  shows "fq (a * c) = fq (b * d)"
proof -
  have "fq (a * c) = fq (fq a * fq c)" by (rule fq_mult)
  also have "\<dots> = fq (fq b * fq d)" using assms by simp
  also have "\<dots> = fq (b * d)" by (rule fq_mult[symmetric])
  finally show ?thesis .
qed

lemma cong_q_add:
  assumes "cong_q a b" and "cong_q c d"
  shows "cong_q (a + c) (b + d)"
proof -
  have h1: "fq a = fq b" using assms by (simp add: cong_q_def)
  have h2: "fq c = fq d" using assms by (simp add: cong_q_def)
  show ?thesis using fq_cong_add[OF h1 h2] by (simp add: cong_q_def)
qed

lemma cong_q_mult:
  assumes "cong_q a b" and "cong_q c d"
  shows "cong_q (a * c) (b * d)"
proof -
  have h1: "fq a = fq b" using assms by (simp add: cong_q_def)
  have h2: "fq c = fq d" using assms by (simp add: cong_q_def)
  show ?thesis using fq_cong_mult[OF h1 h2] by (simp add: cong_q_def)
qed

lemma fq_sum:
  "fq (sum_list xs) = fq (sum_list (map fq xs))"
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons a xs)
  have IH: "fq (sum_list xs) = fq (sum_list (map fq xs))" using Cons.hyps .
  have step: "fq (a + sum_list xs) = fq (fq a + sum_list (map fq xs))"
    using fq_cong_add[of a "fq a" "sum_list xs" "sum_list (map fq xs)"] fq_idem IH by simp
  show ?case using step by simp
qed

lemma fq_sum_cong:
  assumes "\<And>k. k \<in> set ks \<Longrightarrow> fq (g k) = fq (h k)"
  shows "fq (sum_list (map g ks)) = fq (sum_list (map h ks))"
  using assms
proof (induct ks)
  case Nil
  show ?case by simp
next
  case (Cons a ks)
  have ha: "fq (g a) = fq (h a)" using Cons.prems by simp
  have hIH: "fq (sum_list (map g ks)) = fq (sum_list (map h ks))"
    using Cons.prems Cons.hyps by simp
  have step: "fq (g a + sum_list (map g ks)) = fq (h a + sum_list (map h ks))"
    using fq_cong_add[OF ha hIH] .
  show ?case using step by simp
qed

text \<open>Entry of the reduced product.  The two facts below are what lets the outer
  @{text fq} be pulled past an inner @{text fq}: a product whose entries are already reduced
  has the same residue as the integer product, entry by entry.\<close>

lemma entry_mat_mult_mod:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    and rB: "is_rect B" and nB: "n_rows B = m" and cB: "n_cols B = m"
    and m0: "0 < m" and i: "i < m" and j: "j < m"
  shows "entry (mat_mult_mod A B) i j = fq (entry (mat_mult A B) i j)"
proof -
  have hAB: "n_rows (mat_mult A B) = m" using nA by (simp add: n_rows_mat_mult)
  have hi: "i < length (mat_mult A B)" using i hAB by (simp add: n_rows_def)
  have hrowA: "i < n_rows A" using i nA by simp
  have hj: "j < length ((mat_mult A B) ! i)"
    using j cB row_mult_len[of i A B, OF hrowA] by simp
  have "(mat_mult_mod A B) ! i ! j = fq ((mat_mult A B) ! i ! j)"
    using nth_map[OF hi, of "\<lambda>row. map fq row"]
      nth_map[OF hj, of fq]
    by (simp add: mat_mult_mod_def)
  thus ?thesis by (simp add: entry_def)
qed

lemma fq_pull_left:
  "fq (sum_list (map (\<lambda>k. fq (g k) * c k) [0..<n]))
     = fq (sum_list (map (\<lambda>k. g k * c k) [0..<n]))"
proof (rule fq_sum_cong)
  fix k assume "k \<in> set [0..<n]"
  show "fq (fq (g k) * c k) = fq (g k * c k)"
    by (rule fq_cong_mult[OF fq_idem refl])
qed

lemma fq_pull_right:
  "fq (sum_list (map (\<lambda>k. a k * fq (h k)) [0..<n]))
     = fq (sum_list (map (\<lambda>k. a k * h k) [0..<n]))"
proof (rule fq_sum_cong)
  fix k assume "k \<in> set [0..<n]"
  show "fq (a k * fq (h k)) = fq (a k * h k)"
    by (rule fq_cong_mult[OF refl fq_idem])
qed

end
