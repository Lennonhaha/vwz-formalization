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
  imports VWZ_MatAlgebra VWZ_RREF VWZ_KeyGen
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

text \<open>Two-sided invertibility over @{text F_q}.  The definition lives in the
  congruence section near the end of this theory, because the honest version of the
  notion is a congruence rather than an equality: the modular product reduces its
  result, so a witness that is not itself reduced can only be expected to reproduce
  the identity up to @{text cong_q}.  The integer @{text invertible} in VWZ_Matrix
  stays as it was.\<close>

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

section \<open>Shape facts and the entry lemma for the reduced product\<close>

lemma mat_len: "length (mat_mult A B) = n_rows A"
proof -
  have h1: "length (mat_mult A B) = n_rows (mat_mult A B)" by (simp add: n_rows_def)
  have h2: "n_rows (mat_mult A B) = n_rows A" by (rule n_rows_mat_mult)
  show ?thesis using h1 h2 by simp
qed

lemma mat_ne: "n_rows A > 0 \<Longrightarrow> mat_mult A B \<noteq> []"
proof -
  assume h: "n_rows A > 0"
  have len: "length (mat_mult A B) = length A"
    using mat_len[of A B] by (simp add: n_rows_def)
  have pos: "length A > 0" using h by (simp add: n_rows_def)
  have poslen: "length (mat_mult A B) > 0" using len pos by simp
  show ?thesis using poslen by (simp add: length_greater_0_conv)
qed

lemma n_cols_map_map: "X \<noteq> [] \<Longrightarrow> n_cols (map (map f) X) = n_cols X"
  by (simp add: n_cols_def)

lemma n_rows_mod: "n_rows (mat_mult_mod X Y) = n_rows X"
proof -
  have h: "length (mat_mult_mod X Y) = length X"
    using mat_len[of X Y] by (simp add: mat_mult_mod_def n_rows_def)
  show ?thesis using h by (simp add: n_rows_def)
qed

lemma len_mod: "length (mat_mult_mod X Y) = n_rows X"
proof -
  have h: "length (mat_mult_mod X Y) = length X"
    using mat_len[of X Y] by (simp add: mat_mult_mod_def n_rows_def)
  show ?thesis using h by (simp add: n_rows_def)
qed

lemma is_rect_mod:
  assumes rX: "is_rect X" and nX: "n_rows X = m" and cY: "n_cols Y = m" and m0: "0 < m"
  shows "is_rect (mat_mult_mod X Y)"
proof -
  have mpos: "n_rows X > 0" using nX m0 by simp
  have ne: "mat_mult X Y \<noteq> []" using mat_ne[OF mpos] .
  have ir: "is_rect (mat_mult X Y)" using is_rect_mat_mult[OF mpos] .
  have h: "\<forall>r\<in>set (mat_mult X Y). length r = n_cols (mat_mult X Y)"
    using ir by (simp add: is_rect_def)
  show ?thesis
    using h ne by (simp add: mat_mult_mod_def is_rect_def n_cols_map_map)
qed

lemma n_cols_mod:
  assumes nX: "n_rows X = m" and cY: "n_cols Y = m" and m0: "0 < m"
  shows "n_cols (mat_mult_mod X Y) = m"
proof -
  have mpos: "n_rows X > 0" using nX m0 by simp
  have ne: "mat_mult X Y \<noteq> []" using mat_ne[OF mpos] .
  show ?thesis
    using n_cols_mat_mult[OF mpos, of Y] ne cY by (simp add: mat_mult_mod_def n_cols_map_map)
qed

lemma entry_mod_left_inner:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    and rB: "is_rect B" and nB: "n_rows B = m" and cB: "n_cols B = m"
    and rC: "is_rect C" and nC: "n_rows C = m" and cC: "n_cols C = m"
    and m0: "0 < m" and i: "i < m" and j: "j < m"
  shows "entry (mat_mult (mat_mult_mod A B) C) i j
       = sum_list (map (\<lambda>k. entry (mat_mult_mod A B) i k * entry C k j) [0..<m])"
proof -
  have Mr: "is_rect (mat_mult_mod A B)" using rA nA cB m0 by (rule is_rect_mod)
  have Mn: "n_rows (mat_mult_mod A B) = m" using nA by (simp add: n_rows_mod)
  have Mc: "n_cols (mat_mult_mod A B) = m" using nA cB m0 by (rule n_cols_mod)
  have im: "i < n_rows (mat_mult_mod A B)" using Mn i by simp
  have jc: "j < n_cols C" using cC j by simp
  have eq: "n_cols (mat_mult_mod A B) = n_rows C" using Mc nC by simp
  have h: "entry (mat_mult (mat_mult_mod A B) C) i j
      = sum_list (map (\<lambda>k. entry (mat_mult_mod A B) i k * entry C k j)
                   [0..<n_cols (mat_mult_mod A B)])"
    using im jc eq Mr by (rule entry_mult)
  show ?thesis using h Mc by simp
qed

lemma entry_mod_left_fq:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    and rB: "is_rect B" and nB: "n_rows B = m" and cB: "n_cols B = m"
    and rC: "is_rect C" and nC: "n_rows C = m" and cC: "n_cols C = m"
    and m0: "0 < m" and i: "i < m" and j: "j < m"
  shows "sum_list (map (\<lambda>k. entry (mat_mult_mod A B) i k * entry C k j) [0..<m])
       = sum_list (map (\<lambda>k. fq (entry (mat_mult A B) i k) * entry C k j) [0..<m])"
proof (rule arg_cong[where f=sum_list])
  show "map (\<lambda>k. entry (mat_mult_mod A B) i k * entry C k j) [0..<m]
      = map (\<lambda>k. fq (entry (mat_mult A B) i k) * entry C k j) [0..<m]"
  proof (rule map_cong[OF refl])
    fix k assume "k \<in> set [0..<m]"
    hence km: "k < m" by (simp add: set_upt)
    show "entry (mat_mult_mod A B) i k * entry C k j
        = fq (entry (mat_mult A B) i k) * entry C k j"
      using entry_mat_mult_mod[OF rA nA cA rB nB cB m0 i km] by simp
  qed
qed

lemma entry_int_left:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    and rB: "is_rect B" and nB: "n_rows B = m" and cB: "n_cols B = m"
    and rC: "is_rect C" and nC: "n_rows C = m" and cC: "n_cols C = m"
    and m0: "0 < m" and i: "i < m" and j: "j < m"
  shows "entry (mat_mult (mat_mult A B) C) i j
       = sum_list (map (\<lambda>k. entry (mat_mult A B) i k * entry C k j) [0..<m])"
proof -
  have mpos: "n_rows A > 0" using nA m0 by simp
  have ABr: "is_rect (mat_mult A B)" using is_rect_mat_mult[OF mpos] .
  have ABn: "n_rows (mat_mult A B) = m"
    using mat_len[of A B] nA by (simp add: n_rows_def)
  have ABc: "n_cols (mat_mult A B) = m"
    using n_cols_mat_mult[OF mpos, of B] cB by simp
  have im: "i < n_rows (mat_mult A B)" using ABn i by simp
  have jc: "j < n_cols C" using cC j by simp
  have eq: "n_cols (mat_mult A B) = n_rows C" using ABc nC by simp
  have h: "entry (mat_mult (mat_mult A B) C) i j
      = sum_list (map (\<lambda>k. entry (mat_mult A B) i k * entry C k j)
                   [0..<n_cols (mat_mult A B)])"
    using im jc eq ABr by (rule entry_mult)
  show ?thesis using h ABc by simp
qed

lemma entry_mod_left:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    and rB: "is_rect B" and nB: "n_rows B = m" and cB: "n_cols B = m"
    and rC: "is_rect C" and nC: "n_rows C = m" and cC: "n_cols C = m"
    and m0: "0 < m" and i: "i < m" and j: "j < m"
  shows "entry (mat_mult_mod (mat_mult_mod A B) C) i j
       = fq (entry (mat_mult (mat_mult A B) C) i j)"
proof -
  have Mr: "is_rect (mat_mult_mod A B)" using rA nA cB m0 by (rule is_rect_mod)
  have Mn: "n_rows (mat_mult_mod A B) = m" using nA by (simp add: n_rows_mod)
  have Mc: "n_cols (mat_mult_mod A B) = m" using nA cB m0 by (rule n_cols_mod)
  have S1: "entry (mat_mult_mod (mat_mult_mod A B) C) i j
      = fq (entry (mat_mult (mat_mult_mod A B) C) i j)"
    using Mr Mn Mc rC nC cC m0 i j by (rule entry_mat_mult_mod)
  have S2: "entry (mat_mult (mat_mult_mod A B) C) i j
      = sum_list (map (\<lambda>k. entry (mat_mult_mod A B) i k * entry C k j) [0..<m])"
    using rA nA cA rB nB cB rC nC cC m0 i j by (rule entry_mod_left_inner)
  have S4: "sum_list (map (\<lambda>k. entry (mat_mult_mod A B) i k * entry C k j) [0..<m])
      = sum_list (map (\<lambda>k. fq (entry (mat_mult A B) i k) * entry C k j) [0..<m])"
    using rA nA cA rB nB cB rC nC cC m0 i j by (rule entry_mod_left_fq)
  have S5: "fq (sum_list (map (\<lambda>k. fq (entry (mat_mult A B) i k) * entry C k j) [0..<m]))
      = fq (sum_list (map (\<lambda>k. entry (mat_mult A B) i k * entry C k j) [0..<m]))"
    by (rule fq_pull_left)
  have S6: "entry (mat_mult (mat_mult A B) C) i j
      = sum_list (map (\<lambda>k. entry (mat_mult A B) i k * entry C k j) [0..<m])"
    using rA nA cA rB nB cB rC nC cC m0 i j by (rule entry_int_left)
  have A1: "entry (mat_mult_mod (mat_mult_mod A B) C) i j
      = fq (sum_list (map (\<lambda>k. entry (mat_mult_mod A B) i k * entry C k j) [0..<m]))"
    using S1 S2 by (simp only: S1 S2)
  have A2: "fq (sum_list (map (\<lambda>k. entry (mat_mult_mod A B) i k * entry C k j) [0..<m]))
      = fq (sum_list (map (\<lambda>k. fq (entry (mat_mult A B) i k) * entry C k j) [0..<m]))"
    using S4 by (simp only: S4)
  have A3: "fq (sum_list (map (\<lambda>k. fq (entry (mat_mult A B) i k) * entry C k j) [0..<m]))
      = fq (sum_list (map (\<lambda>k. entry (mat_mult A B) i k * entry C k j) [0..<m]))"
    by (rule S5)
  have A4: "fq (sum_list (map (\<lambda>k. entry (mat_mult A B) i k * entry C k j) [0..<m]))
      = fq (entry (mat_mult (mat_mult A B) C) i j)"
    using S6 by (simp only: S6)
  show ?thesis using A1 A2 A3 A4 by simp
qed

section \<open>The same on the right factor\<close>

lemma entry_mod_right_inner:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    and rB: "is_rect B" and nB: "n_rows B = m" and cB: "n_cols B = m"
    and rC: "is_rect C" and nC: "n_rows C = m" and cC: "n_cols C = m"
    and m0: "0 < m" and i: "i < m" and j: "j < m"
  shows "entry (mat_mult A (mat_mult_mod B C)) i j
       = sum_list (map (\<lambda>k. entry A i k * entry (mat_mult_mod B C) k j) [0..<m])"
proof -
  have Mr: "is_rect (mat_mult_mod B C)" using rB nB cC m0 by (rule is_rect_mod)
  have Mn: "n_rows (mat_mult_mod B C) = m" using nB by (simp add: n_rows_mod)
  have Mc: "n_cols (mat_mult_mod B C) = m" using nB cC m0 by (rule n_cols_mod)
  have im: "i < n_rows A" using nA i by simp
  have jc: "j < n_cols (mat_mult_mod B C)" using Mc j by simp
  have eq: "n_cols A = n_rows (mat_mult_mod B C)" using cA Mn by simp
  have h: "entry (mat_mult A (mat_mult_mod B C)) i j
      = sum_list (map (\<lambda>k. entry A i k * entry (mat_mult_mod B C) k j)
                   [0..<n_cols A])"
    using im jc eq rA by (rule entry_mult)
  show ?thesis using h cA by simp
qed

lemma entry_mod_right_fq:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    and rB: "is_rect B" and nB: "n_rows B = m" and cB: "n_cols B = m"
    and rC: "is_rect C" and nC: "n_rows C = m" and cC: "n_cols C = m"
    and m0: "0 < m" and i: "i < m" and j: "j < m"
  shows "sum_list (map (\<lambda>k. entry A i k * entry (mat_mult_mod B C) k j) [0..<m])
       = sum_list (map (\<lambda>k. entry A i k * fq (entry (mat_mult B C) k j)) [0..<m])"
proof (rule arg_cong[where f=sum_list])
  show "map (\<lambda>k. entry A i k * entry (mat_mult_mod B C) k j) [0..<m]
      = map (\<lambda>k. entry A i k * fq (entry (mat_mult B C) k j)) [0..<m]"
  proof (rule map_cong[OF refl])
    fix k assume "k \<in> set [0..<m]"
    hence km: "k < m" by (simp add: set_upt)
    show "entry A i k * entry (mat_mult_mod B C) k j
        = entry A i k * fq (entry (mat_mult B C) k j)"
      using entry_mat_mult_mod[OF rB nB cB rC nC cC m0 km j] by simp
  qed
qed

lemma entry_int_right:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    and rB: "is_rect B" and nB: "n_rows B = m" and cB: "n_cols B = m"
    and rC: "is_rect C" and nC: "n_rows C = m" and cC: "n_cols C = m"
    and m0: "0 < m" and i: "i < m" and j: "j < m"
  shows "entry (mat_mult A (mat_mult B C)) i j
       = sum_list (map (\<lambda>k. entry A i k * entry (mat_mult B C) k j) [0..<m])"
proof -
  have mpos: "n_rows B > 0" using nB m0 by simp
  have BCr: "is_rect (mat_mult B C)" using is_rect_mat_mult[OF mpos] .
  have BCn: "n_rows (mat_mult B C) = m"
    using mat_len[of B C] nB by (simp add: n_rows_def)
  have BCc: "n_cols (mat_mult B C) = m"
    using n_cols_mat_mult[OF mpos, of C] cC by simp
  have im: "i < n_rows A" using nA i by simp
  have jc: "j < n_cols (mat_mult B C)" using BCc j by simp
  have eq: "n_cols A = n_rows (mat_mult B C)" using cA BCn by simp
  have h: "entry (mat_mult A (mat_mult B C)) i j
      = sum_list (map (\<lambda>k. entry A i k * entry (mat_mult B C) k j)
                   [0..<n_cols A])"
    using im jc eq rA by (rule entry_mult)
  show ?thesis using h cA by simp
qed

lemma entry_mod_right:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    and rB: "is_rect B" and nB: "n_rows B = m" and cB: "n_cols B = m"
    and rC: "is_rect C" and nC: "n_rows C = m" and cC: "n_cols C = m"
    and m0: "0 < m" and i: "i < m" and j: "j < m"
  shows "entry (mat_mult_mod A (mat_mult_mod B C)) i j
       = fq (entry (mat_mult A (mat_mult B C)) i j)"
proof -
  have Mr: "is_rect (mat_mult_mod B C)" using rB nB cC m0 by (rule is_rect_mod)
  have Mn: "n_rows (mat_mult_mod B C) = m" using nB by (simp add: n_rows_mod)
  have Mc: "n_cols (mat_mult_mod B C) = m" using nB cC m0 by (rule n_cols_mod)
  have S1: "entry (mat_mult_mod A (mat_mult_mod B C)) i j
      = fq (entry (mat_mult A (mat_mult_mod B C)) i j)"
    using rA nA cA Mr Mn Mc m0 i j by (rule entry_mat_mult_mod)
  have S2: "entry (mat_mult A (mat_mult_mod B C)) i j
      = sum_list (map (\<lambda>k. entry A i k * entry (mat_mult_mod B C) k j) [0..<m])"
    using rA nA cA rB nB cB rC nC cC m0 i j by (rule entry_mod_right_inner)
  have S4: "sum_list (map (\<lambda>k. entry A i k * entry (mat_mult_mod B C) k j) [0..<m])
      = sum_list (map (\<lambda>k. entry A i k * fq (entry (mat_mult B C) k j)) [0..<m])"
    using rA nA cA rB nB cB rC nC cC m0 i j by (rule entry_mod_right_fq)
  have S5: "fq (sum_list (map (\<lambda>k. entry A i k * fq (entry (mat_mult B C) k j)) [0..<m]))
      = fq (sum_list (map (\<lambda>k. entry A i k * entry (mat_mult B C) k j) [0..<m]))"
    by (rule fq_pull_right)
  have S6: "entry (mat_mult A (mat_mult B C)) i j
      = sum_list (map (\<lambda>k. entry A i k * entry (mat_mult B C) k j) [0..<m])"
    using rA nA cA rB nB cB rC nC cC m0 i j by (rule entry_int_right)
  have A1: "entry (mat_mult_mod A (mat_mult_mod B C)) i j
      = fq (sum_list (map (\<lambda>k. entry A i k * entry (mat_mult_mod B C) k j) [0..<m]))"
    using S1 S2 by (simp only: S1 S2)
  have A2: "fq (sum_list (map (\<lambda>k. entry A i k * entry (mat_mult_mod B C) k j) [0..<m]))
      = fq (sum_list (map (\<lambda>k. entry A i k * fq (entry (mat_mult B C) k j)) [0..<m]))"
    using S4 by (simp only: S4)
  have A3: "fq (sum_list (map (\<lambda>k. entry A i k * fq (entry (mat_mult B C) k j)) [0..<m]))
      = fq (sum_list (map (\<lambda>k. entry A i k * entry (mat_mult B C) k j) [0..<m]))"
    by (rule S5)
  have A4: "fq (sum_list (map (\<lambda>k. entry A i k * entry (mat_mult B C) k j) [0..<m]))
      = fq (entry (mat_mult A (mat_mult B C)) i j)"
    using S6 by (simp only: S6)
  show ?thesis using A1 A2 A3 A4 by simp
qed

section \<open>Associativity of the reduced product\<close>

lemma entry_mod_assoc:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    and rB: "is_rect B" and nB: "n_rows B = m" and cB: "n_cols B = m"
    and rC: "is_rect C" and nC: "n_rows C = m" and cC: "n_cols C = m"
    and m0: "0 < m" and i: "i < m" and j: "j < m"
  shows "entry (mat_mult_mod (mat_mult_mod A B) C) i j
       = entry (mat_mult_mod A (mat_mult_mod B C)) i j"
proof -
  have L: "entry (mat_mult_mod (mat_mult_mod A B) C) i j
      = fq (entry (mat_mult (mat_mult A B) C) i j)"
    using rA nA cA rB nB cB rC nC cC m0 i j by (rule entry_mod_left)
  have R: "entry (mat_mult_mod A (mat_mult_mod B C)) i j
      = fq (entry (mat_mult A (mat_mult B C)) i j)"
    using rA nA cA rB nB cB rC nC cC m0 i j by (rule entry_mod_right)
  have I: "mat_mult (mat_mult A B) C = mat_mult A (mat_mult B C)"
    using rA rB rC nA cA nB cB nC cC m0 by (rule mat_mult_assoc_square)
  show ?thesis using L R I by simp
qed

lemma mat_mult_mod_assoc:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    and rB: "is_rect B" and nB: "n_rows B = m" and cB: "n_cols B = m"
    and rC: "is_rect C" and nC: "n_rows C = m" and cC: "n_cols C = m"
    and m0: "0 < m"
  shows "mat_mult_mod (mat_mult_mod A B) C = mat_mult_mod A (mat_mult_mod B C)"
proof (rule nth_equalityI)
  have ln1: "length (mat_mult_mod (mat_mult_mod A B) C) = m"
  proof -
    have a: "length (mat_mult_mod (mat_mult_mod A B) C) = n_rows (mat_mult_mod A B)"
      by (rule len_mod)
    have b: "n_rows (mat_mult_mod A B) = m" using nA by (simp add: n_rows_mod)
    show ?thesis using a b by simp
  qed
  have ln2: "length (mat_mult_mod A (mat_mult_mod B C)) = m"
  proof -
    have a: "length (mat_mult_mod A (mat_mult_mod B C)) = n_rows A" by (rule len_mod)
    show ?thesis using a nA by simp
  qed
  show "length (mat_mult_mod (mat_mult_mod A B) C)
      = length (mat_mult_mod A (mat_mult_mod B C))"
    using ln1 ln2 by simp
  fix i assume hi: "i < length (mat_mult_mod (mat_mult_mod A B) C)"
  hence im: "i < m" using ln1 by simp
  have Mr: "is_rect (mat_mult_mod A B)" using rA nA cB m0 by (rule is_rect_mod)
  have Mn: "n_rows (mat_mult_mod A B) = m" using nA by (simp add: n_rows_mod)
  have Mc: "n_cols (mat_mult_mod A B) = m" using nA cB m0 by (rule n_cols_mod)
  have Lrect: "is_rect (mat_mult_mod (mat_mult_mod A B) C)"
    using Mr Mn cC m0 by (rule is_rect_mod)
  have BCc: "n_cols (mat_mult_mod B C) = m" using nB cC m0 by (rule n_cols_mod)
  have Rrect: "is_rect (mat_mult_mod A (mat_mult_mod B C))"
    using rA nA BCc m0 by (rule is_rect_mod)
  have Lc: "n_cols (mat_mult_mod (mat_mult_mod A B) C) = m"
    using Mn cC m0 by (rule n_cols_mod)
  have Llen: "length ((mat_mult_mod (mat_mult_mod A B) C) ! i) = m"
    using is_rect_rows[OF Lrect, of i] im Lc ln1 by (simp add: n_rows_def)
  have Rc: "n_cols (mat_mult_mod A (mat_mult_mod B C)) = m"
    using nA BCc m0 by (rule n_cols_mod)
  have Rlen: "length ((mat_mult_mod A (mat_mult_mod B C)) ! i) = m"
    using is_rect_rows[OF Rrect, of i] im Rc ln2 by (simp add: n_rows_def)
  show "(mat_mult_mod (mat_mult_mod A B) C) ! i
      = (mat_mult_mod A (mat_mult_mod B C)) ! i"
  proof (rule nth_equalityI)
    show "length ((mat_mult_mod (mat_mult_mod A B) C) ! i)
        = length ((mat_mult_mod A (mat_mult_mod B C)) ! i)"
      using Llen Rlen by simp
    fix j assume hj: "j < length ((mat_mult_mod (mat_mult_mod A B) C) ! i)"
    hence jm: "j < m" using Llen by simp
    have E: "entry (mat_mult_mod (mat_mult_mod A B) C) i j
        = entry (mat_mult_mod A (mat_mult_mod B C)) i j"
      using rA nA cA rB nB cB rC nC cC m0 im jm by (rule entry_mod_assoc)
    show "((mat_mult_mod (mat_mult_mod A B) C) ! i) ! j
        = ((mat_mult_mod A (mat_mult_mod B C)) ! i) ! j"
      using E by (simp add: entry_def)
  qed
qed

section \<open>Pointwise congruence of matrices\<close>

definition cong_q_mat :: "mat \<Rightarrow> mat \<Rightarrow> bool" where
  "cong_q_mat A B = (\<forall>i j. i < n_rows A \<longrightarrow> j < n_cols A
                              \<longrightarrow> cong_q (entry A i j) (entry B i j))"

lemma cong_q_trans: "cong_q x y \<Longrightarrow> cong_q y z \<Longrightarrow> cong_q x z"
  by (simp add: cong_q_def)

lemma cong_q_matI:
  assumes "\<And>i j. i < n_rows A \<Longrightarrow> j < n_cols A \<Longrightarrow> cong_q (entry A i j) (entry B i j)"
  shows "cong_q_mat A B"
  using assms by (simp add: cong_q_mat_def)

lemma cong_q_matD:
  assumes "cong_q_mat A B" and "i < n_rows A" and "j < n_cols A"
  shows "cong_q (entry A i j) (entry B i j)"
  using assms by (simp add: cong_q_mat_def)

lemma cong_q_mat_refl [simp]: "cong_q_mat A A"
  by (simp add: cong_q_mat_def)

lemma cong_q_mat_sym:
  assumes "cong_q_mat A B" and "n_rows A = n_rows B" and "n_cols A = n_cols B"
  shows "cong_q_mat B A"
proof (rule cong_q_matI)
  fix i j assume i: "i < n_rows B" and j: "j < n_cols B"
  have iA: "i < n_rows A" using i assms(2) by simp
  have jA: "j < n_cols A" using j assms(3) by simp
  have h: "cong_q (entry A i j) (entry B i j)" using assms(1) iA jA by (rule cong_q_matD)
  show "cong_q (entry B i j) (entry A i j)" using h by (rule cong_q_sym)
qed

lemma cong_q_mat_trans:
  assumes "cong_q_mat A B" and "cong_q_mat B C"
    and "n_rows A = n_rows B" and "n_cols A = n_cols B" and "n_cols B = n_cols C"
  shows "cong_q_mat A C"
proof (rule cong_q_matI)
  fix i j assume i: "i < n_rows A" and j: "j < n_cols A"
  have iB: "i < n_rows B" using i assms(3) by simp
  have jB: "j < n_cols B" using j assms(4) by simp
  have jC: "j < n_cols C" using jB assms(5) by simp
  have h1: "cong_q (entry A i j) (entry B i j)" using assms(1) i j by (rule cong_q_matD)
  have h2: "cong_q (entry B i j) (entry C i j)" using assms(2) iB jB by (rule cong_q_matD)
  show "cong_q (entry A i j) (entry C i j)" using h1 h2 by (rule cong_q_trans)
qed

lemma cong_q_mat_eq: "A = B \<Longrightarrow> cong_q_mat A B"
  by simp

lemma sum_sel_one_right:
  fixes y :: "int list"
  assumes "i < n"
  shows "sum_list (map (\<lambda>k. y ! k * (if k = i then (1::int) else 0)) [0..<n]) = y ! i"
proof -
  have "sum_list (map (\<lambda>k. y ! k * (if k = i then (1::int) else 0)) [0..<n])
      = sum_list (map (\<lambda>k. (if k = i then (1::int) else 0) * y ! k) [0..<n])"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl], simp add: mult.commute)
  also have "\<dots> = y ! i" using sum_sel_one[OF assms] .
  finally show ?thesis .
qed

lemma n_rows_id_mat [simp]: "n_rows (id_mat m) = m"
  by (simp add: id_mat_def n_rows_def)

lemma n_cols_id_mat: "0 < m \<Longrightarrow> n_cols (id_mat m) = m"
  by (simp add: id_mat_def n_cols_def)

lemma is_rect_id_mat: "0 < m \<Longrightarrow> is_rect (id_mat m)"
  by (simp add: id_mat_def is_rect_def n_cols_def)

lemma entry_double:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    and rC: "is_rect C" and nC: "n_rows C = m" and cC: "n_cols C = m"
    and m0: "0 < m" and i: "i < m" and j: "j < m"
  shows "entry (mat_mult A C) i j
       = sum_list (map (\<lambda>k. entry A i k * entry C k j) [0..<m])"
proof -
  have iA: "i < n_rows A" using i nA by simp
  have jC: "j < n_cols C" using j cC by simp
  have eq: "n_cols A = n_rows C" using cA nC by simp
  have h: "entry (mat_mult A C) i j
      = sum_list (map (\<lambda>k. entry A i k * entry C k j) [0..<n_cols A])"
    using iA jC eq rA by (rule entry_mult)
  show ?thesis using h cA by simp
qed

lemma entry_id_right:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m" and m0: "0 < m"
    and i: "i < m" and j: "j < m"
  shows "entry (mat_mult A (id_mat m)) i j = entry A i j"
proof -
  have cI: "n_cols (id_mat m) = m" using m0 by (rule n_cols_id_mat)
  have h1: "entry (mat_mult A (id_mat m)) i j
      = sum_list (map (\<lambda>k. entry A i k * entry (id_mat m) k j) [0..<m])"
    using entry_double[OF rA nA cA is_rect_id_mat[OF m0] n_rows_id_mat cI m0 i j] .
  have hsum: "sum_list (map (\<lambda>k. entry A i k * entry (id_mat m) k j) [0..<m])
      = sum_list (map (\<lambda>k. (A ! i) ! k * (if k = j then (1::int) else 0)) [0..<m])"
  proof (rule arg_cong[where f=sum_list])
    show "map (\<lambda>k. entry A i k * entry (id_mat m) k j) [0..<m]
        = map (\<lambda>k. (A ! i) ! k * (if k = j then (1::int) else 0)) [0..<m]"
    proof (rule map_cong[OF refl])
      fix k assume "k \<in> set [0..<m]"
      hence km: "k < m" by (simp add: set_upt)
      have e1: "entry A i k = (A ! i) ! k" by (simp add: entry_def)
      have e2: "entry (id_mat m) k j = (if k = j then 1 else 0)"
        using id_mat_nth[OF km j] by (simp add: entry_def)
      show "entry A i k * entry (id_mat m) k j
          = (A ! i) ! k * (if k = j then (1::int) else 0)"
        using e1 e2 by simp
    qed
  qed
  have hsel: "sum_list (map (\<lambda>k. (A ! i) ! k * (if k = j then (1::int) else 0)) [0..<m])
      = (A ! i) ! j"
    by (rule sum_sel_one_right, rule j)
  show ?thesis using h1 hsum hsel by (simp add: entry_def)
qed

lemma entry_id_left:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m" and m0: "0 < m"
    and i: "i < m" and j: "j < m"
  shows "entry (mat_mult (id_mat m) A) i j = entry A i j"
proof -
  have cI: "n_cols (id_mat m) = m" using m0 by (rule n_cols_id_mat)
  have h1: "entry (mat_mult (id_mat m) A) i j
      = sum_list (map (\<lambda>k. entry (id_mat m) i k * entry A k j) [0..<m])"
    using entry_double[OF is_rect_id_mat[OF m0] n_rows_id_mat cI rA nA cA m0 i j] .
  have hsum: "sum_list (map (\<lambda>k. entry (id_mat m) i k * entry A k j) [0..<m])
      = sum_list (map (\<lambda>k. (if k = i then (1::int) else 0) * entry A k j) [0..<m])"
  proof (rule arg_cong[where f=sum_list])
    show "map (\<lambda>k. entry (id_mat m) i k * entry A k j) [0..<m]
        = map (\<lambda>k. (if k = i then (1::int) else 0) * entry A k j) [0..<m]"
    proof (rule map_cong[OF refl])
      fix k assume "k \<in> set [0..<m]"
      hence km: "k < m" by (simp add: set_upt)
      have e1: "entry (id_mat m) i k = (if k = i then 1 else 0)"
        using id_mat_nth[OF i km] by (simp add: entry_def)
      show "entry (id_mat m) i k * entry A k j
          = (if k = i then (1::int) else 0) * entry A k j"
        using e1 by simp
    qed
  qed
  have ydef: "(map (\<lambda>k. entry A k j) [0..<m]) = (map (\<lambda>k. entry A k j) [0..<m])" by simp
  have hmap: "sum_list (map (\<lambda>k. (if k = i then (1::int) else 0) * entry A k j) [0..<m])
      = sum_list (map (\<lambda>k. (if k = i then (1::int) else 0)
                        * (map (\<lambda>k. entry A k j) [0..<m]) ! k) [0..<m])"
  proof (rule arg_cong[where f=sum_list], rule map_cong[OF refl])
    fix k assume "k \<in> set [0..<m]"
    hence km: "k < m" by (simp add: set_upt)
    show "(if k = i then (1::int) else 0) * entry A k j
        = (if k = i then (1::int) else 0) * (map (\<lambda>k. entry A k j) [0..<m]) ! k"
      using km by (simp add: nth_map nth_upt)
  qed
  have hsel: "sum_list (map (\<lambda>k. (if k = i then (1::int) else 0)
                  * (map (\<lambda>k. entry A k j) [0..<m]) ! k) [0..<m])
      = (map (\<lambda>k. entry A k j) [0..<m]) ! i"
    by (rule sum_sel_one, simp add: i)
  have hnth: "(map (\<lambda>k. entry A k j) [0..<m]) ! i = entry A i j"
    using i by (simp add: nth_map nth_upt)
  show ?thesis using h1 hsum hmap hsel hnth by (simp add: entry_def)
qed

lemma cong_mat_mult_id_right:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m" and m0: "0 < m"
  shows "cong_q_mat (mat_mult_mod A (id_mat m)) A"
proof (rule cong_q_matI)
  fix i j
  assume hi: "i < n_rows (mat_mult_mod A (id_mat m))"
    and hj: "j < n_cols (mat_mult_mod A (id_mat m))"
  have im: "i < m" using hi nA by (simp add: n_rows_mod)
  have rI: "is_rect (id_mat m)" using m0 by (rule is_rect_id_mat)
  have cI: "n_cols (id_mat m) = m" using m0 by (rule n_cols_id_mat)
  have jm: "j < m" using hj nA cI m0 by (simp add: n_cols_mod)
  have e1: "entry (mat_mult_mod A (id_mat m)) i j
      = fq (entry (mat_mult A (id_mat m)) i j)"
    using entry_mat_mult_mod[OF rA nA cA rI n_rows_id_mat cI m0 im jm] .
  have e2: "entry (mat_mult A (id_mat m)) i j = entry A i j"
    using entry_id_right[OF rA nA cA m0 im jm] .
  have e3: "entry (mat_mult_mod A (id_mat m)) i j = fq (entry A i j)"
    using e1 e2 by simp
  show "cong_q (entry (mat_mult_mod A (id_mat m)) i j) (entry A i j)"
    using e3 by (simp add: cong_q_def)
qed

lemma cong_mat_mult_id_left:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m" and m0: "0 < m"
  shows "cong_q_mat (mat_mult_mod (id_mat m) A) A"
proof (rule cong_q_matI)
  fix i j
  assume hi: "i < n_rows (mat_mult_mod (id_mat m) A)"
    and hj: "j < n_cols (mat_mult_mod (id_mat m) A)"
  have rI: "is_rect (id_mat m)" using m0 by (rule is_rect_id_mat)
  have cI: "n_cols (id_mat m) = m" using m0 by (rule n_cols_id_mat)
  have im: "i < m" using hi m0 by (simp add: n_rows_mod)
  have jm: "j < m" using hj nA cA m0 by (simp add: n_cols_mod)
  have e1: "entry (mat_mult_mod (id_mat m) A) i j
      = fq (entry (mat_mult (id_mat m) A) i j)"
    using entry_mat_mult_mod[OF rI n_rows_id_mat cI rA nA cA m0 im jm] .
  have e2: "entry (mat_mult (id_mat m) A) i j = entry A i j"
    using entry_id_left[OF rA nA cA m0 im jm] .
  have e3: "entry (mat_mult_mod (id_mat m) A) i j = fq (entry A i j)"
    using e1 e2 by simp
  show "cong_q (entry (mat_mult_mod (id_mat m) A) i j) (entry A i j)"
    using e3 by (simp add: cong_q_def)
qed

lemma cong_q_mat_mult:
  assumes rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    and rB: "is_rect B" and nB: "n_rows B = m" and cB: "n_cols B = m"
    and rC: "is_rect C" and nC: "n_rows C = m" and cC: "n_cols C = m"
    and rD: "is_rect D" and nD: "n_rows D = m" and cD: "n_cols D = m"
    and m0: "0 < m" and AB: "cong_q_mat A B" and CD: "cong_q_mat C D"
  shows "cong_q_mat (mat_mult_mod A C) (mat_mult_mod B D)"
proof (rule cong_q_matI)
  fix i j
  assume hi: "i < n_rows (mat_mult_mod A C)"
    and hj: "j < n_cols (mat_mult_mod A C)"
  have im: "i < m" using hi nA by (simp add: n_rows_mod)
  have jm: "j < m" using hj nA cC m0 by (simp add: n_cols_mod)
  have eL: "entry (mat_mult_mod A C) i j
      = fq (sum_list (map (\<lambda>k. entry A i k * entry C k j) [0..<m]))"
  proof -
    have a: "entry (mat_mult_mod A C) i j = fq (entry (mat_mult A C) i j)"
      using entry_mat_mult_mod[OF rA nA cA rC nC cC m0 im jm] .
    have b: "entry (mat_mult A C) i j
        = sum_list (map (\<lambda>k. entry A i k * entry C k j) [0..<m])"
      using entry_double[OF rA nA cA rC nC cC m0 im jm] .
    show ?thesis using a b by simp
  qed
  have eR: "entry (mat_mult_mod B D) i j
      = fq (sum_list (map (\<lambda>k. entry B i k * entry D k j) [0..<m]))"
  proof -
    have a: "entry (mat_mult_mod B D) i j = fq (entry (mat_mult B D) i j)"
      using entry_mat_mult_mod[OF rB nB cB rD nD cD m0 im jm] .
    have b: "entry (mat_mult B D) i j
        = sum_list (map (\<lambda>k. entry B i k * entry D k j) [0..<m])"
      using entry_double[OF rB nB cB rD nD cD m0 im jm] .
    show ?thesis using a b by simp
  qed
  have mid: "fq (sum_list (map (\<lambda>k. entry A i k * entry C k j) [0..<m]))
      = fq (sum_list (map (\<lambda>k. entry B i k * entry D k j) [0..<m]))"
  proof (rule fq_sum_cong)
    fix k assume "k \<in> set [0..<m]"
    hence km: "k < m" by (simp add: set_upt)
    have kA: "k < n_cols A" using km cA by simp
    have kC: "k < n_cols C" using km cC by simp
    have iA: "i < n_rows A" using im nA by simp
    have h1: "cong_q (entry A i k) (entry B i k)" using AB iA kA by (rule cong_q_matD)
    have jC: "j < n_cols C" using jm cC by simp
    have kCr: "k < n_rows C" using km nC by simp
    have h2: "cong_q (entry C k j) (entry D k j)" using CD kCr jC by (rule cong_q_matD)
    have h1f: "fq (entry A i k) = fq (entry B i k)" using h1 by (simp add: cong_q_def)
    have h2f: "fq (entry C k j) = fq (entry D k j)" using h2 by (simp add: cong_q_def)
    show "fq (entry A i k * entry C k j) = fq (entry B i k * entry D k j)"
      using fq_cong_mult[OF h1f h2f] .
  qed
  show "cong_q (entry (mat_mult_mod A C) i j) (entry (mat_mult_mod B D) i j)"
    using eL eR mid by (simp add: cong_q_def)
qed

section \<open>Reduced matrices and the congruence-based notion of invertibility\<close>

definition reduced :: "mat \<Rightarrow> bool" where
  "reduced A = (\<forall>r \<in> set A. \<forall>x \<in> set r. 0 \<le> x \<and> x < 3329)"

lemma reducedD:
  assumes "reduced A" and "r \<in> set A" and "x \<in> set r"
  shows "0 \<le> x \<and> x < 3329"
  using assms by (simp add: reduced_def)

lemma reduced_id_mat: "reduced (id_mat m)"
  by (simp add: reduced_def id_mat_def)

lemma map2_fq_range:
  fixes k :: int
  shows "\<forall>x \<in> set (map2 (\<lambda>x y. fq (x + k * y)) us vs). 0 \<le> x \<and> x < 3329"
proof (induct us arbitrary: vs)
  case Nil
  show ?case by simp
next
  case (Cons a us)
  show ?case
  proof (cases vs)
    case Nil
    thus ?thesis by simp
  next
    case (Cons b vs)
    have h1: "0 \<le> fq (a + k * b) \<and> fq (a + k * b) < 3329" using fq_range by simp
    have h2: "\<forall>x \<in> set (map2 (\<lambda>x y. fq (x + k * y)) us vs). 0 \<le> x \<and> x < 3329"
      using Cons.hyps by simp
    show ?thesis using h1 h2 Cons by simp
  qed
qed

lemma reduced_add_row_mult:
  assumes red: "reduced A"
  shows "reduced (add_row_mult A i j k)"
proof (unfold reduced_def, intro ballI)
  let ?nr = "map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)"
  have upd: "add_row_mult A i j k = A[i := ?nr]" by (simp add: add_row_mult_def)
  have nrred: "\<forall>x \<in> set ?nr. 0 \<le> x \<and> x < 3329"
    using fq_range by auto
  fix r x
  assume rA: "r \<in> set (add_row_mult A i j k)" and xr: "x \<in> set r"
  have sub: "set (A[i := ?nr]) \<subseteq> insert ?nr (set A)"
    by (rule set_update_subset_insert)
  have rA2: "r \<in> set (A[i := ?nr])" using rA upd by simp
  have rin: "r \<in> insert ?nr (set A)" using sub rA2 by (meson in_mono)
  show "0 \<le> x \<and> x < 3329"
  proof (cases "r = ?nr")
    case True
    have xn: "x \<in> set ?nr" using xr True by simp
    with nrred show ?thesis by blast
  next
    case False
    have "r \<in> set A" using rin False by simp
    thus ?thesis using red xr by (simp add: reduced_def)
  qed
qed

text \<open>The restated notion of invertibility, as approved on 2026-10-21: a matrix is
  invertible over @{text F_q} when some square witness reproduces the identity up to
  the reduction congruence, on both sides.  Equality would be too strong, because the
  modular product always reduces its result and a witness need not be reduced.\<close>

definition invertible_mod :: "mat \<Rightarrow> bool" where
  "invertible_mod A =
     (\<exists>B. n_rows B = n_rows A \<and> n_cols B = n_rows A \<and> is_rect B \<and>
          cong_q_mat (mat_mult_mod A B) (id_mat (n_rows A)) \<and>
          cong_q_mat (mat_mult_mod B A) (id_mat (n_rows A)))"

lemma inv_id:
  assumes m0: "0 < m"
  shows "invertible_mod (id_mat m)"
proof -
  have rI: "is_rect (id_mat m)" using m0 by (rule is_rect_id_mat)
  have c1: "cong_q_mat (mat_mult_mod (id_mat m) (id_mat m)) (id_mat m)"
    using cong_mat_mult_id_left[OF rI n_rows_id_mat n_cols_id_mat[OF m0] m0] .
  have c2: "cong_q_mat (mat_mult_mod (id_mat m) (id_mat m)) (id_mat m)"
    using cong_mat_mult_id_right[OF rI n_rows_id_mat n_cols_id_mat[OF m0] m0] .
  show ?thesis
    by (unfold invertible_mod_def, intro exI[of _ "id_mat m"] conjI)
       (simp_all add: n_cols_id_mat[OF m0] rI c1 c2)
qed

lemma inv_sq_shape:
  assumes "invertible_mod A" and "n_rows A = m"
  shows "\<exists>B. n_rows B = m \<and> n_cols B = m \<and> is_rect B
            \<and> cong_q_mat (mat_mult_mod A B) (id_mat m)
            \<and> cong_q_mat (mat_mult_mod B A) (id_mat m)"
  using assms by (auto simp add: invertible_mod_def)

lemma sq_mult_left:
  assumes rX: "is_rect X" and nX: "n_rows X = m" and m0: "0 < m"
    and rY: "is_rect Y" and nY: "n_rows Y = m" and cY: "n_cols Y = m"
  shows "is_rect (mat_mult_mod X Y) \<and> n_rows (mat_mult_mod X Y) = m
       \<and> n_cols (mat_mult_mod X Y) = m"
proof -
  have ir: "is_rect (mat_mult_mod X Y)" using rX nX cY m0 by (rule is_rect_mod)
  have nr: "n_rows (mat_mult_mod X Y) = m" using nX by (simp add: n_rows_mod)
  have nc: "n_cols (mat_mult_mod X Y) = m" using nX cY m0 by (rule n_cols_mod)
  show ?thesis using ir nr nc by simp
qed

section \<open>Invertibility is preserved by a row addition\<close>

abbreviation sq :: "nat \<Rightarrow> mat \<Rightarrow> bool" where
  "sq m X \<equiv> (is_rect X \<and> n_rows X = m \<and> n_cols X = m)"

lemma sq_id [simp]:
  assumes m0: "0 < m"
  shows "sq m (id_mat m)"
proof -
  have r: "is_rect (id_mat m)" using m0 by (rule is_rect_id_mat)
  have c: "n_cols (id_mat m) = m" using m0 by (rule n_cols_id_mat)
  have n: "n_rows (id_mat m) = m" by (rule n_rows_id_mat)
  show ?thesis using r c n by simp
qed

lemma sq_row_add [simp]:
  assumes m0: "0 < m"
  shows "sq m (row_add_matrix m i j f)"
proof -
  have rows: "\<forall>r \<in> set (row_add_matrix m i j f). length r = m"
    by (auto simp add: row_add_matrix_def)
  have n: "n_rows (row_add_matrix m i j f) = m"
    by (simp add: n_rows_def row_add_matrix_def)
  have ne: "row_add_matrix m i j f \<noteq> []" using m0 by (simp add: row_add_matrix_def)
  have c: "n_cols (row_add_matrix m i j f) = m"
    using rows n ne m0 by (auto simp add: n_cols_def)
  have r: "is_rect (row_add_matrix m i j f)"
    using rows c by (simp add: is_rect_def)
  show ?thesis using r n c by simp
qed

lemma sq_mod [simp]:
  assumes sX: "sq m X" and sY: "sq m Y" and m0: "0 < m"
  shows "sq m (mat_mult_mod X Y)"
proof -
  have rX: "is_rect X" and nX: "n_rows X = m" and cX: "n_cols X = m" using sX by simp_all
  have rY: "is_rect Y" and nY: "n_rows Y = m" and cY: "n_cols Y = m" using sY by simp_all
  have r: "is_rect (mat_mult_mod X Y)" using rX nX cY m0 by (rule is_rect_mod)
  have n: "n_rows (mat_mult_mod X Y) = m" using nX by (simp add: n_rows_mod)
  have c: "n_cols (mat_mult_mod X Y) = m" using nX cY m0 by (rule n_cols_mod)
  show ?thesis using r n c by simp
qed

lemma sq_add_row:
  assumes sA: "sq m A" and im: "i < m" and jm: "j < m"
  shows "sq m (add_row_mult A i j k)"
proof -
  have rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m" using sA by simp_all
  have n: "n_rows (add_row_mult A i j k) = m"
    using nA by (simp add: n_rows_def add_row_mult_def)
  have leni: "length (A ! i) = m" using rA nA cA im is_rect_rows by simp
  have lenj: "length (A ! j) = m" using rA nA cA jm is_rect_rows by simp
  let ?nr = "map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)"
  have lennr: "length ?nr = m" using leni lenj by simp
  have upd: "add_row_mult A i j k = A[i := ?nr]" by (simp add: add_row_mult_def)
  have rows: "\<forall>r \<in> set (add_row_mult A i j k). length r = m"
  proof (intro ballI)
    fix r assume rA': "r \<in> set (add_row_mult A i j k)"
    have sub: "set (A[i := ?nr]) \<subseteq> insert ?nr (set A)"
      by (rule set_update_subset_insert)
    have rA2: "r \<in> set (A[i := ?nr])" using rA' upd by simp
    have rin: "r \<in> insert ?nr (set A)" using sub rA2 by (meson in_mono)
    show "length r = m"
    proof (cases "r = ?nr")
      case True
      thus ?thesis using lennr by simp
    next
      case False
      have "r \<in> set A" using rin False by simp
      thus ?thesis using rA cA by (simp add: is_rect_def)
    qed
  qed
  have c: "n_cols (add_row_mult A i j k) = m"
  proof -
    have len: "length (add_row_mult A i j k) = m" using n by (simp add: n_rows_def)
    have ne: "add_row_mult A i j k \<noteq> []"
    proof (cases "add_row_mult A i j k")
      case Nil
      thus ?thesis using len im by simp
    next
      case Cons
      thus ?thesis by simp
    qed
    have r0: "add_row_mult A i j k ! 0 \<in> set (add_row_mult A i j k)"
      using ne by simp
    have "length (add_row_mult A i j k ! 0) = m" using rows r0 by simp
    thus ?thesis using ne by (simp add: n_cols_def)
  qed
  have r: "is_rect (add_row_mult A i j k)" using rows c by (simp add: is_rect_def)
  show ?thesis using r n c by simp
qed

lemma cong_trans_sq:
  assumes sP: "sq m P" and sQ: "sq m Q" and sR: "sq m R"
    and PQ: "cong_q_mat P Q" and QR: "cong_q_mat Q R"
  shows "cong_q_mat P R"
  using cong_q_mat_trans[OF PQ QR] sP sQ sR by simp

lemma cong_mult_sq:
  assumes sP: "sq m P" and sQ: "sq m Q" and sR: "sq m R" and sS: "sq m S"
    and m0: "0 < m" and PQ: "cong_q_mat P Q" and RS: "cong_q_mat R S"
  shows "cong_q_mat (mat_mult_mod P R) (mat_mult_mod Q S)"
  using cong_q_mat_mult[OF _ _ _ _ _ _ _ _ _ _ _ _ m0 PQ RS] sP sQ sR sS by simp

lemma cong_id_left_sq:
  assumes sP: "sq m P" and m0: "0 < m"
  shows "cong_q_mat (mat_mult_mod (id_mat m) P) P"
  using cong_mat_mult_id_left[of P m] sP m0 by simp

lemma cong_id_right_sq:
  assumes sP: "sq m P" and m0: "0 < m"
  shows "cong_q_mat (mat_mult_mod P (id_mat m)) P"
  using cong_mat_mult_id_right[of P m] sP m0 by simp

lemma assoc_sq:
  assumes sP: "sq m P" and sQ: "sq m Q" and sR: "sq m R" and m0: "0 < m"
  shows "mat_mult_mod (mat_mult_mod P Q) R = mat_mult_mod P (mat_mult_mod Q R)"
  using mat_mult_mod_assoc[of P m Q R] sP sQ sR m0 by simp


lemma inv_nil [simp]:
  shows "invertible_mod []"
proof (unfold invertible_mod_def, intro exI[of _ "[]"] conjI)
  show "n_rows [] = n_rows []" by simp
  show "n_cols [] = n_rows []" by (simp add: n_cols_def n_rows_def)
  show "is_rect []" by (simp add: is_rect_def)
  show "cong_q_mat (mat_mult_mod [] []) (id_mat (n_rows []))"
    by (unfold cong_q_mat_def, simp add: n_rows_def mat_mult_mod_def mat_mult_def)
  show "cong_q_mat (mat_mult_mod [] []) (id_mat (n_rows []))"
    by (unfold cong_q_mat_def, simp add: n_rows_def mat_mult_mod_def mat_mult_def)
qed

lemma add_row_mult_nil [simp]:
  "add_row_mult [] i j k = []"
  by (simp add: add_row_mult_def)

lemma rim_iter_nil [simp]:
  "\<And>m s. fst (rim_iter f m [] s) = []"
proof (induct f)
  case 0
  show ?case by (simp add: rim_iter.simps)
next
  case (Suc f)
  obtain a s1 where d1: "next_u16_mod m s = (a, s1)"
    by (cases "next_u16_mod m s") auto
  obtain b s2 where d2: "next_u16_mod m s1 = (b, s2)"
    by (cases "next_u16_mod m s1") auto
  show ?case using Suc.hyps
    by (simp add: rim_iter.simps d1 d2 split: prod.split if_split)
qed

lemma inv_step:
  assumes im: "i < m" and jm: "j < m" and ij: "i \<noteq> j"
    and sA: "sq m A" and redA: "reduced A" and invA: "invertible_mod A"
  shows "invertible_mod (add_row_mult A i j (int c))"
proof -
  have m0: "0 < m" using im by simp
  have rA: "is_rect A" and nA: "n_rows A = m" and cA: "n_cols A = m"
    using sA by simp_all
  have redA': "\<forall>r \<in> set A. \<forall>x \<in> set r. 0 \<le> x \<and> x < 3329"
    using redA by (simp add: reduced_def)
  obtain B where hBn: "n_rows B = m" and hBc: "n_cols B = m" and rB: "is_rect B"
    and hAB: "cong_q_mat (mat_mult_mod A B) (id_mat m)"
    and hBA: "cong_q_mat (mat_mult_mod B A) (id_mat m)"
    using inv_sq_shape[OF invA nA] by blast
  have sB: "sq m B" using hBn hBc rB by simp
  let ?E = "row_add_matrix m i j (int c)"
  let ?Ei = "row_add_matrix m i j (- int c)"
  let ?A' = "add_row_mult A i j (int c)"
  let ?W = "mat_mult_mod B ?Ei"
  have sE: "sq m ?E" using m0 by (rule sq_row_add)
  have sEi: "sq m ?Ei" using m0 by (rule sq_row_add)
  have cEi: "n_cols ?Ei = m" using sEi by simp
  have nEi: "n_rows ?Ei = m" using sEi by simp
  have sI: "sq m (id_mat m)" using m0 by (rule sq_id)
  have sA': "sq m ?A'" using sq_add_row[OF sA im jm] .
  have sW: "sq m ?W" using sB sEi m0 by (rule sq_mod)
  have sAB: "sq m (mat_mult_mod A B)" using sA sB m0 by (rule sq_mod)
  have sIE: "sq m (mat_mult_mod ?Ei ?E)" using sEi sE m0 by (rule sq_mod)
  have sABEi: "sq m (mat_mult_mod (mat_mult_mod A B) ?Ei)"
    using sAB sEi m0 by (rule sq_mod)
  have rEE: "cong_q_mat ?Ei ?Ei" by (rule cong_q_mat_refl)
  have rEE' : "cong_q_mat (row_add_matrix m i j (- int c))
      (row_add_matrix m i j (- int c))" by (rule cong_q_mat_refl)
  have rAA: "cong_q_mat A A" by (rule cong_q_mat_refl)
  have rBB: "cong_q_mat B B" by (rule cong_q_mat_refl)
  have rEE2: "cong_q_mat (row_add_matrix m i j (int c))
      (row_add_matrix m i j (int c))" by (rule cong_q_mat_refl)
  have hbr: "mat_mult_mod ?E A = ?A'"
    using mat_mult_mod_row_add[OF im jm ij nA rA redA', of "int c"] .
  have hEI: "mat_mult_mod ?E ?Ei = id_mat m"
    using mat_mult_mod_elem_inverse[OF im jm ij, of "int c"] .
  have hIE: "mat_mult_mod ?Ei ?E = id_mat m"
    using mat_mult_mod_elem_inverse[OF im jm ij, of "- int c"] by simp
  have cIE: "cong_q_mat (mat_mult_mod ?Ei ?E) (id_mat m)"
    using hIE by (simp add: cong_q_mat_refl)
  have cEI: "cong_q_mat (mat_mult_mod ?E ?Ei) (id_mat m)"
    using hEI by (simp add: cong_q_mat_refl)
  have nA': "n_rows ?A' = m" using nA by (simp add: n_rows_def add_row_mult_def)

  have h1: "cong_q_mat (mat_mult_mod ?A' ?W) (id_mat m)"
  proof -
    have a1: "mat_mult_mod ?A' ?W = mat_mult_mod (mat_mult_mod ?E A) ?W"
      using hbr by simp
    have a2: "mat_mult_mod (mat_mult_mod ?E A) ?W
        = mat_mult_mod ?E (mat_mult_mod A ?W)"
      using assoc_sq[OF sE sA sW m0] .
    have a3: "mat_mult_mod A ?W = mat_mult_mod (mat_mult_mod A B) ?Ei"
      using assoc_sq[OF sA sB sEi m0] by simp
    have sIA: "sq m (mat_mult_mod (id_mat m) ?Ei)" using sI sEi m0 by (rule sq_mod)
    have p1: "cong_q_mat (mat_mult_mod (mat_mult_mod A B) ?Ei)
        (mat_mult_mod (id_mat m) ?Ei)"
    proof (rule cong_mult_sq)
      show "sq m (mat_mult_mod A B)" using sAB .
      show "sq m (id_mat m)" using sI .
      show "sq m ?Ei" using sEi .
      show "sq m ?Ei" using sEi .
      show "0 < m" using m0 .
      show "cong_q_mat (mat_mult_mod A B) (id_mat m)" using hAB .
      show "cong_q_mat ?Ei ?Ei" using rEE .
    qed
    have p2: "cong_q_mat (mat_mult_mod (id_mat m) ?Ei) ?Ei"
      using cong_id_left_sq[OF sEi m0] .
    have p3: "cong_q_mat (mat_mult_mod (mat_mult_mod A B) ?Ei) ?Ei"
      using cong_trans_sq[OF sABEi sIA sEi p1 p2] .
    have sEp: "sq m (mat_mult_mod ?E (mat_mult_mod (mat_mult_mod A B) ?Ei))"
      using sE sABEi m0 by (rule sq_mod)
    have sEE: "sq m (mat_mult_mod ?E ?Ei)" using sE sEi m0 by (rule sq_mod)
    have p4: "cong_q_mat (mat_mult_mod ?E (mat_mult_mod (mat_mult_mod A B) ?Ei))
        (mat_mult_mod ?E ?Ei)"
    proof (rule cong_mult_sq)
      show "sq m ?E" using sE .
      show "sq m ?E" using sE .
      show "sq m (mat_mult_mod (mat_mult_mod A B) ?Ei)" using sABEi .
      show "sq m ?Ei" using sEi .
      show "0 < m" using m0 .
      show "cong_q_mat ?E ?E" using rEE2 .
      show "cong_q_mat (mat_mult_mod (mat_mult_mod A B) ?Ei) ?Ei" using p3 .
    qed
    have p5: "cong_q_mat (mat_mult_mod ?E (mat_mult_mod (mat_mult_mod A B) ?Ei))
        (id_mat m)"
      using cong_trans_sq[OF sEp sEE sI p4 cEI] .
    show ?thesis
    proof (subst a1, subst a2, subst a3)
      show "cong_q_mat (mat_mult_mod ?E (mat_mult_mod (mat_mult_mod A B) ?Ei))
          (id_mat m)" using p5 .
    qed
  qed

  have h2: "cong_q_mat (mat_mult_mod ?W ?A') (id_mat m)"
  proof -
    have b1: "mat_mult_mod ?W ?A' = mat_mult_mod (mat_mult_mod B ?Ei) ?A'" by simp
    have b2: "mat_mult_mod (mat_mult_mod B ?Ei) ?A'
        = mat_mult_mod B (mat_mult_mod ?Ei ?A')"
      using assoc_sq[OF sB sEi sA' m0] .
    have b3: "mat_mult_mod ?Ei ?A' = mat_mult_mod ?Ei (mat_mult_mod ?E A)"
      using hbr by (simp only: hbr[symmetric])
    have b4: "mat_mult_mod ?Ei (mat_mult_mod ?E A) = mat_mult_mod (mat_mult_mod ?Ei ?E) A"
      using assoc_sq[OF sEi sE sA m0] by simp
    have sIA2: "sq m (mat_mult_mod (id_mat m) A)" using sI sA m0 by (rule sq_mod)
    have q1: "cong_q_mat (mat_mult_mod (mat_mult_mod ?Ei ?E) A)
        (mat_mult_mod (id_mat m) A)"
    proof (rule cong_mult_sq)
      show "sq m (mat_mult_mod ?Ei ?E)" using sIE .
      show "sq m (id_mat m)" using sI .
      show "sq m A" using sA .
      show "sq m A" using sA .
      show "0 < m" using m0 .
      show "cong_q_mat (mat_mult_mod ?Ei ?E) (id_mat m)" using cIE .
      show "cong_q_mat A A" using rAA .
    qed
    have q2: "cong_q_mat (mat_mult_mod (id_mat m) A) A"
      using cong_id_left_sq[OF sA m0] .
    have sIEA: "sq m (mat_mult_mod (mat_mult_mod ?Ei ?E) A)" using sIE sA m0 by (rule sq_mod)
    have q3: "cong_q_mat (mat_mult_mod (mat_mult_mod ?Ei ?E) A) A"
      using cong_trans_sq[OF sIEA sIA2 sA q1 q2] .
    have sBq: "sq m (mat_mult_mod B (mat_mult_mod (mat_mult_mod ?Ei ?E) A))"
      using sB sIEA m0 by (rule sq_mod)
    have sBA: "sq m (mat_mult_mod B A)" using sB sA m0 by (rule sq_mod)
    have q4: "cong_q_mat (mat_mult_mod B (mat_mult_mod (mat_mult_mod ?Ei ?E) A))
        (mat_mult_mod B A)"
    proof (rule cong_mult_sq)
      show "sq m B" using sB .
      show "sq m B" using sB .
      show "sq m (mat_mult_mod (mat_mult_mod ?Ei ?E) A)" using sIEA .
      show "sq m A" using sA .
      show "0 < m" using m0 .
      show "cong_q_mat B B" using rBB .
      show "cong_q_mat (mat_mult_mod (mat_mult_mod ?Ei ?E) A) A" using q3 .
    qed
    have cBA: "cong_q_mat (mat_mult_mod B A) (id_mat m)" using hBA .
    have q5: "cong_q_mat (mat_mult_mod B (mat_mult_mod (mat_mult_mod ?Ei ?E) A))
        (id_mat m)"
      using cong_trans_sq[OF sBq sBA sI q4 cBA] .
    show ?thesis
    proof (subst b1, subst b2, subst b3, subst b4)
      show "cong_q_mat (mat_mult_mod B (mat_mult_mod (mat_mult_mod ?Ei ?E) A))
          (id_mat m)" using q5 .
    qed
  qed

  show ?thesis
  proof (unfold invertible_mod_def, intro exI[of _ ?W] conjI)
    show "n_rows ?W = n_rows ?A'" using hBn nA' by (simp add: n_rows_mod)
    have ncW: "n_cols ?W = m" using n_cols_mod[OF hBn cEi m0] .
    show "n_cols ?W = n_rows ?A'" using ncW nA' by simp
    show "is_rect ?W" using sW by simp
    show "cong_q_mat (mat_mult_mod ?A' ?W) (id_mat (n_rows ?A'))"
      using h1 nA' by (simp only: nA')
    show "cong_q_mat (mat_mult_mod ?W ?A') (id_mat (n_rows ?A'))"
      using h2 nA' by (simp only: nA')
  qed
qed

lemma rim_iter_inv:
  "\<And>A s. sq m A \<Longrightarrow> reduced A \<Longrightarrow> invertible_mod A
     \<Longrightarrow> invertible_mod (fst (rim_iter f m A s))"
proof (induct f)
  case 0
  have f0: "fst (rim_iter 0 m A s) = A" by (simp add: rim_iter.simps)
  thus ?case
  proof (subst f0)
    show "invertible_mod A" using "0.prems" by blast
  qed
next
  case (Suc f)
  show ?case
  proof (cases "m = 0")
    case True
    have sz: "n_rows A = 0" using Suc.prems(1) True by simp
    have Az: "A = []"
    proof (cases A)
      case Nil
      thus ?thesis .
    next
      case (Cons x xs)
      thus ?thesis using sz by (simp add: n_rows_def)
    qed
    have hz: "fst (rim_iter (Suc f) m A s) = []"
    proof -
      have one: "fst (rim_iter (Suc f) m A s) = fst (rim_iter (Suc f) m [] s)"
        using Az by (simp only: Az)
      have two: "fst (rim_iter (Suc f) m [] s) = []" by (simp only: rim_iter_nil)
      show ?thesis using one two by simp
    qed
    show ?thesis using hz by simp
  next
    case False
    have m0: "0 < m" using False by simp
    obtain i s1 where d1: "next_u16_mod m s = (i, s1)"
      by (cases "next_u16_mod m s") auto
    obtain j s2 where d2: "next_u16_mod m s1 = (j, s2)"
      by (cases "next_u16_mod m s1") auto
    have im: "i < m" using d1 m0 next_u16_mod_lt[of m s] by simp
    have jm: "j < m" using d2 m0 next_u16_mod_lt[of m s1] by simp
    have u: "rim_iter (Suc f) m A s =
        (if i = j then rim_iter f m A s2
         else (let (c, s3) = randrange 1 3329 s2
               in rim_iter f m (add_row_mult A i j (int c)) s3))"
      by (simp add: rim_iter.simps d1 d2)
    show ?thesis
    proof (cases "i = j")
      case True
      have eq: "fst (rim_iter (Suc f) m A s) = fst (rim_iter f m A s2)"
        using u True by simp
      show ?thesis
      proof (subst eq)
        show "invertible_mod (fst (rim_iter f m A s2))"
          using Suc.hyps[OF Suc.prems(1) Suc.prems(2) Suc.prems(3)] .
      qed
    next
      case False
      obtain c s3 where d3: "randrange 1 3329 s2 = (c, s3)"
        by (cases "randrange 1 3329 s2") auto
      have eq: "fst (rim_iter (Suc f) m A s)
          = fst (rim_iter f m (add_row_mult A i j (int c)) s3)"
        using u False d3 by simp
      have sA': "sq m (add_row_mult A i j (int c))"
        using sq_add_row[OF Suc.prems(1) im jm] .
      have redA': "reduced (add_row_mult A i j (int c))"
        using reduced_add_row_mult[OF Suc.prems(2)] .
      have invA': "invertible_mod (add_row_mult A i j (int c))"
        using inv_step[OF im jm False Suc.prems(1) Suc.prems(2) Suc.prems(3)] .
      show ?thesis
      proof (subst eq)
        show "invertible_mod (fst (rim_iter f m (add_row_mult A i j (int c)) s3))"
          using Suc.hyps[OF sA' redA' invA'] .
      qed
    qed
  qed
qed

(* seg: rowops-batch1 *)
section \<open>Elementary row operations as left multiplication\<close>

text \<open>The row operations in @{text VWZ_RREF} reduce modulo 3329 inside the
operation (@{text scale_row} applies @{text fq}, @{text add_row_mult} applies
@{text fq}).  The integer product @{text mat_mult} does not reduce, so an
equality against @{text mat_mult} cannot hold in general; the correct
statement lives in the modular product @{text mat_mult_mod} and needs the
subject matrix to be @{text reduced}, i.e. already normalised.\<close>

definition uvec :: "nat \<Rightarrow> nat \<Rightarrow> int list" where
  "uvec n k = map (\<lambda>col. if col = k then (1::int) else 0) [0..<n]"

definition svec :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "svec n k c = map (\<lambda>col. if col = k then c else 0) [0..<n]"

lemma uvec_len [simp]: "length (uvec n k) = n"
  by (simp add: uvec_def)

lemma svec_len [simp]: "length (svec n k c) = n"
  by (simp add: svec_def)

lemma fq_row_id:
  assumes "\<forall>x \<in> set r. 0 \<le> x \<and> x < 3329"
  shows "map fq r = r"
  using assms
proof (induct r)
  case Nil show ?case by simp
next
  case (Cons a r)
  have ha: "fq a = a" using Cons.prems fq_reduced by auto
  have hr: "map fq r = r" using Cons.prems Cons.hyps by auto
  show ?case using ha hr by simp
qed

lemma id_mat_row:
  assumes r: "r < m"
  shows "id_mat m ! r = uvec m r"
proof -
  have "id_mat m ! r = map (\<lambda>j. if r = j then (1::int) else 0) [0..<m]"
    using r by (simp add: id_mat_def nth_map)
  also have "\<dots> = uvec m r"
  proof (unfold uvec_def)
    show "map (\<lambda>j. if r = j then (1::int) else 0) [0..<m]
        = map (\<lambda>col. if col = r then (1::int) else 0) [0..<m]"
    proof (rule map_cong[OF refl])
      fix j assume "j \<in> set [0..<m]"
      show "(if r = j then (1::int) else 0) = (if j = r then (1::int) else 0)"
        by (cases "r = j") simp_all
    qed
  qed
  finally show ?thesis .
qed

lemma swap_rows_nth:
  assumes r: "r < length A" and i: "i < length A" and j: "j < length A"
  shows "swap_rows A i j ! r = (if r = i then A ! j else (if r = j then A ! i else A ! r))"
proof (cases "i = j")
  case True
  then show ?thesis using r i by (simp add: swap_rows_def)
next
  case False
  show ?thesis
  proof (cases "r = i")
    case True
    with False r i j show ?thesis by (simp add: swap_rows_def nth_list_update_neq nth_list_update)
  next
    case False
    show ?thesis
    proof (cases "r = j")
      case True
      with False r i j show ?thesis by (simp add: swap_rows_def nth_list_update)
    next
      case False
      with r i j show ?thesis by (simp add: swap_rows_def nth_list_update_neq)
    qed
  qed
qed

lemma row_mat_mult_mod:
  assumes r: "r < n_rows A"
  shows "mat_mult_mod A B ! r = map (\<lambda>j. fq (dot (row_vec A r) (col_vec B j))) [0..<n_cols B]"
proof -
  have len: "r < length (mat_mult A B)" using r by (simp add: mat_len n_rows_def)
  have h1: "mat_mult_mod A B ! r = map fq ((mat_mult A B) ! r)"
    using len by (simp add: mat_mult_mod_def nth_map)
  have h2: "(mat_mult A B) ! r = map (\<lambda>j. dot (row_vec A r) (col_vec B j)) [0..<n_cols B]"
    using r by (simp add: mat_mult_def nth_map n_rows_def)
  show ?thesis using h1 h2 by simp
qed

lemma dot_uvec_col:
  assumes km: "k < m" and lenA: "length A = m"
  shows "dot (uvec m k) (col_vec A d) = A ! k ! d"
proof -
  have ylen: "length (col_vec A d) = m" by (simp add: col_vec_def lenA)
  have "dot (uvec m k) (col_vec A d) = col_vec A d ! k"
    using km ylen unfolding uvec_def by (rule dot_unit_row)
  also have "\<dots> = A ! k ! d" using km lenA by (simp add: col_vec_def nth_map)
  finally show ?thesis .
qed

lemma dot_svec_col:
  assumes km: "k < m" and lenA: "length A = m"
  shows "dot (svec m k c) (col_vec A d) = c * (A ! k ! d)"
proof -
  let ?y = "col_vec A d"
  have ylen: "length ?y = m" by (simp add: col_vec_def lenA)
  have xs: "length (svec m k c) = m" by (simp add: svec_def)
  have conv: "map2 (*) (svec m k c) ?y = map (\<lambda>l. (svec m k c) ! l * ?y ! l) [0..<m]"
    using xs ylen by (rule map2_conv_idx)
  have ent: "\<And>l. l < m \<Longrightarrow> (svec m k c) ! l * ?y ! l
      = c * ((if l = k then (1::int) else 0) * ?y ! l)"
  proof -
    fix l assume lm: "l < m"
    have e: "(svec m k c) ! l = (if l = k then c else 0)"
      using lm km by (simp add: svec_def nth_map)
    show "(svec m k c) ! l * ?y ! l
        = c * ((if l = k then (1::int) else 0) * ?y ! l)"
      using e by (cases "l = k") simp_all
  qed
  have eq: "map (\<lambda>l. (svec m k c) ! l * ?y ! l) [0..<m]
      = map (\<lambda>l. c * ((if l = k then (1::int) else 0) * ?y ! l)) [0..<m]"
  proof (rule map_cong[OF refl])
    fix l assume lin: "l \<in> set [0..<m]"
    hence lm: "l < m" by simp
    show "(svec m k c) ! l * ?y ! l
        = c * ((if l = k then (1::int) else 0) * ?y ! l)"
      using ent[OF lm] .
  qed
  have sum: "sum_list (map (\<lambda>l. c * ((if l = k then (1::int) else 0) * ?y ! l)) [0..<m])
      = c * ?y ! k"
    using sum_sel_scaled[OF km] .
  have "dot (svec m k c) ?y = sum_list (map2 (*) (svec m k c) ?y)"
    by (simp add: dot_def)
  also have "\<dots> = sum_list (map (\<lambda>l. c * ((if l = k then (1::int) else 0) * ?y ! l)) [0..<m])"
    using conv eq by simp
  also have "\<dots> = c * ?y ! k" using sum .
  also have "\<dots> = c * (A ! k ! d)" using km lenA by (simp add: col_vec_def nth_map)
  finally show ?thesis .
qed

(* seg: rowops-batch2 *)
lemma nth_row_swap_matrix_i:
  assumes im: "i < m"
  shows "row_swap_matrix m i j ! i = uvec m j"
proof (rule nth_equalityI)
  show "length (row_swap_matrix m i j ! i) = length (uvec m j)"
    using im by (simp add: row_swap_matrix_def uvec_def)
  fix c assume c: "c < length (row_swap_matrix m i j ! i)"
  hence cm: "c < m" using im by (simp add: row_swap_matrix_def)
  show "row_swap_matrix m i j ! i ! c = uvec m j ! c"
    using im cm by (simp add: row_swap_matrix_def uvec_def nth_map)
qed

lemma nth_row_swap_matrix_j:
  assumes jm: "j < m"
  shows "row_swap_matrix m i j ! j = uvec m i"
proof (rule nth_equalityI)
  show "length (row_swap_matrix m i j ! j) = length (uvec m i)"
    using jm by (simp add: row_swap_matrix_def uvec_def)
  fix c assume c: "c < length (row_swap_matrix m i j ! j)"
  hence cm: "c < m" using jm by (simp add: row_swap_matrix_def)
  show "row_swap_matrix m i j ! j ! c = uvec m i ! c"
    using jm cm by (simp add: row_swap_matrix_def uvec_def nth_map)
qed

lemma nth_row_swap_matrix_other:
  assumes rm: "r < m" and ri: "r \<noteq> i" and rj: "r \<noteq> j"
  shows "row_swap_matrix m i j ! r = uvec m r"
proof (rule nth_equalityI)
  show "length (row_swap_matrix m i j ! r) = length (uvec m r)"
    using rm by (simp add: row_swap_matrix_def uvec_def)
  fix c assume c: "c < length (row_swap_matrix m i j ! r)"
  hence cm: "c < m" using rm by (simp add: row_swap_matrix_def)
  have a: "(row_swap_matrix m i j ! r) ! c = (if r = c then (1::int) else 0)"
    using rm ri rj cm by (simp add: row_swap_matrix_def nth_map)
  have b: "uvec m r ! c = (if c = r then (1::int) else 0)"
    using cm by (simp add: uvec_def nth_map)
  show "row_swap_matrix m i j ! r ! c = uvec m r ! c"
    using a b by (cases "c = r") simp_all
qed

lemma nth_row_scale_matrix_i:
  assumes im: "i < m"
  shows "row_scale_matrix m i c ! i = svec m i c"
proof (rule nth_equalityI)
  show "length (row_scale_matrix m i c ! i) = length (svec m i c)"
    using im by (simp add: row_scale_matrix_def svec_def)
  fix col assume co: "col < length (row_scale_matrix m i c ! i)"
  hence cm: "col < m" using im by (simp add: row_scale_matrix_def)
  have a: "(row_scale_matrix m i c ! i) ! col
      = (if col = i then c else (if i = col then (1::int) else 0))"
    using im cm by (simp add: row_scale_matrix_def nth_map)
  have b: "svec m i c ! col = (if col = i then c else 0)"
    using cm by (simp add: svec_def nth_map)
  show "row_scale_matrix m i c ! i ! col = svec m i c ! col"
    using a b by (cases "col = i") simp_all
qed

lemma nth_row_scale_matrix_other:
  assumes rm: "r < m" and ri: "r \<noteq> i"
  shows "row_scale_matrix m i c ! r = uvec m r"
proof (rule nth_equalityI)
  show "length (row_scale_matrix m i c ! r) = length (uvec m r)"
    using rm by (simp add: row_scale_matrix_def uvec_def)
  fix col assume co: "col < length (row_scale_matrix m i c ! r)"
  hence cm: "col < m" using rm by (simp add: row_scale_matrix_def)
  have a: "(row_scale_matrix m i c ! r) ! col
      = (if r = col then (1::int) else 0)"
    using rm ri cm by (simp add: row_scale_matrix_def nth_map)
  have b: "uvec m r ! col = (if col = r then (1::int) else 0)"
    using cm by (simp add: uvec_def nth_map)
  show "row_scale_matrix m i c ! r ! col = uvec m r ! col"
    using a b by (cases "col = r") simp_all
qed

lemma mat_mult_mod_row_eq_uvec:
  assumes rm: "r < m" and EM: "n_rows M = m"
    and rectA: "is_rect A" and rowsA: "n_rows A = m" and redA: "reduced A"
    and e: "M ! r = uvec m k" and km: "k < m"
  shows "mat_mult_mod M A ! r = A ! k"
proof -
  have lenA: "length A = m" using rowsA by (simp add: n_rows_def)
  have klen: "length (A ! k) = n_cols A"
  proof (rule is_rect_rows)
    show "is_rect A" using rectA .
    show "k < n_rows A" using rowsA km by simp
  qed
  have h: "mat_mult_mod M A ! r
      = map (\<lambda>c. fq (dot (M ! r) (col_vec A c))) [0..<n_cols A]"
  proof -
    have rr: "r < n_rows M" using EM rm by simp
    have "mat_mult_mod M A ! r
        = map (\<lambda>j. fq (dot (row_vec M r) (col_vec A j))) [0..<n_cols A]"
      using rr by (rule row_mat_mult_mod)
    thus ?thesis by (simp add: row_vec_def)
  qed
  have step1: "map (\<lambda>c. fq (dot (M ! r) (col_vec A c))) [0..<n_cols A]
      = map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A]"
  proof (rule map_cong[OF refl])
    fix c assume cin: "c \<in> set [0..<n_cols A]"
    have d: "dot (M ! r) (col_vec A c) = A ! k ! c"
      using km lenA e by (simp add: dot_uvec_col)
    show "fq (dot (M ! r) (col_vec A c)) = fq (A ! k ! c)" using d by simp
  qed
  have step2: "map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A] = A ! k"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A]) = length (A ! k)"
      using klen by simp
    fix c assume c: "c < length (map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A])"
    hence cm: "c < n_cols A" by simp
    have rowin: "A ! k \<in> set A" using km rowsA by (simp add: n_rows_def nth_mem)
    have val: "A ! k ! c \<in> set (A ! k)"
    proof -
      have cl: "c < length (A ! k)" using cm klen by simp
      show ?thesis by (rule nth_mem[OF cl])
    qed
    have rng: "0 \<le> A ! k ! c \<and> A ! k ! c < 3329"
      using reducedD[OF redA rowin val] .
    have l: "map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A] ! c = fq (A ! k ! c)"
      using cm by (simp add: nth_map)
    have r: "fq (A ! k ! c) = A ! k ! c" using rng by (simp add: fq_reduced)
    show "map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A] ! c = A ! k ! c"
      using l r by simp
  qed
  have "mat_mult_mod M A ! r = map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A]"
    using h step1 by simp
  also have "\<dots> = A ! k" using step2 .
  finally show ?thesis .
qed

lemma mat_mult_mod_row_eq_svec:
  assumes rm: "r < m" and EM: "n_rows M = m"
    and rectA: "is_rect A" and rowsA: "n_rows A = m"
    and e: "M ! r = svec m k c" and km: "k < m"
  shows "mat_mult_mod M A ! r = map (\<lambda>x. fq (c * x)) (A ! k)"
proof -
  have lenA: "length A = m" using rowsA by (simp add: n_rows_def)
  have klen: "length (A ! k) = n_cols A"
  proof (rule is_rect_rows)
    show "is_rect A" using rectA .
    show "k < n_rows A" using rowsA km by simp
  qed
  have h: "mat_mult_mod M A ! r
      = map (\<lambda>d. fq (dot (M ! r) (col_vec A d))) [0..<n_cols A]"
  proof -
    have rr: "r < n_rows M" using EM rm by simp
    have "mat_mult_mod M A ! r
        = map (\<lambda>j. fq (dot (row_vec M r) (col_vec A j))) [0..<n_cols A]"
      using rr by (rule row_mat_mult_mod)
    thus ?thesis by (simp add: row_vec_def)
  qed
  have step1: "map (\<lambda>d. fq (dot (M ! r) (col_vec A d))) [0..<n_cols A]
      = map (\<lambda>d. fq (c * (A ! k ! d))) [0..<n_cols A]"
  proof (rule map_cong[OF refl])
    fix d assume din: "d \<in> set [0..<n_cols A]"
    have dd: "dot (M ! r) (col_vec A d) = c * (A ! k ! d)"
      using km lenA e by (simp add: dot_svec_col)
    show "fq (dot (M ! r) (col_vec A d)) = fq (c * (A ! k ! d))" using dd by simp
  qed
  have step2: "map (\<lambda>d. fq (c * (A ! k ! d))) [0..<n_cols A]
      = map (\<lambda>x. fq (c * x)) (A ! k)"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>d. fq (c * (A ! k ! d))) [0..<n_cols A])
        = length (map (\<lambda>x. fq (c * x)) (A ! k))"
      using klen by simp
    fix d assume d: "d < length (map (\<lambda>d. fq (c * (A ! k ! d))) [0..<n_cols A])"
    hence dm: "d < n_cols A" by simp
    have l: "map (\<lambda>d. fq (c * (A ! k ! d))) [0..<n_cols A] ! d = fq (c * (A ! k ! d))"
      using dm by (simp add: nth_map)
    have r: "map (\<lambda>x. fq (c * x)) (A ! k) ! d = fq (c * (A ! k ! d))"
      using dm klen by (simp add: nth_map)
    show "map (\<lambda>d. fq (c * (A ! k ! d))) [0..<n_cols A] ! d
        = map (\<lambda>x. fq (c * x)) (A ! k) ! d"
      using l r by simp
  qed
  have "mat_mult_mod M A ! r = map (\<lambda>d. fq (c * (A ! k ! d))) [0..<n_cols A]"
    using h step1 by simp
  also have "\<dots> = map (\<lambda>x. fq (c * x)) (A ! k)" using step2 .
  finally show ?thesis .
qed

lemma reduced_row_swap_matrix [simp]:
  shows "reduced (row_swap_matrix m i j)"
  by (auto simp add: reduced_def row_swap_matrix_def split: if_split)

lemma is_rect_row_swap_matrix [simp]:
  shows "is_rect (row_swap_matrix m i j)"
proof (cases "m = 0")
  case True
  then show ?thesis by (simp add: row_swap_matrix_def is_rect_def)
next
  case False
  hence m0: "0 < m" by simp
  have nc: "n_cols (row_swap_matrix m i j) = m"
    using m0 by (simp add: n_cols_def row_swap_matrix_def)
  show ?thesis
    unfolding is_rect_def using nc by (simp add: row_swap_matrix_def)
qed

(* seg: rowops-batch3 *)
lemma swap_rows_self:
  assumes i: "i < length A"
  shows "swap_rows A i i = A"
proof (rule nth_equalityI)
  show "length (swap_rows A i i) = length A" using i by (simp add: swap_rows_def)
  fix r assume r: "r < length (swap_rows A i i)"
  have rA: "r < length A" using r i by (simp add: swap_rows_def)
  show "swap_rows A i i ! r = A ! r"
  proof (cases "r = i")
    case True
    thus ?thesis using i rA by (simp add: swap_rows_def)
  next
    case False
    thus ?thesis using i rA by (simp add: swap_rows_def nth_list_update_neq)
  qed
qed

lemma mat_mult_mod_row_eq_swap_row:
  assumes rm: "r < m" and rectA: "is_rect A" and rowsA: "n_rows A = m" and redA: "reduced A"
    and e: "row_swap_matrix m i j ! r = uvec m k" and km: "k < m"
  shows "mat_mult_mod (row_swap_matrix m i j) A ! r = A ! k"
proof (rule mat_mult_mod_row_eq_uvec)
  show "r < m" using rm .
  show "n_rows (row_swap_matrix m i j) = m" by (simp add: n_rows_def row_swap_matrix_def)
  show "is_rect A" using rectA .
  show "n_rows A = m" using rowsA .
  show "reduced A" using redA .
  show "row_swap_matrix m i j ! r = uvec m k" using e .
  show "k < m" using km .
qed

lemma mat_mult_mod_row_swap:
  assumes im: "i < m" and jm: "j < m" and rowsA: "n_rows A = m"
    and rectA: "is_rect A" and redA: "reduced A"
  shows "mat_mult_mod (row_swap_matrix m i j) A = swap_rows A i j"
proof -
  let ?E = "row_swap_matrix m i j"
  have En: "n_rows ?E = m" by (simp add: n_rows_def row_swap_matrix_def)
  have lenA: "length A = m" using rowsA by (simp add: n_rows_def)
  have lenL: "length (mat_mult_mod ?E A) = m"
  proof -
    have "length (mat_mult_mod ?E A) = length (mat_mult ?E A)"
      by (simp add: mat_mult_mod_def)
    also have "\<dots> = n_rows ?E" by (simp add: mat_len)
    also have "\<dots> = m" using En .
    finally show ?thesis .
  qed
  have lenR: "length (swap_rows A i j) = m" using lenA by (simp add: swap_rows_def)
  show ?thesis
  proof (rule nth_equalityI)
    show "length (mat_mult_mod ?E A) = length (swap_rows A i j)" using lenL lenR by simp
    fix r assume rl: "r < length (mat_mult_mod ?E A)"
    hence rm: "r < m" using lenL by simp
    show "mat_mult_mod ?E A ! r = swap_rows A i j ! r"
    proof (cases "i = j")
      case True
      have E_id: "?E = id_mat m" using True by (simp add: aux_rref_swap_self)
      have row: "mat_mult_mod ?E A ! r = A ! r"
      proof (rule mat_mult_mod_row_eq_swap_row)
        show "r < m" using rm .
        show "is_rect A" using rectA .
        show "n_rows A = m" using rowsA .
        show "reduced A" using redA .
        show "?E ! r = uvec m r" using rm E_id by (simp add: id_mat_row)
        show "r < m" using rm .
      qed
      have srow: "swap_rows A i j ! r = A ! r" using True im lenA by (simp add: swap_rows_self)
      with row show ?thesis by simp
    next
      case False
      have ij: "i \<noteq> j" using False by simp
      show ?thesis
      proof (cases "r = i")
        case True
        have row: "mat_mult_mod ?E A ! r = A ! j"
        proof (rule mat_mult_mod_row_eq_swap_row)
          show "r < m" using rm .
          show "is_rect A" using rectA .
          show "n_rows A = m" using rowsA .
          show "reduced A" using redA .
          show "?E ! r = uvec m j" using True im by (simp add: nth_row_swap_matrix_i)
          show "j < m" using jm .
        qed
        have srow: "swap_rows A i j ! r = A ! j"
          using True ij rm lenA im jm by (simp add: swap_rows_nth)
        with row show ?thesis by simp
      next
        case False
        have ri: "r \<noteq> i" using False by simp
        show ?thesis
        proof (cases "r = j")
          case True
          have row: "mat_mult_mod ?E A ! r = A ! i"
          proof (rule mat_mult_mod_row_eq_swap_row)
            show "r < m" using rm .
            show "is_rect A" using rectA .
            show "n_rows A = m" using rowsA .
            show "reduced A" using redA .
            show "?E ! r = uvec m i" using True jm by (simp add: nth_row_swap_matrix_j)
            show "i < m" using im .
          qed
          have srow: "swap_rows A i j ! r = A ! i"
            using True ri rm lenA im jm by (simp add: swap_rows_nth)
          with row show ?thesis by simp
        next
          case False
          have rj: "r \<noteq> j" using False by simp
          have row: "mat_mult_mod ?E A ! r = A ! r"
          proof (rule mat_mult_mod_row_eq_swap_row)
            show "r < m" using rm .
            show "is_rect A" using rectA .
            show "n_rows A = m" using rowsA .
            show "reduced A" using redA .
            show "?E ! r = uvec m r"
              using rm ri rj by (simp add: nth_row_swap_matrix_other)
            show "r < m" using rm .
          qed
          have srow: "swap_rows A i j ! r = A ! r"
            using ri rj rm lenA im jm by (simp add: swap_rows_nth)
          with row show ?thesis by simp
        qed
      qed
    qed
  qed
qed

lemma swap_rows_row_swap_matrix_id:
  assumes im: "i < m" and jm: "j < m"
  shows "swap_rows (row_swap_matrix m i j) i j = id_mat m"
proof -
  let ?E = "row_swap_matrix m i j"
  have En: "n_rows ?E = m" by (simp add: n_rows_def row_swap_matrix_def)
  have lenE: "length ?E = m" using En by (simp add: n_rows_def)
  show ?thesis
  proof (rule nth_equalityI)
    show "length (swap_rows ?E i j) = length (id_mat m)"
      using lenE by (simp add: swap_rows_def id_mat_def)
    fix r assume rl: "r < length (swap_rows ?E i j)"
    hence rm: "r < m" using lenE by (simp add: swap_rows_def)
    show "swap_rows ?E i j ! r = id_mat m ! r"
    proof (cases "i = j")
      case True
      have E_id: "?E = id_mat m" using True by (simp add: aux_rref_swap_self)
      have "swap_rows ?E i j ! r = ?E ! r" using True im lenE by (simp add: swap_rows_self)
      also have "\<dots> = id_mat m ! r" using E_id by simp
      finally show ?thesis .
    next
      case False
      have ij: "i \<noteq> j" using False by simp
      show ?thesis
      proof (cases "r = i")
        case True
        have "swap_rows ?E i j ! r = ?E ! j"
          using True ij rm lenE im jm by (simp add: swap_rows_nth)
        also have "\<dots> = uvec m i" using jm by (simp add: nth_row_swap_matrix_j)
        also have "\<dots> = id_mat m ! i" using im by (simp add: id_mat_row)
        finally show ?thesis using True by simp
      next
        case False
        have ri: "r \<noteq> i" using False by simp
        show ?thesis
        proof (cases "r = j")
          case True
          have "swap_rows ?E i j ! r = ?E ! i"
            using True ri rm lenE im jm by (simp add: swap_rows_nth)
          also have "\<dots> = uvec m j" using im by (simp add: nth_row_swap_matrix_i)
          also have "\<dots> = id_mat m ! j" using jm by (simp add: id_mat_row)
          finally show ?thesis using True by simp
        next
          case False
          have rj: "r \<noteq> j" using False by simp
          have "swap_rows ?E i j ! r = ?E ! r"
            using ri rj rm lenE im jm by (simp add: swap_rows_nth)
          also have "\<dots> = uvec m r" using rm ri rj by (simp add: nth_row_swap_matrix_other)
          also have "\<dots> = id_mat m ! r" using rm by (simp add: id_mat_row)
          finally show ?thesis .
        qed
      qed
    qed
  qed
qed

lemma row_swap_matrix_invertible_mod:
  assumes im: "i < m" and jm: "j < m"
  shows "invertible_mod (row_swap_matrix m i j)"
proof -
  let ?E = "row_swap_matrix m i j"
  have m0: "0 < m" using im by simp
  have En: "n_rows ?E = m" by (simp add: n_rows_def row_swap_matrix_def)
  have idE: "mat_mult_mod ?E ?E = id_mat m"
  proof -
    have "mat_mult_mod ?E ?E = swap_rows ?E i j"
      by (rule mat_mult_mod_row_swap[OF im jm En is_rect_row_swap_matrix reduced_row_swap_matrix])
    also have "\<dots> = id_mat m" by (rule swap_rows_row_swap_matrix_id[OF im jm])
    finally show ?thesis .
  qed
  show ?thesis
    unfolding invertible_mod_def
  proof (intro exI[of _ ?E] conjI)
    show "n_rows ?E = n_rows ?E" by simp
    show "n_cols ?E = n_rows ?E" using m0 En by (simp add: n_cols_def row_swap_matrix_def)
    show "is_rect ?E" by simp
    show "cong_q_mat (mat_mult_mod ?E ?E) (id_mat (n_rows ?E))" using idE En by (simp add: cong_q_mat_eq)
    show "cong_q_mat (mat_mult_mod ?E ?E) (id_mat (n_rows ?E))" using idE En by (simp add: cong_q_mat_eq)
  qed
qed

(* seg: rowops-batch4 *)
lemma is_rect_row_scale_matrix [simp]:
  shows "is_rect (row_scale_matrix m i c)"
proof (cases "m = 0")
  case True
  then show ?thesis by (simp add: row_scale_matrix_def is_rect_def)
next
  case False
  hence m0: "0 < m" by simp
  have nc: "n_cols (row_scale_matrix m i c) = m"
    using m0 by (simp add: n_cols_def row_scale_matrix_def)
  show ?thesis
    unfolding is_rect_def using nc by (simp add: row_scale_matrix_def)
qed

lemma map_fq_uvec [simp]: "map fq (uvec m k) = uvec m k"
proof (rule nth_equalityI)
  show "length (map fq (uvec m k)) = length (uvec m k)" by simp
  fix c assume c: "c < length (map fq (uvec m k))"
  hence cm: "c < m" by (simp add: uvec_def)
  have l: "map fq (uvec m k) ! c = fq (uvec m k ! c)"
    using cm by (simp add: uvec_def nth_map)
  have r: "uvec m k ! c = (if c = k then (1::int) else 0)"
    using cm by (simp add: uvec_def nth_map)
  show "map fq (uvec m k) ! c = uvec m k ! c"
    using l r by (cases "c = k") simp_all
qed

lemma mat_mult_mod_row_eq_uvec_fq:
  assumes rm: "r < m" and EM: "n_rows M = m"
    and rectA: "is_rect A" and rowsA: "n_rows A = m"
    and e: "M ! r = uvec m k" and km: "k < m"
  shows "mat_mult_mod M A ! r = map fq (A ! k)"
proof -
  have lenA: "length A = m" using rowsA by (simp add: n_rows_def)
  have klen: "length (A ! k) = n_cols A"
  proof (rule is_rect_rows)
    show "is_rect A" using rectA .
    show "k < n_rows A" using rowsA km by simp
  qed
  have h: "mat_mult_mod M A ! r
      = map (\<lambda>c. fq (dot (M ! r) (col_vec A c))) [0..<n_cols A]"
  proof -
    have rr: "r < n_rows M" using EM rm by simp
    have "mat_mult_mod M A ! r
        = map (\<lambda>j. fq (dot (row_vec M r) (col_vec A j))) [0..<n_cols A]"
      using rr by (rule row_mat_mult_mod)
    thus ?thesis by (simp add: row_vec_def)
  qed
  have step1: "map (\<lambda>c. fq (dot (M ! r) (col_vec A c))) [0..<n_cols A]
      = map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A]"
  proof (rule map_cong[OF refl])
    fix c assume cin: "c \<in> set [0..<n_cols A]"
    have d: "dot (M ! r) (col_vec A c) = A ! k ! c"
      using km lenA e by (simp add: dot_uvec_col)
    show "fq (dot (M ! r) (col_vec A c)) = fq (A ! k ! c)" using d by simp
  qed
  have step2: "map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A] = map fq (A ! k)"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A]) = length (map fq (A ! k))"
      using klen by simp
    fix c assume c: "c < length (map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A])"
    hence cm: "c < n_cols A" by simp
    have l: "map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A] ! c = fq (A ! k ! c)"
      using cm by (simp add: nth_map)
    have r: "map fq (A ! k) ! c = fq (A ! k ! c)"
      using cm klen by (simp add: nth_map)
    show "map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A] ! c = map fq (A ! k) ! c"
      using l r by simp
  qed
  have "mat_mult_mod M A ! r = map (\<lambda>c. fq (A ! k ! c)) [0..<n_cols A]"
    using h step1 by simp
  also have "\<dots> = map fq (A ! k)" using step2 .
  finally show ?thesis .
qed

lemma mat_mult_mod_row_scale:
  assumes im: "i < m" and rowsA: "n_rows A = m"
    and rectA: "is_rect A" and redA: "reduced A"
  shows "mat_mult_mod (row_scale_matrix m i c) A = scale_row A i c"
proof -
  let ?S = "row_scale_matrix m i c"
  have Sn: "n_rows ?S = m" by (simp add: n_rows_def row_scale_matrix_def)
  have lenA: "length A = m" using rowsA by (simp add: n_rows_def)
  have lenL: "length (mat_mult_mod ?S A) = m"
  proof -
    have "length (mat_mult_mod ?S A) = length (mat_mult ?S A)"
      by (simp add: mat_mult_mod_def)
    also have "\<dots> = n_rows ?S" by (simp add: mat_len)
    also have "\<dots> = m" using Sn .
    finally show ?thesis .
  qed
  have lenR: "length (scale_row A i c) = m" using lenA by (simp add: scale_row_def)
  show ?thesis
  proof (rule nth_equalityI)
    show "length (mat_mult_mod ?S A) = length (scale_row A i c)" using lenL lenR by simp
    fix r assume rl: "r < length (mat_mult_mod ?S A)"
    hence rm: "r < m" using lenL by simp
    show "mat_mult_mod ?S A ! r = scale_row A i c ! r"
    proof (cases "r = i")
      case True
      have row: "mat_mult_mod ?S A ! r = map (\<lambda>x. fq (c * x)) (A ! i)"
      proof (rule mat_mult_mod_row_eq_svec)
        show "r < m" using rm .
        show "n_rows ?S = m" using Sn .
        show "is_rect A" using rectA .
        show "n_rows A = m" using rowsA .
        show "?S ! r = svec m i c" using True im by (simp add: nth_row_scale_matrix_i)
        show "i < m" using im .
      qed
      have sz: "scale_row A i c ! r = map (\<lambda>x. fq (c * x)) (A ! i)"
        using True im lenA by (simp add: scale_row_def)
      with row show ?thesis by simp
    next
      case False
      have ri: "r \<noteq> i" using False by simp
      have row: "mat_mult_mod ?S A ! r = A ! r"
      proof (rule mat_mult_mod_row_eq_uvec)
        show "r < m" using rm .
        show "n_rows ?S = m" using Sn .
        show "is_rect A" using rectA .
        show "n_rows A = m" using rowsA .
        show "reduced A" using redA .
        show "?S ! r = uvec m r" using rm ri by (simp add: nth_row_scale_matrix_other)
        show "r < m" using rm .
      qed
      have sz: "scale_row A i c ! r = A ! r"
        using ri im lenA by (simp add: scale_row_def nth_list_update_neq)
      with row show ?thesis by simp
    qed
  qed
qed

lemma mat_mult_mod_row_scale_id:
  assumes im: "i < m" and unit: "fq (c * d) = 1"
  shows "mat_mult_mod (row_scale_matrix m i c) (row_scale_matrix m i d) = id_mat m"
proof -
  let ?Sc = "row_scale_matrix m i c"
  let ?Sd = "row_scale_matrix m i d"
  have Scn: "n_rows ?Sc = m" by (simp add: n_rows_def row_scale_matrix_def)
  have Sdn: "n_rows ?Sd = m" by (simp add: n_rows_def row_scale_matrix_def)
  have lenL: "length (mat_mult_mod ?Sc ?Sd) = m"
  proof -
    have "length (mat_mult_mod ?Sc ?Sd) = length (mat_mult ?Sc ?Sd)"
      by (simp add: mat_mult_mod_def)
    also have "\<dots> = n_rows ?Sc" by (simp add: mat_len)
    also have "\<dots> = m" using Scn .
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule nth_equalityI)
    show "length (mat_mult_mod ?Sc ?Sd) = length (id_mat m)"
      using lenL by (simp add: id_mat_def)
    fix r assume rl: "r < length (mat_mult_mod ?Sc ?Sd)"
    hence rm: "r < m" using lenL by simp
    show "mat_mult_mod ?Sc ?Sd ! r = id_mat m ! r"
    proof (cases "r = i")
      case True
      have rowf: "mat_mult_mod ?Sc ?Sd ! r = map (\<lambda>x. fq (c * x)) (?Sd ! i)"
      proof (rule mat_mult_mod_row_eq_svec)
        show "r < m" using rm .
        show "n_rows ?Sc = m" using Scn .
        show "is_rect ?Sd" by simp
        show "n_rows ?Sd = m" using Sdn .
        show "?Sc ! r = svec m i c" using True im by (simp add: nth_row_scale_matrix_i)
        show "i < m" using im .
      qed
      have sd: "?Sd ! i = svec m i d" using im by (simp add: nth_row_scale_matrix_i)
      have mapeq: "map (\<lambda>x. fq (c * x)) (svec m i d) = uvec m i"
      proof (rule nth_equalityI)
        show "length (map (\<lambda>x. fq (c * x)) (svec m i d)) = length (uvec m i)"
          by (simp add: svec_def uvec_def)
        fix col assume co: "col < length (map (\<lambda>x. fq (c * x)) (svec m i d))"
        hence cm: "col < m" by (simp add: svec_def)
        have l: "map (\<lambda>x. fq (c * x)) (svec m i d) ! col = fq (c * (svec m i d ! col))"
          using cm by (simp add: svec_def nth_map)
        have sv: "svec m i d ! col = (if col = i then d else 0)"
          using cm by (simp add: svec_def nth_map)
        have u: "uvec m i ! col = (if col = i then (1::int) else 0)"
          using cm by (simp add: uvec_def nth_map)
        show "map (\<lambda>x. fq (c * x)) (svec m i d) ! col = uvec m i ! col"
          using l sv u unit by (cases "col = i") simp_all
      qed
      have "mat_mult_mod ?Sc ?Sd ! r = uvec m i" using rowf sd mapeq by simp
      also have "\<dots> = id_mat m ! i" using im by (simp add: id_mat_row)
      finally show ?thesis using True by simp
    next
      case False
      have ri: "r \<noteq> i" using False by simp
      have rowf: "mat_mult_mod ?Sc ?Sd ! r = map fq (?Sd ! r)"
      proof (rule mat_mult_mod_row_eq_uvec_fq)
        show "r < m" using rm .
        show "n_rows ?Sc = m" using Scn .
        show "is_rect ?Sd" by simp
        show "n_rows ?Sd = m" using Sdn .
        show "?Sc ! r = uvec m r" using rm ri by (simp add: nth_row_scale_matrix_other)
        show "r < m" using rm .
      qed
      have sd: "?Sd ! r = uvec m r" using rm ri by (simp add: nth_row_scale_matrix_other)
      have "mat_mult_mod ?Sc ?Sd ! r = uvec m r" using rowf sd by simp
      also have "\<dots> = id_mat m ! r" using rm by (simp add: id_mat_row)
      finally show ?thesis .
    qed
  qed
qed

lemma invertible_modI:
  assumes a1: "n_rows B = n_rows A" and a2: "n_cols B = n_rows A"
    and a3: "is_rect B"
    and a4: "cong_q_mat (mat_mult_mod A B) (id_mat (n_rows A))"
    and a5: "cong_q_mat (mat_mult_mod B A) (id_mat (n_rows A))"
  shows "invertible_mod A"
proof -
  have "\<exists>B. n_rows B = n_rows A \<and> n_cols B = n_rows A \<and> is_rect B \<and>
      cong_q_mat (mat_mult_mod A B) (id_mat (n_rows A)) \<and>
      cong_q_mat (mat_mult_mod B A) (id_mat (n_rows A))"
  proof (rule exI[of _ B])
    show "n_rows B = n_rows A \<and> n_cols B = n_rows A \<and> is_rect B \<and>
        cong_q_mat (mat_mult_mod A B) (id_mat (n_rows A)) \<and>
        cong_q_mat (mat_mult_mod B A) (id_mat (n_rows A))"
      using a1 a2 a3 a4 a5 by simp
  qed
  thus ?thesis unfolding invertible_mod_def .
qed

lemma is_rect_row_add_matrix [simp]:
  shows "is_rect (row_add_matrix m i j f)"
proof (cases "m = 0")
  case True
  then show ?thesis by (simp add: row_add_matrix_def is_rect_def)
next
  case False
  hence m0: "0 < m" by simp
  have nc: "n_cols (row_add_matrix m i j f) = m"
    using m0 by (simp add: n_cols_def row_add_matrix_def)
  show ?thesis
    unfolding is_rect_def using nc by (simp add: row_add_matrix_def)
qed

lemma row_scale_matrix_invertible_mod:
  assumes im: "i < m" and unit: "fq (c * d) = 1"
  shows "invertible_mod (row_scale_matrix m i c)"
proof -
  let ?Sc = "row_scale_matrix m i c"
  let ?Sd = "row_scale_matrix m i d"
  have m0: "0 < m" using im by simp
  have Scn: "n_rows ?Sc = m" by (simp add: n_rows_def row_scale_matrix_def)
  have Sdn: "n_rows ?Sd = m" by (simp add: n_rows_def row_scale_matrix_def)
  have ncd: "n_cols ?Sd = m" using m0 by (simp add: n_cols_def row_scale_matrix_def)
  have comm: "d * c = c * d" by (rule mult.commute)
  have unit': "fq (d * c) = 1"
  proof (subst comm)
    show "fq (c * d) = 1" using unit .
  qed
  have L: "mat_mult_mod ?Sc ?Sd = id_mat m"
    by (rule mat_mult_mod_row_scale_id[OF im unit])
  have R: "mat_mult_mod ?Sd ?Sc = id_mat m"
    by (rule mat_mult_mod_row_scale_id[OF im unit'])
  have rc1: "cong_q_mat (mat_mult_mod ?Sc ?Sd) (id_mat m)" using L by (simp add: cong_q_mat_eq)
  have rc2: "cong_q_mat (mat_mult_mod ?Sd ?Sc) (id_mat m)" using R by (simp add: cong_q_mat_eq)
  have a1: "n_rows ?Sd = n_rows ?Sc" using Sdn Scn by simp
  have a2: "n_cols ?Sd = n_rows ?Sc" using ncd Scn by simp
  have a3: "is_rect ?Sd" by simp
  have a4: "cong_q_mat (mat_mult_mod ?Sc ?Sd) (id_mat (n_rows ?Sc))" using rc1 Scn by simp
  have a5: "cong_q_mat (mat_mult_mod ?Sd ?Sc) (id_mat (n_rows ?Sc))" using rc2 Scn by simp
  show ?thesis by (rule invertible_modI[OF a1 a2 a3 a4 a5])
qed

lemma row_add_matrix_invertible_mod:
  assumes im: "i < m" and jm: "j < m" and ij: "i \<noteq> j"
  shows "invertible_mod (row_add_matrix m i j f)"
proof -
  let ?E = "row_add_matrix m i j f"
  let ?F = "row_add_matrix m i j (- f)"
  have m0: "0 < m" using im by simp
  have En: "n_rows ?E = m" by (simp add: n_rows_def row_add_matrix_def)
  have Fn: "n_rows ?F = m" by (simp add: n_rows_def row_add_matrix_def)
  have ncf: "n_cols ?F = m" using m0 by (simp add: n_cols_def row_add_matrix_def)
  have L: "mat_mult_mod ?E ?F = id_mat m"
    by (rule mat_mult_mod_elem_inverse[OF im jm ij])
  have R0: "mat_mult_mod (row_add_matrix m i j (- f)) (row_add_matrix m i j (- (- f))) = id_mat m"
    by (rule mat_mult_mod_elem_inverse[OF im jm ij])
  have R: "mat_mult_mod ?F ?E = id_mat m" using R0 by simp
  have rc1: "cong_q_mat (mat_mult_mod ?E ?F) (id_mat m)" using L by (simp add: cong_q_mat_eq)
  have rc2: "cong_q_mat (mat_mult_mod ?F ?E) (id_mat m)" using R by (simp add: cong_q_mat_eq)
  have a1: "n_rows ?F = n_rows ?E" using Fn En by simp
  have a2: "n_cols ?F = n_rows ?E" using ncf En by simp
  have a3: "is_rect ?F" by simp
  have a4: "cong_q_mat (mat_mult_mod ?E ?F) (id_mat (n_rows ?E))" using rc1 En by simp
  have a5: "cong_q_mat (mat_mult_mod ?F ?E) (id_mat (n_rows ?E))" using rc2 En by simp
  show ?thesis by (rule invertible_modI[OF a1 a2 a3 a4 a5])
qed


(* seg: minors-migrated *)
section \<open>2x2 minors under elementary row operations\<close>

text \<open>These statements are what the rank argument needs: a nonzero minor is an
  obstruction to rank at most one, and it survives every elementary row operation.
  The proofs work with divisibility, never by rewriting inside @{text mod}, because
  the two natural simplification rules for @{text mod} cancel each other.
  Nothing here adds a sorry: the obligation ledger is unchanged.\<close>

section \<open>The 2x2 minor of a matrix, by row and column indices\<close>

text \<open>The ledger writes a 2x2 determinant out as four entries.  Naming that
  expression makes the statements below readable, and @{text minor2_def} lets
  each proof fall back to the entry level.\<close>

definition minor2 :: "mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "minor2 A a b c d = entry A a c * entry A b d - entry A a d * entry A b c"

text \<open>Trading two rows is a permutation of the row indices, and it is its own
  inverse, which is what makes the swap case exact rather than merely
  congruent.\<close>

abbreviation swap_idx :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "swap_idx i j r \<equiv> (if r = i then j else (if r = j then i else r))"

lemma swap_idx_invol [simp]: "swap_idx i j (swap_idx i j r) = r"
  by (cases "r = i"; cases "r = j"; cases "i = j"; simp_all)

lemma swap_idx_lt:
  assumes "i < n" and "j < n" and "r < n"
  shows "swap_idx i j r < n"
  using assms by (cases "r = i"; cases "r = j"; simp_all)

lemma swap_idx_neq:
  assumes "a \<noteq> b"
  shows "swap_idx i j a \<noteq> swap_idx i j b"
  using assms by (cases "a = i"; cases "a = j"; cases "b = i"; cases "b = j"; simp_all)



text \<open>Row @{text r} of the swapped matrix is row @{text "swap_idx i j r"} of the
  original, for every column.  This is the only place where the definition of
  @{const swap_rows} is unfolded.\<close>

lemma entry_swap_rows:
  assumes i: "i < n_rows A" and j: "j < n_rows A" and r: "r < n_rows A"
  shows "entry (swap_rows A i j) r c = entry A (swap_idx i j r) c"
proof -
  have h: "swap_rows A i j ! r
             = (if r = i then A ! j else (if r = j then A ! i else A ! r))"
    using i j r by (simp add: swap_rows_nth n_rows_def)
  have "entry (swap_rows A i j) r c
          = (if r = i then A ! j else (if r = j then A ! i else A ! r)) ! c"
    using h by (simp add: entry_def)
  also have "\<dots> = entry A (swap_idx i j r) c"
  proof (cases "r = i")
    case True
    thus ?thesis by (simp add: entry_def)
  next
    case False
    show ?thesis
    proof (cases "r = j")
      case True
      thus ?thesis using False by (simp add: entry_def)
    next
      case False2: False
      thus ?thesis using False by (simp add: entry_def)
    qed
  qed
  finally show ?thesis .
qed

text \<open>Consequently the minor of the swapped matrix is the minor of the original
  at the permuted pair, with no sign: @{const swap_rows} permutes the rows and
  the minor reads the two rows in the order the indices give.\<close>

lemma minor2_swap:
  assumes i: "i < n_rows A" and j: "j < n_rows A"
    and a: "a < n_rows A" and b: "b < n_rows A"
  shows "minor2 (swap_rows A i j) a b c d
           = minor2 A (swap_idx i j a) (swap_idx i j b) c d"
proof -
  have ea: "entry (swap_rows A i j) a c = entry A (swap_idx i j a) c"
    using i j a by (rule entry_swap_rows)
  have eb: "entry (swap_rows A i j) b d = entry A (swap_idx i j b) d"
    using i j b by (rule entry_swap_rows)
  have ec: "entry (swap_rows A i j) a d = entry A (swap_idx i j a) d"
    using i j a by (rule entry_swap_rows)
  have ed: "entry (swap_rows A i j) b c = entry A (swap_idx i j b) c"
    using i j b by (rule entry_swap_rows)
  show ?thesis by (simp add: minor2_def ea eb ec ed)
qed

section \<open>Scaling one row multiplies the minors that mention it\<close>

text \<open>Scaling rewrites exactly one row, entry by entry, through @{text fq}, so
  the entries of that row are congruent to @{text "k * x"} rather than equal to
  it.  The two lemmas below are therefore stated so that the residue of the
  scaled minor is again zero, which is the form the induction later needs.\<close>

lemma entry_scale_row:
  assumes i: "i < n_rows A" and rect: "is_rect A"
    and r: "r < n_rows A" and col: "col < n_cols A"
  shows "entry (scale_row A i k) r col
           = (if r = i then fq (k * entry A i col) else entry A r col)"
proof -
  have il: "i < length A" using i by (simp add: n_rows_def)
  have mem: "A ! i \<in> set A" using il by (rule nth_mem)
  have len: "length (A ! i) = n_cols A" using rect mem by (simp add: is_rect_def)
  have hlen: "col < length (A ! i)" using col len by simp
  have upd: "(A[i := map (\<lambda>x. fq (k * x)) (A ! i)]) ! i
               = map (\<lambda>x. fq (k * x)) (A ! i)"
    using il by (rule nth_list_update_eq)
  show ?thesis
  proof (cases "r = i")
    case True
    have "entry (scale_row A i k) r col = (map (\<lambda>x. fq (k * x)) (A ! i)) ! col"
      using True upd by (simp add: scale_row_def entry_def)
    also have "\<dots> = fq (k * entry A i col)" using hlen by (simp add: entry_def nth_map)
    finally show ?thesis using True by simp
  next
    case False
    have rl: "r < length A" using r by (simp add: n_rows_def)
    have neq: "(A[i := map (\<lambda>x. fq (k * x)) (A ! i)]) ! r = A ! r"
      using rl False by (simp add: nth_list_update_neq)
    have "entry (scale_row A i k) r col = (A ! r) ! col"
      using neq by (simp add: scale_row_def entry_def)
    thus ?thesis using False by (simp add: entry_def)
  qed
qed

text \<open>Every residue differs from the number it came from by a multiple of the
  modulus.  Keeping that as a divisibility fact, rather than rewriting inside
  @{text mod}, keeps the simplifier away from the pair of rules that cancel
  each other.\<close>

lemma dvd_fq_diff:
  fixes x :: int
  shows "3329 dvd x - fq x"
proof -
  have "x = x div 3329 * 3329 + x mod 3329" by (simp add: div_mult_mod_eq)
  hence h1: "x - fq x = 3329 * (x div 3329)" by (simp add: fq_def algebra_simps)
  show ?thesis using h1 by (simp add: dvd_triv_left)
qed

lemma minor2_scale_row_first:
  assumes i: "i < n_rows A" and rect: "is_rect A"
    and b: "b < n_rows A" and ib: "i \<noteq> b"
    and c: "c < n_cols A" and d: "d < n_cols A"
    and h: "minor2 A i b c d mod 3329 = 0"
  shows "minor2 (scale_row A i k) i b c d mod 3329 = 0"
proof -
  have eic: "entry (scale_row A i k) i c = fq (k * entry A i c)"
    using i rect c by (simp add: entry_scale_row)
  have eid: "entry (scale_row A i k) i d = fq (k * entry A i d)"
    using i rect d by (simp add: entry_scale_row)
  have ebc: "entry (scale_row A i k) b c = entry A b c"
    using i rect b c ib by (simp add: entry_scale_row)
  have ebd: "entry (scale_row A i k) b d = entry A b d"
    using i rect b d ib by (simp add: entry_scale_row)
  have eq: "minor2 (scale_row A i k) i b c d
              = fq (k * entry A i c) * entry A b d
                - fq (k * entry A i d) * entry A b c"
    using eic eid ebc ebd by (simp add: minor2_def)
  have dX: "3329 dvd (k * entry A i c - fq (k * entry A i c)) * entry A b d"
    by (rule dvd_mult2[OF dvd_fq_diff])
  have dZ: "3329 dvd (k * entry A i d - fq (k * entry A i d)) * entry A b c"
    by (rule dvd_mult2[OF dvd_fq_diff])
  have dd: "3329 dvd (k * entry A i c - fq (k * entry A i c)) * entry A b d
                     - (k * entry A i d - fq (k * entry A i d)) * entry A b c"
    using dX dZ by (rule dvd_diff)
  have dm0: "3329 dvd minor2 A i b c d" using h by (simp add: dvd_eq_mod_eq_0)
  have dm: "3329 dvd k * minor2 A i b c d" using dm0 by (rule dvd_mult)
  have dv: "3329 dvd k * minor2 A i b c d
                     - ((k * entry A i c - fq (k * entry A i c)) * entry A b d
                        - (k * entry A i d - fq (k * entry A i d)) * entry A b c)"
    using dm dd by (rule dvd_diff)
  have split_eq: "k * minor2 A i b c d
                    - ((k * entry A i c - fq (k * entry A i c)) * entry A b d
                       - (k * entry A i d - fq (k * entry A i d)) * entry A b c)
                  = minor2 (scale_row A i k) i b c d"
    using eq by (simp add: minor2_def algebra_simps)
  from dv split_eq have "3329 dvd minor2 (scale_row A i k) i b c d" by simp
  thus ?thesis by (simp add: dvd_eq_mod_eq_0)
qed

lemma minor2_scale_row_second:
  assumes i: "i < n_rows A" and rect: "is_rect A"
    and b: "b < n_rows A" and ib: "i \<noteq> b"
    and c: "c < n_cols A" and d: "d < n_cols A"
    and h: "minor2 A b i c d mod 3329 = 0"
  shows "minor2 (scale_row A i k) b i c d mod 3329 = 0"
proof -
  have eic: "entry (scale_row A i k) i c = fq (k * entry A i c)"
    using i rect c by (simp add: entry_scale_row)
  have eid: "entry (scale_row A i k) i d = fq (k * entry A i d)"
    using i rect d by (simp add: entry_scale_row)
  have ebc: "entry (scale_row A i k) b c = entry A b c"
    using i rect b c ib by (simp add: entry_scale_row)
  have ebd: "entry (scale_row A i k) b d = entry A b d"
    using i rect b d ib by (simp add: entry_scale_row)
  have eq: "minor2 (scale_row A i k) b i c d
              = entry A b c * fq (k * entry A i d)
                - entry A b d * fq (k * entry A i c)"
    using eic eid ebc ebd by (simp add: minor2_def)
  have dS: "3329 dvd (k * entry A i d - fq (k * entry A i d)) * entry A b c"
    by (rule dvd_mult2[OF dvd_fq_diff])
  have dR: "3329 dvd (k * entry A i c - fq (k * entry A i c)) * entry A b d"
    by (rule dvd_mult2[OF dvd_fq_diff])
  have dd: "3329 dvd (k * entry A i d - fq (k * entry A i d)) * entry A b c
                     - (k * entry A i c - fq (k * entry A i c)) * entry A b d"
    using dS dR by (rule dvd_diff)
  have dm0: "3329 dvd minor2 A b i c d" using h by (simp add: dvd_eq_mod_eq_0)
  have dm: "3329 dvd k * minor2 A b i c d" using dm0 by (rule dvd_mult)
  have dv: "3329 dvd k * minor2 A b i c d
                     - ((k * entry A i d - fq (k * entry A i d)) * entry A b c
                        - (k * entry A i c - fq (k * entry A i c)) * entry A b d)"
    using dm dd by (rule dvd_diff)
  have split_eq: "k * minor2 A b i c d
                    - ((k * entry A i d - fq (k * entry A i d)) * entry A b c
                       - (k * entry A i c - fq (k * entry A i c)) * entry A b d)
                  = minor2 (scale_row A i k) b i c d"
    using eq by (simp add: minor2_def algebra_simps)
  from dv split_eq have "3329 dvd minor2 (scale_row A i k) b i c d" by simp
  thus ?thesis by (simp add: dvd_eq_mod_eq_0)
qed

lemma minor2_scale_row_other:
  assumes i: "i < n_rows A" and rect: "is_rect A"
    and a: "a < n_rows A" and b: "b < n_rows A"
    and ai: "a \<noteq> i" and bi: "b \<noteq> i"
    and c: "c < n_cols A" and d: "d < n_cols A"
  shows "minor2 (scale_row A i k) a b c d = minor2 A a b c d"
proof -
  have eac: "entry (scale_row A i k) a c = entry A a c"
    using i rect a c ai by (simp add: entry_scale_row)
  have ead: "entry (scale_row A i k) a d = entry A a d"
    using i rect a d ai by (simp add: entry_scale_row)
  have ebc: "entry (scale_row A i k) b c = entry A b c"
    using i rect b c bi by (simp add: entry_scale_row)
  have ebd: "entry (scale_row A i k) b d = entry A b d"
    using i rect b d bi by (simp add: entry_scale_row)
  show ?thesis by (simp add: minor2_def eac ead ebc ebd)
qed


section \<open>Adding a multiple of one row leaves the residues of all minors unchanged\<close>

text \<open>Row addition rewrites row @{text i} as the entrywise residue of
  @{text "P + k * S"}, so a minor that uses row @{text i} picks up a residue on
  two of its four entries.  As with scaling, the statement is phrased as
  preservation of a vanishing residue; the arithmetic stays on the divisibility
  side and never rewrites inside @{text mod}.\<close>

lemma entry_add_row_mult:
  assumes i: "i < n_rows A" and j: "j < n_rows A" and rect: "is_rect A"
    and r: "r < n_rows A" and col: "col < n_cols A"
  shows "entry (add_row_mult A i j k) r col
           = (if r = i then fq (entry A i col + k * entry A j col) else entry A r col)"
proof -
  have il: "i < length A" using i by (simp add: n_rows_def)
  have memi: "A ! i \<in> set A" using il by (rule nth_mem)
  have memj: "A ! j \<in> set A" using j by (simp add: n_rows_def; rule nth_mem)
  have leni: "length (A ! i) = n_cols A" using rect memi by (simp add: is_rect_def)
  have lenj: "length (A ! j) = n_cols A" using rect memj by (simp add: is_rect_def)
  show ?thesis
  proof (cases "r = i")
    case True
    have upd: "(A[i := map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)]) ! i
                 = map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)"
      using il by (rule nth_list_update_eq)
    have conv: "map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)
                  = map (\<lambda>l. fq ((A ! i) ! l + k * (A ! j) ! l)) [0..<n_cols A]"
      using leni lenj by (rule map2_conv_idx)
    have nth: "(map (\<lambda>l. fq ((A ! i) ! l + k * (A ! j) ! l)) [0..<n_cols A]) ! col
                 = fq (entry A i col + k * entry A j col)"
      using col by (simp add: entry_def nth_map)
    have "entry (add_row_mult A i j k) r col
            = (map (\<lambda>l. fq ((A ! i) ! l + k * (A ! j) ! l)) [0..<n_cols A]) ! col"
      using True upd conv by (simp add: add_row_mult_def entry_def)
    also have "\<dots> = fq (entry A i col + k * entry A j col)" using nth .
    finally show ?thesis using True by simp
  next
    case False
    have rl: "r < length A" using r by (simp add: n_rows_def)
    have neq: "(A[i := map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)]) ! r = A ! r"
      using rl False by (simp add: nth_list_update_neq)
    have "entry (add_row_mult A i j k) r col = (A ! r) ! col"
      using neq by (simp add: add_row_mult_def entry_def)
    thus ?thesis using False by (simp add: entry_def)
  qed
qed

lemma minor2_add_row_other:
  assumes i: "i < n_rows A" and j: "j < n_rows A" and rect: "is_rect A"
    and a: "a < n_rows A" and b: "b < n_rows A"
    and ai: "a \<noteq> i" and bi: "b \<noteq> i"
    and c: "c < n_cols A" and d: "d < n_cols A"
  shows "minor2 (add_row_mult A i j k) a b c d = minor2 A a b c d"
proof -
  have eac: "entry (add_row_mult A i j k) a c = entry A a c"
    using i j rect a c ai by (simp add: entry_add_row_mult)
  have ead: "entry (add_row_mult A i j k) a d = entry A a d"
    using i j rect a d ai by (simp add: entry_add_row_mult)
  have ebc: "entry (add_row_mult A i j k) b c = entry A b c"
    using i j rect b c bi by (simp add: entry_add_row_mult)
  have ebd: "entry (add_row_mult A i j k) b d = entry A b d"
    using i j rect b d bi by (simp add: entry_add_row_mult)
  show ?thesis by (simp add: minor2_def eac ead ebc ebd)
qed

text \<open>When the rewritten row is the upper row of the minor, the residue of the
  new minor is the residue of @{text "minor (i,b) + k * minor (j,b)"}: the row
  swap that would put @{text j} in place of @{text i} is not needed, because
  the addition itself is linear in that row.\<close>

lemma minor2_add_row_first:
  assumes i: "i < n_rows A" and j: "j < n_rows A" and rect: "is_rect A"
    and b: "b < n_rows A" and bi: "b \<noteq> i"
    and c: "c < n_cols A" and d: "d < n_cols A"
    and h1: "minor2 A i b c d mod 3329 = 0"
    and h2: "minor2 A j b c d mod 3329 = 0"
  shows "minor2 (add_row_mult A i j k) i b c d mod 3329 = 0"
proof -
  have eic: "entry (add_row_mult A i j k) i c = fq (entry A i c + k * entry A j c)"
    using i j rect c by (simp add: entry_add_row_mult)
  have eid: "entry (add_row_mult A i j k) i d = fq (entry A i d + k * entry A j d)"
    using i j rect d by (simp add: entry_add_row_mult)
  have ebc: "entry (add_row_mult A i j k) b c = entry A b c"
    using i j rect b c bi by (simp add: entry_add_row_mult)
  have ebd: "entry (add_row_mult A i j k) b d = entry A b d"
    using i j rect b d bi by (simp add: entry_add_row_mult)
  have eq: "minor2 (add_row_mult A i j k) i b c d
              = fq (entry A i c + k * entry A j c) * entry A b d
                - fq (entry A i d + k * entry A j d) * entry A b c"
    using eic eid ebc ebd by (simp add: minor2_def)
  have d1: "3329 dvd (entry A i c + k * entry A j c
                        - fq (entry A i c + k * entry A j c)) * entry A b d"
    by (rule dvd_mult2[OF dvd_fq_diff])
  have d2: "3329 dvd (entry A i d + k * entry A j d
                        - fq (entry A i d + k * entry A j d)) * entry A b c"
    by (rule dvd_mult2[OF dvd_fq_diff])
  have dd: "3329 dvd (entry A i c + k * entry A j c
                        - fq (entry A i c + k * entry A j c)) * entry A b d
                     - (entry A i d + k * entry A j d
                        - fq (entry A i d + k * entry A j d)) * entry A b c"
    using d1 d2 by (rule dvd_diff)
  have h1d: "3329 dvd minor2 A i b c d" using h1 by (simp add: dvd_eq_mod_eq_0)
  have h2d: "3329 dvd minor2 A j b c d" using h2 by (simp add: dvd_eq_mod_eq_0)
  have h2k: "3329 dvd k * minor2 A j b c d" using h2d by (rule dvd_mult)
  have hs: "3329 dvd minor2 A i b c d + k * minor2 A j b c d"
    using h1d h2k by (rule dvd_add)
  have dv: "3329 dvd minor2 A i b c d + k * minor2 A j b c d
                     - ((entry A i c + k * entry A j c
                          - fq (entry A i c + k * entry A j c)) * entry A b d
                        - (entry A i d + k * entry A j d
                          - fq (entry A i d + k * entry A j d)) * entry A b c)"
    using hs dd by (rule dvd_diff)
  have split_eq: "minor2 A i b c d + k * minor2 A j b c d
                    - ((entry A i c + k * entry A j c
                         - fq (entry A i c + k * entry A j c)) * entry A b d
                       - (entry A i d + k * entry A j d
                         - fq (entry A i d + k * entry A j d)) * entry A b c)
                  = minor2 (add_row_mult A i j k) i b c d"
    using eq by (simp add: minor2_def algebra_simps)
  from dv split_eq have "3329 dvd minor2 (add_row_mult A i j k) i b c d" by simp
  thus ?thesis by (simp add: dvd_eq_mod_eq_0)
qed

lemma minor2_add_row_second:
  assumes i: "i < n_rows A" and j: "j < n_rows A" and rect: "is_rect A"
    and b: "b < n_rows A" and bi: "b \<noteq> i"
    and c: "c < n_cols A" and d: "d < n_cols A"
    and h1: "minor2 A b i c d mod 3329 = 0"
    and h2: "minor2 A b j c d mod 3329 = 0"
  shows "minor2 (add_row_mult A i j k) b i c d mod 3329 = 0"
proof -
  have eic: "entry (add_row_mult A i j k) i c = fq (entry A i c + k * entry A j c)"
    using i j rect c by (simp add: entry_add_row_mult)
  have eid: "entry (add_row_mult A i j k) i d = fq (entry A i d + k * entry A j d)"
    using i j rect d by (simp add: entry_add_row_mult)
  have ebc: "entry (add_row_mult A i j k) b c = entry A b c"
    using i j rect b c bi by (simp add: entry_add_row_mult)
  have ebd: "entry (add_row_mult A i j k) b d = entry A b d"
    using i j rect b d bi by (simp add: entry_add_row_mult)
  have eq: "minor2 (add_row_mult A i j k) b i c d
              = entry A b c * fq (entry A i d + k * entry A j d)
                - entry A b d * fq (entry A i c + k * entry A j c)"
    using eic eid ebc ebd by (simp add: minor2_def)
  have d1: "3329 dvd (entry A i d + k * entry A j d
                        - fq (entry A i d + k * entry A j d)) * entry A b c"
    by (rule dvd_mult2[OF dvd_fq_diff])
  have d2: "3329 dvd (entry A i c + k * entry A j c
                        - fq (entry A i c + k * entry A j c)) * entry A b d"
    by (rule dvd_mult2[OF dvd_fq_diff])
  have dd: "3329 dvd (entry A i d + k * entry A j d
                        - fq (entry A i d + k * entry A j d)) * entry A b c
                     - (entry A i c + k * entry A j c
                        - fq (entry A i c + k * entry A j c)) * entry A b d"
    using d1 d2 by (rule dvd_diff)
  have h1d: "3329 dvd minor2 A b i c d" using h1 by (simp add: dvd_eq_mod_eq_0)
  have h2d: "3329 dvd minor2 A b j c d" using h2 by (simp add: dvd_eq_mod_eq_0)
  have h2k: "3329 dvd k * minor2 A b j c d" using h2d by (rule dvd_mult)
  have hs: "3329 dvd minor2 A b i c d + k * minor2 A b j c d"
    using h1d h2k by (rule dvd_add)
  have dv: "3329 dvd minor2 A b i c d + k * minor2 A b j c d
                     - ((entry A i d + k * entry A j d
                          - fq (entry A i d + k * entry A j d)) * entry A b c
                        - (entry A i c + k * entry A j c
                          - fq (entry A i c + k * entry A j c)) * entry A b d)"
    using hs dd by (rule dvd_diff)
  have split_eq: "minor2 A b i c d + k * minor2 A b j c d
                    - ((entry A i d + k * entry A j d
                         - fq (entry A i d + k * entry A j d)) * entry A b c
                       - (entry A i c + k * entry A j c
                         - fq (entry A i c + k * entry A j c)) * entry A b d)
                  = minor2 (add_row_mult A i j k) b i c d"
    using eq by (simp add: minor2_def algebra_simps)

  from dv split_eq have "3329 dvd minor2 (add_row_mult A i j k) b i c d" by simp
  thus ?thesis by (simp add: dvd_eq_mod_eq_0)
qed

(* seg: minors-zero-layer-20261023 *)
section \<open>Duplicate indices and the all-minors-vanish predicate\<close>

text \<open>Two facts the rank argument needs before any induction: a minor with a
  repeated row or a repeated column is zero, and a minor changes sign when its
  own two rows are traded.  Neither proof touches @{text mod}; both are
  identities in the integers.\<close>

lemma minor2_repeat_row [simp]: "minor2 A a a c d = 0"
  by (simp add: minor2_def)

lemma minor2_repeat_col [simp]: "minor2 A a b c c = 0"
  by (simp add: minor2_def)

lemma minor2_repeat [simp]:
  assumes "a = b \<or> c = d"
  shows "minor2 A a b c d = 0"
  using assms by (auto simp: minor2_def)

text \<open>@{text minor2_swap} says a row swap permutes the row indices of the
  minor.  When the swapped pair is exactly the pair the minor reads, that
  permutation is the transposition of those two rows, so the minor changes
  sign.\<close>

lemma minor2_swap_antisym:
  assumes a: "a < n_rows A" and b: "b < n_rows A" and ab: "a \<noteq> b"
  shows "minor2 (swap_rows A a b) a b c d = - minor2 A a b c d"
proof -
  have "minor2 (swap_rows A a b) a b c d
          = minor2 A (swap_idx a b a) (swap_idx a b b) c d"
    by (rule minor2_swap [OF a b a b])
  also have "\<dots> = minor2 A b a c d" using ab by simp
  also have "\<dots> = - minor2 A a b c d" by (simp add: minor2_def algebra_simps)
  finally show ?thesis .
qed

text \<open>A matrix has vanishing minors when every @{text "2 x 2"} minor is
  divisible by @{text 3329}.  The predicate is phrased with divisibility rather
  than an equation under @{text mod}, so that a later induction over
  @{text rref_fuel} can carry the hypothesis along without asking the
  simplifier to normalise residues.\<close>

definition minors_zero :: "mat \<Rightarrow> bool" where
  "minors_zero A = (\<forall>a b c d. a < n_rows A \<longrightarrow> b < n_rows A \<longrightarrow>
      c < n_cols A \<longrightarrow> d < n_cols A \<longrightarrow> 3329 dvd minor2 A a b c d)"

lemma minors_zeroI:
  assumes "\<And>a b c d. a < n_rows A \<Longrightarrow> b < n_rows A \<Longrightarrow> c < n_cols A \<Longrightarrow>
             d < n_cols A \<Longrightarrow> 3329 dvd minor2 A a b c d"
  shows "minors_zero A"
  using assms by (simp add: minors_zero_def)

lemma minors_zeroE:
  assumes h: "minors_zero A" and a: "a < n_rows A" and b: "b < n_rows A"
    and c: "c < n_cols A" and d: "d < n_cols A"
  shows "3329 dvd minor2 A a b c d"
  using h a b c d by (simp add: minors_zero_def)

(* seg: minors-preserve-20261023 *)

section \<open>Minors survive the three elementary row operations\<close>

text \<open>Each operation touches the minors in one of three ways: a swap permutes the
  row indices, a scale multiplies a minor, and a row addition replaces a minor by
  itself plus a multiple of another one.  Everything is stated as divisibility by
  the modulus, which is the form @{const minors_zero} uses.\<close>

lemma n_cols_swap_rows:
  assumes i: "i < n_rows A" and j: "j < n_rows A" and rect: "is_rect A"
  shows "n_cols (swap_rows A i j) = n_cols A"
proof (cases "A = []")
  case True
  thus ?thesis by (simp add: swap_rows_def n_cols_def)
next
  case ne0: False
  hence len0: "0 < length A" by simp
  have n0: "0 < n_rows A" using len0 by (simp add: n_rows_def)
  have iA: "i < length A" using i by (simp add: n_rows_def)
  have jA: "j < length A" using j by (simp add: n_rows_def)
  have h: "(swap_rows A i j) ! 0
             = (if 0 = i then A ! j else (if 0 = j then A ! i else A ! 0))"
    using len0 iA jA by (rule swap_rows_nth)
  have ne: "swap_rows A i j \<noteq> []" using ne0 by (simp add: swap_rows_def)
  have l0: "length (A ! 0) = n_cols A" using rect n0 by (rule is_rect_rows)
  have li: "length (A ! i) = n_cols A" using rect i by (rule is_rect_rows)
  have lj: "length (A ! j) = n_cols A" using rect j by (rule is_rect_rows)
  have "n_cols (swap_rows A i j) = length ((swap_rows A i j) ! 0)"
    by (simp add: n_cols_def ne)
  also have "\<dots> = n_cols A"
  proof (cases "0 = i")
    case True
    thus ?thesis using h lj by simp
  next
    case f1: False
    show ?thesis
    proof (cases "0 = j")
      case True
      thus ?thesis using h f1 li by simp
    next
      case f2: False
      thus ?thesis using h f1 l0 by simp
    qed
  qed
  finally show ?thesis .
qed

lemma n_cols_scale_row:
  shows "n_cols (scale_row A i k) = n_cols A"
proof (cases "A = []")
  case True
  thus ?thesis by (simp add: scale_row_def n_cols_def)
next
  case ne0: False
  hence len0: "0 < length A" by simp
  have ne: "scale_row A i k \<noteq> []" using ne0 by (simp add: scale_row_def)
  have "n_cols (scale_row A i k) = length ((scale_row A i k) ! 0)"
    by (simp add: n_cols_def ne)
  also have "\<dots> = length (A ! 0)"
  proof (cases "i = 0")
    case True
    have upd: "(A[i := map (\<lambda>x. fq (k * x)) (A ! i)]) ! i
                 = map (\<lambda>x. fq (k * x)) (A ! i)"
      using len0 True by (simp add: nth_list_update_eq)
    have "(scale_row A i k) ! 0 = map (\<lambda>x. fq (k * x)) (A ! 0)"
      using True upd by (simp add: scale_row_def)
    thus ?thesis by simp
  next
    case f: False
    have "(scale_row A i k) ! 0 = A ! 0"
      using len0 f by (simp add: scale_row_def nth_list_update_neq)
    thus ?thesis by simp
  qed
  also have "\<dots> = n_cols A" using ne0 by (simp add: n_cols_def)
  finally show ?thesis .
qed

lemma n_cols_add_row_mult:
  assumes i: "i < n_rows A" and j: "j < n_rows A" and rect: "is_rect A"
  shows "n_cols (add_row_mult A i j k) = n_cols A"
proof (cases "A = []")
  case True
  thus ?thesis by (simp add: add_row_mult_def n_cols_def)
next
  case ne0: False
  hence len0: "0 < length A" by simp
  have li: "length (A ! i) = n_cols A" using rect i by (rule is_rect_rows)
  have lj: "length (A ! j) = n_cols A" using rect j by (rule is_rect_rows)
  have conv: "map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)
                = map (\<lambda>l. fq ((A ! i) ! l + k * (A ! j) ! l)) [0..<n_cols A]"
    using li lj by (rule map2_conv_idx)
  have ne: "add_row_mult A i j k \<noteq> []" using ne0 by (simp add: add_row_mult_def)
  have "n_cols (add_row_mult A i j k) = length ((add_row_mult A i j k) ! 0)"
    by (simp add: n_cols_def ne)
  also have "\<dots> = n_cols A"
  proof (cases "i = 0")
    case True
    have upd: "(A[i := map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)]) ! i
                 = map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)"
      using len0 True by (simp add: nth_list_update_eq)
    have "(add_row_mult A i j k) ! 0
            = map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)"
      using True upd by (simp add: add_row_mult_def)
    thus ?thesis using conv by simp
  next
    case f: False
    have "(add_row_mult A i j k) ! 0 = A ! 0"
      using len0 f by (simp add: add_row_mult_def nth_list_update_neq)
    thus ?thesis using ne0 by (simp add: n_cols_def)
  qed
  finally show ?thesis .
qed

text \<open>Trading two rows only permutes the row indices of a minor, so divisibility
  carries over with no arithmetic at all.\<close>

lemma minors_zero_swap:
  assumes mz: "minors_zero A" and i: "i < n_rows A" and j: "j < n_rows A"
    and rect: "is_rect A"
  shows "minors_zero (swap_rows A i j)"
proof (rule minors_zeroI)
  fix a b c d
  assume a: "a < n_rows (swap_rows A i j)" and b: "b < n_rows (swap_rows A i j)"
    and c: "c < n_cols (swap_rows A i j)" and d: "d < n_cols (swap_rows A i j)"
  have an: "a < n_rows A" using a by (simp add: n_rows_def swap_rows_def)
  have bn: "b < n_rows A" using b by (simp add: n_rows_def swap_rows_def)
  have nc: "n_cols (swap_rows A i j) = n_cols A" by (rule n_cols_swap_rows [OF i j rect])
  have cn: "c < n_cols A" using c nc by simp
  have dn: "d < n_cols A" using d nc by simp
  have al: "swap_idx i j a < n_rows A" using i j an by (rule swap_idx_lt)
  have bl: "swap_idx i j b < n_rows A" using i j bn by (rule swap_idx_lt)
  have eq: "minor2 (swap_rows A i j) a b c d
              = minor2 A (swap_idx i j a) (swap_idx i j b) c d"
    using i j an bn by (rule minor2_swap)
  have dv: "3329 dvd minor2 A (swap_idx i j a) (swap_idx i j b) c d"
    using mz al bl cn dn by (rule minors_zeroE)
  show "3329 dvd minor2 (swap_rows A i j) a b c d" using eq dv by simp
qed

text \<open>Scaling multiplies exactly the minors that read the scaled row, so
  divisibility is preserved by multiplying the witness.\<close>

lemma minors_zero_scale_row:
  assumes mz: "minors_zero A" and i: "i < n_rows A" and rect: "is_rect A"
  shows "minors_zero (scale_row A i k)"
proof (rule minors_zeroI)
  fix a b c d
  assume a: "a < n_rows (scale_row A i k)" and b: "b < n_rows (scale_row A i k)"
    and c: "c < n_cols (scale_row A i k)" and d: "d < n_cols (scale_row A i k)"
  have an: "a < n_rows A" using a by (simp add: n_rows_def scale_row_def)
  have bn: "b < n_rows A" using b by (simp add: n_rows_def scale_row_def)
  have nc: "n_cols (scale_row A i k) = n_cols A" by (rule n_cols_scale_row)
  have cn: "c < n_cols A" using c nc by simp
  have dn: "d < n_cols A" using d nc by simp
  have dv: "3329 dvd minor2 A a b c d" using mz an bn cn dn by (rule minors_zeroE)
  show "3329 dvd minor2 (scale_row A i k) a b c d"
  proof (cases "a = i")
    case aT: True
    show ?thesis
    proof (cases "b = i")
      case True
      thus ?thesis by (simp add: aT True)
    next
      case bF: False
      have bi: "i \<noteq> b" using bF by simp
      have hm: "minor2 A i b c d mod 3329 = 0"
        using dv aT by (simp add: dvd_eq_mod_eq_0)
      have z: "minor2 (scale_row A i k) i b c d mod 3329 = 0"
        using i rect bn bi cn dn hm by (rule minor2_scale_row_first)
      show ?thesis using aT z by (simp add: dvd_eq_mod_eq_0)
    qed
  next
    case aF: False
    show ?thesis
    proof (cases "b = i")
      case bT: True
      have ai: "i \<noteq> a" using aF by simp
      have hm: "minor2 A a i c d mod 3329 = 0"
        using dv bT by (simp add: dvd_eq_mod_eq_0)
      have z: "minor2 (scale_row A i k) a i c d mod 3329 = 0"
        using i rect an ai cn dn hm by (rule minor2_scale_row_second)
      show ?thesis using bT z by (simp add: dvd_eq_mod_eq_0)
    next
      case bF: False
      have ai: "a \<noteq> i" using aF by simp
      have bi: "b \<noteq> i" using bF by simp
      have eq: "minor2 (scale_row A i k) a b c d = minor2 A a b c d"
        using i rect an bn ai bi cn dn by (rule minor2_scale_row_other)
      show ?thesis using eq dv by simp
    qed
  qed
qed

text \<open>Adding a multiple of one row to another replaces a minor by itself plus a
  multiple of the minor that reads the added row, so divisibility is inherited.\<close>

lemma minors_zero_add_row:
  assumes mz: "minors_zero A" and i: "i < n_rows A" and j: "j < n_rows A"
    and ij: "i \<noteq> j" and rect: "is_rect A"
  shows "minors_zero (add_row_mult A i j k)"
proof (rule minors_zeroI)
  fix a b c d
  assume a: "a < n_rows (add_row_mult A i j k)" and b: "b < n_rows (add_row_mult A i j k)"
    and c: "c < n_cols (add_row_mult A i j k)" and d: "d < n_cols (add_row_mult A i j k)"
  have an: "a < n_rows A" using a by (simp add: n_rows_def add_row_mult_def)
  have bn: "b < n_rows A" using b by (simp add: n_rows_def add_row_mult_def)
  have nc: "n_cols (add_row_mult A i j k) = n_cols A"
    by (rule n_cols_add_row_mult [OF i j rect])
  have cn: "c < n_cols A" using c nc by simp
  have dn: "d < n_cols A" using d nc by simp
  have dvab: "3329 dvd minor2 A a b c d" using mz an bn cn dn by (rule minors_zeroE)
  have dvai: "3329 dvd minor2 A a i c d" using mz an i cn dn by (rule minors_zeroE)
  have dvaj: "3329 dvd minor2 A a j c d" using mz an j cn dn by (rule minors_zeroE)
  have dvib: "3329 dvd minor2 A i b c d" using mz i bn cn dn by (rule minors_zeroE)
  have dvjb: "3329 dvd minor2 A j b c d" using mz j bn cn dn by (rule minors_zeroE)
  show "3329 dvd minor2 (add_row_mult A i j k) a b c d"
  proof (cases "a = i")
    case aT: True
    show ?thesis
    proof (cases "b = i")
      case True
      thus ?thesis by (simp add: aT True)
    next
      case bF: False
      have bi: "b \<noteq> i" using bF by simp
      show ?thesis
      proof (cases "b = j")
        case bT: True
        have h1: "minor2 A i j c d mod 3329 = 0" using dvib bT by (simp add: dvd_eq_mod_eq_0)
        have h2: "minor2 A j j c d mod 3329 = 0" by simp
        have ji: "j \<noteq> i" using bF bT by simp
        have "minor2 (add_row_mult A i j k) i j c d mod 3329 = 0"
          by (rule minor2_add_row_first [where b=j, OF i j rect j ji cn dn h1 h2])
        thus ?thesis using aT bT by (simp add: dvd_eq_mod_eq_0)
      next
        case bFj: False
        have h1: "minor2 A i b c d mod 3329 = 0" using dvib by (simp add: dvd_eq_mod_eq_0)
        have h2: "minor2 A j b c d mod 3329 = 0" using dvjb by (simp add: dvd_eq_mod_eq_0)
        have z: "minor2 (add_row_mult A i j k) i b c d mod 3329 = 0"
          using i j rect bn bi cn dn h1 h2 by (rule minor2_add_row_first)
        thus ?thesis using aT by (simp add: dvd_eq_mod_eq_0)
      qed
    qed
  next
    case aF: False
    show ?thesis
    proof (cases "b = i")
      case bT: True
      show ?thesis
      proof (cases "a = j")
        case aT2: True
        have h1: "minor2 A j i c d mod 3329 = 0" using dvai aT2 by (simp add: dvd_eq_mod_eq_0)
        have h2: "minor2 A j j c d mod 3329 = 0" by simp
        have ji: "j \<noteq> i" using ij by simp
        have "minor2 (add_row_mult A i j k) j i c d mod 3329 = 0"
          by (rule minor2_add_row_second [where b=j, OF i j rect j ji cn dn h1 h2])
        thus ?thesis using bT aT2 by (simp add: dvd_eq_mod_eq_0)
      next
        case aFj: False
        have h1: "minor2 A a i c d mod 3329 = 0" using dvai by (simp add: dvd_eq_mod_eq_0)
        have h2: "minor2 A a j c d mod 3329 = 0" using dvaj by (simp add: dvd_eq_mod_eq_0)
        have z: "minor2 (add_row_mult A i j k) a i c d mod 3329 = 0"
          using i j rect an aF cn dn h1 h2 by (rule minor2_add_row_second)
        thus ?thesis using bT by (simp add: dvd_eq_mod_eq_0)
      qed
    next
      case bF: False
      have ai: "a \<noteq> i" using aF by simp
      have bi: "b \<noteq> i" using bF by simp
      have eq: "minor2 (add_row_mult A i j k) a b c d = minor2 A a b c d"
        using i j rect an bn ai bi cn dn by (rule minor2_add_row_other)
      show ?thesis using eq dvab by simp
    qed
  qed
qed
(* seg: shape-rect-20261023 *)
section \<open>Row counts and rectangularity under the row operations\<close>

text \<open>Column counts for the three operations are already proved above.  What
  the elimination fold needs on top of that is that rectangularity itself is
  preserved, and that the row count never moves.  Both are list facts: every
  operation is a single update, and the replacement row has the common width.\<close>

lemma n_rows_swap_rows [simp]: "n_rows (swap_rows A i j) = n_rows A"
  by (simp add: swap_rows_def n_rows_def)

lemma n_rows_scale_row [simp]: "n_rows (scale_row A i k) = n_rows A"
  by (simp add: scale_row_def n_rows_def)

lemma n_rows_add_row_mult [simp]: "n_rows (add_row_mult A i j k) = n_rows A"
  by (simp add: add_row_mult_def n_rows_def)

lemma n_rows_eliminate_fold [simp]:
  "n_rows (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c)) A ks)
     = n_rows A"
  by (induct ks arbitrary: A) simp_all

lemma n_rows_eliminate_col [simp]: "n_rows (eliminate_col A r c) = n_rows A"
  by (simp add: eliminate_col_def)

lemma is_rect_swap_rows:
  assumes rect: "is_rect A" and i: "i < n_rows A" and j: "j < n_rows A"
  shows "is_rect (swap_rows A i j)"
proof (simp add: is_rect_def, intro ballI)
  fix row
  assume h: "row \<in> set (swap_rows A i j)"
  have nc: "n_cols (swap_rows A i j) = n_cols A"
    by (rule n_cols_swap_rows [OF i j rect])
  obtain p where p: "p < length (swap_rows A i j)" "swap_rows A i j ! p = row"
    using h by (auto simp: in_set_conv_nth)
  have lp: "length (swap_rows A i j) = length A"
    by (simp add: swap_rows_def)
  have pA: "p < length A" using p lp by simp
  have iA: "i < length A" and jA: "j < length A" using i j by (simp_all add: n_rows_def)
  have row_eq: "row = (if p = i then A ! j else (if p = j then A ! i else A ! p))"
    using swap_rows_nth [OF pA iA jA] p by simp
  show "length row = n_cols (swap_rows A i j)"
    using row_eq nc rect iA jA pA
    by (cases "p = i"; cases "p = j") (auto simp: is_rect_rows n_rows_def)
qed

lemma is_rect_scale_row:
  assumes rect: "is_rect A" and i: "i < n_rows A"
  shows "is_rect (scale_row A i k)"
proof (simp add: is_rect_def, intro ballI)
  fix row
  assume h: "row \<in> set (scale_row A i k)"
  have nc: "n_cols (scale_row A i k) = n_cols A" by (rule n_cols_scale_row)
  obtain p where p: "p < length (scale_row A i k)" "scale_row A i k ! p = row"
    using h by (auto simp: in_set_conv_nth)
  have lp: "p < length A" using p by (simp add: scale_row_def)
  show "length row = n_cols (scale_row A i k)"
  proof (cases "p = i")
    case True
    have eq: "row = map (\<lambda>x. fq (k * x)) (A ! i)"
      using p True i by (simp add: scale_row_def n_rows_def nth_list_update_eq)
    have li: "length (A ! i) = n_cols A" using rect i by (simp add: is_rect_rows)
    show ?thesis using eq li nc by simp
  next
    case False
    have eq: "row = A ! p"
      using p False i by (simp add: scale_row_def n_rows_def nth_list_update_neq)
    have lp2: "length (A ! p) = n_cols A" using rect lp by (simp add: is_rect_rows n_rows_def)
    show ?thesis using eq lp2 nc by simp
  qed
qed

lemma is_rect_add_row_mult:
  assumes rect: "is_rect A" and i: "i < n_rows A" and j: "j < n_rows A"
  shows "is_rect (add_row_mult A i j k)"
proof (simp add: is_rect_def, intro ballI)
  fix row
  assume h: "row \<in> set (add_row_mult A i j k)"
  have nc: "n_cols (add_row_mult A i j k) = n_cols A"
    by (rule n_cols_add_row_mult [OF i j rect])
  obtain p where p: "p < length (add_row_mult A i j k)" "add_row_mult A i j k ! p = row"
    using h by (auto simp: in_set_conv_nth)
  have lp: "p < length A" using p by (simp add: add_row_mult_def)
  show "length row = n_cols (add_row_mult A i j k)"
  proof (cases "p = i")
    case True
    have li: "length (A ! i) = n_cols A" using rect i by (simp add: is_rect_rows)
    have lj: "length (A ! j) = n_cols A" using rect j by (simp add: is_rect_rows)
    have conv: "map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)
                  = map (\<lambda>l. fq ((A ! i) ! l + k * (A ! j) ! l)) [0..<n_cols A]"
      using li lj by (rule map2_conv_idx)
    have eq: "row = map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)"
      using p True i by (simp add: add_row_mult_def n_rows_def nth_list_update_eq)
    show ?thesis using eq conv nc by simp
  next
    case False
    have eq: "row = A ! p"
      using p False i by (simp add: add_row_mult_def n_rows_def nth_list_update_neq)
    have lp2: "length (A ! p) = n_cols A" using rect lp by (simp add: is_rect_rows n_rows_def)
    show ?thesis using eq lp2 nc by simp
  qed
qed

(* seg: shape-eliminate-20261023 *)
text \<open>@{const eliminate_col} is a fold of row additions over
  @{text "[0..<n_rows A]"}, so every fact above lifts to it by induction on the
  index list.  The bound hypothesis says every index the fold visits is a real
  row; @{const eliminate_col} discharges it because its list is exactly the row
  range.\<close>

lemma is_rect_eliminate_fold:
  assumes rect: "is_rect A" and r: "r < n_rows A" and ks: "\<forall>k\<in>set ks. k < n_rows A"
  shows "is_rect (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c)) A ks)"
  using assms
proof (induct ks arbitrary: A)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  have xb: "x < n_rows A" using Cons.prems by simp
  show ?case
  proof (cases "x = r")
    case True
    thus ?thesis using Cons.hyps [of A] Cons.prems by simp
  next
    case False
    have rA: "r < n_rows A" using Cons.prems by simp
    let ?B = "add_row_mult A x r (- entry A x c)"
    have nr: "n_rows ?B = n_rows A" by simp
    have rect2: "is_rect ?B"
    proof (rule is_rect_add_row_mult)
      show "is_rect A" using Cons.prems by simp
      show "x < n_rows A" using xb by simp
      show "r < n_rows A" using rA by simp
    qed
    have rb: "r < n_rows ?B" using rA nr by simp
    have xsb: "\<forall>k\<in>set xs. k < n_rows ?B" using Cons.prems nr by simp
    have ih: "is_rect (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c)) ?B xs)"
      using Cons.hyps [of ?B] rect2 rb xsb by simp
    show ?thesis using False ih by simp
  qed
qed

lemma n_cols_eliminate_fold:
  assumes rect: "is_rect A" and r: "r < n_rows A" and ks: "\<forall>k\<in>set ks. k < n_rows A"
  shows "n_cols (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c)) A ks)
           = n_cols A"
  using assms
proof (induct ks arbitrary: A)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  have xb: "x < n_rows A" using Cons.prems by simp
  show ?case
  proof (cases "x = r")
    case True
    thus ?thesis using Cons.hyps [of A] Cons.prems by simp
  next
    case False
    have rA: "r < n_rows A" using Cons.prems by simp
    let ?B = "add_row_mult A x r (- entry A x c)"
    have nr: "n_rows ?B = n_rows A" by simp
    have nc1: "n_cols ?B = n_cols A"
    proof (rule n_cols_add_row_mult)
      show "x < n_rows A" using xb by simp
      show "r < n_rows A" using rA by simp
      show "is_rect A" using Cons.prems by simp
    qed
    have rect2: "is_rect ?B"
    proof (rule is_rect_add_row_mult)
      show "is_rect A" using Cons.prems by simp
      show "x < n_rows A" using xb by simp
      show "r < n_rows A" using rA by simp
    qed
    have rb: "r < n_rows ?B" using rA nr by simp
    have xsb: "\<forall>k\<in>set xs. k < n_rows ?B" using Cons.prems nr by simp
    have ih: "n_cols (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c)) ?B xs)
                = n_cols ?B"
      using Cons.hyps [of ?B] rect2 rb xsb by simp
    show ?thesis using False ih nc1 by simp
  qed
qed

lemma minors_zero_eliminate_fold:
  assumes mz: "minors_zero A" and rect: "is_rect A" and r: "r < n_rows A"
    and ks: "\<forall>k\<in>set ks. k < n_rows A"
  shows "minors_zero (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c)) A ks)"
  using assms
proof (induct ks arbitrary: A)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  have xb: "x < n_rows A" using Cons.prems by simp
  show ?case
  proof (cases "x = r")
    case True
    thus ?thesis using Cons.hyps [of A] Cons.prems by simp
  next
    case False
    have rA: "r < n_rows A" using Cons.prems by simp
    let ?B = "add_row_mult A x r (- entry A x c)"
    have nr: "n_rows ?B = n_rows A" by simp
    have rect2: "is_rect ?B"
    proof (rule is_rect_add_row_mult)
      show "is_rect A" using Cons.prems by simp
      show "x < n_rows A" using xb by simp
      show "r < n_rows A" using rA by simp
    qed
    have mz2: "minors_zero ?B"
    proof (rule minors_zero_add_row)
      show "minors_zero A" using Cons.prems by simp
      show "x < n_rows A" using xb by simp
      show "r < n_rows A" using rA by simp
      show "x \<noteq> r" using False by simp
      show "is_rect A" using Cons.prems by simp
    qed
    have rb: "r < n_rows ?B" using rA nr by simp
    have xsb: "\<forall>k\<in>set xs. k < n_rows ?B" using Cons.prems nr by simp
    have ih: "minors_zero (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c)) ?B xs)"
      using Cons.hyps [of ?B] mz2 rect2 rb xsb by simp
    show ?thesis using False ih by simp
  qed
qed

lemma is_rect_eliminate_col:
  assumes rect: "is_rect A" and r: "r < n_rows A"
  shows "is_rect (eliminate_col A r c)"
  using assms by (simp add: eliminate_col_def is_rect_eliminate_fold)

lemma n_cols_eliminate_col:
  assumes rect: "is_rect A" and r: "r < n_rows A"
  shows "n_cols (eliminate_col A r c) = n_cols A"
  using assms by (simp add: eliminate_col_def n_cols_eliminate_fold)

lemma minors_zero_eliminate_col:
  assumes mz: "minors_zero A" and rect: "is_rect A" and r: "r < n_rows A"
  shows "minors_zero (eliminate_col A r c)"
  using assms by (simp add: eliminate_col_def minors_zero_eliminate_fold)

section \<open>Reflecting vanishing minors back through a row operation\<close>

text \<open>The lemmas above transport @{const minors_zero} forward through the three
  elementary row operations.  Transporting a statement about @{const rref} back to
  the matrix it was computed from needs the opposite direction, and that direction
  cannot be phrased as an equality of matrices: @{text "scale_row (scale_row A i q) i p"}
  agrees with @{text A} only up to @{text fq} on the touched row, two
  @{text add_row_mult} steps behave the same way, and @{text eliminate_col} is
  idempotent rather than invertible, so replaying it does not undo it.  The
  reflection lemmas are therefore stated on residues: a minor of the transformed
  matrix and the corresponding minor of the original differ by a multiple of the
  modulus.\<close>

text \<open>Two rewrites of @{text fq} that are used below.  They are proved from
  @{text fq_add} and @{text fq_mult} with controlled rewriting only: putting those
  two lemmas into the simplifier makes it rewrite @{text "fq (fq a * fq b)"} back to
  itself after @{text fq_idem}, which diverges.\<close>

lemma fq_add_fq: "fq (fq x + y) = fq (x + y)"
proof -
  have l: "fq (fq x + y) = fq (fq (fq x) + fq y)" by (rule fq_add)
  have r: "fq (x + y) = fq (fq x + fq y)" by (rule fq_add)
  show ?thesis using l r by (simp only: fq_idem)
qed

lemma dvd_fq_sub: "3329 dvd (fq x - x)"
proof -
  have h: "fq x - x = - (x - fq x)" by simp
  have d: "3329 dvd (x - fq x)" using dvd_fq_diff [of x] .
  have e: "3329 dvd - (x - fq x)" using d by (simp only: dvd_minus_iff)
  show ?thesis using h e by simp
qed

lemma fq_scale_cancel:
  assumes pq: "fq (p * q) = 1"
  shows "fq (p * fq (q * x)) = fq x"
proof -
  have a1: "fq (p * fq (q * x)) = fq (fq p * fq (fq (q * x)))" by (rule fq_mult)
  have a2: "fq (p * (q * x)) = fq (fq p * fq (q * x))" by (rule fq_mult)
  have a: "fq (p * fq (q * x)) = fq (p * (q * x))" using a1 a2 by (simp only: fq_idem)
  have b: "fq ((p * q) * x) = fq (fq (p * q) * fq x)" by (rule fq_mult)
  have c: "fq (fq (p * q) * fq x) = fq x" using pq by simp
  have d: "fq (p * (q * x)) = fq ((p * q) * x)" by (simp only: mult.assoc)
  show ?thesis using a b c d by simp
qed

lemma fq_add_cancel_aux: "fq (fq (x + k * y) - k * y) = fq x"
proof -
  have h1: "fq (fq (x + k * y) - k * y) = fq ((x + k * y) - k * y)"
    using fq_add_fq [of "x + k * y" "- (k * y)"] by simp
  also have "\<dots> = fq x" by simp
  finally show ?thesis .
qed

lemma fq_add_cancel: "fq (fq (x + k * y) + (- k) * y) = fq x"
proof -
  have h: "(- k) * y = - (k * y)" by simp
  show ?thesis using fq_add_cancel_aux [of x k y] h by simp
qed

text \<open>Two matrices whose four entries of a @{text "2 x 2"} block agree modulo the
  modulus have minors that agree modulo the modulus: the difference of the minors
  is a telescoping combination of the four entry differences.\<close>

lemma dvd_minor2_cong:
  assumes ac: "3329 dvd (entry B a c - entry A a c)"
    and bd: "3329 dvd (entry B b d - entry A b d)"
    and ad: "3329 dvd (entry B a d - entry A a d)"
    and bc: "3329 dvd (entry B b c - entry A b c)"
  shows "3329 dvd (minor2 B a b c d - minor2 A a b c d)"
proof -
  have eq: "minor2 B a b c d - minor2 A a b c d
      = ((entry B a c - entry A a c) * entry B b d
          + entry A a c * (entry B b d - entry A b d))
        - ((entry B a d - entry A a d) * entry B b c
          + entry A a d * (entry B b c - entry A b c))"
    by (simp add: minor2_def algebra_simps)
  have h1: "3329 dvd ((entry B a c - entry A a c) * entry B b d
                       + entry A a c * (entry B b d - entry A b d))"
    using ac bd by (simp add: dvd_add dvd_mult dvd_mult2)
  have h2: "3329 dvd ((entry B a d - entry A a d) * entry B b c
                       + entry A a d * (entry B b c - entry A b c))"
    using ad bc by (simp add: dvd_add dvd_mult dvd_mult2)
  show ?thesis using eq h1 h2 by (simp add: dvd_diff)
qed

text \<open>The entry formulas of the two operations are used below at a fixed row, so the
  instantiated forms are collected here; applying the general lemmas inside
  @{text simp} leaves their schematic row premise open.\<close>

lemma entry_scale_row_at_self:
  assumes i: "i < n_rows A" and rect: "is_rect A" and col: "col < n_cols A"
  shows "entry (scale_row A i k) i col = fq (k * entry A i col)"
  using entry_scale_row [OF i rect i col] by simp

lemma entry_scale_row_at_other:
  assumes i: "i < n_rows A" and rect: "is_rect A"
    and r: "r < n_rows A" and col: "col < n_cols A" and ri: "r \<noteq> i"
  shows "entry (scale_row A i k) r col = entry A r col"
  using entry_scale_row [OF i rect r col] ri by simp

lemma entry_add_row_mult_at_self:
  assumes i: "i < n_rows A" and j: "j < n_rows A" and rect: "is_rect A"
    and col: "col < n_cols A"
  shows "entry (add_row_mult A i j k) i col = fq (entry A i col + k * entry A j col)"
  using entry_add_row_mult [OF i j rect i col] by simp

lemma entry_add_row_mult_at_other:
  assumes i: "i < n_rows A" and j: "j < n_rows A" and rect: "is_rect A"
    and r: "r < n_rows A" and col: "col < n_cols A" and ri: "r \<noteq> i"
  shows "entry (add_row_mult A i j k) r col = entry A r col"
  using entry_add_row_mult [OF i j rect r col] ri by simp

text \<open>A swap is its own inverse on rows, so the reflection is exact: the minor of
  the original is the minor of the swapped matrix read at the permuted pair.\<close>

lemma minors_zero_swap_undo:
  assumes mz: "minors_zero (swap_rows A i j)"
    and i: "i < n_rows A" and j: "j < n_rows A" and rect: "is_rect A"
  shows "minors_zero A"
proof (rule minors_zeroI)
  fix a b c d
  assume a: "a < n_rows A" and b: "b < n_rows A"
    and c: "c < n_cols A" and d: "d < n_cols A"
  have nrS: "n_rows (swap_rows A i j) = n_rows A"
    by (simp add: swap_rows_def n_rows_def)
  have ncS: "n_cols (swap_rows A i j) = n_cols A"
    by (rule n_cols_swap_rows [OF i j rect])
  have al: "swap_idx i j a < n_rows A" using i j a by (rule swap_idx_lt)
  have bl: "swap_idx i j b < n_rows A" using i j b by (rule swap_idx_lt)
  have alS: "swap_idx i j a < n_rows (swap_rows A i j)" using al nrS by simp
  have blS: "swap_idx i j b < n_rows (swap_rows A i j)" using bl nrS by simp
  have cS: "c < n_cols (swap_rows A i j)" using c ncS by simp
  have dS: "d < n_cols (swap_rows A i j)" using d ncS by simp
  have dv: "3329 dvd minor2 (swap_rows A i j) (swap_idx i j a) (swap_idx i j b) c d"
    using mz alS blS cS dS by (rule minors_zeroE)
  have eq: "minor2 (swap_rows A i j) (swap_idx i j a) (swap_idx i j b) c d
              = minor2 A a b c d"
  proof -
    have "minor2 (swap_rows A i j) (swap_idx i j a) (swap_idx i j b) c d
            = minor2 A (swap_idx i j (swap_idx i j a)) (swap_idx i j (swap_idx i j b)) c d"
      using i j al bl by (rule minor2_swap)
    thus ?thesis by simp
  qed
  show "3329 dvd minor2 A a b c d" using dv eq by simp
qed

text \<open>Scaling by @{text q} is undone by scaling by @{text p} whenever
  @{text "p * q"} is a unit, which is what residue-level reflection needs, since the
  composite leaves the row unchanged only modulo the modulus.\<close>

lemma minors_zero_scale_row_undo:
  assumes mz: "minors_zero (scale_row A i q)"
    and i: "i < n_rows A" and rect: "is_rect A" and pq: "fq (p * q) = 1"
  shows "minors_zero A"
proof (rule minors_zeroI)
  fix a b c d
  assume a: "a < n_rows A" and b: "b < n_rows A"
    and c: "c < n_cols A" and d: "d < n_cols A"
  define B where "B = scale_row (scale_row A i q) i p"
  have rect1: "is_rect (scale_row A i q)" using rect i by (rule is_rect_scale_row)
  have nrB: "n_rows B = n_rows A" by (simp add: B_def)
  have ncB: "n_cols B = n_cols A"
  proof -
    have h1: "n_cols (scale_row A i q) = n_cols A" by (rule n_cols_scale_row)
    have h2: "n_cols (scale_row (scale_row A i q) i p) = n_cols (scale_row A i q)"
      by (rule n_cols_scale_row)
    show ?thesis using h1 h2 by (simp add: B_def)
  qed
  have rectB: "is_rect B"
  proof -
    have h: "is_rect (scale_row (scale_row A i q) i p)"
    proof (rule is_rect_scale_row)
      show "is_rect (scale_row A i q)" using rect1 .
      show "i < n_rows (scale_row A i q)" using i by simp
    qed
    thus ?thesis by (simp add: B_def)
  qed
  have mzB: "minors_zero B"
  proof -
    have h: "minors_zero (scale_row (scale_row A i q) i p)"
    proof (rule minors_zero_scale_row)
      show "minors_zero (scale_row A i q)" using mz .
      show "i < n_rows (scale_row A i q)" using i by simp
      show "is_rect (scale_row A i q)" using rect1 .
    qed
    thus ?thesis by (simp add: B_def)
  qed
  have cong: "\<And>r col. r < n_rows A \<Longrightarrow> col < n_cols A
                \<Longrightarrow> 3329 dvd (entry B r col - entry A r col)"
  proof -
    fix r col
    assume r: "r < n_rows A" and col: "col < n_cols A"
    show "3329 dvd (entry B r col - entry A r col)"
    proof (cases "r = i")
      case True
      have e1: "entry (scale_row A i q) i col = fq (q * entry A i col)"
        using i rect col by (simp add: entry_scale_row_at_self)
      have m: "i < n_rows (scale_row A i q)" using i by simp
      have c2: "col < n_cols (scale_row A i q)" using col by (simp add: n_cols_scale_row)
      have e2: "entry B i col = fq (p * entry (scale_row A i q) i col)"
      proof -
        have h: "entry (scale_row (scale_row A i q) i p) i col
                    = fq (p * entry (scale_row A i q) i col)"
          using entry_scale_row_at_self [OF m rect1 c2] .
        thus ?thesis by (simp add: B_def)
      qed
      have e3: "entry B i col = fq (entry A i col)"
        using e1 e2 pq by (simp add: fq_scale_cancel)
      show ?thesis using True e3 by (simp add: dvd_fq_sub)
    next
      case False
      have e1: "entry (scale_row A i q) r col = entry A r col"
        using i rect r col False by (simp add: entry_scale_row_at_other)
      have m: "i < n_rows (scale_row A i q)" using i by simp
      have mr: "r < n_rows (scale_row A i q)" using r by simp
      have c2: "col < n_cols (scale_row A i q)" using col by (simp add: n_cols_scale_row)
      have e2: "entry B r col = entry (scale_row A i q) r col"
      proof -
        have h: "entry (scale_row (scale_row A i q) i p) r col
                    = entry (scale_row A i q) r col"
          using entry_scale_row_at_other [OF m rect1 mr c2 False] .
        thus ?thesis by (simp add: B_def)
      qed
      show ?thesis using e1 e2 False by simp
    qed
  qed
  have aB: "a < n_rows B" using a nrB by simp
  have bB: "b < n_rows B" using b nrB by simp
  have cB: "c < n_cols B" using c ncB by simp
  have dB: "d < n_cols B" using d ncB by simp
  have dvB: "3329 dvd minor2 B a b c d"
    using mzB aB bB cB dB by (rule minors_zeroE)
  have h1: "3329 dvd (entry B a c - entry A a c)" using cong [OF a c] .
  have h2: "3329 dvd (entry B b d - entry A b d)" using cong [OF b d] .
  have h3: "3329 dvd (entry B a d - entry A a d)" using cong [OF a d] .
  have h4: "3329 dvd (entry B b c - entry A b c)" using cong [OF b c] .
  have dcong: "3329 dvd (minor2 B a b c d - minor2 A a b c d)"
    using dvd_minor2_cong [OF h1 h2 h3 h4] .
  have "3329 dvd (minor2 B a b c d - (minor2 B a b c d - minor2 A a b c d))"
    using dvB dcong by (rule dvd_diff)
  thus "3329 dvd minor2 A a b c d" by simp
qed

text \<open>Adding @{text "k"} times row @{text j} to row @{text i} is undone by adding
  @{text "- k"} times the same row; again the composite is the identity only modulo
  the modulus, so this reflection also lives on residues.\<close>

lemma minors_zero_add_row_undo:
  assumes mz: "minors_zero (add_row_mult A i j k)"
    and i: "i < n_rows A" and j: "j < n_rows A" and ij: "i \<noteq> j"
    and rect: "is_rect A"
  shows "minors_zero A"
proof (rule minors_zeroI)
  fix a b c d
  assume a: "a < n_rows A" and b: "b < n_rows A"
    and c: "c < n_cols A" and d: "d < n_cols A"
  define M where "M = add_row_mult A i j k"
  define B where "B = add_row_mult M i j (- k)"
  have rectM: "is_rect M"
  proof -
    have h: "is_rect (add_row_mult A i j k)" using rect i j by (rule is_rect_add_row_mult)
    thus ?thesis by (simp add: M_def)
  qed
  have nrM: "n_rows M = n_rows A" by (simp add: M_def)
  have nrB: "n_rows B = n_rows A" by (simp add: B_def M_def)
  have ncB: "n_cols B = n_cols A"
  proof -
    have h1: "n_cols (add_row_mult A i j k) = n_cols A"
      by (rule n_cols_add_row_mult [OF i j rect])
    have h2: "n_cols (add_row_mult M i j (- k)) = n_cols M"
    proof (rule n_cols_add_row_mult)
      show "i < n_rows M" using i by (simp add: nrM)
      show "j < n_rows M" using j by (simp add: nrM)
      show "is_rect M" using rectM .
    qed
    show ?thesis using h1 h2 by (simp add: B_def M_def)
  qed
  have mzB: "minors_zero B"
  proof -
    have h: "minors_zero (add_row_mult M i j (- k))"
    proof (rule minors_zero_add_row)
      show "minors_zero M" using mz by (simp add: M_def)
      show "i < n_rows M" using i by (simp add: nrM)
      show "j < n_rows M" using j by (simp add: nrM)
      show "i \<noteq> j" using ij .
      show "is_rect M" using rectM .
    qed
    thus ?thesis by (simp add: B_def)
  qed
  have ncM: "n_cols M = n_cols A"
  proof -
    have h: "n_cols (add_row_mult A i j k) = n_cols A"
      by (rule n_cols_add_row_mult [OF i j rect])
    thus ?thesis by (simp add: M_def)
  qed
  have cong: "\<And>r col. r < n_rows A \<Longrightarrow> col < n_cols A
                \<Longrightarrow> 3329 dvd (entry B r col - entry A r col)"
  proof -
    fix r col
    assume r: "r < n_rows A" and col: "col < n_cols A"
    have cM: "col < n_cols M" using ncM col by simp
    show "3329 dvd (entry B r col - entry A r col)"
    proof (cases "r = i")
      case True
      have e1: "entry M i col = fq (entry A i col + k * entry A j col)"
        using i j rect col by (simp add: M_def entry_add_row_mult_at_self)
      have m: "i < n_rows M" using i by (simp add: nrM)
      have mj: "j < n_rows M" using j by (simp add: nrM)
      have e2: "entry B i col = fq (entry M i col + (- k) * entry M j col)"
      proof -
        have h: "entry (add_row_mult M i j (- k)) i col
                    = fq (entry M i col + (- k) * entry M j col)"
          using entry_add_row_mult_at_self [OF m mj rectM cM] .
        thus ?thesis by (simp add: B_def)
      qed
      have ji: "j \<noteq> i" using ij by simp
      have e3: "entry M j col = entry A j col"
        using i j rect col ji by (simp add: M_def entry_add_row_mult_at_other)
      have key: "entry B i col
              = fq (fq (entry A i col + k * entry A j col)
                    + (- k) * entry A j col)"
        using e1 e2 e3 by simp
      have cancel: "fq (fq (entry A i col + k * entry A j col)
                    + (- k) * entry A j col) = fq (entry A i col)"
        by (simp add: fq_add_cancel_aux)
      have "entry B i col = fq (entry A i col)" using key cancel by simp
      thus ?thesis using True by (simp add: dvd_fq_sub)
    next
      case False
      have e1: "entry M r col = entry A r col"
        using i j rect r col False by (simp add: M_def entry_add_row_mult_at_other)
      have m: "i < n_rows M" using i by (simp add: nrM)
      have mj: "j < n_rows M" using j by (simp add: nrM)
      have mr: "r < n_rows M" using r by (simp add: nrM)
      have e2: "entry B r col = entry M r col"
      proof -
        have h: "entry (add_row_mult M i j (- k)) r col = entry M r col"
          using entry_add_row_mult_at_other [OF m mj rectM mr cM False] .
        thus ?thesis by (simp add: B_def)
      qed
      show ?thesis using e1 e2 False by simp
    qed
  qed
  have aB: "a < n_rows B" using a nrB by simp
  have bB: "b < n_rows B" using b nrB by simp
  have cB: "c < n_cols B" using c ncB by simp
  have dB: "d < n_cols B" using d ncB by simp
  have dvB: "3329 dvd minor2 B a b c d"
    using mzB aB bB cB dB by (rule minors_zeroE)
  have h1: "3329 dvd (entry B a c - entry A a c)" using cong [OF a c] .
  have h2: "3329 dvd (entry B b d - entry A b d)" using cong [OF b d] .
  have h3: "3329 dvd (entry B a d - entry A a d)" using cong [OF a d] .
  have h4: "3329 dvd (entry B b c - entry A b c)" using cong [OF b c] .
  have dcong: "3329 dvd (minor2 B a b c d - minor2 A a b c d)"
    using dvd_minor2_cong [OF h1 h2 h3 h4] .
  have "3329 dvd (minor2 B a b c d - (minor2 B a b c d - minor2 A a b c d))"
    using dvB dcong by (rule dvd_diff)
  thus "3329 dvd minor2 A a b c d" by simp
qed

end
