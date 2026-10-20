(*  Title:      VWZ_RREF.thy
    SPDX-License-Identifier: Apache-2.0

    VWZ A3 -- elementary row operations (PROOF TOOLING, not obligations).

    Scope: the three elementary row operations as matrices, the structural
    facts that follow directly from their definitions, and two primitives a
    scale-matrix inverse proof needs.

    Honest status: the row-operation matrices and their degeneration laws are
    proved.  The inverse laws (mat_mult E E' = id_mat) are NOT proved here --
    they are recorded in the formalization notes as open work, because they
    need a full sum-splitting argument over mat_mult.

    What IS here: a fuel-parameterised Gauss-Jordan reduction (rref), and the
    two definitions that were previously uninterpreted constants -- mat_rank
    and dim_nullspace.  Fuel makes the recursion structural, so no termination
    proof is needed; correctness of the reduction (that it reaches a normal
    form, and that mat_rank is the field rank) is NOT claimed and is not
    proved.  The definitions are executable, and the evaluation lemmas at the
    end of the RREF section are the evidence for that.

    mat_inv and mat_solve remain uninterpreted constants in VWZ_Matrix: both
    need the augmented-matrix solve, which is the next step.

    Convention on dim_nullspace: it is n_rows A - mat_rank A, not
    n_cols A - mat_rank A.  That is the convention T2_D4 is stated in (it
    bounds k - 1 for a (k+1)-row matrix), and it matches the spec's use of the
    row count.  The textbook nullity of the column space is the other one;
    the difference is recorded here rather than papered over.
*)
theory VWZ_RREF
  imports VWZ_Aux
begin

section \<open>Elementary row operations as matrices\<close>

definition row_swap_matrix :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> mat" where
  "row_swap_matrix m i j =
     map (\<lambda>r. map (\<lambda>c. if r = i then (if c = j then 1 else 0)
                              else (if r = j then (if c = i then 1 else 0)
                                    else (if r = c then 1 else 0))) [0..<m]) [0..<m]"

definition row_scale_matrix :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> mat" where
  "row_scale_matrix m i c =
     map (\<lambda>r. map (\<lambda>col. if r = i \<and> col = i then c
                              else (if r = col then 1 else 0)) [0..<m]) [0..<m]"

text \<open>--- R1.1: a self-swap is the identity ---\<close>
lemma aux_rref_swap_self: "row_swap_matrix m i i = id_mat m"
  by (simp add: row_swap_matrix_def id_mat_def)

text \<open>--- R1.2: swap is symmetric in its two indices ---\<close>
lemma aux_rref_swap_comm: "row_swap_matrix m i j = row_swap_matrix m j i"
  by (simp add: row_swap_matrix_def)

text \<open>--- R1.3: scaling a row by 1 is the identity ---\<close>
lemma aux_rref_scale_one: "row_scale_matrix m i 1 = id_mat m"
  by (simp add: row_scale_matrix_def id_mat_def)

text \<open>--- R1.4: out-of-range indices never fire ---\<close>
lemma aux_rref_swap_nofire:
  assumes "m \<le> i" and "m \<le> j"
  shows "row_swap_matrix m i j = id_mat m"
  by (simp add: row_swap_matrix_def id_mat_def) (use assms in simp)

lemma aux_rref_scale_nofire:
  assumes "m \<le> i"
  shows "row_scale_matrix m i c = id_mat m"
  by (simp add: row_scale_matrix_def id_mat_def) (use assms in simp)

text \<open>--- R1.5: scaling a row by 0 gives an all-zero row ---\<close>
lemma aux_rref_scale_zero_row:
  assumes im: "i < m"
  shows "row_scale_matrix m i 0 ! i = replicate m 0"
proof -
  have idx: "i < length [0..<m]" using im by simp
  have a: "row_scale_matrix m i 0 ! i
         = map (\<lambda>col. if i = i \<and> col = i then (0::int)
              else (if i = col then 1 else 0)) [0..<m]"
    using idx by (simp add: row_scale_matrix_def nth_map)
  have b: "map (\<lambda>col. if i = i \<and> col = i then (0::int)
              else (if i = col then 1 else 0)) [0..<m]
         = map (\<lambda>col. (0::int)) [0..<m]"
    by (rule map_cong) simp_all
  have c: "map (\<lambda>col. (0::int)) [0..<m] = replicate m 0"
    by (simp add: map_replicate_const)
  show ?thesis using a b c by simp
qed

text \<open>--- R1.6: a zero row forces the determinant to vanish ---\<close>
lemma aux_rref_det_scale_zero:
  assumes im: "i < m"
  shows "det (row_scale_matrix m i 0) = 0"
proof -
  have row: "row_scale_matrix m i 0 ! i = replicate m 0"
    by (rule aux_rref_scale_zero_row) (rule im)
  have zrep: "zrow (replicate m (0::int))"
    by (simp add: aux_zrow_iff)
  have zr: "zrow (row_scale_matrix m i 0 ! i)"
    using row zrep by simp
  have len: "length (row_scale_matrix m i 0) = m"
    by (simp add: row_scale_matrix_def)
  have mem: "row_scale_matrix m i 0 ! i \<in> set (row_scale_matrix m i 0)"
    by (rule nth_mem) (use im len in simp)
  have zhas: "zhas (row_scale_matrix m i 0)"
    using zr mem by (auto simp: zhas_def)
  show ?thesis by (rule aux_det_zero_row) (rule zhas)
qed

lemma aux_rref_map_zero_replicate:
  assumes "\<And>k. k < n \<Longrightarrow> f k = (0::int)"
  shows "map f [0..<n] = replicate n 0"
proof -
  have a: "map f [0..<n] = map (\<lambda>k. (0::int)) [0..<n]"
    by (rule map_cong) (use assms in simp_all)
  have b: "map (\<lambda>k. (0::int)) [0..<n] = replicate n 0"
    by (simp add: map_replicate_const)
  show ?thesis using a b by simp
qed

text \<open>--- Single-point collapse: single-point collapse of a sum ---\<close>
lemma aux_rref_sum_single:
  assumes "i < n"
  shows "sum_list (map (\<lambda>k. if k = i then (x::int) else 0) [0..<n]) = x"
  using assms
proof (induct n)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have split: "[0..<Suc n] = [0..<n] @ [n]"
    by (rule upt_Suc_append) simp
  show ?case
  proof (cases "i = n")
    case True
    have g0: "\<And>k. k < n \<Longrightarrow> (if k = i then (x::int) else 0) = 0"
      using True by simp
    have mz: "map (\<lambda>k. if k = i then (x::int) else 0) [0..<n] = replicate n (0::int)"
      by (rule aux_rref_map_zero_replicate) (rule g0)
    have last: "(if n = i then (x::int) else 0) = x" using True by simp
    have "map (\<lambda>k. if k = i then (x::int) else 0) ([0..<n] @ [n])
         = replicate n (0::int) @ [x]"
      using mz last by simp
    hence "sum_list (map (\<lambda>k. if k = i then (x::int) else 0) ([0..<n] @ [n]))
         = sum_list (replicate n (0::int)) + x"
      by simp
    hence "sum_list (map (\<lambda>k. if k = i then (x::int) else 0) ([0..<n] @ [n])) = x"
      by (simp add: aux_sum_list_zero)
    thus ?thesis using split by simp
  next
    case False
    hence inlt: "i < n" using Suc.prems by simp
    have gn: "(if n = i then (x::int) else 0) = 0" using False by simp
    have "map (\<lambda>k. if k = i then (x::int) else 0) ([0..<n] @ [n])
         = map (\<lambda>k. if k = i then (x::int) else 0) [0..<n] @ [0]"
      using gn by simp
    hence "sum_list (map (\<lambda>k. if k = i then (x::int) else 0) ([0..<n] @ [n]))
         = sum_list (map (\<lambda>k. if k = i then (x::int) else 0) [0..<n])"
      by simp
    also have "\<dots> = x" using Suc.hyps [OF inlt] by simp
    finally show ?thesis using split by simp
  qed
qed

text \<open>--- Unit-vector dot product: dot of two unit-like vectors ---\<close>
lemma aux_rref_dot_unit:
  assumes "i < n" and "j < n"
  shows "dot (map (\<lambda>c. if c = i then (a::int) else 0) [0..<n])
             (map (\<lambda>c. if c = j then b else 0) [0..<n])
       = (if i = j then a * b else 0)"
proof -
  have prod: "\<And>k. (if k = i then (a::int) else 0) * (if k = j then b else 0)
            = (if i = j then (if k = i then a * b else 0) else 0)"
  proof -
    fix k
    show "(if k = i then (a::int) else 0) * (if k = j then b else 0)
        = (if i = j then (if k = i then a * b else 0) else 0)"
    proof (cases "i = j")
      case True
      thus ?thesis by (cases "k = i") simp_all
    next
      case False
      show ?thesis
      proof (cases "k = i")
        case True
        hence "k \<noteq> j" using False by simp
        thus ?thesis using True False by simp
      next
        case False
        thus ?thesis using False by simp
      qed
    qed
  qed
  have "dot (map (\<lambda>c. if c = i then (a::int) else 0) [0..<n])
            (map (\<lambda>c. if c = j then b else 0) [0..<n])
      = sum_list (map2 (\<lambda>x y. x * y)
            (map (\<lambda>c. if c = i then (a::int) else 0) [0..<n])
            (map (\<lambda>c. if c = j then b else 0) [0..<n]))"
    by (simp add: dot_def)
  also have "\<dots> = sum_list (map (\<lambda>k. (if k = i then (a::int) else 0)
                          * (if k = j then b else 0)) [0..<n])"
    by (simp add: map2_map_map)
  also have "\<dots> = sum_list (map (\<lambda>k. (if i = j then (if k = i then a * b else 0) else 0))
                          [0..<n])"
    by (rule arg_cong [where f = sum_list])
       (rule map_cong, simp_all add: prod)
  also have "\<dots> = (if i = j then a * b else 0)"
  proof (cases "i = j")
    case True
    hence "map (\<lambda>k. (if i = j then (if k = i then a * b else 0) else 0)) [0..<n]
         = map (\<lambda>k. if k = i then a * b else 0) [0..<n]"
      by simp
    thus ?thesis using True aux_rref_sum_single [OF assms(1)] by simp
  next
    case False
    have z: "\<And>k. k < n \<Longrightarrow>
              (if i = j then (if k = i then a * b else 0) else 0) = (0::int)"
      using False by simp
    have "map (\<lambda>k. (if i = j then (if k = i then a * b else 0) else 0)) [0..<n]
        = replicate n (0::int)"
      by (rule aux_rref_map_zero_replicate) (rule z)
    thus ?thesis using False by (simp add: aux_sum_list_zero)
  qed
  finally show ?thesis .
qed

section \<open>Gauss-Jordan reduction, fuel-parameterised\<close>

text \<open>The reduction carries an explicit fuel argument, so the recursion is
  structural in the fuel and no termination proof is needed.  Fuel is consumed
  whether or not a pivot is found, and the bound used by @{text rref} is one
  more than the number of cells, which covers the worst case (every column
  scanned, every row used).\<close>

definition fq :: "int \<Rightarrow> int" where
  "fq x = x mod 3329"

definition all_zero_row :: "int list \<Rightarrow> bool" where
  "all_zero_row r = (\<forall>x \<in> set r. fq x = 0)"

text \<open>First row at or below @{text r} whose entry in column @{text c} is
  nonzero modulo @{text q}.  Fuel-bounded for the same reason as the
  reduction itself.\<close>

fun find_pivot_fuel :: "nat \<Rightarrow> mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "find_pivot_fuel 0 A r c = None"
| "find_pivot_fuel (Suc f) A r c =
     (if r < n_rows A \<and> fq (entry A r c) \<noteq> 0 then Some r
      else if r < n_rows A then find_pivot_fuel f A (r + 1) c
      else None)"

definition swap_rows :: "mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> mat" where
  "swap_rows A i j = (A[i := A ! j])[j := A ! i]"

definition scale_row :: "mat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> mat" where
  "scale_row A i k = A[i := map (\<lambda>x. fq (k * x)) (A ! i)]"

definition add_row_mult :: "mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> mat" where
  "add_row_mult A i j k = A[i := map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)]"

text \<open>Subtract from every other row the multiple of the pivot row that clears
  column @{text c}.  Rows are visited by index, which keeps the definition
  executable without a separate map-with-index.\<close>

definition eliminate_col :: "mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> mat" where
  "eliminate_col A r c =
     foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- (entry B k c)))
           A [0..<n_rows A]"

fun rref_fuel :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> mat \<Rightarrow> mat" where
  "rref_fuel 0 r c A = A"
| "rref_fuel (Suc f) r c A =
     (if r < n_rows A \<and> c < n_cols A then
        (case find_pivot_fuel (n_rows A) A r c of
           None \<Rightarrow> rref_fuel f r (c + 1) A
         | Some i \<Rightarrow>
             (let A1 = swap_rows A r i;
                  p  = entry A1 r c;
                  A2 = scale_row A1 r (invmod p);
                  A3 = eliminate_col A2 r c
              in rref_fuel f (r + 1) (c + 1) A3))
      else A)"

definition rref :: "mat \<Rightarrow> mat" where
  "rref A = rref_fuel (n_rows A * n_cols A + n_rows A + 1) 0 0 A"

text \<open>Rank as the number of nonzero rows of the reduced form.  This is the
  definition the T2 obligations now refer to; that it agrees with the field
  rank is a theorem, not a definition, and it is not proved yet.\<close>

definition mat_rank :: "mat \<Rightarrow> nat" where
  "mat_rank A = length (filter (\<lambda>r. \<not> all_zero_row r) (rref A))"

text \<open>Nullspace dimension in the row-count convention of the spec and of
  T2_D4: @{text "n_rows A - mat_rank A"}.  This is the nullity of the transpose
  map, not of the column space; see the file header.\<close>

definition dim_nullspace :: "mat \<Rightarrow> nat" where
  "dim_nullspace A = n_rows A - mat_rank A"

text \<open>The one lemma about the definition that is worth having: unfolding it.
  Kept here rather than in the obligation file so that the ledger counts only
  obligations.\<close>

lemma mat_rank_unfold:
  "mat_rank A = length (filter (\<lambda>r. \<not> all_zero_row r) (rref A))"
  by (simp add: mat_rank_def)

text \<open>Three evaluation checks.  These are not theorems about rank in general:
  they show that the definitions compute, on the identity, on a rank-1 2x2
  matrix, and on the nullspace count.  If the fuel bound were too small, or a
  step did not fire, these would fail.\<close>

lemma rref_rank_identity_2: "mat_rank [[1,0],[0,1]] = 2"
  by eval

lemma rref_rank_singular_2: "mat_rank [[1,2],[2,4]] = 1"
  by eval

lemma rref_dim_nullspace_singular_2: "dim_nullspace [[1,2],[2,4]] = 1"
  by eval

text \<open>Probes shaped like the T2_B7 subject: a 3x3 slice of full rank, and the
  same slice with its last row zeroed.  If these came out as anything other
  than 3 and 2, the rank definition would be wrong before any obligation is
  attempted.\<close>

lemma rref_rank_full_3: "mat_rank [[1,2,3],[0,1,4],[0,0,1]] = 3"
  by eval

lemma rref_rank_slice_3: "mat_rank [[1,0,0],[0,1,0],[0,0,0]] = 2"
  by eval

section \<open>Scope note\<close>

text \<open>The determinant of \<open>row_add_matrix\<close> is proved in \<open>VWZ_Aux\<close>
  (\<open>T2_B2\<close>).  The determinant laws for swaps and scalings are not
  formalised: the sign law for a swap needs an alternation argument, which is
  a separate development.

  \<open>mat_rank\<close> and \<open>dim_nullspace\<close> are now DEFINED (by fuel-counted
  Gauss-Jordan), so the T2 obligations that mention them are no longer
  statements about uninterpreted functions.  They remain open for a different
  reason: \<open>psi_slice\<close> and \<open>rows3_of\<close> -- the matrices those obligations
  are about -- are themselves uninterpreted constants.  A rank obligation
  about an undefined matrix cannot be closed by proving a rank theorem.\<close>

end
