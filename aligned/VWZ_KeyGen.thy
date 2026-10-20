(*  Title:      VWZ_KeyGen.thy
    SPDX-License-Identifier: Apache-2.0

    Key generation: the deterministic draws of Sec 3.1-3.2, the row-addition
    matrix generator of Sec 3.3, and the KeyGen assembly of Sec 3.4-3.6.

    Scope, stated up front because it is easy to over-read:

      * This file defines the sampling *algorithms* and proves what they return
        -- partial correctness, not termination.
      * Rejection sampling terminates with probability 1, not by construction,
        so no unconditional "returns n points" theorem is proved here.  The
        guarantee is conditional on a non-empty result, which is exactly what
        the algorithm provides.
      * The ledger's T3_B1 is restated against this API, not weakened to fit
        it: the original wording quantified over a list-valued sampler that
        cannot exist.  The restated form carries the failure guard that the
        algorithm actually has, and it is discharged by the lemma below.
*)
theory VWZ_KeyGen
  imports VWZ_RREF
begin

section \<open>Fixed-length draws (spec Sec 3.2)\<close>

text \<open>Draw @{text n} values in @{text "[1, q)"} from a state.  The state is
  threaded explicitly, which is the point: the spec's generator is a state
  machine, not a list.\<close>

fun draw_list :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<times> nat" where
  "draw_list 0 s = ([], s)"
| "draw_list (Suc n) s =
     (fst (randrange 1 3329 s) # fst (draw_list n (snd (randrange 1 3329 s))),
      snd (draw_list n (snd (randrange 1 3329 s))))"

lemma draw_list_len [simp]: "length (fst (draw_list n s)) = n"
proof (induction n arbitrary: s)
  case 0
  then show ?case by (simp add: draw_list.simps)
next
  case (Suc n)
  obtain a st1 where d1: "randrange (Suc 0) 3329 s = (a, st1)"
    by (cases "randrange (Suc 0) 3329 s") auto
  obtain ys st2 where d2: "draw_list n st1 = (ys, st2)"
    by (cases "draw_list n st1") auto
  have step: "fst (draw_list (Suc n) s) = a # fst (draw_list n st1)"
    by (simp add: draw_list.simps d1)
  then show ?case using Suc.IH[of st1] d2 by simp
qed

lemma draw_list_range:
  "set (fst (draw_list n s)) \<subseteq> {1..<3329}"
proof (induction n arbitrary: s)
  case 0
  then show ?case by (simp add: draw_list.simps)
next
  case (Suc n)
  obtain a st1 where d1: "randrange (Suc 0) 3329 s = (a, st1)"
    by (cases "randrange (Suc 0) 3329 s") auto
  obtain ys st2 where d2: "draw_list n st1 = (ys, st2)"
    by (cases "draw_list n st1") auto
  have r: "1 \<le> a \<and> a < 3329"
    using d1 randrange_range[of 1 3329 s] by (simp add: One_nat_def)
  have step: "fst (draw_list (Suc n) s) = a # fst (draw_list n st1)"
    by (simp add: draw_list.simps d1)
  then show ?case using Suc.IH[of st1] r d2 by auto
qed

section \<open>Distinct evaluation points (spec Sec 3.2)\<close>

text \<open>The spec says "repeat ... until all pairwise distinct".  That is a loop
  whose length is not bounded by the input, so it is fuel-parameterised the
  same way the reduction is: fuel bounds how many *rounds* of drawing are
  attempted, and running out returns the empty list.  Callers must therefore
  treat @{text "[]"} as failure, which is also what the spec's retry logic
  does.\<close>

fun distinct_lam_fuel :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<times> nat" where
  "distinct_lam_fuel 0 n s = ([], s)"
| "distinct_lam_fuel (Suc f) n s =
     (if distinct (fst (draw_list n s))
      then (fst (draw_list n s), snd (draw_list n s))
      else distinct_lam_fuel f n (snd (draw_list n s)))"

text \<open>Partial correctness: if it returns anything, the result is @{text n}
  points, pairwise distinct, inside @{text "[1, q)"}.  Those are the three
  conjuncts of T3_B1, minus the unconditional existence that rejection sampling
  cannot give without a probabilistic termination proof.\<close>

lemma distinct_lam_fuel_correct:
  "fst (distinct_lam_fuel f n s) \<noteq> [] \<Longrightarrow>
     length (fst (distinct_lam_fuel f n s)) = n \<and>
     distinct (fst (distinct_lam_fuel f n s)) \<and>
     set (fst (distinct_lam_fuel f n s)) \<subseteq> {1..<3329}"
proof (induction f arbitrary: n s)
  case 0
  then show ?case by (simp add: distinct_lam_fuel.simps)
next
  case (Suc f)
  obtain pts st1 where d: "draw_list n s = (pts, st1)"
    by (cases "draw_list n s") auto
  show ?case
  proof (cases "distinct pts")
    case True
    have eq: "fst (distinct_lam_fuel (Suc f) n s) = pts"
      by (simp add: distinct_lam_fuel.simps d True)
    have len: "length pts = n"
    proof -
      have "pts = fst (draw_list n s)" using d by simp
      then show ?thesis by (simp add: draw_list_len)
    qed
    have sub: "set pts \<subseteq> {1..<3329}"
    proof -
      have "set pts = set (fst (draw_list n s))" using d by simp
      then show ?thesis using draw_list_range[of n s] by (simp add: One_nat_def)
    qed
    with eq len True show ?thesis by simp
  next
    case False
    have eq: "fst (distinct_lam_fuel (Suc f) n s) =
              fst (distinct_lam_fuel f n st1)"
      by (simp add: distinct_lam_fuel.simps d False)
    then show ?thesis
      using Suc.prems Suc.IH[of n st1] by simp
  qed
qed

text \<open>Satisfiability check on the recurrence itself: one step of the LCG from the
  zero state returns the increment, so the two constants are wired the way the
  spec writes them and not swapped.  A single step is used on purpose:
  @{text eval} over the full 64-bit recurrence is slow enough to be unusable as
  a build step (it did not finish in 90 s), so the generator is covered by the
  partial-correctness lemma above rather than by brute-force evaluation.\<close>

lemma lcg_step_zero: "lcg_step 0 = 1442695040888963407"
  by (simp add: lcg_step_def lcg_mod_def)

section \<open>The sampler as a named operation (spec Sec 3.2)\<close>

text \<open>The spec names @{text "distinct_lam n"} and treats it as total.  The
  implementation is rejection sampling, so it is total only in the sense that
  it always returns a pair; the list is empty when the fuel runs out.  The fuel
  is chosen generously (@{text "8 * n + 8"} rounds, each drawing @{text n}
  points) so that exhaustion is a theoretical corner rather than an operational
  one; no probabilistic bound is claimed here.\<close>

definition distinct_lam :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<times> nat" where
  "distinct_lam n s = distinct_lam_fuel (8 * n + 8) n s"

lemma distinct_lam_partial_correct:
  "fst (distinct_lam n s) \<noteq> [] \<Longrightarrow>
     length (fst (distinct_lam n s)) = n \<and>
     distinct (fst (distinct_lam n s)) \<and>
     set (fst (distinct_lam n s)) \<subseteq> {1..<3329}"
  unfolding distinct_lam_def
  by (rule distinct_lam_fuel_correct)


section \<open>Spec 3.3 -- random invertible matrices by row additions\<close>

text \<open>The spec writes a fixed loop of @{text "m\<^sup>2"} rounds, so the round count
  is structural: no fuel argument is needed here, and none is invented.  Each
  round draws @{text i} and @{text j} unconditionally -- the @{text "i = j"}
  branch still consumes both draws, which the spec calls out explicitly -- and
  only then, when @{text "i \<noteq> j"}, draws the factor.

  Two honest limits.  (1) @{text add_row_mult} is total in HOL, so out-of-range
  indices are defined rather than rejected; the guard is the caller's, and
  @{text "next_u16_mod m"} keeps it in range for @{text "0 < m"}.  (2) This defines
  what the algorithm computes; it does not prove that the result is invertible.
  That is T2_B3, and it needs determinant or elementary-matrix reasoning that
  the library layer does not have yet.\<close>

fun rim_iter :: "nat \<Rightarrow> nat \<Rightarrow> mat \<Rightarrow> nat \<Rightarrow> mat \<times> nat" where
  "rim_iter 0 m A s = (A, s)"
| "rim_iter (Suc f) m A s =
     (let (i, s1) = next_u16_mod m s;
          (j, s2) = next_u16_mod m s1
      in (if i = j then rim_iter f m A s2
          else (let (c, s3) = randrange 1 3329 s2
                in rim_iter f m (add_row_mult A i j (int c)) s3)))"

definition random_invertible_matrix :: "nat \<Rightarrow> nat \<Rightarrow> mat \<times> nat" where
  "random_invertible_matrix m s = rim_iter (m * m) m (id_mat m) s"

lemma add_row_mult_n_rows [simp]:
  "n_rows (add_row_mult A i j k) = n_rows A"
  by (simp add: n_rows_def add_row_mult_def)

lemma rim_iter_n_rows [simp]:
  "n_rows (fst (rim_iter f m A s)) = n_rows A"
proof (induction f arbitrary: A s)
  case 0
  then show ?case by (simp add: rim_iter.simps)
next
  case (Suc f)
  obtain i s1 where d1: "next_u16_mod m s = (i, s1)"
    by (cases "next_u16_mod m s") auto
  obtain j s2 where d2: "next_u16_mod m s1 = (j, s2)"
    by (cases "next_u16_mod m s1") auto
  show ?case
  proof (cases "i = j")
    case True
    then show ?thesis using Suc.IH d1 d2 by (simp add: rim_iter.simps)
  next
    case False
    obtain c s3 where d3: "randrange (Suc 0) 3329 s2 = (c, s3)"
      by (cases "randrange (Suc 0) 3329 s2") auto
    have "n_rows (fst (rim_iter f m (add_row_mult A i j (int c)) s3)) =
          n_rows (add_row_mult A i j (int c))"
      using Suc.IH by simp
    then show ?thesis
      using False d1 d2 d3 by (simp add: rim_iter.simps)
  qed
qed

lemma rim_iter_square:
  "\<lbrakk> n_rows A = m; \<forall>r \<in> set A. length r = m \<rbrakk> \<Longrightarrow>
   n_rows (fst (rim_iter f m A s)) = m"
  by simp

section \<open>Spec 3.2 -- the three evaluation-point lists\<close>

text \<open>Positions and field elements are both carried as @{typ int} in the protocol
  layer, so the sampled @{typ nat} lists are coerced once, here, and not at each
  use site.\<close>

definition lams_of :: "nat \<Rightarrow> nat \<Rightarrow> int list \<times> int list \<times> int list \<times> nat" where
  "lams_of n s =
     (let (la, s1) = distinct_lam n s;
          (lb, s2) = distinct_lam n s1;
          (lc, s3) = distinct_lam n s2
      in (map int la, map int lb, map int lc, s3))"

section \<open>Spec 3.3 -- the four matrices, in the order the spec fixes\<close>

definition mats_of :: "nat \<Rightarrow> nat \<Rightarrow> mat \<times> mat \<times> mat \<times> mat \<times> nat" where
  "mats_of m s =
     (let (A, s1) = random_invertible_matrix m s;
          (B, s2) = random_invertible_matrix m s1;
          (C, s3) = random_invertible_matrix m s2;
          (D, s4) = random_invertible_matrix m s3
      in (A, B, C, D, s4))"

text \<open>Named projections, so obligations can say @{text "X2a_of m s"} instead of
  counting @{text snd}s.  They are views on @{text mats_of}, not independent
  draws: the state is threaded once, in @{text mats_of}.\<close>

definition X2a_of :: "nat \<Rightarrow> nat \<Rightarrow> mat" where
  "X2a_of m s = fst (mats_of m s)"

definition X2b_of :: "nat \<Rightarrow> nat \<Rightarrow> mat" where
  "X2b_of m s = fst (snd (mats_of m s))"

definition X3a_of :: "nat \<Rightarrow> nat \<Rightarrow> mat" where
  "X3a_of m s = fst (snd (snd (mats_of m s)))"

definition X3b_of :: "nat \<Rightarrow> nat \<Rightarrow> mat" where
  "X3b_of m s = fst (snd (snd (snd (mats_of m s))))"

definition mats_succ :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mats_succ m s = snd (snd (snd (snd (mats_of m s))))"

section \<open>Spec 3.4 -- the secret vector x1\<close>

fun draw_x1 :: "nat \<Rightarrow> nat \<Rightarrow> int list \<times> nat" where
  "draw_x1 0 s = ([], s)"
| "draw_x1 (Suc n) s =
     (let (v, s1) = randrange 1 3329 s;
          (xs, s2) = draw_x1 n s1
      in (int v # xs, s2))"

lemma draw_x1_len [simp]: "length (fst (draw_x1 n s)) = n"
proof (induction n arbitrary: s)
  case 0
  then show ?case by (simp add: draw_x1.simps)
next
  case (Suc n)
  obtain v s1 where d1: "randrange (Suc 0) 3329 s = (v, s1)"
    by (cases "randrange (Suc 0) 3329 s") auto
  obtain xs s2 where d2: "draw_x1 n s1 = (xs, s2)"
    by (cases "draw_x1 n s1") auto
  then show ?case using Suc.IH[of s1] d1 d2 by (simp add: draw_x1.simps)
qed

lemma draw_x1_range:
  "set (fst (draw_x1 n s)) \<subseteq> {1..<3329}"
proof (induction n arbitrary: s)
  case 0
  then show ?case by (simp add: draw_x1.simps)
next
  case (Suc n)
  obtain v s1 where d1: "randrange (Suc 0) 3329 s = (v, s1)"
    by (cases "randrange (Suc 0) 3329 s") auto
  obtain xs s2 where d2: "draw_x1 n s1 = (xs, s2)"
    by (cases "draw_x1 n s1") auto
  have vrange: "1 \<le> v \<and> v < 3329"
    using randrange_range[of "Suc 0" 3329 s] d1 by simp
  have ih: "set xs \<subseteq> {1..<3329}" using Suc.IH[of s1] d2 by simp
  show ?case using vrange ih d1 d2 by (simp add: draw_x1.simps)
qed

section \<open>Spec 3.5 -- the public tensor\<close>

definition transpose :: "mat \<Rightarrow> mat" where
  "transpose A = map (\<lambda>j. map (\<lambda>r. r ! j) A) [0..<n_cols A]"

text \<open>One @{text "m \<times> m"} slice: @{text "x0 * (ua[i2] * va[i3] + ub[i2] * vb[i3])"},
  reduced modulo @{text q}.  @{text map2} zips the two outer-product factors, so
  the index pair @{text "(i2, i3)"} is carried by construction rather than by
  @{text nth}.\<close>

definition psi_slice_of :: "int \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> mat" where
  "psi_slice_of x0 ua va ub vb =
     map2 (\<lambda>a b. map2 (\<lambda>c d. (x0 * (a * c + b * d)) mod 3329) va vb) ua ub"

definition psi_of ::
  "nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow>
   mat \<Rightarrow> mat \<Rightarrow> mat \<Rightarrow> mat \<Rightarrow> int list \<Rightarrow> int list list list" where
  "psi_of n m la lb lc X2a X2b X3a X3b x1 =
     map (\<lambda>i. psi_slice_of (x1 ! i)
                (matvec (transpose X2a) (vand (la ! i) m))
                (matvec (transpose X3a) (vand (lc ! i) m))
                (matvec (transpose X2b) (vand (lb ! i) m))
                (matvec (transpose X3b) (vand (lc ! i) m)))
         [0..<n]"

section \<open>Spec 3.6 -- KeyGen\<close>

text \<open>The order of draws is normative (Sec 3.2, then 3.3, then 3.4); reordering
  them would change every output byte, so the lets follow the spec's order
  rather than dependency order.  The secret key stores the values Sec 3.6 lists,
  including the two inverses and the two products, computed with the definitions
  already in @{text VWZ_RREF} -- they are not separate draws.\<close>

definition KeyGen :: "nat \<Rightarrow> nat \<Rightarrow> pkey \<times> skey" where
  "KeyGen k seed =
     (let n = par_n k; m = par_m k;
          (la, lb, lc, s1) = lams_of n (lcg_init seed);
          (X2a, X2b, X3a, X3b, s2) = mats_of m s1;
          (x1, s3) = draw_x1 n s2
      in (\<lparr> pk_k = k,
             pk_psi = psi_of n m la lb lc X2a X2b X3a X3b x1 \<rparr>,
          \<lparr> sk_k = k, sk_lam_a = la, sk_lam_b = lb, sk_lam_c = lc,
             sk_a2inv = mat_inv X2a, sk_a3inv = mat_inv X3a,
             sk_m2 = mat_mult X2b (mat_inv X2a),
             sk_m3 = mat_mult X3b (mat_inv X3a),
             sk_x1 = x1, sk_seed = seed \<rparr>))"

end
