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
  imports VWZ_ModAlgebra
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

section \<open>Minors of a matrix of rank at most one\<close>

text \<open>Everything here is preparation for @{text rank_le_one_imp_minors_vanish}.
  Two facts carry the weight: on the counting side, a list in which fewer than two
  positions satisfy a predicate, and on the arithmetic side, a \<open>2 x 2\<close>
  determinant with a row whose entries are all @{text 0} modulo @{text 3329}.

  Note that @{text all_zero_row} is the modulo-@{text q} notion: it says
  @{text "fq x = 0"} for each entry, so the vanishing it induces is congruence
  modulo @{text 3329}, not integer equality.  The @{text zrow} predicate of
  @{file VWZ_Aux.thy} is the stricter integer notion and is deliberately not used
  here, because @{text rref} reduces every entry modulo @{text q} as it goes.\<close>

lemma filter_le_one_two_positions:
  fixes P :: "'a \<Rightarrow> bool" and xs :: "'a list" and i j :: nat
  assumes len: "length (filter P xs) \<le> 1"
    and il: "i < length xs" and jl: "j < length xs" and ij: "i \<noteq> j"
    and Pi: "P (xs ! i)" and Pj: "P (xs ! j)"
  shows False
proof -
  let ?S = "{k. k < length xs \<and> P (xs ! k)}"
  have card_le: "card ?S \<le> 1"
    using len by (simp add: length_filter_conv_card)
  have sub_lt: "?S \<subseteq> {..<length xs}" by auto
  have fin: "finite ?S" by (rule finite_subset[OF sub_lt finite_lessThan])
  have sub: "{i, j} \<subseteq> ?S" using il jl Pi Pj by auto
  have "card {i, j} \<le> card ?S" by (rule card_mono[OF fin sub])
  moreover have "card {i, j} = 2" using ij by simp
  ultimately have "2 \<le> card ?S" by simp
  with card_le show False by arith
qed

lemma all_zero_row_entry:
  assumes "all_zero_row r" and "k < length r"
  shows "fq (r ! k) = 0"
  using assms by (auto simp: all_zero_row_def)

text \<open>The arithmetic side: an integer divisible by @{text 3329} stays divisible
  when multiplied, and the difference of two such integers is divisible again.
  The proofs go through @{text dvd} rather than through @{text div_mult_mod_eq},
  which keeps them independent of any particular division algorithm.\<close>

lemma mod_zero_mult_left:
  fixes x y :: int
  assumes "x mod 3329 = 0"
  shows "(x * y) mod 3329 = 0"
proof -
  from assms have "3329 dvd x" by (simp add: dvd_eq_mod_eq_0)
  hence "3329 dvd x * y" by (rule dvd_mult2)
  thus ?thesis by (simp add: dvd_eq_mod_eq_0)
qed

lemma mod_zero_mult_right:
  fixes x y :: int
  assumes "y mod 3329 = 0"
  shows "(x * y) mod 3329 = 0"
proof -
  from assms have "3329 dvd y" by (simp add: dvd_eq_mod_eq_0)
  hence "3329 dvd x * y" by (rule dvd_mult)
  thus ?thesis by (simp add: dvd_eq_mod_eq_0)
qed

lemma mod_zero_diff:
  fixes a b :: int
  assumes "a mod 3329 = 0" and "b mod 3329 = 0"
  shows "(a - b) mod 3329 = 0"
proof -
  from assms(1) have da: "3329 dvd a" by (simp add: dvd_eq_mod_eq_0)
  from assms(2) have "3329 dvd b" by (simp add: dvd_eq_mod_eq_0)
  hence "3329 dvd a - b" using da by simp
  thus ?thesis by (simp add: dvd_eq_mod_eq_0)
qed

text \<open>The two orientations of "a determinant with a zero row vanishes".
  Which row is the zero one depends on the matrix, so both are needed.\<close>

lemma det2_minor_zero_left:
  fixes x y u v :: int
  assumes xz: "fq x = 0" and uz: "fq u = 0"
  shows "(x * y - u * v) mod 3329 = 0"
proof -
  have xm: "x mod 3329 = 0" using xz by (simp add: fq_def)
  have um: "u mod 3329 = 0" using uz by (simp add: fq_def)
  have xy: "(x * y) mod 3329 = 0" using xm by (rule mod_zero_mult_left)
  have uv: "(u * v) mod 3329 = 0" using um by (rule mod_zero_mult_left)
  show ?thesis by (rule mod_zero_diff[OF xy uv])
qed

lemma det2_minor_zero_right:
  fixes x y u v :: int
  assumes yz: "fq y = 0" and vz: "fq v = 0"
  shows "(x * y - u * v) mod 3329 = 0"
proof -
  have ym: "y mod 3329 = 0" using yz by (simp add: fq_def)
  have vm: "v mod 3329 = 0" using vz by (simp add: fq_def)
  have xy: "(x * y) mod 3329 = 0" using ym by (rule mod_zero_mult_right)
  have uv: "(u * v) mod 3329 = 0" using vm by (rule mod_zero_mult_right)
  show ?thesis by (rule mod_zero_diff[OF xy uv])
qed

section \<open>Rank at most one forces the minors to vanish\<close>

text \<open>The counting lemma above is now combined with @{text mat_rank}, which
  counts the nonzero rows of the reduced form.  If that count is at most one,
  then of any two distinct rows of the reduced matrix at least one is zero in
  the modulo-@{text q} sense.\<close>

lemma row_zero_or_zero_of_rank_le_one:
  assumes rk: "mat_rank A \<le> 1"
    and a: "a < n_rows (rref A)" and b: "b < n_rows (rref A)" and ab: "a \<noteq> b"
  shows "all_zero_row (rref A ! a) \<or> all_zero_row (rref A ! b)"
proof (rule ccontr)
  let ?R = "rref A"
  let ?P = "\<lambda>r. \<not> all_zero_row r"
  assume "\<not> (all_zero_row (?R ! a) \<or> all_zero_row (?R ! b))"
  hence Pa: "?P (?R ! a)" and Pb: "?P (?R ! b)" by simp_all
  have len: "length (filter ?P ?R) \<le> 1" using rk by (simp add: mat_rank_def)
  have al: "a < length ?R" using a by (simp add: n_rows_def)
  have bl: "b < length ?R" using b by (simp add: n_rows_def)
  from len al bl ab Pa Pb show False by (rule filter_le_one_two_positions)
qed

(* seg: shape-batch1 *)
section \<open>The reduced form keeps its rectangular shape\<close>

text \<open>@{const is_rect} is stated with @{const n_cols}, which is a lookup into the
  first row.  Recomputing it after every row operation would force a case split
  on emptiness each time, so the invariant below fixes the row length instead:
  @{text "rect_len n A"} says every row of @{text A} has length @{text n} for one
  fixed @{text n}.  For a rectangular @{text A} the two notions agree
  (@{text rect_len_is_rect}, @{text rect_len_n_cols}), and @{text rect_len} is
  stable under all three row operations because each of them either permutes rows
  or maps over rows of equal length.

  Nothing here needs the pigeonhole or inverse arguments of the rank lemmas
  below; this is a purely structural layer.\<close>

definition rect_len :: "nat \<Rightarrow> mat \<Rightarrow> bool" where
  "rect_len n A = (\<forall>r \<in> set A. length r = n)"

lemma rect_lenD:
  assumes rl: "rect_len n A" and rm: "r \<in> set A"
  shows "length r = n"
  using rl rm by (simp add: rect_len_def)

lemma rect_len_is_rect:
  assumes "is_rect A"
  shows "rect_len (n_cols A) A"
  using assms by (simp add: is_rect_def rect_len_def)

lemma rect_len_n_cols:
  assumes rl: "rect_len n A" and ne: "A \<noteq> []"
  shows "n_cols A = n"
proof -
  have h: "A ! 0 \<in> set A" using ne by simp
  have h0: "length (A ! 0) = n" using rl h by (rule rect_lenD)
  show ?thesis using h0 ne by (simp add: n_cols_def)
qed

text \<open>The number of rows is untouched by every row operation, which is what lets
  the fold in @{const eliminate_col} keep its bounds and what shows that the
  reduced form of a nonempty matrix is nonempty.\<close>

lemma n_rows_swap_rows [simp]: "n_rows (swap_rows A i j) = n_rows A"
  by (simp add: swap_rows_def n_rows_def)

lemma n_rows_scale_row [simp]: "n_rows (scale_row A i k) = n_rows A"
  by (simp add: scale_row_def n_rows_def)

lemma n_rows_add_row_mult [simp]: "n_rows (add_row_mult A i j k) = n_rows A"
  by (simp add: add_row_mult_def n_rows_def)

text \<open>A swap replaces one row by another row of the same matrix and then does the
  same again.  The two updates are therefore subsets of the original row set:
  @{text set_list_update} bounds a single update by
  @{text "insert x (set xs)"}, and both inserted rows come from @{text A} because
  the indices are in range.

  The subset facts below are deliberately kept out of @{text simp}.  Chaining a
  fact of the form @{text "set B \<subseteq> set A"} into @{text simp} lets the
  simplifier search for set inclusions, and on this goal that search does not
  terminate promptly; @{text blast} discharges each step directly.\<close>

lemma set_list_update_subset:
  assumes i: "i < length xs" and x: "x \<in> set xs"
  shows "set (xs[i := x]) \<subseteq> set xs"
  using set_update_subset_insert[of xs i x] x by blast

lemma rect_len_swap_rows:
  assumes rl: "rect_len n A" and i: "i < n_rows A" and j: "j < n_rows A"
  shows "rect_len n (swap_rows A i j)"
  unfolding rect_len_def
proof
  fix r
  assume rm: "r \<in> set (swap_rows A i j)"
  have iA: "i < length A" using i by (simp add: n_rows_def)
  have jA: "j < length A" using j by (simp add: n_rows_def)
  have jm: "A ! j \<in> set A"
  proof (rule nth_mem)
    show "j < length A" using jA .
  qed
  have im: "A ! i \<in> set A"
  proof (rule nth_mem)
    show "i < length A" using iA .
  qed
  have h1: "set (A[i := A ! j]) \<subseteq> set A" using iA jm by (rule set_list_update_subset)
  have ins: "r \<in> insert (A ! i) (set (A[i := A ! j]))"
  proof -
    have sub: "set ((A[i := A ! j])[j := A ! i])
                 \<subseteq> insert (A ! i) (set (A[i := A ! j]))"
      using set_update_subset_insert[of "A[i := A ! j]" j "A ! i"] .
    have "r \<in> set ((A[i := A ! j])[j := A ! i])" using rm by (simp add: swap_rows_def)
    with sub show ?thesis by blast
  qed
  have rA: "r \<in> set A"
  proof (cases "r = A ! i")
    case True
    with im show ?thesis by simp
  next
    case False
    with ins have "r \<in> set (A[i := A ! j])" by simp
    with h1 show ?thesis by blast
  qed
  with rl show "length r = n" by (rule rect_lenD)
qed

text \<open>Scaling rewrites exactly one row, with @{text map}, and @{text map} keeps
  the length.  The other rows are untouched.\<close>

lemma rect_len_scale_row:
  assumes rl: "rect_len n A" and i: "i < n_rows A"
  shows "rect_len n (scale_row A i k)"
  unfolding rect_len_def
proof
  fix r
  assume rm: "r \<in> set (scale_row A i k)"
  have ins: "r \<in> insert (map (\<lambda>x. fq (k * x)) (A ! i)) (set A)"
  proof -
    have sub: "set (A[i := map (\<lambda>x. fq (k * x)) (A ! i)])
                 \<subseteq> insert (map (\<lambda>x. fq (k * x)) (A ! i)) (set A)"
      using set_update_subset_insert[of A i "map (\<lambda>x. fq (k * x)) (A ! i)"] .
    have "r \<in> set (A[i := map (\<lambda>x. fq (k * x)) (A ! i)])"
      using rm by (simp add: scale_row_def)
    with sub show ?thesis by blast
  qed
  have disj: "r = map (\<lambda>x. fq (k * x)) (A ! i) \<or> r \<in> set A" using ins by simp
  show "length r = n"
  proof (cases "r \<in> set A")
    case True
    with rl show ?thesis by (rule rect_lenD)
  next
    case False
    with disj have eq: "r = map (\<lambda>x. fq (k * x)) (A ! i)" by blast
    have li: "length (A ! i) = n" using rl i by (simp add: rect_lenD n_rows_def)
    show ?thesis using eq li by simp
  qed
qed

text \<open>Adding a multiple of one row to another uses @{text map2}, whose length is
  the minimum of the two row lengths.  Equal lengths turn the minimum back into
  @{text n}, which is the only place where rectangularity is really used.\<close>

lemma rect_len_add_row_mult:
  assumes rl: "rect_len n A" and i: "i < n_rows A" and j: "j < n_rows A"
  shows "rect_len n (add_row_mult A i j k)"
  unfolding rect_len_def
proof
  fix r
  assume rm: "r \<in> set (add_row_mult A i j k)"
  have ins: "r \<in> insert (map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)) (set A)"
  proof -
    have sub: "set (A[i := map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)])
                 \<subseteq> insert (map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)) (set A)"
      using set_update_subset_insert[of A i "map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)"] .
    have "r \<in> set (A[i := map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)])"
      using rm by (simp add: add_row_mult_def)
    with sub show ?thesis by blast
  qed
  have disj: "r = map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j) \<or> r \<in> set A" using ins by simp
  show "length r = n"
  proof (cases "r \<in> set A")
    case True
    with rl show ?thesis by (rule rect_lenD)
  next
    case False
    with disj have eq: "r = map2 (\<lambda>x y. fq (x + k * y)) (A ! i) (A ! j)" by blast
    have li: "length (A ! i) = n" using rl i by (simp add: rect_lenD n_rows_def)
    have lj: "length (A ! j) = n" using rl j by (simp add: rect_lenD n_rows_def)
    have "length r = min (length (A ! i)) (length (A ! j))" using eq by simp
    thus ?thesis using li lj by simp
  qed
qed

(* seg: shape-batch2 *)
text \<open>@{const eliminate_col} is a @{text foldl} over all row indices, adding a
  multiple of the pivot row to every other row.  Two invariants have to be
  threaded through the fold: the row length (@{text rect_len}) and the number of
  rows, because @{const add_row_mult} needs both of its indices to be in range
  when it is applied again at the next step.\<close>

lemma n_rows_foldl_elim:
  "n_rows (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c)) A xs) = n_rows A"
proof (induct xs arbitrary: A)
  case Nil
  then show ?case by simp
next
  case (Cons k ks)
  show ?case
  proof (cases "k = r")
    case True
    have ih: "n_rows (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c)) A ks)
                = n_rows A"
      by (rule Cons.hyps)
    with True show ?thesis by simp
  next
    case False
    have step: "n_rows (add_row_mult A k r (- entry A k c)) = n_rows A" by simp
    have ih: "n_rows (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c))
                          (add_row_mult A k r (- entry A k c)) ks)
                = n_rows (add_row_mult A k r (- entry A k c))"
      by (rule Cons.hyps)
    with step False show ?thesis by simp
  qed
qed

lemma n_rows_eliminate_col [simp]:
  "n_rows (eliminate_col A r c) = n_rows A"
  using n_rows_foldl_elim[where A=A and r=r and c=c and xs="[0..<n_rows A]"]
  by (simp add: eliminate_col_def)

lemma rect_len_foldl_elim:
  assumes rl: "rect_len n A"
    and kn: "\<forall>k \<in> set xs. k < n_rows A"
    and rn: "r < n_rows A"
  shows "rect_len n (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c)) A xs)"
proof -
  have main: "\<And>A. rect_len n A \<Longrightarrow> (\<forall>k \<in> set xs. k < n_rows A) \<Longrightarrow> r < n_rows A
        \<Longrightarrow> rect_len n (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c)) A xs)"
    for xs :: "nat list"
  proof (induct xs)
    case Nil
    show ?case using Nil.prems by simp
  next
    case (Cons k ks)
    have rlA: "rect_len n A" using Cons.prems(1) .
    have kn: "\<forall>k' \<in> set (k # ks). k' < n_rows A" using Cons.prems(2) .
    have rn: "r < n_rows A" using Cons.prems(3) .
    have knA: "k < n_rows A" using kn by simp
    show ?case
    proof (cases "k = r")
      case True
      have ksA: "\<forall>k' \<in> set ks. k' < n_rows A" using kn by simp
      have ih: "rect_len n (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c)) A ks)"
        using rlA ksA rn by (rule Cons.hyps)
      with True show ?thesis by simp
    next
      case False
      note neq = \<open>k \<noteq> r\<close>
      have ks: "\<forall>k' \<in> set ks. k' < n_rows (add_row_mult A k r (- entry A k c))"
        using kn by simp
      have step: "rect_len n (add_row_mult A k r (- entry A k c))"
        using rlA knA rn by (rule rect_len_add_row_mult)
      have rn2: "r < n_rows (add_row_mult A k r (- entry A k c))" using rn by simp
      have ih: "rect_len n (foldl (\<lambda>B k. if k = r then B else add_row_mult B k r (- entry B k c))
                    (add_row_mult A k r (- entry A k c)) ks)"
        using step ks rn2 by (rule Cons.hyps)
      with neq show ?thesis by simp
    qed
  qed
  from main[OF rl kn rn] show ?thesis .
qed

lemma rect_len_eliminate_col:
  assumes rl: "rect_len n A" and rn: "r < n_rows A"
  shows "rect_len n (eliminate_col A r c)"
proof -
  have kn: "\<forall>k \<in> set [0..<n_rows A]. k < n_rows A" by simp
  show ?thesis
    using rect_len_foldl_elim[OF rl kn rn] by (simp add: eliminate_col_def)
qed

text \<open>The number of rows survives the whole reduction, which is also what shows
  that the reduced form of a nonempty matrix stays nonempty.\<close>

lemma n_rows_rref_fuel:
  "n_rows (rref_fuel f r c A) = n_rows A"
proof (induct f arbitrary: r c A)
  case 0
  then show ?case by simp
next
  case (Suc f)
  show ?case
  proof (cases "r < n_rows A")
    case False
    note rF = \<open>\<not> (r < n_rows A)\<close>
    thus ?thesis by simp
  next
    case True
    note rT = \<open>r < n_rows A\<close>
    show ?thesis
    proof (cases "c < n_cols A")
      case False
      note cF = \<open>\<not> (c < n_cols A)\<close>
      show ?thesis using rT cF by simp
    next
      case True
      note cT = \<open>c < n_cols A\<close>
      show ?thesis
      proof (cases "find_pivot_fuel (n_rows A) A r c")
        case None
        note nN = \<open>find_pivot_fuel (n_rows A) A r c = None\<close>
        have eq: "rref_fuel (Suc f) r c A = rref_fuel f r (c + 1) A"
          using rT cT nN by simp
        with Suc.hyps show ?thesis by simp
      next
        case (Some i)
        note sS = \<open>find_pivot_fuel (n_rows A) A r c = Some i\<close>
        have eq: "rref_fuel (Suc f) r c A
                = rref_fuel f (r + 1) (c + 1)
                    (eliminate_col (scale_row (swap_rows A r i) r
                       (invmod (entry (swap_rows A r i) r c))) r c)"
          using rT cT sS by (simp add: Let_def)
        have st: "n_rows (rref_fuel f (r + 1) (c + 1)
                     (eliminate_col (scale_row (swap_rows A r i) r
                        (invmod (entry (swap_rows A r i) r c))) r c)) = n_rows A"
          using Suc.hyps by simp
        with eq show ?thesis by simp
      qed
    qed
  qed
qed

lemma n_rows_rref [simp]:
  "n_rows (rref A) = n_rows A"
  using n_rows_rref_fuel[of "n_rows A * n_cols A + n_rows A + 1" 0 0 A]
  by (simp add: rref_def)

(* seg: shape-batch3 *)
text \<open>@{const find_pivot_fuel} returns an index only if that index is a real row.
  The reduction needs this to know that the swap it performs is in range.\<close>

lemma find_pivot_fuel_bound:
  "find_pivot_fuel f A r c = Some i \<Longrightarrow> i < n_rows A"
proof (induct f arbitrary: r)
  case 0
  then show ?case by simp
next
  case (Suc f)
  show ?case
  proof (cases "r < n_rows A")
    case False
    hence "find_pivot_fuel (Suc f) A r c = None" by simp
    with Suc.prems show ?thesis by simp
  next
    case True
    note rT = \<open>r < n_rows A\<close>
    show ?thesis
    proof (cases "fq (entry A r c) \<noteq> 0")
      case True
      hence "find_pivot_fuel (Suc f) A r c = Some r" using rT by simp
      with Suc.prems have "i = r" by simp
      with rT show ?thesis by simp
    next
      case False
      hence eq: "find_pivot_fuel (Suc f) A r c = find_pivot_fuel f A (r + 1) c"
        using rT by simp
      from Suc.prems eq have "find_pivot_fuel f A (r + 1) c = Some i" by simp
      with Suc.hyps show ?thesis by simp
    qed
  qed
qed

text \<open>Shape preservation for the whole reduction, by induction on the fuel.  Each
  step only applies the three row operations proved above, and the pivot index is
  in range by @{text find_pivot_fuel_bound}.\<close>

lemma rect_len_rref_fuel_helper:
  "\<And>A r c. rect_len n A \<Longrightarrow> rect_len n (rref_fuel f r c A)"
  by (induct f)
     (simp_all add: rref_fuel.simps Let_def rect_len_swap_rows rect_len_scale_row
        rect_len_eliminate_col find_pivot_fuel_bound split: option.split)

lemma rect_len_rref_fuel:
  assumes rl: "rect_len n A"
  shows "rect_len n (rref_fuel f r c A)"
  using rl by (rule rect_len_rref_fuel_helper)

lemma rect_len_rref:
  assumes rl: "rect_len n A"
  shows "rect_len n (rref A)"
  unfolding rref_def using rl by (rule rect_len_rref_fuel)

text \<open>The headline result of this section: the reduced form of a rectangular
  matrix is rectangular.  The only remaining step is bookkeeping, turning
  @{text rect_len} back into @{const is_rect} by computing @{text n_cols} of the
  reduced form from its first row.\<close>

lemma is_rect_rref:
  assumes "is_rect A"
  shows "is_rect (rref A)"
proof (cases "A = []")
  case True
  have h: "rref A = []" using True by (simp add: rref_def rref_fuel.simps n_rows_def n_cols_def)
  show ?thesis unfolding h by (simp add: is_rect_def)
next
  case False
  have rl: "rect_len (n_cols A) A" using assms by (rule rect_len_is_rect)
  have rlR: "rect_len (n_cols A) (rref A)" using rl by (rule rect_len_rref)
  have nr: "n_rows (rref A) = n_rows A" by simp
  have ne: "rref A \<noteq> []"
  proof
    assume "rref A = []"
    hence "n_rows (rref A) = 0" by (simp add: n_rows_def)
    with nr have "n_rows A = 0" by simp
    with False show False by (simp add: n_rows_def)
  qed
  have nc: "n_cols (rref A) = n_cols A" using rlR ne by (rule rect_len_n_cols)
  show ?thesis using rlR nc by (simp add: is_rect_def rect_len_def)
qed

text \<open>The main lemma of this section.  Because @{text all_zero_row} is the
  modulo-@{text q} notion, what it yields is congruence of the minor to zero
  modulo @{text 3329}, not integer equality.  That is the right conclusion for
  this development: @{text mat_rank2} and @{text mat_rank1} are also stated
  modulo @{text q}.

  The hypothesis @{text "is_rect A"} is what turns a column index below
  @{text n_cols} into an index below the length of a row: the shape section above
  shows that @{text rref} preserves rectangularity, so @{text "is_rect (rref A)"}
  is derived here rather than assumed.\<close>

lemma rank_le_one_imp_minors_vanish:
  assumes rk: "mat_rank A \<le> 1"
    and rect0: "is_rect A"
    and a: "a < n_rows (rref A)" and b: "b < n_rows (rref A)" and ab: "a \<noteq> b"
    and c: "c < n_cols (rref A)" and d: "d < n_cols (rref A)"
  shows "(entry (rref A) a c * entry (rref A) b d
            - entry (rref A) a d * entry (rref A) b c) mod 3329 = 0"
proof -
  have rect: "is_rect (rref A)" using rect0 by (rule is_rect_rref)
  let ?R = "rref A"
  have z: "all_zero_row (?R ! a) \<or> all_zero_row (?R ! b)"
    by (rule row_zero_or_zero_of_rank_le_one[OF rk a b ab])
  have la: "length (?R ! a) = n_cols ?R"
    using rect a by (simp add: is_rect_def n_rows_def)
  have lb: "length (?R ! b) = n_cols ?R"
    using rect b by (simp add: is_rect_def n_rows_def)
  show ?thesis
  proof (cases "all_zero_row (?R ! a)")
    case True
    have xz: "fq (entry ?R a c) = 0"
      using True c la by (simp add: entry_def all_zero_row_entry)
    have uz: "fq (entry ?R a d) = 0"
      using True d la by (simp add: entry_def all_zero_row_entry)
    show ?thesis by (rule det2_minor_zero_left[OF xz uz])
  next
    case False
    hence zb: "all_zero_row (?R ! b)" using z by simp
    have yz: "fq (entry ?R b d) = 0"
      using zb d lb by (simp add: entry_def all_zero_row_entry)
    have vz: "fq (entry ?R b c) = 0"
      using zb c lb by (simp add: entry_def all_zero_row_entry)
    show ?thesis by (rule det2_minor_zero_right[OF yz vz])
  qed
qed

section \<open>What is still missing for T2_B7\<close>

text \<open>Nothing in this file bounds the rank of a sum of two outer products, and
  that is deliberate rather than an oversight.  @{text mat_rank} counts the nonzero
  rows of @{text rref}, so every statement about @{text A} has to be carried through
  the reduction, and the status of the ingredients differs from what an earlier note
  in this section claimed:

  \<^enum> @{text rref_step}: not available as stated.  Reading a row operation as
  multiplication on the left by an invertible matrix needs @{text mat_inv} to be a
  two-sided inverse, and @{file VWZ_RREF.thy} leaves that as an unproved claim.  The
  bridge is therefore built without left multiplication.
  \<^enum> @{text minors_invariant_under_row_ops}: the forward direction is complete
  and already general in the index pairs.  @{text minors_zero_swap},
  @{text minors_zero_scale_row}, @{text minors_zero_add_row} and
  @{text minors_zero_eliminate_col} in @{file VWZ_ModAlgebra.thy} say
  @{text "minors_zero A \<Longrightarrow> minors_zero (op A)"} for every operation, and the
  predicate itself quantifies over all index pairs, so nothing is left to
  generalise here.
  \<^enum> the opposite direction, @{text "minors_zero (op A) \<Longrightarrow> minors_zero A"},
  is now complete.  It cannot be stated as an equality of matrices:
  @{text "scale_row (scale_row A i q) i p"} agrees with @{text A} only up to
  @{text fq} on the touched row, two @{text add_row_mult} steps behave the same
  way, and @{text eliminate_col} is idempotent rather than invertible, so
  replaying it does not undo it.  @{file VWZ_ModAlgebra.thy} carries the residue
  form of the single steps (@{text dvd_minor2_cong} with
  @{text minors_zero_swap_undo}, @{text minors_zero_scale_row_undo} and
  @{text minors_zero_add_row_undo}) plus the fold-level reflection
  @{text minors_zero_eliminate_col_undo}; this file carries the fuel induction
  @{text minors_zero_rref_fuel_undo} and its wrapper @{text minors_zero_rref_undo}.
  \<^enum> @{text rank_le_one_imp_minors_vanish}: proved in this file together with
  @{text row_zero_or_zero_of_rank_le_one} and the shape lemma @{text is_rect_rref};
  it assumes only @{text "is_rect A"} and gives vanishing minors of the reduced
  form.
  \<^enum> @{text rank_ge_two_of_nonzero_minor} is now an assembly step:
  @{text rank_le_one_imp_minors_vanish} gives vanishing minors of the reduced
  form from @{text "mat_rank A \<le> 1"}, and @{text minors_zero_rref_undo} carries
  that back to @{text A}.  @{text rank_outer_sum_le_two} still needs the
  inner-dimension bound @{text "mat_rank (mat_mult A B) \<le> n_cols A"}, and that
  is not what @{text mat_rank_le_n_cols} provides: instantiating the latter at
  @{text "mat_mult A B"} yields @{text "mat_rank (mat_mult A B) \<le> n_cols B"},
  which constrains the outer dimension instead.

  Writing the remaining headers down without proofs would put @{text sorry}s
  outside the obligation ledger, so they stay a work list: the ledger in
  @{file VWZ_ObligationsAligned.thy} keeps its 7 @{text sorry}, and the lemmas
  added alongside carry no @{text sorry} at all.\<close>

(* seg: rank-lead-invmod-20261023 *)

text \<open>The leading column of a row is the index of its first entry that is nonzero
  modulo @{text 3329}; a zero row has no such index and gets the length of the row
  instead.  The recursion mirrors the list, which keeps the two facts that matter --
  entries before the leading column vanish, the entry at it does not -- available by
  plain induction.\<close>

fun lead :: "int list \<Rightarrow> nat" where
  "lead [] = 0"
| "lead (x # xs) = (if fq x = 0 then Suc (lead xs) else 0)"

lemma lead_le_length [simp]: "lead r \<le> length r"
  by (induct r) simp_all

lemma lead_nth_zero:
  assumes j: "j < lead r"
  shows "fq (r ! j) = 0"
  using j
proof (induct r arbitrary: j)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "fq x = 0")
    case hx: True
    show ?thesis
    proof (cases j)
      case 0
      thus ?thesis using hx by simp
    next
      case (Suc k)
      with Cons.prems have "k < lead xs" using hx by simp
      with Cons.hyps have "fq (xs ! k) = 0" .
      thus ?thesis using Suc by simp
    qed
  next
    case hx: False
    with Cons.prems have False by simp
    thus ?thesis ..
  qed
qed

lemma lead_nth_nonzero:
  assumes k: "lead r < length r"
  shows "fq (r ! lead r) \<noteq> 0"
  using k
proof (induct r)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "fq x = 0")
    case True
    hence l: "lead (x # xs) = Suc (lead xs)" by simp
    with Cons.prems have "lead xs < length xs" by simp
    with Cons.hyps have "fq (xs ! lead xs) \<noteq> 0" .
    thus ?thesis using True l by simp
  next
    case False
    thus ?thesis by simp
  qed
qed

lemma lead_eq_length_all_zero [simp]: "lead r = length r \<longleftrightarrow> all_zero_row r"
proof
  assume h: "lead r = length r"
  have idx: "\<forall>j < length r. fq (r ! j) = 0"
  proof (intro allI impI)
    fix j
    assume jl: "j < length r"
    have "j < lead r" using h jl by simp
    thus "fq (r ! j) = 0" by (rule lead_nth_zero)
  qed
  have "\<forall>x \<in> set r. fq x = 0"
  proof
    fix x
    assume xs: "x \<in> set r"
    then obtain j where j: "j < length r" and jx: "r ! j = x"
      by (metis in_set_conv_nth)
    have z: "fq (r ! j) = 0" using idx j by auto
    thus "fq x = 0" using jx by simp
  qed
  thus "all_zero_row r" by (simp add: all_zero_row_def)
next
  assume h: "all_zero_row r"
  show "lead r = length r"
    using h
  proof (induct r)
    case Nil
    thus ?case by simp
  next
    case (Cons x xs)
    have hx: "fq x = 0" using Cons.prems by (auto simp add: all_zero_row_def)
    have hxs: "all_zero_row xs" using Cons.prems by (auto simp add: all_zero_row_def)
    have "lead xs = length xs" by (rule Cons.hyps [OF hxs])
    thus ?case using hx by simp
  qed
qed


text \<open>Normalising a pivot to @{text 1} needs @{text "x * invmod x \<equiv> 1"}.  The
  inverse is defined through Fermat's little theorem as @{text "x ^ (3329 - 2)"}, and
  the library theorem is stated for @{typ nat}, so the residue is carried to
  @{typ int} below.  Without this fact no elimination step can be shown to clear a
  column, which is what the column count of the reduced form rests on.\<close>

lemma invmod_correct:
  assumes x0: "0 < x" and xq: "x < 3329"
  shows "fq (x * invmod x) = 1"
proof -
  have p: "prime (3329::nat)" by (rule prime_3329)
  have xn0: "0 < nat x" using x0 by simp
  have xnl: "nat x < 3329" using xq by simp
  have nd: "\<not> 3329 dvd nat x"
  proof
    assume d: "3329 dvd nat x"
    have le: "3329 \<le> nat x" using xn0 d by (metis dvd_imp_le less_le_trans)
    with xnl show False by simp
  qed
  have f: "[(nat x) ^ (3329 - 1) = 1] (mod 3329)"
    by (rule fermat_theorem [OF p nd])
  have xn1: "1 \<le> nat x" using xn0 by simp
  have ge: "1 \<le> (nat x) ^ (3329 - 1)" using xn1 by (rule one_le_power)
  have d1: "3329 dvd (nat x) ^ (3329 - 1) - 1"
    using f ge by (simp add: cong_altdef_nat)
  from d1 obtain k where k: "(nat x) ^ (3329 - 1) - 1 = 3329 * k"
    by (rule dvdE)
  have np: "(nat x) ^ (3329 - 1) = 3329 * k + 1" using k ge by simp
  have imod: "(x ^ (3329 - 1)) mod 3329 = 1"
  proof -
    have ip: "x ^ (3329 - 1) = int (3329 * k + 1)"
    proof -
      have xr: "int (nat x) = x" using x0 by simp
      have "x ^ (3329 - 1) = (int (nat x)) ^ (3329 - 1)" using xr by simp
      also have "\<dots> = int ((nat x) ^ (3329 - 1))" by (simp add: of_nat_power)
      also have "\<dots> = int (3329 * k + 1)" using np by simp
      finally show ?thesis .
    qed
    have h: "int (3329 * k + 1) mod (int 3329) = 1"
    proof -
      have "int (3329 * k + 1) mod (int 3329) = int ((3329 * k + 1) mod 3329)"
        by (simp add: zmod_int)
      also have "\<dots> = (1::int)" by (simp add: mod_mult_self1)
      finally show ?thesis .
    qed
    show ?thesis using ip h by simp
  qed
  have step: "fq (x * invmod x) = fq (x ^ (3329 - 1))"
  proof -
    have a1: "fq (x * invmod x) = fq (x * (x ^ (3329 - 2) mod 3329))"
      by (simp add: invmod_def)
    have a2: "fq (x * (x ^ (3329 - 2) mod 3329)) = fq (x * x ^ (3329 - 2))"
      by (simp add: fq_def mod_mult_right_eq)
    have a3: "x ^ (3329 - 1) = x * x ^ (3329 - 2)"
    proof -
      have c: "x * x ^ (3329 - 2) = x ^ (3329 - 2) * x" by (rule mult.commute)
      also have "\<dots> = x ^ Suc (3329 - 2)" by (rule power_Suc2 [symmetric])
      also have "\<dots> = x ^ (3329 - 1)" by simp
      finally show ?thesis by (rule sym)
    qed
    show ?thesis using a1 a2 a3 by simp
  qed
  show ?thesis using step imod by (simp add: fq_def)
qed

lemma cong_q_power: "cong_q x y \<Longrightarrow> cong_q (x ^ n) (y ^ n)"
proof (induct n)
  case 0
  show ?case by (simp add: cong_q_def)
next
  case (Suc n)
  have p: "x ^ Suc n = x * x ^ n" by simp
  have q: "y ^ Suc n = y * y ^ n" by simp
  have hh: "cong_q x y" using Suc.prems by simp
  have ih: "cong_q (x ^ n) (y ^ n)" using Suc.hyps hh by simp
  have mid: "cong_q (x * x ^ n) (y * y ^ n)" using hh ih by (rule cong_q_mult)
  from mid have mf: "fq (x * x ^ n) = fq (y * y ^ n)" by (simp add: cong_q_def)
  from mf p q show ?case by (simp add: cong_q_def)
qed

lemma fq_power_cong: "fq (x ^ n) = fq ((fq x) ^ n)"
  using cong_q_power[OF cong_q_sym[OF cong_q_fq]] by (simp add: cong_q_def)

lemma fq_mult_invmod: "fq (x * invmod x) = fq (x ^ (3329 - 1))"
proof -
  have a1: "fq (x * invmod x) = fq (x * (x ^ (3329 - 2) mod 3329))"
    by (simp add: invmod_def)
  have a2: "fq (x * (x ^ (3329 - 2) mod 3329)) = fq (x * x ^ (3329 - 2))"
    by (simp add: fq_def mod_mult_right_eq)
  have a3: "x ^ (3329 - 1) = x * x ^ (3329 - 2)"
  proof -
    have c: "x * x ^ (3329 - 2) = x ^ (3329 - 2) * x" by (rule mult.commute)
    also have "\<dots> = x ^ Suc (3329 - 2)" by (rule power_Suc2 [symmetric])
    also have "\<dots> = x ^ (3329 - 1)" by simp
    finally show ?thesis by (rule sym)
  qed
  show ?thesis using a1 a2 a3 by simp
qed

(* seg: rank-col-bound-1-20261023 *)
section \<open>Clearing a column below the pivot\<close>

text \<open>@{const eliminate_col} folds row additions over all row indices, so the
  entry of the result needs an induction over that list.  The pivot row itself is
  skipped by the step, and the row that is being cleared is touched exactly once,
  which is why the entry of the result is a single subtraction.\<close>

lemma entry_foldl_elim:
  fixes A :: mat and ks :: "nat list"
  assumes d: "distinct ks" and bound: "\<forall>a\<in>set ks. a < n_rows A"
    and rect: "is_rect A" and r: "r < n_rows A" and k: "k < n_rows A"
    and col: "col < n_cols A" and c: "c < n_cols A"
  shows "entry (foldl (\<lambda>B a. if a = r then B else add_row_mult B a r (- (entry B a c))) A ks) k col
           = (if k \<noteq> r \<and> k \<in> set ks then fq (entry A k col - entry A k c * entry A r col)
                else entry A k col)"
  using d bound rect r k col c
proof (induct ks arbitrary: A)
  case Nil
  then show ?case by simp
next
  case (Cons a ks)
  then show ?case
    by (cases "a = r"; cases "k = a")
       (simp_all add: entry_add_row_mult is_rect_add_row_mult n_cols_add_row_mult algebra_simps)
qed

lemma entry_eliminate_col:
  assumes rect: "is_rect A" and r: "r < n_rows A" and k: "k < n_rows A"
    and col: "col < n_cols A" and c: "c < n_cols A"
  shows "entry (eliminate_col A r c) k col
           = (if k = r then entry A k col
                else fq (entry A k col - entry A k c * entry A r col))"
proof -
  have d: "distinct [0..<n_rows A]" by simp
  have b: "\<forall>a\<in>set [0..<n_rows A]. a < n_rows A" by simp
  note h = entry_foldl_elim[OF d b rect r k col c]
  show ?thesis using h r k by (simp add: eliminate_col_def)
qed

(* seg: rank-col-bound-2-20261023 *)
text \<open>A pivot of the reduction is a nonzero entry, and after scaling its row by
  the modular inverse it becomes exactly 1.  Elimination then turns every other
  entry of that column into 0, because each subtraction is a multiple of 1.\<close>

lemma invmod_correct_gen:
  assumes nz: "fq x \<noteq> 0"
  shows "fq (x * invmod x) = 1"
proof -
  have y0: "0 < fq x"
  proof -
    have le: "0 \<le> fq x" and ne: "fq x \<noteq> 0" using fq_range nz by auto
    show ?thesis using le ne by simp
  qed
  have yl: "fq x < 3329" using fq_range by simp
  have iy: "fq (fq x * invmod (fq x)) = 1" using invmod_correct[OF y0 yl] .
  have e1: "fq (x * invmod x) = fq (x ^ (3329 - 1))" by (rule fq_mult_invmod)
  have e2: "fq (x ^ (3329 - 1)) = fq ((fq x) ^ (3329 - 1))" by (rule fq_power_cong)
  have e3: "fq ((fq x) ^ (3329 - 1)) = fq (fq x * invmod (fq x))"
    using fq_mult_invmod[of "fq x"] by simp
  show ?thesis using e1 e2 e3 iy by simp
qed

lemma entry_scale_row_pivot:
  assumes rect: "is_rect A" and r: "r < n_rows A" and c: "c < n_cols A"
    and pv: "entry A r c = p" and nz: "fq p \<noteq> 0"
  shows "entry (scale_row A r (invmod p)) r c = 1"
proof -
  have e: "entry (scale_row A r (invmod p)) r c = fq (invmod p * entry A r c)"
    using entry_scale_row[OF r rect r c] by simp
  have ic: "fq (p * invmod p) = 1" using invmod_correct_gen[OF nz] .
  have e2: "invmod p * entry A r c = entry A r c * invmod p" by (rule mult.commute)
  have e3: "entry A r c * invmod p = p * invmod p" using pv by simp
  show ?thesis using e ic e2 e3 by simp
qed

lemma entry_eliminate_col_self:
  assumes rect: "is_rect A" and r: "r < n_rows A" and col: "col < n_cols A" and c: "c < n_cols A"
  shows "entry (eliminate_col A r c) r col = entry A r col"
  using entry_eliminate_col[OF rect r r col c] by simp

lemma entry_eliminate_col_below:
  assumes rect: "is_rect A" and r: "r < n_rows A" and k: "k < n_rows A"
    and kn: "k \<noteq> r" and c: "c < n_cols A" and piv: "entry A r c = 1"
  shows "entry (eliminate_col A r c) k c = 0"
proof -
  have h: "entry (eliminate_col A r c) k c
              = fq (entry A k c - entry A k c * entry A r c)"
    using entry_eliminate_col[OF rect r k c c] kn by simp
  have z: "entry A k c - entry A k c * entry A r c = 0" using piv by simp
  show ?thesis using h z by simp
qed

(* seg: rank-col-bound-3-20261023 *)
section \<open>What the pivot search reports\<close>

text \<open>@{const find_pivot_fuel} walks down a column from a given row.  A hit is the
  first row of the column that is nonzero modulo 3329, and a miss over the full
  fuel -- which is always the row count here -- means the whole column below is
  zero.  Both halves are needed to say what a reduction step does to the shape.\<close>

lemma pivot_some_ge:
  "\<And>r i. find_pivot_fuel f A r c = Some i \<Longrightarrow> r \<le> i"
proof (induct f)
  case 0
  then show ?case by simp
next
  case (Suc f)
  note h = Suc.prems
  show ?case
  proof (cases "r < n_rows A \<and> fq (entry A r c) \<noteq> 0")
    case True
    with h show ?thesis by simp
  next
    case fls: False
    with h have h2: "find_pivot_fuel f A (r + 1) c = Some i" and rn: "r < n_rows A"
      by (auto split: if_split_asm)
    have ge: "r + 1 \<le> i" using Suc.hyps[OF h2] .
    show ?thesis using ge by simp
  qed
qed

lemma pivot_some_lt:
  "\<And>r i. find_pivot_fuel f A r c = Some i \<Longrightarrow> i < n_rows A"
  by (induct f) (auto split: if_split_asm)

lemma pivot_some_nz:
  "\<And>r i. find_pivot_fuel f A r c = Some i \<Longrightarrow> fq (entry A i c) \<noteq> 0"
  by (induct f) (auto split: if_split_asm)

lemma pivot_some_zeros:
  "\<And>r i. find_pivot_fuel f A r c = Some i
    \<Longrightarrow> \<forall>j. r \<le> j \<longrightarrow> j < i \<longrightarrow> fq (entry A j c) = 0"
proof (induct f)
  case 0
  then show ?case by simp
next
  case (Suc f)
  note h = Suc.prems
  show ?case
  proof (cases "r < n_rows A \<and> fq (entry A r c) \<noteq> 0")
    case True
    with h show ?thesis by simp
  next
    case fls: False
    with h have h2: "find_pivot_fuel f A (r + 1) c = Some i" and rn: "r < n_rows A"
      by (auto split: if_split_asm)
    have rz: "fq (entry A r c) = 0" using fls rn by simp
    note ih = Suc.hyps[OF h2]
    show ?thesis
    proof (intro allI impI)
      fix j
      assume rj: "r \<le> j" and ji: "j < i"
      show "fq (entry A j c) = 0"
      proof (cases "j = r")
        case True
        with rz show ?thesis by simp
      next
        case jr2: False
        with rj have "r + 1 \<le> j" by simp
        with ih ji show ?thesis by simp
      qed
    qed
  qed
qed

lemma pivot_none_zeros:
  "\<And>r. find_pivot_fuel f A r c = None \<Longrightarrow> n_rows A \<le> r + f
    \<Longrightarrow> \<forall>j. r \<le> j \<longrightarrow> j < n_rows A \<longrightarrow> fq (entry A j c) = 0"
proof (induct f)
  case 0
  then show ?case by simp
next
  case (Suc f)
  note h = Suc.prems(1)
  note fuel = Suc.prems(2)
  show ?case
  proof (cases "r < n_rows A \<and> fq (entry A r c) \<noteq> 0")
    case True
    with h show ?thesis by simp
  next
    case fls: False
    show ?thesis
    proof (intro allI impI)
      fix j
      assume rj: "r \<le> j" and jn: "j < n_rows A"
      have rn: "r < n_rows A" using rj jn by simp
      have nz: "fq (entry A r c) = 0" using fls rn by simp
      have h2: "find_pivot_fuel f A (r + 1) c = None" using h rn nz by (simp add: find_pivot_fuel.simps)
      have fuel2: "n_rows A \<le> (r + 1) + f" using fuel by simp
      note ih = Suc.hyps[OF h2 fuel2]
      show "fq (entry A j c) = 0"
      proof (cases "j = r")
        case True
        with nz show ?thesis by simp
      next
        case jr2: False
        with rj have "r + 1 \<le> j" by simp
        with ih jn show ?thesis by simp
      qed
    qed
  qed
qed

(* seg: rank-col-bound-4-20261023 *)
section \<open>Rows below the pointer stay zero in the columns already scanned\<close>

text \<open>The invariant of the reduction is not a statement about rank but about
  position: below the row pointer every entry in the columns already scanned is
  zero modulo the modulus.  That is all the counting at the end needs, because
  the number of rows is otherwise bounded by the row pointer, and the row
  pointer never overtakes the column pointer.\<close>

definition zero_below :: "nat \<Rightarrow> nat \<Rightarrow> mat \<Rightarrow> bool" where
  "zero_below r c A = (\<forall>k col. r \<le> k \<and> k < n_rows A \<and> col < c \<longrightarrow> fq (entry A k col) = 0)"

lemma zero_below_entry:
  assumes zb: "zero_below r c A" and a: "r \<le> a" and b: "a < n_rows A" and col: "col < c"
  shows "fq (entry A a col) = 0"
  using assms by (simp add: zero_below_def)

lemma zero_below_skip:
  assumes zb: "zero_below r c A"
    and colz: "\<forall>k. r \<le> k \<and> k < n_rows A \<longrightarrow> fq (entry A k c) = 0"
  shows "zero_below r (c + 1) A"
  using zb colz by (auto simp add: zero_below_def less_Suc_eq)

lemma entry_scale_row_other:
  assumes rect: "is_rect A" and i: "i < n_rows A" and k: "k < n_rows A"
    and kn: "k \<noteq> i" and col: "col < n_cols A"
  shows "entry (scale_row A i x) k col = entry A k col"
  using entry_scale_row[OF i rect k col] kn by simp

lemma swap_idx_ge:
  assumes ri: "r \<le> i" and rk: "r \<le> k"
  shows "r \<le> swap_idx r i k"
  using assms by (cases "k = r"; cases "k = i"; simp_all)

lemma zero_below_pivot:
  assumes zb: "zero_below r c A" and rect: "is_rect A"
    and rn: "r < n_rows A" and cn: "c < n_cols A"
    and i: "i < n_rows A" and ri: "r \<le> i"
    and pnz: "fq (entry A i c) \<noteq> 0"
  shows "zero_below (r + 1) (c + 1)
           (eliminate_col (scale_row (swap_rows A r i) r
              (invmod (entry (swap_rows A r i) r c))) r c)"
proof (unfold zero_below_def, intro allI impI)
  fix k col
  assume pre: "r + 1 \<le> k \<and> k < n_rows (eliminate_col (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r c) \<and> col < c + 1"
  from pre have klo: "r + 1 \<le> k" and kn: "k < n_rows (eliminate_col (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r c)" and clo: "col < c + 1" by simp_all
  have nc1: "n_cols (swap_rows A r i) = n_cols A" using n_cols_swap_rows[OF rn i rect] .
  have nc2: "n_cols (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) = n_cols A"
    using n_cols_scale_row[of "(swap_rows A r i)" r "invmod (entry (swap_rows A r i) r c)"] nc1 by simp
  have r1: "is_rect (swap_rows A r i)" using is_rect_swap_rows[OF rect rn i] .
  have rn1: "r < n_rows (swap_rows A r i)" using rn by simp
  have r2: "is_rect (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c)))" using is_rect_scale_row[OF r1 rn1] .
  have rn2: "r < n_rows (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c)))" using rn by simp
  have knA: "k < n_rows A" using kn by simp
  have kn1: "k < n_rows (swap_rows A r i)" using kn by simp
  have kn2: "k < n_rows (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c)))" using kn by simp
  have knr: "k \<noteq> r" using klo by simp
  have cn1: "c < n_cols (swap_rows A r i)" using cn nc1 by simp
  have cn2: "c < n_cols (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c)))" using cn nc2 by simp
  have pv: "entry (swap_rows A r i) r c = entry A i c"
    using entry_swap_rows[OF rn i rn] by simp
  have pnz1: "fq (entry (swap_rows A r i) r c) \<noteq> 0" using pnz pv by simp
  have piv: "entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r c = 1"
    using entry_scale_row_pivot[of "(swap_rows A r i)" r c "entry (swap_rows A r i) r c", OF r1 rn1 cn1 refl pnz1] .
  have e2k: "\<forall>col. col < c \<longrightarrow> fq (entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) k col) = 0"
  proof (intro allI impI)
    fix col
    assume colc: "col < c"
    have colA: "col < n_cols A" using colc cn by simp
    have col1: "col < n_cols (swap_rows A r i)" using colA nc1 by simp
    have s1: "entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) k col = entry (swap_rows A r i) k col"
      using entry_scale_row_other[OF r1 rn1 kn1 knr col1] .
    have s2: "entry (swap_rows A r i) k col = entry A (swap_idx r i k) col"
      using entry_swap_rows[OF rn i knA] .
    have swlt: "swap_idx r i k < n_rows A" using swap_idx_lt[OF rn i knA] .
    have swge: "r \<le> swap_idx r i k" using swap_idx_ge[OF ri] klo by simp
    have z: "fq (entry A (swap_idx r i k) col) = 0"
      using zb swge swlt colc by (rule zero_below_entry)
    show "fq (entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) k col) = 0" using s1 s2 z by simp
  qed
  have e2r: "\<forall>col. col < c \<longrightarrow> fq (entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r col) = 0"
  proof (intro allI impI)
    fix col
    assume colc: "col < c"
    have colA: "col < n_cols A" using colc cn by simp
    have col1: "col < n_cols (swap_rows A r i)" using colA nc1 by simp
    have s2: "entry (swap_rows A r i) r col = entry A (swap_idx r i r) col"
      using entry_swap_rows[OF rn i rn] .
    have si: "swap_idx r i r = i" by simp
    have z1: "fq (entry A i col) = 0" using zb ri i colc by (rule zero_below_entry)
    have z2: "fq (entry (swap_rows A r i) r col) = 0" using s2 si z1 by simp
    have s3: "entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r col = fq (invmod (entry (swap_rows A r i) r c) * entry (swap_rows A r i) r col)"
      using entry_scale_row[OF rn1 r1 rn1 col1] by simp
    show "fq (entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r col) = 0" using s3 z2 by (simp add: fq_mult fq_idem)
  qed
  have ez: "fq (entry (eliminate_col (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r c) k col) = 0"
  proof (cases "col < c")
    case True
    have colA: "col < n_cols A" using True cn by simp
    have col2: "col < n_cols (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c)))" using colA nc2 by simp
    have e: "entry (eliminate_col (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r c) k col = fq (entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) k col - entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) k c * entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r col)"
      using entry_eliminate_col[OF r2 rn2 kn2 col2 cn2] knr by simp
    have za: "3329 dvd entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) k col" using e2k True by (simp add: fq_def dvd_eq_mod_eq_0)
    have zr: "3329 dvd entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r col" using e2r True by (simp add: fq_def dvd_eq_mod_eq_0)
    have zd: "3329 dvd entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) k col - entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) k c * entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r col"
      using za zr by (simp add: dvd_diff dvd_mult2)
    have zm: "(entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) k col - entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) k c * entry (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r col) mod 3329 = 0"
      using zd by (simp add: dvd_eq_mod_eq_0)
    show ?thesis using e zm by (simp add: fq_def)
  next
    case fls: False
    with clo have ceq: "col = c" by simp
    have e: "entry (eliminate_col (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r c) k c = 0"
      using entry_eliminate_col_below[OF r2 rn2 kn2 knr cn2 piv] .
    show ?thesis using e ceq by simp
  qed
  show "fq (entry (eliminate_col (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r c) k col) = 0" using ez .
qed

lemma zero_below_step_skip:
  assumes zb: "zero_below r c A" and rect: "is_rect A"
    and rn: "r < n_rows A" and cn: "c < n_cols A"
    and none: "find_pivot_fuel (n_rows A) A r c = None"
  shows "zero_below r (c + 1) A"
proof (rule zero_below_skip)
  show "zero_below r c A" by (rule zb)
next
  show "\<forall>k. r \<le> k \<and> k < n_rows A \<longrightarrow> fq (entry A k c) = 0"
    using pivot_none_zeros[where f="n_rows A" and A=A and c=c and r=r] none by simp
qed


(* seg: rank-col-bound-5-20261023 *)
section \<open>Counting columns: the rank is bounded by the number of columns\<close>

text \<open>The elimination is driven by the column pointer, which increases at
  every step, and by the row pointer, which never overtakes it.  Hence at the
  end either the columns are exhausted or the rows are, and in both cases the
  number of nonzero rows is at most the number of columns.\<close>

lemma zero_below_zero [simp]: "zero_below 0 0 A"
  by (simp add: zero_below_def)

lemma n_cols_pivot_step:
  assumes rn: "r < n_rows A" and i: "i < n_rows A" and rect: "is_rect A"
  shows "n_cols (eliminate_col (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r c) = n_cols A"
proof -
  have a1: "n_cols (swap_rows A r i) = n_cols A"
    using n_cols_swap_rows[OF rn i rect] .
  have a2: "n_cols (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) = n_cols A"
    using n_cols_scale_row[of "(swap_rows A r i)" r "invmod (entry (swap_rows A r i) r c)"] a1 by simp
  have rn1: "r < n_rows (swap_rows A r i)" using rn by simp
  have r1: "is_rect (swap_rows A r i)" using is_rect_swap_rows[OF rect rn i] .
  have r2: "is_rect (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c)))" using is_rect_scale_row[OF r1 rn1] .
  have rn2: "r < n_rows (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c)))" using rn by simp
  show ?thesis using n_cols_eliminate_col[OF r2 rn2] a2 by simp
qed

lemma all_zero_row_below:
  assumes zb: "zero_below r (n_cols B) B" and rect: "is_rect B"
    and kn: "k < n_rows B" and rk: "r \<le> k"
  shows "all_zero_row (B ! k)"
proof (unfold all_zero_row_def, intro ballI)
  fix x
  assume xm: "x \<in> set (B ! k)"
  have len: "length (B ! k) = n_cols B" using is_rect_rows[OF rect kn] .
  obtain col where col: "col < length (B ! k)" and x: "x = (B ! k) ! col"
    using xm by (auto simp add: in_set_conv_nth)
  have cn: "col < n_cols B" using col len by simp
  have e: "fq (entry B k col) = 0" using zb rk kn cn by (rule zero_below_entry)
  show "fq x = 0" using x e by (simp add: entry_def)
qed

lemma filter_take_eq:
  assumes all: "\<forall>x \<in> set (drop r xs). \<not> P x"
  shows "filter P xs = filter P (take r xs)"
proof -
  have e0: "take r xs @ drop r xs = xs" using append_take_drop_id .
  have e1: "filter P xs = filter P (take r xs @ drop r xs)" using e0 by (simp only: e0)
  have e2: "filter P (take r xs @ drop r xs) = filter P (take r xs) @ filter P (drop r xs)"
    by (simp only: filter_append)
  have e3: "filter P (drop r xs) = []" using all by (simp only: filter_empty_conv)
  show ?thesis using e1 e2 e3 by simp
qed

lemma mat_rank_le_of_zero_below:
  assumes zb: "zero_below r' c' B" and rc: "r' \<le> c'" and cn: "c' \<le> n_cols B"
    and nc: "n_cols B = n_cols A" and rect: "is_rect B"
    and disj: "n_rows B \<le> r' \<or> n_cols B \<le> c'"
  shows "length (filter (\<lambda>r. \<not> all_zero_row r) B) \<le> n_cols A"
proof -
  have le: "length (filter (\<lambda>r. \<not> all_zero_row r) B) \<le> r'"
  proof -
    have allz: "\<forall>x \<in> set (drop r' B). all_zero_row x"
    proof (intro ballI)
      fix x
      assume xm: "x \<in> set (drop r' B)"
      obtain j where j: "j < length (drop r' B)" and x: "(drop r' B) ! j = x"
        using xm by (auto simp add: in_set_conv_nth)
      have idx: "r' + j < n_rows B"
      proof -
        have l1: "length (drop r' B) = length B - r'" by simp
        have l2: "j < length B - r'" using j l1 by simp
        have l4: "r' + j < length B" using l2 by (simp add: less_diff_conv add.commute)
        show ?thesis using l4 by (simp add: n_rows_def)
      qed
      have xe: "x = B ! (r' + j)" using x j by (simp add: nth_drop)
      show "all_zero_row x"
      proof (cases "n_cols B \<le> c'")
        case True
        have z1: "zero_below r' (n_cols B) B" using zb True by (simp add: zero_below_def)
        have az: "all_zero_row (B ! (r' + j))"
          using z1 rect idx by (rule all_zero_row_below, simp)
        show ?thesis using xe az by simp
      next
        case fls: False
        with disj have nr: "n_rows B \<le> r'" by simp
        with idx show ?thesis by simp
      qed
    qed
    have allz2: "\<forall>x \<in> set (drop r' B). \<not> (\<lambda>r. \<not> all_zero_row r) x"
      using allz by simp
    have e: "filter (\<lambda>r. \<not> all_zero_row r) B
        = filter (\<lambda>r. \<not> all_zero_row r) (take r' B)"
      using allz2 by (rule filter_take_eq)
    have "length (filter (\<lambda>r. \<not> all_zero_row r) B)
        = length (filter (\<lambda>r. \<not> all_zero_row r) (take r' B))" using e by simp
    also have "\<dots> \<le> length (take r' B)" by (rule length_filter_le)
    also have "\<dots> \<le> r'" by (simp add: length_take min_def)
    finally show ?thesis .
  qed
  have "r' \<le> n_cols A" using rc cn nc by simp
  with le show ?thesis by simp
qed

(* seg: rank-col-bound-shape-20261023 *)

text \<open>The column pointer never waits.  A step either fails to find a pivot and
  moves on to the next column, or finds one and advances both pointers, so every
  step that stays inside the guard increases @{text c} by one.  A run that burns
  its whole fuel without leaving the guard has therefore advanced the column
  pointer by exactly the fuel, and no run can push it past @{text "n_cols A"}.
  The invariant also records rectangularity and the preserved row and column
  counts, which is what the final rank bound consumes.\<close>

lemma rref_fuel_shape:
  "zero_below r c A \<Longrightarrow> r \<le> c \<Longrightarrow> c \<le> n_cols A \<Longrightarrow> is_rect A \<Longrightarrow>
     \<exists>r0 c0. r \<le> r0 \<and> r0 \<le> c0 \<and> c \<le> c0 \<and> c0 \<le> n_cols A
       \<and> zero_below r0 c0 (rref_fuel f r c A)
       \<and> is_rect (rref_fuel f r c A)
       \<and> n_cols (rref_fuel f r c A) = n_cols A
       \<and> n_rows (rref_fuel f r c A) = n_rows A
       \<and> (n_rows A \<le> r0 \<or> n_cols A \<le> c0 \<or> c + f \<le> c0)"
proof (induct f arbitrary: r c A)
  case 0
  then show ?case by (rule_tac x=r in exI, rule_tac x=c in exI, intro conjI, simp_all)
next
  case (Suc f)
  have zb: "zero_below r c A" using Suc.prems by simp
  have rc: "r \<le> c" using Suc.prems by simp
  have cn: "c \<le> n_cols A" using Suc.prems by simp
  have rect: "is_rect A" using Suc.prems by simp
  show ?case
  proof (cases "r < n_rows A \<and> c < n_cols A")
    case False
    have hd: "n_rows A \<le> r \<or> n_cols A \<le> c" using False by presburger
    then show ?thesis
      using zb rc cn rect hd
      by (rule_tac x=r in exI, rule_tac x=c in exI, intro conjI, simp_all add: rref_fuel.simps False)
  next
    case True
    have rn: "r < n_rows A" and cnlt: "c < n_cols A" using True by simp_all
    show ?thesis
    proof (cases "find_pivot_fuel (n_rows A) A r c")
      case None
      have eq: "rref_fuel (Suc f) r c A = rref_fuel f r (c + 1) A"
        by (simp add: rref_fuel.simps None rn cnlt)
      have zb': "zero_below r (c + 1) A"
        using zero_below_step_skip[OF zb rect rn cnlt None] .
      have rc': "r \<le> c + 1" using rc by simp
      have cn': "c + 1 \<le> n_cols A" using cnlt by simp
      have ih: "\<exists>r' c'. r \<le> r' \<and> r' \<le> c' \<and> c + 1 \<le> c' \<and> c' \<le> n_cols A
                   \<and> zero_below r' c' (rref_fuel f r (c + 1) A)
                   \<and> is_rect (rref_fuel f r (c + 1) A)
                   \<and> n_cols (rref_fuel f r (c + 1) A) = n_cols A
                   \<and> n_rows (rref_fuel f r (c + 1) A) = n_rows A
                   \<and> (n_rows A \<le> r' \<or> n_cols A \<le> c' \<or> (c + 1) + f \<le> c')"
        by (rule Suc.hyps[of r "c + 1" A, OF zb' rc' cn' rect])
      then obtain r' c' where
        rle: "r \<le> r'" and rcle: "r' \<le> c'" and cle: "c + 1 \<le> c'" and cnle: "c' \<le> n_cols A"
        and zbR: "zero_below r' c' (rref_fuel f r (c + 1) A)"
        and rectR: "is_rect (rref_fuel f r (c + 1) A)"
        and ncR: "n_cols (rref_fuel f r (c + 1) A) = n_cols A"
        and nrR: "n_rows (rref_fuel f r (c + 1) A) = n_rows A"
        and cnd: "n_rows A \<le> r' \<or> n_cols A \<le> c' \<or> (c + 1) + f \<le> c'"
        using ih by blast
      have h: "r \<le> r' \<and> r' \<le> c' \<and> c \<le> c' \<and> c' \<le> n_cols A
               \<and> zero_below r' c' (rref_fuel (Suc f) r c A)
               \<and> is_rect (rref_fuel (Suc f) r c A)
               \<and> n_cols (rref_fuel (Suc f) r c A) = n_cols A
               \<and> n_rows (rref_fuel (Suc f) r c A) = n_rows A
               \<and> (n_rows A \<le> r' \<or> n_cols A \<le> c' \<or> c + Suc f \<le> c')"
      proof (intro conjI)
        show "r \<le> r'" by (rule rle)
      next
        show "r' \<le> c'" by (rule rcle)
      next
        show "c \<le> c'" using cle by presburger
      next
        show "c' \<le> n_cols A" by (rule cnle)
      next
        show "zero_below r' c' (rref_fuel (Suc f) r c A)" using zbR eq by simp
      next
        show "is_rect (rref_fuel (Suc f) r c A)" using rectR eq by simp
      next
        show "n_cols (rref_fuel (Suc f) r c A) = n_cols A" using ncR eq by simp
      next
        show "n_rows (rref_fuel (Suc f) r c A) = n_rows A" using nrR eq by simp
      next
        show "n_rows A \<le> r' \<or> n_cols A \<le> c' \<or> c + Suc f \<le> c'"
          using cnd by (elim disjE, simp_all)
      qed
      from h show ?thesis
        by (rule_tac x=r' in exI, rule_tac x=c' in exI, assumption)
    next
      case (Some i)
      have ib: "i < n_rows A" using Some by (rule pivot_some_lt)
      have ri: "r \<le> i" using Some by (rule pivot_some_ge)
      have pnz: "fq (entry A i c) \<noteq> 0" using Some by (rule pivot_some_nz)
      define B where "B = eliminate_col (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c))) r c"
      have eq: "rref_fuel (Suc f) r c A = rref_fuel f (r + 1) (c + 1) B"
        by (simp add: B_def rref_fuel.simps Some Let_def rn cnlt)
      have zbB: "zero_below (r + 1) (c + 1) B"
        using zero_below_pivot[OF zb rect rn cnlt ib ri pnz] by (simp add: B_def)
      have r0: "is_rect (swap_rows A r i)" using is_rect_swap_rows[OF rect rn ib] .
      have rn0: "r < n_rows (swap_rows A r i)" using rn by simp
      have r1: "is_rect (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c)))"
        using is_rect_scale_row[OF r0 rn0] .
      have rn1: "r < n_rows (scale_row (swap_rows A r i) r (invmod (entry (swap_rows A r i) r c)))"
        using rn by simp
      have rectB: "is_rect B" using is_rect_eliminate_col[OF r1 rn1] by (simp add: B_def)
      have ncB: "n_cols B = n_cols A" using n_cols_pivot_step[OF rn ib rect] by (simp add: B_def)
      have nrB: "n_rows B = n_rows A" by (simp add: B_def)
      have rcB: "r + 1 \<le> c + 1" using rc by simp
      have cnB: "c + 1 \<le> n_cols B" using cnlt ncB by simp
      have ih: "\<exists>r' c'. r + 1 \<le> r' \<and> r' \<le> c' \<and> c + 1 \<le> c' \<and> c' \<le> n_cols B
                   \<and> zero_below r' c' (rref_fuel f (r + 1) (c + 1) B)
                   \<and> is_rect (rref_fuel f (r + 1) (c + 1) B)
                   \<and> n_cols (rref_fuel f (r + 1) (c + 1) B) = n_cols B
                   \<and> n_rows (rref_fuel f (r + 1) (c + 1) B) = n_rows B
                   \<and> (n_rows B \<le> r' \<or> n_cols B \<le> c' \<or> (c + 1) + f \<le> c')"
        by (rule Suc.hyps[of "r + 1" "c + 1" B, OF zbB rcB cnB rectB])
      then obtain r' c' where
        rle: "r + 1 \<le> r'" and rcle: "r' \<le> c'" and cle: "c + 1 \<le> c'" and cnle: "c' \<le> n_cols B"
        and zbR: "zero_below r' c' (rref_fuel f (r + 1) (c + 1) B)"
        and rectR: "is_rect (rref_fuel f (r + 1) (c + 1) B)"
        and ncR: "n_cols (rref_fuel f (r + 1) (c + 1) B) = n_cols B"
        and nrR: "n_rows (rref_fuel f (r + 1) (c + 1) B) = n_rows B"
        and cnd: "n_rows B \<le> r' \<or> n_cols B \<le> c' \<or> (c + 1) + f \<le> c'"
        using ih by blast
      have h: "r \<le> r' \<and> r' \<le> c' \<and> c \<le> c' \<and> c' \<le> n_cols A
               \<and> zero_below r' c' (rref_fuel (Suc f) r c A)
               \<and> is_rect (rref_fuel (Suc f) r c A)
               \<and> n_cols (rref_fuel (Suc f) r c A) = n_cols A
               \<and> n_rows (rref_fuel (Suc f) r c A) = n_rows A
               \<and> (n_rows A \<le> r' \<or> n_cols A \<le> c' \<or> c + Suc f \<le> c')"
      proof (intro conjI)
        show "r \<le> r'" using rle by presburger
      next
        show "r' \<le> c'" by (rule rcle)
      next
        show "c \<le> c'" using cle by presburger
      next
        show "c' \<le> n_cols A" using cnle ncB by simp
      next
        show "zero_below r' c' (rref_fuel (Suc f) r c A)" using zbR eq by simp
      next
        show "is_rect (rref_fuel (Suc f) r c A)" using rectR eq by simp
      next
        show "n_cols (rref_fuel (Suc f) r c A) = n_cols A" using ncR eq ncB by simp
      next
        show "n_rows (rref_fuel (Suc f) r c A) = n_rows A" using nrR eq nrB by simp
      next
        show "n_rows A \<le> r' \<or> n_cols A \<le> c' \<or> c + Suc f \<le> c'"
          using cnd nrB ncB by (elim disjE, simp_all)
      qed
      from h show ?thesis
        by (rule_tac x=r' in exI, rule_tac x=c' in exI, assumption)
    qed
  qed
qed

lemma mat_rank_le_n_cols:
  assumes rect: "is_rect A"
  shows "mat_rank A \<le> n_cols A"
proof -
  have sh: "\<exists>r' c'. 0 \<le> r' \<and> r' \<le> c' \<and> c' \<le> n_cols A
              \<and> zero_below r' c' (rref A)
              \<and> is_rect (rref A)
              \<and> n_cols (rref A) = n_cols A
              \<and> n_rows (rref A) = n_rows A
              \<and> (n_rows A \<le> r' \<or> n_cols A \<le> c' \<or> (n_rows A * n_cols A + n_rows A + 1) \<le> c')"
    using rref_fuel_shape[of 0 0 A "n_rows A * n_cols A + n_rows A + 1"] rect
    by (simp add: rref_def)
  obtain r' c' where
    rcle: "r' \<le> c'" and cnle: "c' \<le> n_cols A"
    and zbR: "zero_below r' c' (rref A)"
    and rectR: "is_rect (rref A)"
    and ncR: "n_cols (rref A) = n_cols A"
    and nrR: "n_rows (rref A) = n_rows A"
    and cnd: "n_rows A \<le> r' \<or> n_cols A \<le> c' \<or> (n_rows A * n_cols A + n_rows A + 1) \<le> c'"
    using sh by blast
  have nc_le: "n_cols A \<le> n_rows A * n_cols A"
  proof (cases "n_cols A = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have nz: "0 < n_cols A" using False by simp
    have nr1: "1 \<le> n_rows A"
    proof (rule ccontr)
      assume "\<not> 1 \<le> n_rows A"
      hence "n_rows A = 0" by simp
      hence "A = []" by (simp add: n_rows_def)
      hence "n_cols A = 0" by (simp add: n_cols_def)
      with nz show False by simp
    qed
    have "1 * n_cols A \<le> n_rows A * n_cols A" using nr1 by (rule mult_le_mono1)
    thus ?thesis by simp
  qed
  have nN: "n_cols A < n_rows A * n_cols A + n_rows A + 1" using nc_le by linarith
  have disj: "n_rows (rref A) \<le> r' \<or> n_cols (rref A) \<le> c'"
  proof -
    have nbig: "\<not> (n_rows A * n_cols A + n_rows A + 1) \<le> c'" using cnle nN by linarith
    with cnd have "n_rows A \<le> r' \<or> n_cols A \<le> c'" by blast
    with nrR ncR show ?thesis by simp
  qed
  have cnB: "c' \<le> n_cols (rref A)" using cnle ncR by simp
  have le: "length (filter (\<lambda>r. \<not> all_zero_row r) (rref A)) \<le> n_cols A"
    using mat_rank_le_of_zero_below[OF zbR rcle cnB ncR rectR disj] .
  show ?thesis using le by (simp add: mat_rank_def)
qed
section \<open>Reflecting the reduction back to the original matrix\<close>

text \<open>The reduction is a sequence of three elementary operations per pivot step, so
  a vanishing-minor statement about @{const rref_fuel} reflects back one step at a
  time: undo the elimination sweep, undo the scaling, undo the swap.  The fuel
  induction below makes that sequence explicit; the guard of the step decides
  which of the three shapes the recursive call takes.\<close>

lemma minors_zero_rref_fuel_undo:
  "is_rect A \<Longrightarrow> minors_zero (rref_fuel f r c A) \<Longrightarrow> minors_zero A"
proof (induct f arbitrary: r c A rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (Suc f)
  show ?case
  proof (cases "r < n_rows A \<and> c < n_cols A")
    case False
    show ?thesis using Suc.prems False by (simp add: rref_fuel.simps)
  next
    case True
    have rA: "r < n_rows A" and cA: "c < n_cols A" using True by simp_all
    show ?thesis
    proof (cases "find_pivot_fuel (n_rows A) A r c")
      case None
      have mz1: "minors_zero (rref_fuel f r (c + 1) A)"
        using Suc.prems True None by (simp add: rref_fuel.simps)
      show ?thesis
      proof (rule Suc.hyps [of A r "c + 1"])
        show "is_rect A" using Suc.prems(1) .
        show "minors_zero (rref_fuel f r (c + 1) A)" using mz1 .
      qed
    next
      case (Some i)
      define A1 where "A1 = swap_rows A r i"
      define p where "p = entry A1 r c"
      define A2 where "A2 = scale_row A1 r (invmod p)"
      define A3 where "A3 = eliminate_col A2 r c"
      have mz3: "minors_zero (rref_fuel f (r + 1) (c + 1) A3)"
        using Suc.prems True Some
        by (simp add: rref_fuel.simps Let_def A1_def[symmetric] p_def[symmetric]
                      A2_def[symmetric] A3_def[symmetric])
      have iA: "i < n_rows A" using Some by (rule pivot_some_lt)
      have pnzA: "fq (entry A i c) \<noteq> 0" using Some by (rule pivot_some_nz)
      have eA: "entry A1 r c = entry A i c"
      proof -
        have h: "entry (swap_rows A r i) r c = entry A (swap_idx r i r) c"
        proof (rule entry_swap_rows)
          show "r < n_rows A" using rA .
          show "i < n_rows A" using iA .
          show "r < n_rows A" using rA .
        qed
        have "entry A1 r c = entry (swap_rows A r i) r c" by (simp add: A1_def)
        thus ?thesis using h by simp
      qed
      have pnz: "fq p \<noteq> 0" using pnzA eA by (simp add: p_def)
      have pq: "fq (p * invmod p) = 1" using pnz by (rule invmod_correct_gen)
      have rectA1: "is_rect A1"
        using is_rect_swap_rows [OF Suc.prems(1) rA iA] by (simp add: A1_def)
      have rA1: "r < n_rows A1" using rA by (simp add: A1_def)
      have rectA2: "is_rect A2"
        using is_rect_scale_row [OF rectA1 rA1] by (simp add: A2_def)
      have rA2: "r < n_rows A2" using rA1 by (simp add: A2_def)
      have rectA3: "is_rect A3"
        using is_rect_eliminate_col [OF rectA2 rA2] by (simp add: A3_def)
      have mzA3: "minors_zero A3"
      proof (rule Suc.hyps [of A3 "r + 1" "c + 1"])
        show "is_rect A3" using rectA3 .
        show "minors_zero (rref_fuel f (r + 1) (c + 1) A3)" using mz3 .
      qed
      have mzE: "minors_zero (eliminate_col A2 r c)" using mzA3 by (simp add: A3_def)
      have mzA2: "minors_zero A2"
        using mzE rectA2 rA2 by (rule minors_zero_eliminate_col_undo)
      have mzS: "minors_zero (scale_row A1 r (invmod p))" using mzA2 by (simp add: A2_def)
      have mzA1: "minors_zero A1"
        using mzS rA1 rectA1 pq by (rule minors_zero_scale_row_undo)
      have mzS1: "minors_zero (swap_rows A r i)" using mzA1 by (simp add: A1_def)
      have mzA: "minors_zero A"
        using mzS1 rA iA Suc.prems(1) by (rule minors_zero_swap_undo)
      show ?thesis using mzA .
    qed
  qed
qed

lemma minors_zero_rref_undo:
  assumes rect: "is_rect A" and mz: "minors_zero (rref A)"
  shows "minors_zero A"
proof -
  have h: "minors_zero (rref_fuel (n_rows A * n_cols A + n_rows A + 1) 0 0 A)"
    using mz by (simp add: rref_def)
  show ?thesis
  proof (rule minors_zero_rref_fuel_undo)
    show "is_rect A" using rect .
    show "minors_zero (rref_fuel (n_rows A * n_cols A + n_rows A + 1) 0 0 A)" using h .
  qed
qed
end
