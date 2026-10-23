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
  that is deliberate rather than an oversight.  The two lemmas the obligation
  needs are out of reach of the definitions in @{file VWZ_RREF.thy} alone,
  because @{text mat_rank} is defined as a count of nonzero rows of @{text rref}
  and no bridge from @{text rref} back to matrix invariants exists yet.  Status of
  each ingredient:

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
  nonzero row, every @{text "2 x 2"} minor of the reduced form vanishes.  Proved
  in this file, together with @{text row_zero_or_zero_of_rank_le_one} and the
  shape lemma @{text is_rect_rref}; it assumes only @{text "is_rect A"}.
  \<^enum> combining the three gives @{text rank_ge_two_of_nonzero_minor}, while
  @{text rank_outer_sum_le_two} additionally needs the bound
  @{text "mat_rank (mat_mult A B) \<le> n_cols A"} -- that the rank is at most the
  number of pivot columns, which is again the reduced-shape characterisation.

  Writing the remaining headers down without proofs would put @{text sorry}s
  outside the obligation ledger, so they stay a work list: the ledger keeps its
  exact count of 56 lemmas and 7 sorry, and the lemmas added above carry no
  @{text sorry} at all.\<close>

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

end
