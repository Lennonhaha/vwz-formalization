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

text \<open>The main lemma of this section.  Because @{text all_zero_row} is the
  modulo-@{text q} notion, what it yields is congruence of the minor to zero
  modulo @{text 3329}, not integer equality.  That is the right conclusion for
  this development: @{text mat_rank2} and @{text mat_rank1} are also stated
  modulo @{text q}.

  The hypothesis @{text "is_rect (rref A)"} is what turns a column index below
  @{text n_cols} into an index below the length of a row; establishing that the
  reduction preserves rectangularity is a separate shape lemma about
  @{text rref_fuel} and is not part of this section.\<close>

lemma rank_le_one_imp_minors_vanish:
  assumes rk: "mat_rank A \<le> 1"
    and rect: "is_rect (rref A)"
    and a: "a < n_rows (rref A)" and b: "b < n_rows (rref A)" and ab: "a \<noteq> b"
    and c: "c < n_cols (rref A)" and d: "d < n_cols (rref A)"
  shows "(entry (rref A) a c * entry (rref A) b d
            - entry (rref A) a d * entry (rref A) b c) mod 3329 = 0"
proof -
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
  nonzero row, every @{text "2 x 2"} minor of the reduced form vanishes.  This one
  is now proved, above, together with @{text row_zero_or_zero_of_rank_le_one};
  it still assumes @{text "is_rect (rref A)"}, because the shape lemma for
  @{text rref_fuel} is not established yet.
  \<^enum> combining the three gives @{text rank_ge_two_of_nonzero_minor}, while
  @{text rank_outer_sum_le_two} additionally needs the bound
  @{text "mat_rank (mat_mult A B) \<le> n_cols A"} -- that the rank is at most the
  number of pivot columns, which is again the reduced-shape characterisation.

  Writing the remaining headers down without proofs would put @{text sorry}s
  outside the obligation ledger, so they stay a work list: the ledger keeps its
  exact count of 56 lemmas and 7 sorry, and the lemmas added above carry no
  @{text sorry} at all.\<close>

end
