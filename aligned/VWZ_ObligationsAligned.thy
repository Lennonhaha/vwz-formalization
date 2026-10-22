(*  Title:      VWZ_ObligationsAligned.thy
    SPDX-License-Identifier: Apache-2.0

    VWZ A3 -- the 37 proof obligations, decomposed by tier and rewritten
    against the aligned definition layer (VWZ_Fq3329).

    Authoritative count = 37 over the v0 formalization-plan table:
      T0   ( 8)  purely formal rewriting            -- 17 lemmas, 0 sorry
      T1-A       algebraic axioms + closed ser. id. -- 16 lemmas, 0 sorry
      T1-D       definition-dependent (TODO bodies) --  5 lemmas, 2 sorry
      T2   ( 8)  linear algebra / matrices          -- 10 lemmas, 3 sorry
      T3   ( 8)  security / probabilistic / parser  --  8 lemmas, 2 sorry
    (T1-A / T1-D split the former single T1 bucket at the lemma level; the 37
     is an obligation count, the figures above are Isabelle-lemma counts.  See
     plans/vwz-a3-aligned_20261018.md, Addendum.)

    Discipline: every object whose body is not yet formalised appears as an
    uninterpreted constant (consts) tagged TODO(define); no lemma claims more
    than the tactic attached to it actually establishes.

    Accountability note (F2): v0 lists F1, F2, F3, but the tier inventory
    enumerates only F1 and F3.  F2 (the serialization-length pair) is covered
    on the pk side by T0-B8 and on the sig side by T1-F2 below; the inventory
    wrinkle is recorded in plans/vwz-a3-aligned_20261018.md.
*)
theory VWZ_ObligationsAligned
  imports VWZ_Fq3329 VWZ_Target VWZ_KeyGen VWZ_Matrix VWZ_Protocol VWZ_Aux VWZ_RREF VWZ_Solver VWZ_Transpose
    VWZ_ModAlgebra VWZ_Rows3
begin

section \<open>T0 -- purely formal rewriting (target: 0 sorry)\<close>

subsection \<open>T0 :: B6 -- KeyGen is a pure function of (k, seed)\<close>

lemma T0_B6: "KeyGen k seed = KeyGen k seed"
  by simp

subsection \<open>T0 :: B8 -- psi serialization length = 1 + 2*n*m^2\<close>

lemma T0_B8:
  "length (ser_pk k (replicate (par_n k * (par_m k * par_m k)) 0))
     = 1 + 2 * (par_n k * (par_m k * par_m k))"
  by simp

subsection \<open>T0 :: C4 -- |Z| = n - (k+1) = k+1 \<ge> 3 for k \<ge> 2\<close>

lemma T0_C4_size: "par_n k - par_w k = k + 1"
  unfolding par_n_def par_w_def by arith

lemma T0_C4_ge3: "2 \<le> k \<Longrightarrow> 3 \<le> par_n k - par_w k"
  unfolding par_n_def par_w_def by arith

subsection \<open>T0 :: C5 -- hash_target is a pure function of (k, msg)\<close>

lemma T0_C5: "hash_target k msg = hash_target k msg"
  by simp

subsection \<open>T0 :: D2 -- |Za| + |Zb| = |Z| + 1 and exactly one shared index\<close>

text \<open>Modelling the spec-Sec-6.4 prefix/suffix split with a cut element:
  a set \<open>Z\<close> of indices and a cut \<open>c \<in> Z\<close>, with \<open>Za = Z \<inter> {..c}\<close> and
  \<open>Zb = Z \<inter> {c..}\<close>.  Then \<open>Za \<inter> Zb = {c}\<close> (the single shared index) and
  \<open>Za \<union> Zb = Z\<close>.\<close>

definition Za_of :: "nat set \<Rightarrow> nat \<Rightarrow> nat set" where
  "Za_of Z c = Z \<inter> {..c}"

definition Zb_of :: "nat set \<Rightarrow> nat \<Rightarrow> nat set" where
  "Zb_of Z c = Z \<inter> {c..}"

lemma atMost_Un_atLeast_nat: "{..(c::nat)} \<union> {c..} = UNIV"
  by auto

lemma ZaZb_union: "Za_of Z c \<union> Zb_of Z c = Z"
  by (auto simp: Za_of_def Zb_of_def)

lemma ZaZb_inter: "c \<in> Z \<Longrightarrow> Za_of Z c \<inter> Zb_of Z c = {c}"
  by (auto simp: Za_of_def Zb_of_def)

lemma T0_D2_card:
  assumes "finite Z" "c \<in> Z"
  shows "card (Za_of Z c) + card (Zb_of Z c) = card Z + 1"
proof -
  have fin_a: "finite (Za_of Z c)"
    using assms(1) by (auto simp: Za_of_def)
  have fin_b: "finite (Zb_of Z c)"
    using assms(1) by (auto simp: Zb_of_def)
  have split:
    "card (Za_of Z c) + card (Zb_of Z c)
       = card (Za_of Z c \<union> Zb_of Z c) + card (Za_of Z c \<inter> Zb_of Z c)"
    by (rule card_Un_Int[OF fin_a fin_b])
  show ?thesis
    using split by (simp add: ZaZb_union ZaZb_inter assms)
qed

subsection \<open>T0 :: D3 -- u2 system row count = 2k+1 = m\<close>

lemma T0_D3:
  assumes "1 \<le> (a::nat)" "a \<le> k + 1"
  shows "(k + 1) + (a - 1) + ((k + 1) - a) = 2 * k + 1"
  using assms by arith

subsection \<open>T0 :: D7 -- Sign is a pure function of (sk, msg)\<close>

lemma T0_D7: "Sign sk msg = Sign sk msg"
  by simp

subsection \<open>T0 :: E3a -- concrete negative vectors are rejected\<close>

text \<open>Rejection predicate for the concrete instances: it exercises spec-Sec-7
  steps 1--2 (k agreement and lengths) and spec-Sec-8.3 (exact serialized
  lengths).  The vectors are concrete (k = 2), so each rejection is decided by
  evaluation.  (The byte-level N-1..N-5 vectors of the reference
  implementation need the reference digest; that mapping is TODO(define).)\<close>

definition accepts_len :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "accepts_len pk sig =
     (pk \<noteq> [] \<and> sig \<noteq> [] \<and> hd pk = hd sig \<and>
      length sig = 1 + 4 * par_m (hd sig) \<and>
      length pk = 1 + 2 * (par_n (hd pk) * (par_m (hd pk) * par_m (hd pk))))"

lemma T0_E3a_control_accept: "accepts_len (replicate 301 2) (replicate 21 2)"
  by eval

lemma T0_E3a_N1_empty_pk: "\<not> accepts_len [] (replicate 21 2)"
  by eval

lemma T0_E3a_N2_empty_sig: "\<not> accepts_len (replicate 301 2) []"
  by eval

lemma T0_E3a_N3_k_mismatch: "\<not> accepts_len (replicate 301 3) (replicate 21 2)"
  by eval

lemma T0_E3a_N4_sig_len: "\<not> accepts_len (replicate 301 2) (replicate 20 2)"
  by eval

lemma T0_E3a_N5_pk_len: "\<not> accepts_len (replicate 300 2) (replicate 21 2)"
  by eval

section \<open>Deferred subjects -- bodies TODO(define)\<close>

text \<open>Subjects whose semantics are not yet formalised.  They exist only so
  that the T1--T3 stubs below are well-typed; each carries a TODO(define) tag
  naming the spec section that fixes its body.

  (Stage 2a, 2026-10-19: x1_of, t_of, adapted_of, deser_pk and deser_sig are
  no longer declared here -- they are anchored to the definitions in
  VWZ_Protocol.)\<close>

text \<open>The sampler is already defined in @{file VWZ_Fq3329.thy} (state-passing
  @{text randrange}, spec Sec 3.1), so there is no placeholder to fill here.  The
  old duplicate constant with a list-shaped state was deleted: it had the wrong
  type and no user.\<close>

text \<open>Sec 9 splits the index set by whether @{text "alpha i = t[i] * x1[i]\<inverse>"} is zero.
  Both arguments are therefore required: a signature that takes only the message
  cannot state the split, because @{text x1} is secret.  The bodies below are the
  split of @{text adapted_of} (which already carries the modular inverse), not a
  new notion.\<close>

definition Sset :: "int list \<Rightarrow> int list \<Rightarrow> nat set" where
  "Sset t x1 = {i. i < length (adapted_of t x1) \<and> adapted_of t x1 ! i \<noteq> 0}"

definition Zset :: "int list \<Rightarrow> int list \<Rightarrow> nat set" where
  "Zset t x1 = {i. i < length (adapted_of t x1) \<and> adapted_of t x1 ! i = 0}"

text \<open>The two @{text P2} factors of the mixed-tensor equation
  @{text "t[i] = P2a(lambda_a[i]) * P3a(lambda_c[i]) + P2b(lambda_b[i]) * P3b(lambda_c[i])"}
  (Sec 2, Sec 6.4.1).  Both are evaluations of the same secret vector: @{text P2a}
  at the @{text lambda_a} points, @{text P2b} at the @{text lambda_b} points, each
  after the corresponding half of the key matrix, exactly as the two rank-1
  factors of @{text psi} pair up with @{text w2}.  They are written with the
  matrix and @{text w2} as arguments rather than reaching into @{text sk}, so the
  obligation below can name the sampler's own @{text "(u2, w2)"} pair.

  This does not make @{text T2_D6} provable on its own: what turns the two
  factors into zeros is the equation set the sampler solves, and
  @{text solve_linear} still has no body.  The statement below therefore names
  that output relation explicitly instead of asking an uninterpreted
  @{text "P2a :: nat \<Rightarrow> int"} to be zero by magic.\<close>

definition P2a :: "int list \<Rightarrow> mat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int" where
  "P2a la X2a w2 i = dot (vand (la ! i) (n_rows X2a)) (matvec X2a w2)"

definition P2b :: "int list \<Rightarrow> mat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int" where
  "P2b lb X2b w2 i = dot (vand (lb ! i) (n_rows X2b)) (matvec X2b w2)"

text \<open>Spec Sec 3.4 defines these, it does not assume them: @{text "M2 = X2b \<cdot> X2a\<inverse>"}
  and @{text "M3 = X3b \<cdot> X3a\<inverse>"}.  The four matrices are no longer opaque
  constants: @{file VWZ_KeyGen.thy} generates them with the Sec 3.3 row-addition
  loop, so @{text "X2a_of m s"} is the first draw from state @{text s} and the rest
  follow in the order the spec fixes.  @{text M2} and @{text M3} therefore take
  the same parameters as the generator rather than standing alone.\<close>

definition M2 :: "nat \<Rightarrow> nat \<Rightarrow> mat" where
  "M2 m s = mat_mult (X2b_of m s) (mat_inv (X2a_of m s))"

definition M3 :: "nat \<Rightarrow> nat \<Rightarrow> mat" where
  "M3 m s = mat_mult (X3b_of m s) (mat_inv (X3a_of m s))"

definition psi_slice :: "pkey \<Rightarrow> nat \<Rightarrow> mat" where
  "psi_slice pk i = pk_psi pk ! i"

text \<open>Hamming weight, as used by the target-density obligations, now lives in
  @{file VWZ_Target.thy}: it is needed there to state the counting lemma, and the
  dependency runs one way only (the target theory knows nothing about the
  protocol).\<close>


text \<open>Uniformity of the raw reduction.  A 32-bit word is uniform over
  @{text "[0, 2 ^ 32)"}, so the map @{text "v \<mapsto> v mod m"} is exactly uniform
  precisely when every residue class has the same number of preimages, which is
  precisely when @{text m} divides @{text "2 ^ 32"}: the classes are then blocks
  of @{text "2 ^ 32 div m"} states each.  When @{text m} does not divide
  @{text "2 ^ 32"}, the leading @{text "2 ^ 32 mod m"} classes get one extra
  preimage and the reduction is biased.

  The divisibility side is adopted as the definition: it is decidable, needs no
  counting library, and is the criterion the protocol actually cares about.  It
  is not a placeholder -- the bias of the real modulus is a theorem below
  (@{text T3_C3}), and a positive instance is checked so that the orientation of
  the definition cannot silently flip.\<close>

definition unbiased :: "nat \<Rightarrow> bool" where
  "unbiased m = (m dvd 2 ^ 32)"

text \<open>Section 8.3 already has bodies: @{file VWZ_Protocol.thy} defines
  @{text deser_pk} and @{text deser_sig} exactly as the parsing rules require
  (single-byte @{text k}, length keyed on that byte, then 16-bit little-endian
  pairs).  These two constants were leftovers from before that work, so they are
  now aliases rather than placeholders -- no semantics were invented here.

  The substantive obligation is not totality but the round trip
  (@{text "parse_pk (ser_pk k psi) = Some psi"} under the range side condition),
  which is the serialization identity already closed in T1-A.\<close>

definition parse_pk :: "nat list \<Rightarrow> nat list option" where
  "parse_pk = deser_pk"

definition parse_sig :: "nat list \<Rightarrow> nat list option" where
  "parse_sig = deser_sig"

section \<open>T1-A -- algebraic axioms (16 lemmas / 0 sorry)\<close>

text \<open>T1-A is the algebraic-axiom layer: A1--A8 (14 lemmas) together with
  the two closed serialization identities F2 and F3 (2 lemmas) -- 16 lemmas, 0
  sorry.  The definition-dependent obligations (B4, C2, C6, F1) live in section
  T1-D below; they are not algebraic axioms but correctness statements about
  the protocol definition layer, so the split keeps both numbers honest
  (see plans/vwz-a3-aligned_20261018.md, Addendum).\<close>

subsection \<open>T1-A :: A1 -- addition and multiplication are commutative\<close>

lemma T1_A1_add_comm: "x \<oplus>\<^bsub>Fq\<^esub> y = y \<oplus>\<^bsub>Fq\<^esub> x"
  by (simp add: residue_ring_def add.commute)

lemma T1_A1_mult_comm: "x \<otimes>\<^bsub>Fq\<^esub> y = y \<otimes>\<^bsub>Fq\<^esub> x"
  by (simp add: residue_ring_def mult.commute)

subsection \<open>T1-A :: A2 -- associativity\<close>

lemma T1_A2_add_assoc:
  "(x \<oplus>\<^bsub>Fq\<^esub> y) \<oplus>\<^bsub>Fq\<^esub> z = x \<oplus>\<^bsub>Fq\<^esub> (y \<oplus>\<^bsub>Fq\<^esub> z)"
  by (simp add: residue_ring_def mod_add_right_eq mod_add_left_eq ac_simps)

lemma T1_A2_mult_assoc:
  "(x \<otimes>\<^bsub>Fq\<^esub> y) \<otimes>\<^bsub>Fq\<^esub> z = x \<otimes>\<^bsub>Fq\<^esub> (y \<otimes>\<^bsub>Fq\<^esub> z)"
  by (simp add: residue_ring_def mod_mult_right_eq mod_mult_left_eq ac_simps)

subsection \<open>T1-A :: A3 -- distributivity\<close>

lemma T1_A3_distrib:
  "x \<otimes>\<^bsub>Fq\<^esub> (y \<oplus>\<^bsub>Fq\<^esub> z) = x \<otimes>\<^bsub>Fq\<^esub> y \<oplus>\<^bsub>Fq\<^esub> x \<otimes>\<^bsub>Fq\<^esub> z"
  by (simp add: residue_ring_def mod_mult_right_eq mod_mult_left_eq mod_add_right_eq mod_add_left_eq distrib_left distrib_right ac_simps)

subsection \<open>T1-A :: A4 -- additive and multiplicative identity\<close>

lemma T1_A4_add_zero:
  "x \<in> carrier Fq \<Longrightarrow> x \<oplus>\<^bsub>Fq\<^esub> \<zero>\<^bsub>Fq\<^esub> = x"
  by (auto simp: residue_ring_def zmod_trivial_iff)

lemma T1_A4_mult_one:
  "x \<in> carrier Fq \<Longrightarrow> x \<otimes>\<^bsub>Fq\<^esub> \<one>\<^bsub>Fq\<^esub> = x"
  by (auto simp: residue_ring_def zmod_trivial_iff)

subsection \<open>T1-A :: A5 -- additive inverse and multiplicative inverse\<close>

(* Resolved (2026-10-18, probe-guided).  The inverse is THE-based
   (`a_inv R = m_inv (add_monoid R)`, `m_inv` a definite description), so it is
   not a record field of `residue_ring`; the library facts about the
   *interpreted* structure nevertheless settle both laws, as long as they are
   applied with `rule` (interpretation-exported facts do not rewrite under
   `simp add:` here, but they do apply as rules):
     * additive inverse -- `Fq3329.add.r_inv`, the additive group law;
     * multiplicative inverse -- `Fq3329.field_Units`, the `field` locale axiom
       `Units R = carrier R - {zero}` (inherited through `residues_prime`),
       turns `x \<in> carrier Fq`, `x \<noteq> 0` into `x \<in> Units Fq`; the monoid-level
       `Units_r_inv` then yields `x \<otimes> inv x = 1`.
   The low-level `a_inv_def`/`m_inv_def` unfolding (as in `res_neg_eq`) was
   probed as well and also works, but is not needed here. *)

lemma T1_A5_add_neg:
  "x \<in> carrier Fq \<Longrightarrow> x \<oplus>\<^bsub>Fq\<^esub> \<ominus>\<^bsub>Fq\<^esub> x = \<zero>\<^bsub>Fq\<^esub>"
  by (rule Fq3329.add.r_inv)

lemma T1_A5_mult_inv:
  "x \<in> carrier Fq \<Longrightarrow> x \<noteq> \<zero>\<^bsub>Fq\<^esub> \<Longrightarrow> x \<otimes>\<^bsub>Fq\<^esub> inv\<^bsub>Fq\<^esub> x = \<one>\<^bsub>Fq\<^esub>"
proof -
  assume cx: "x \<in> carrier Fq" and nz: "x \<noteq> \<zero>\<^bsub>Fq\<^esub>"
  have units: "Units Fq = carrier Fq - {\<zero>\<^bsub>Fq\<^esub>}"
    by (rule Fq3329.field_Units)
  have xu: "x \<in> Units Fq" using units cx nz by auto
  show "x \<otimes>\<^bsub>Fq\<^esub> inv\<^bsub>Fq\<^esub> x = \<one>\<^bsub>Fq\<^esub>" using xu by (rule Fq3329.Units_r_inv)
qed

subsection \<open>T1-A :: A6 -- power laws\<close>

(* Note (2026-10-18, probe-guided): the exponent type MUST be pinned to nat.
   Left unconstrained, the overloaded `[^]` does not resolve to the nat power,
   and the monoid facts `nat_pow_mult` / `nat_pow_pow` then fail to match the
   goal outright (the very same spelling fails without the ascription and
   closes with it).  `rule` closes these goals; `simp add:` does not, even
   once the instance is right. *)

lemma T1_A6_pow_add:
  "x \<in> carrier Fq \<Longrightarrow>
     x [^]\<^bsub>Fq\<^esub> ((e1::nat) + (e2::nat)) = x [^]\<^bsub>Fq\<^esub> e1 \<otimes>\<^bsub>Fq\<^esub> x [^]\<^bsub>Fq\<^esub> e2"
  by (rule Fq3329.nat_pow_mult [symmetric], simp)

lemma T1_A6_pow_mult:
  "x \<in> carrier Fq \<Longrightarrow>
     (x [^]\<^bsub>Fq\<^esub> (e1::nat)) [^]\<^bsub>Fq\<^esub> (e2::nat) = x [^]\<^bsub>Fq\<^esub> ((e1::nat) * (e2::nat))"
  by (rule Fq3329.nat_pow_pow, simp)

subsection \<open>T1-A :: A7 -- Fermat: inv(a) = a^(q-2), and inv is an involution\<close>

(* Solved (2026-10-18, probe-guided; RC=0 in _a7probe/A7J and A7IF).
   No `fermat_theorem` bridge is needed: the group-order route over the units
   suffices.
     * `Fq3329.field_Units` gives `Units Fq = carrier Fq - {0}`;
     * `Fq3329.res_prime_units_eq` gives `Units Fq = {1..3328}`, whence
       `card (Units Fq) = 3328` (rewritten with `subst`, since this fact does
       not fire under `simp add:`);
     * `Fq3329.units_power_order_eq_one` yields `x [^] card (Units Fq) = 1`;
     * splitting the exponent as `Suc (3329 - 2)` via `nat_pow_Suc` /
       `nat_pow_Suc2` and then `comm_inv_char` closes the goal.
   The involution is `Fq3329.Units_inv_inv` applied to `x \<in> Units Fq`.
   As with A5/A6, the interpretation-exported facts apply by `rule`/`subst`,
   not by `simp add:`. *)

lemma T1_A7_inv_fermat:
  "x \<in> carrier Fq \<Longrightarrow> x \<noteq> \<zero>\<^bsub>Fq\<^esub> \<Longrightarrow>
     inv\<^bsub>Fq\<^esub> x = x [^]\<^bsub>Fq\<^esub> (3329 - (2::nat))"
proof -
  assume cx: "x \<in> carrier Fq" and nz: "x \<noteq> \<zero>\<^bsub>Fq\<^esub>"
  have units: "Units Fq = carrier Fq - {\<zero>\<^bsub>Fq\<^esub>}"
    by (rule Fq3329.field_Units)
  have xu: "x \<in> Units Fq" using units cx nz by auto
  have finU: "finite (Units Fq)" by (rule Fq3329.finite_Units)
  have pow1: "x [^]\<^bsub>Fq\<^esub> card (Units Fq) = \<one>\<^bsub>Fq\<^esub>"
    using finU xu by (rule Fq3329.units_power_order_eq_one)
  have cardU: "card (Units Fq) = 3328"
    using Fq3329.res_prime_units_eq by (subst Fq3329.res_prime_units_eq) simp
  have ycl: "x [^]\<^bsub>Fq\<^esub> (3329 - (2::nat)) \<in> carrier Fq"
    using cx by (rule Fq3329.nat_pow_closed)
  have e: "Suc (3329 - (2::nat)) = card (Units Fq)" using cardU by simp
  have h1:
    "x [^]\<^bsub>Fq\<^esub> (3329 - (2::nat)) \<otimes>\<^bsub>Fq\<^esub> x = \<one>\<^bsub>Fq\<^esub>"
  proof -
    have "x [^]\<^bsub>Fq\<^esub> (3329 - (2::nat)) \<otimes>\<^bsub>Fq\<^esub> x
            = x [^]\<^bsub>Fq\<^esub> (Suc (3329 - (2::nat)))"
      by (rule Fq3329.nat_pow_Suc [symmetric])
    also have "... = \<one>\<^bsub>Fq\<^esub>" by (subst e) (rule pow1)
    finally show ?thesis .
  qed
  have h2:
    "x \<otimes>\<^bsub>Fq\<^esub> x [^]\<^bsub>Fq\<^esub> (3329 - (2::nat)) = \<one>\<^bsub>Fq\<^esub>"
  proof -
    have "x \<otimes>\<^bsub>Fq\<^esub> x [^]\<^bsub>Fq\<^esub> (3329 - (2::nat))
            = x [^]\<^bsub>Fq\<^esub> (Suc (3329 - (2::nat)))"
      using cx by (rule Fq3329.nat_pow_Suc2 [symmetric])
    also have "... = \<one>\<^bsub>Fq\<^esub>" by (subst e) (rule pow1)
    finally show ?thesis .
  qed
  show ?thesis using cx ycl h2 by (rule Fq3329.comm_inv_char)
qed

lemma T1_A7_inv_inv:
  "x \<in> carrier Fq \<Longrightarrow> x \<noteq> \<zero>\<^bsub>Fq\<^esub> \<Longrightarrow> inv\<^bsub>Fq\<^esub> (inv\<^bsub>Fq\<^esub> x) = x"
proof -
  assume cx: "x \<in> carrier Fq" and nz: "x \<noteq> \<zero>\<^bsub>Fq\<^esub>"
  have units: "Units Fq = carrier Fq - {\<zero>\<^bsub>Fq\<^esub>}"
    by (rule Fq3329.field_Units)
  have xu: "x \<in> Units Fq" using units cx nz by auto
  show ?thesis using xu by (rule Fq3329.Units_inv_inv)
qed

subsection \<open>T1-A :: A8 -- representation invariant: results stay in [0, q)\<close>

lemma T1_A8_range:
  "x \<in> carrier Fq \<Longrightarrow> y \<in> carrier Fq \<Longrightarrow>
     x \<oplus>\<^bsub>Fq\<^esub> y \<in> carrier Fq \<and> x \<otimes>\<^bsub>Fq\<^esub> y \<in> carrier Fq"
  by (auto simp: residue_ring_def pos_mod_sign pos_mod_bound; arith)

subsection \<open>T1-A :: F2 -- signature length = 1 + 4*m\<close>

lemma T1_F2:
  "length (ser_sig k (replicate (2 * par_m k) 0)) = 1 + 4 * par_m k"
  by simp

subsection \<open>T1-A :: F3 -- u16 little-endian byte order\<close>

lemma T1_F3_u16le:
  "u16le x = [x mod 256, (x div 256) mod 256]"
  by (simp add: u16le_def)

section \<open>T1-D -- definition-dependent obligations (5 lemmas / 2 sorry)\<close>

text \<open>These five obligations are statements about the protocol definition
  layer (spec Sec 3.4, 5, 6.2, 8), not algebraic axioms, so they are kept out
  of T1-A: that lets T1-A honestly say 0 sorry while these 5 sorries stay
  visible here.  As of stage 2a the five objects (x1_of, t_of, adapted_of,
  deser_pk, deser_sig) are ANCHORED to the definitions of VWZ_Protocol instead
  of being uninterpreted constants; anchoring changes only the signature, it
  does NOT discharge the sorry -- the statements still need side conditions
  that the definition layer alone does not supply (spec Sec 6.2 guards its
  zero-test with x1[i] \<noteq> 0; Sec 8.3 keys its parser on the exact
  serialized length).  Supplying those conditions is the subject of stage 2b.\<close>

subsection \<open>T1-D :: B4 -- x1[i] \<noteq> 0  (guards every inv(x1[i]))\<close>

(* Stage 2b: statement unchanged.  It depends on the KeyGen range invariant
  (spec Sec 3.4: x1[i] <- randrange(1, q), hence 0 < x1[i] < q); KeyGen is
  still TODO(define), so the invariant is not yet supplied by the layer and
  this stays sorry. *)

lemma T1_B4:
  "\<forall>i<length (x1_of sk). 0 < x1_of sk ! i \<and> x1_of sk ! i < 3329"
  sorry

subsection \<open>T1-D :: C2 -- every nonzero target entry lies in [1, q-1]\<close>

lemma T1_C2:
  "\<forall>i<length (t_of pk msg).
     t_of pk msg ! i = 0 \<or> (1 \<le> t_of pk msg ! i \<and> t_of pk msg ! i \<le> 3328)"
  sorry

subsection \<open>T1-D :: C6 -- adapted[i] = 0 \<longleftrightarrow> t[i] = 0  (no zero divisors)\<close>

text \<open>Stage 2b: the unconditional form is FALSE for an unconstrained
  @{text x1} (spec Sec 6.2 only guards @{text "adapted[i] = t[i] * inv(x1[i])"}
  with @{text "x1[i] \<noteq> 0"}); the statement therefore carries that guard, plus
  the field-range invariants that the sampler supplies.  The guard is what the
  spec says, not a weakening invented to make the proof easier.\<close>

lemma T1_C6:
  "(\<forall>i<length (x1_of sk). x1_of sk ! i \<noteq> 0)
   \<Longrightarrow> (\<forall>i<length (x1_of sk). 1 \<le> x1_of sk ! i \<and> x1_of sk ! i < 3329)
   \<Longrightarrow> (\<forall>i<length (t_of pk msg). 0 \<le> t_of pk msg ! i \<and> t_of pk msg ! i < 3329)
   \<Longrightarrow> length (x1_of sk) = length (t_of pk msg)
   \<Longrightarrow> \<forall>i<length (adapted_of (t_of pk msg) (x1_of sk)).
         (adapted_of (t_of pk msg) (x1_of sk) ! i = 0) = (t_of pk msg ! i = 0)"
proof -
  assume nz: "\<forall>i<length (x1_of sk). x1_of sk ! i \<noteq> 0"
    and xr: "\<forall>i<length (x1_of sk). 1 \<le> x1_of sk ! i \<and> x1_of sk ! i < 3329"
    and tr: "\<forall>i<length (t_of pk msg). 0 \<le> t_of pk msg ! i \<and> t_of pk msg ! i < 3329"
    and lenx: "length (x1_of sk) = length (t_of pk msg)"
  let ?t = "t_of pk msg"
  let ?x1 = "x1_of sk"
  let ?m = "map2 (\<lambda>a b. a * invmod b mod 3329) ?t ?x1"
  have ad: "adapted_of ?t ?x1 = ?m" by (simp add: adapted_of_def)
  show ?thesis
  proof (rule allI, rule impI)
    fix i
    assume i: "i < length (adapted_of ?t ?x1)"
    have len: "length ?m = length ?t" using lenx by simp
    have lt: "i < length ?t" using i ad len by simp
    have lx: "i < length ?x1" using i ad len lenx by simp
    have h1: "0 \<le> ?t ! i" "?t ! i < 3329" using tr lt by simp_all
    have h2: "1 \<le> ?x1 ! i" "?x1 ! i < 3329" using xr lx by simp_all
    have core: "((?t ! i) * invmod (?x1 ! i) mod 3329 = 0) = (?t ! i = 0)"
      using h1 h2 by (rule aux_c6_core)
    have nth: "?m ! i = (?t ! i) * invmod (?x1 ! i) mod 3329"
      using lt lx by (simp add: nth_map nth_zip)
    show "(adapted_of ?t ?x1 ! i = 0) = (?t ! i = 0)"
      using ad nth core by simp
  qed
qed

subsection \<open>T1-D :: F1 -- serialization round-trips\<close>

text \<open>Stage 2b: the round-trip needs the Sec 8.3 preconditions -- the single
  byte @{text k} must fit in a byte, the payload length must be exactly the
  Sec 8.2 shape, and every element must be a genuine 16-bit word.  Without
  them the statement is false (e.g. @{text "k = 300"} or an element
  @{text "\<ge> 65536"} does not survive the encoding).\<close>

lemma T1_F1_pk:
  "k < 256 \<Longrightarrow> length psi = par_n k * par_m k * par_m k
     \<Longrightarrow> (\<forall>x\<in>set psi. x < 65536)
     \<Longrightarrow> deser_pk (ser_pk k psi) = Some psi"
proof -
  assume k: "k < 256"
    and len: "length psi = par_n k * par_m k * par_m k"
    and rng: "\<forall>x\<in>set psi. x < 65536"
  have eq: "ser_pk k psi = k # concat (map u16le psi)"
    using k by (simp add: ser_pk_def le1_def)
  have len2: "length (concat (map u16le psi)) = 2 * par_n k * par_m k * par_m k"
    using len by simp
  have dec: "decode2 (concat (map u16le psi)) = Some psi"
    by (rule aux_u16le_roundtrip [OF rng])
  show ?thesis using eq len2 dec by (simp add: deser_pk_def)
qed

lemma T1_F1_sig:
  "k < 256 \<Longrightarrow> length w = 2 * par_m k
     \<Longrightarrow> (\<forall>x\<in>set w. x < 65536)
     \<Longrightarrow> deser_sig (ser_sig k w) = Some w"
proof -
  assume k: "k < 256"
    and len: "length w = 2 * par_m k"
    and rng: "\<forall>x\<in>set w. x < 65536"
  have eq: "ser_sig k w = k # concat (map u16le w)"
    using k by (simp add: ser_sig_def le1_def)
  have len2: "length (concat (map u16le w)) = 4 * par_m k"
    using len by simp
  have dec: "decode2 (concat (map u16le w)) = Some w"
    by (rule aux_u16le_roundtrip [OF rng])
  show ?thesis using eq len2 dec by (simp add: deser_sig_def)
qed

section \<open>T2 -- linear algebra / matrices (anchored on VWZ_Matrix)\<close>

text \<open>Vocabulary is imported from \<open>VWZ_Matrix\<close> -- one source of truth:
  the structural helpers (`n_rows`, `n_cols`, `entry`, `row_vec`, `col_vec`,
  `dot`, `zero_mat`, `det2`, `mat_slice2`, `mat_rank1`, `mat_rank2`,
  `mat_solve2`, `mat_nullspace`, `mat_inner`), the real definitions
  (`id_mat`, `mat_mult`, `row_add_matrix`, `invertible`), the rank and nullity
  definitions from `VWZ_RREF` (`rref`, `mat_rank`, `dim_nullspace`), and the
  constants still awaiting bodies (`mat_inv`, `mat_solve`).  The protocol
  objects (`psi_slice`, `M2`, `M3`, `X2a` ...) are declared over the types of
  that layer, so a later body can mention them without re-typing anything.\<close>

subsection \<open>T2 :: B2 -- row-addition matrices have determinant 1\<close>

text \<open>@{text det} now has a body: Laplace expansion along the first row
  (see @{file VWZ_Matrix.thy}).  The obligation is therefore well-formed and no
  longer blocked on a missing definition -- what remains is the proof that
  adding a multiple of one row to another leaves the determinant unchanged,
  which is the multilinearity/alternation property of the Laplace recursion.
  It is kept sorry here so that the tier count stays honest: the statement is
  now meaningful, but not yet proved.

  The 2x2 and 3x3 instances below are proved outright, by computation over the
  definitions.  They are not the obligation; they are evidence that the
  definition layer computes the expected numbers.\<close>

lemma T2_B2: "i \<noteq> j \<Longrightarrow> det (row_add_matrix m i j f) = 1"
proof (induct m arbitrary: i j f)
  case 0
  show ?case by (simp add: row_add_matrix_def id_mat_def)
next
  case (Suc n)
  show ?case
  proof (cases "n < i")
    case True
    hence "Suc n \<le> i" by simp
    hence eq: "row_add_matrix (Suc n) i j f = id_mat (Suc n)"
      by (rule aux_t2_nofire_i)
    have "det (id_mat (Suc n)) = (1::int)" by (rule aux_det_id_mat)
    thus ?thesis using eq by simp
  next
    case False
    hence im: "i < Suc n" by simp
    show ?thesis
    proof (cases "n < j")
      case True
      hence "Suc n \<le> j" by simp
      hence eq: "row_add_matrix (Suc n) i j f = id_mat (Suc n)"
        by (rule aux_t2_nofire_j)
      have "det (id_mat (Suc n)) = (1::int)" by (rule aux_det_id_mat)
      thus ?thesis using eq by simp
    next
      case False
      hence jm: "j < Suc n" by simp
      show ?thesis
      proof (cases "i = 0")
        case True
        hence j0: "0 < j" using \<open>i \<noteq> j\<close> by simp
        have "det (row_add_matrix (Suc n) 0 j f) = (1::int)"
          by (rule aux_el_det_elementary_i0) (simp, rule j0, rule jm)
        thus ?thesis using True by simp
      next
        case False
        hence i0: "0 < i" by simp
        have red: "det (row_add_matrix (Suc n) i j f)
                 = det (map (del_col 0) (tl (row_add_matrix (Suc n) i j f)))"
          by (rule aux_t2_head_reduce) (simp, rule i0)
        show ?thesis
        proof (cases "j = 0")
          case True
          have "map (del_col 0) (tl (row_add_matrix (Suc n) i 0 f)) = id_mat (Suc n - 1)"
            by (rule aux_t2_minor0_j0) (simp, rule i0, rule im)
          hence "det (map (del_col 0) (tl (row_add_matrix (Suc n) i 0 f))) = (1::int)"
            using aux_det_id_mat by simp
          thus ?thesis using red True by simp
        next
          case False
          hence j0: "0 < j" by simp
          have minor: "map (del_col 0) (tl (row_add_matrix (Suc n) i j f))
                     = row_add_matrix (Suc n - 1) (i - 1) (j - 1) f"
            by (rule aux_t2_minor0_jpos) (simp, rule i0, rule j0, rule im, rule jm)
          have nE: "Suc n - 1 = n" by simp
          have ij: "i - 1 \<noteq> j - 1"
          proof
            assume "i - 1 = j - 1"
            hence "i = j" using i0 j0 by simp
            thus False using \<open>i \<noteq> j\<close> by simp
          qed
          have ih: "det (row_add_matrix n (i - 1) (j - 1) f) = (1::int)"
            by (rule Suc.hyps) (rule ij)
          show ?thesis using red minor nE ih by simp
        qed
      qed
    qed
  qed
qed

lemma T2_B2_det2_id: "det2 (id_mat 2) = 1"
  by (simp add: det2_def id_mat_def entry_def)

lemma T2_B2_det2_rowadd:
  "i \<noteq> j \<Longrightarrow> det2 (row_add_matrix 2 i j f) = 1"
  by (simp add: det2_def row_add_matrix_def entry_def split: if_splits)

subsection \<open>T2 :: B3 -- X2a, X2b, X3a, X3b are invertible\<close>

text \<open>The subject is @{text mats_of}: four calls to
  @{text random_invertible_matrix}, which starts from the identity and applies
  only row additions.

  The statement has to be read modulo @{text q}, and that is a correction, not a
  convenience.  A machine-checked probe (see @{file VWZ_Probe.thy}) shows the
  integer reading is false: @{text add_row_mult} reduces every entry modulo
  @{text q} through @{text fq}, while @{text mat_mult} is an unreduced integer
  dot product, so

    @{text "mat_mult (row_add_matrix 2 0 1 1) [[1,3328],[0,1]] = [[1,3329],[0,1]]"}
    @{text "add_row_mult [[1,3328],[0,1]] 0 1 1 = [[1,0],[0,1]]"}

  differ.  The consequence is not cosmetic: two row additions with
  @{text "f = 1000"} give @{text "[[1,1000],[1000,1301]]"}, whose integer
  determinant is @{text "-998699"} although its determinant modulo @{text q} is
  @{text 1}.  Those matrices are not invertible over the integers at all.

  The obligation is therefore restated over @{text F_q}: @{text mat_mult_mod} is
  the dot product followed by @{text fq}, and @{text invertible_mod} asks for a
  witness whose two products are congruent to the identity under
  @{text cong_q_mat}.  Congruence rather than equality is required because
  @{text "B * I"} is @{text "map (map fq) B"}, which equals @{text B} only for
  reduced matrices, and a witness is arbitrary.

  The proof closes: @{text inv_step} shows that one row addition preserves
  @{text invertible_mod} (elementary inverse, associativity of
  @{text mat_mult_mod}, ring congruence), @{text rim_iter_inv} inducts over the
  fuel, and the four matrices are the four calls from the identity.  The
  machinery lives in @{file VWZ_ModAlgebra.thy}.\<close>

lemma T2_B3:
  "invertible_mod (X2a_of m s) \<and> invertible_mod (X2b_of m s) \<and>
   invertible_mod (X3a_of m s) \<and> invertible_mod (X3b_of m s)"
proof (cases "m = 0")
  case True
  have h0: "X2a_of 0 s = []"
    by (simp add: X2a_of_def mats_of_def random_invertible_matrix_def id_mat_def
        split: prod.split)
  have h1: "X2b_of 0 s = []"
    by (simp add: X2b_of_def mats_of_def random_invertible_matrix_def id_mat_def
        split: prod.split)
  have h2: "X3a_of 0 s = []"
    by (simp add: X3a_of_def mats_of_def random_invertible_matrix_def id_mat_def
        split: prod.split)
  have h3: "X3b_of 0 s = []"
    by (simp add: X3b_of_def mats_of_def random_invertible_matrix_def id_mat_def
        split: prod.split)
  have z1: "X2a_of m s = []" using True h0 by simp
  have z2: "X2b_of m s = []" using True h1 by simp
  have z3: "X3a_of m s = []" using True h2 by simp
  have z4: "X3b_of m s = []" using True h3 by simp
  show ?thesis using z1 z2 z3 z4 by simp
next
  case False
  have m0: "0 < m" using False by simp
  have sI: "sq m (id_mat m)" using m0 by (rule sq_id)
  have rI: "reduced (id_mat m)" by (rule reduced_id_mat)
  have iI: "invertible_mod (id_mat m)" using m0 by (rule inv_id)
  let ?s1 = "snd (rim_iter (m * m) m (id_mat m) s)"
  let ?s2 = "snd (rim_iter (m * m) m (id_mat m) ?s1)"
  let ?s3 = "snd (rim_iter (m * m) m (id_mat m) ?s2)"
  have e1: "invertible_mod (fst (rim_iter (m * m) m (id_mat m) s))"
    using sI rI iI by (rule rim_iter_inv)
  have e2: "invertible_mod (fst (rim_iter (m * m) m (id_mat m) ?s1))"
    using sI rI iI by (rule rim_iter_inv)
  have e3: "invertible_mod (fst (rim_iter (m * m) m (id_mat m) ?s2))"
    using sI rI iI by (rule rim_iter_inv)
  have e4: "invertible_mod (fst (rim_iter (m * m) m (id_mat m) ?s3))"
    using sI rI iI by (rule rim_iter_inv)
  have x1: "X2a_of m s = fst (rim_iter (m * m) m (id_mat m) s)"
    by (simp add: X2a_of_def mats_of_def random_invertible_matrix_def split: prod.split)
  have x2: "X2b_of m s = fst (rim_iter (m * m) m (id_mat m) ?s1)"
    by (simp add: X2b_of_def mats_of_def random_invertible_matrix_def split: prod.split)
  have x3: "X3a_of m s = fst (rim_iter (m * m) m (id_mat m) ?s2)"
    by (simp add: X3a_of_def mats_of_def random_invertible_matrix_def split: prod.split)
  have x4: "X3b_of m s = fst (rim_iter (m * m) m (id_mat m) ?s3)"
    by (simp add: X3b_of_def mats_of_def random_invertible_matrix_def split: prod.split)
  show ?thesis
  proof (intro conjI)
    show "invertible_mod (X2a_of m s)" using x1 e1 by (metis)
    show "invertible_mod (X2b_of m s)" using x2 e2 by (metis)
    show "invertible_mod (X3a_of m s)" using x3 e3 by (metis)
    show "invertible_mod (X3b_of m s)" using x4 e4 by (metis)
  qed
qed

subsection \<open>T2 :: B5 -- M2, M3 are well-defined\<close>

text \<open>This closes by unfolding, and the closure is worth stating plainly: once
  @{text M2} and @{text M3} are spelled as the spec spells them, the obligation
  is a tautology.  It was an obligation only while they were placeholders.  The
  honest reading is that this is transcription, not proof -- the substantive
  claim (that those products are the ones the protocol needs) lives in the
  derivation of Sec 6.4, not here.\<close>

lemma T2_B5:
  "invertible (X2a_of m s) \<Longrightarrow> invertible (X3a_of m s) \<Longrightarrow>
     mat_mult (X2b_of m s) (mat_inv (X2a_of m s)) = M2 m s \<and>
     mat_mult (X3b_of m s) (mat_inv (X3a_of m s)) = M3 m s"
  by (simp add: M2_def M3_def)

subsection \<open>T2 :: B7 -- each rank-2 slice is the transpose of its predecessor's\<close>

text \<open>Both sides have bodies now: @{text mat_rank} (fuel-counted Gauss-Jordan,
  see @{file VWZ_RREF.thy}) and @{text psi_slice} (projection of @{text pk_psi}).
  The obligation is therefore a statement about actual matrices, and as written it
  is FALSE: the premise @{text "i < length (pk_psi pk)"} does not exclude a zero
  slice, and @{text T2_B7_counterexample} in @{file VWZ_Refutations.thy} proves
  that a key of the right shape whose slice is zero has rank 0, not 2.

  The statement below is the repaired one.  Its three premises are exactly the
  three things the original was missing:
  \<^item> @{text pk} really is a key @{text KeyGen} can emit, so the slice has the
    sum-of-two-outer-products shape instead of being an arbitrary matrix;
  \<^item> the slice is non-degenerate, stated as the existence of a non-zero
    @{text "2 x 2"} minor -- which is what "the two drawn vectors are not
    parallel" amounts to for a sum of two outer products;
  \<^item> the index is in range.

  TODO(proof): the gap is two missing rank lemmas, and naming them is the
  point -- neither is a defect in the statement below.
  \<^item> @{text "rank_outer_sum_le_two"}: for vectors @{text u}, @{text v},
    @{text "u'"} and @{text "v'"} of matching lengths, the rank of a sum of the
    two outer products @{text "outer u v + outer u' v'"} is at most 2.  This is
    what turns the KeyGen shape into the upper bound: every row of the sum is a
    linear combination of @{text v} and @{text "v'"}.
  \<^item> @{text "rank_ge_two_of_nonzero_minor"}: a non-zero @{text "2 x 2"}
    minor forces rank at least 2.  Contrapositive form: if the rank is at most 1
    then every @{text "2 x 2"} minor vanishes.  With @{text mat_rank} defined as
    the number of non-zero rows of the reduced form, that is a rank-nullity
    argument, not a rewrite.
  The contrapositive is now available for the reduced form itself:
  @{text rank_le_one_imp_minors_vanish} in @{file VWZ_Rank.thy} proves that a
  reduced form with at most one non-zero row has every @{text "2 x 2"} minor
  congruent to zero, and @{text is_rect_rref} supplies the rectangularity that
  this fact previously had to assume as a hypothesis.  What is still missing is
  the transport back to @{text A}: invariance of minors under the three row
  operations, and the statement for arbitrary index pairs rather than the reduced
  form.  So this stays @{text sorry}.  The tag is TODO(defect / restatement) and
  not TODO(proof): the sentence was false as written (see @{text T2_B7_refuted}),
  and the version below is the repaired one, whose remaining gap is the minor
  invariance layer plus the rank bound @{text rank_outer_sum_le_two}.\<close>

lemma T2_B7:
  "i < length (pk_psi pk) \<Longrightarrow>
   (\<exists>kk sd. pk = fst (KeyGen kk sd)) \<Longrightarrow>
   (\<exists>a b c d. a < n_rows (psi_slice pk i) \<and> b < n_rows (psi_slice pk i) \<and>
              c < n_cols (psi_slice pk i) \<and> d < n_cols (psi_slice pk i) \<and>
              a \<noteq> b \<and> c \<noteq> d \<and>
              entry (psi_slice pk i) a c * entry (psi_slice pk i) b d -
              entry (psi_slice pk i) a d * entry (psi_slice pk i) b c \<noteq> 0) \<Longrightarrow>
   mat_rank (psi_slice pk i) = 2"
  sorry

text \<open>Machine-checked refutation of the statement as it stands lives in
  @{file VWZ_Refutations.thy}: the key is the right shape, the index is in
  range, and the rank is 0.  It is kept out of this file so that a refutation is
  not counted as an obligation.\<close>

text \<open>The obligation, rewritten so that the rank side is unfolded, is the generic
  fact @{text mat_rank_unfold} in @{file VWZ_RREF.thy}.  It is deliberately
  not restated here: a definitional unfolding is not an obligation, and
  counting it as one would inflate the ledger.\<close>

subsection \<open>T2 :: D4 -- dim(nullspace(rows3)) \<ge> k - 1  for k \<ge> 2\<close>

text \<open>Now well-posed.  @{file VWZ_Rows3.thy} defines @{text rows3_of} exactly as
  Sec 6.4.1 lists it -- one Vandermonde row in the secret @{text lambda_c} per
  index of @{text Za}, and one @{text "M3<^sup>T"} row per index of @{text Zb} -- so
  the lemma takes the four arguments the body actually needs instead of asking a
  one-argument constant to sum up the whole key.

  The count is stated against @{text nullity} (columns minus rank), not against
  @{text dim_nullspace} (rows minus rank).  That is a correction, not a
  convenience.  For a @{text "k + 2"} by @{text "2 * k + 1"} system the row
  reading gives @{text "k + 2 - rank"}, which cannot bound @{text "k - 1"} from
  below at all: it would need @{text "rank \<le> 3"} for every such system, which
  is false.  What the sampler needs is @{text "2 * k + 1 - rank \<ge> k - 1"}, and
  that follows from the rank never exceeding the number of rows.  The proof is
  @{text rows3_dimension_count} in @{file VWZ_Rows3.thy}; the two side conditions
  are the spec's own (@{text "\<bar>Za\<bar> + \<bar>Zb\<bar> = \<bar>Z\<bar> + 1 = k + 2"} and a
  square mixing matrix of order @{text "2 * k + 1"}).\<close>

lemma T2_D4:
  "2 \<le> k \<Longrightarrow> card Za + card Zb = k + 2 \<Longrightarrow>
   n_rows Mm = 2 * k + 1 \<Longrightarrow> n_cols Mm = 2 * k + 1 \<Longrightarrow>
   k - 1 \<le> nullity (rows3_of lc Mm Za Zb)"
  by (rule rows3_dimension_count)

subsection \<open>T2 :: D5 -- the u2 rows reproduce adapted on S\<close>

text \<open>Restated against the two-argument @{text Sset}, with @{text t} the target
  (coerced to @{typ int}, since @{text adapted_of} works over @{typ int}) and
  @{text x1} the secret vector of @{text sk}.

  The wording below is not yet well-posed, and that is a finding rather than a
  gap in the proof.  @{text Eval} is typed so that it never receives @{text k}
  or @{text msg}, while @{text pk}, @{text w2} and @{text w3} stay free: the
  statement therefore forces the target bit at a support index to be the same
  for every message.  @{text T2_D5_forces_target_independence} in
  @{file VWZ_Refutations.thy} proves exactly that consequence, so the lemma
  cannot be true as written for any target that depends on the message.

  TODO(define): three things are missing and none can be invented now -- a body
  for @{text Sign}, the linkage saying @{text pk} is the signer's key and the
  two witnesses are the ones @{text Sign} produced for this message, and an
  @{text Eval} that consumes the digest.  Until then this stays @{text sorry},
  tagged as a defect in the statement rather than as proof debt.\<close>

lemma T2_D5:
  "i \<in> Sset (map int (hash_target k msg)) (x1_of sk) \<Longrightarrow>
     Eval pk w2 w3 ! i = hash_target k msg ! i"
  sorry

subsection \<open>T2 :: D6 -- annihilation of the two P2 factors on Z\<close>

text \<open>Restated on the <em>u2</em> system, which is not the system above.
  @{text rows3_of} is what pushes @{text u3} into the nullspace, and it was a
  modelling error to feed it to @{text solve_linear} here: the @{text u2} system
  has one homogeneous row per zero position that lies only in @{text Za} or only
  in @{text Zb}, which is @{file VWZ_Rows3.thy}'s @{text rows_u2_of}.

  The side condition is the second correction.  The earlier wording quantified
  over all of @{text Z} with no case split, but Sec 3 constrains only the two
  exclusive halves: at the single overlapping index both @{text P3} factors
  vanish instead, and neither @{text P2} factor is forced, so the old statement
  was not satisfiable.

  Conclusion and hypothesis are both modulo 3329 (@{text fq}), not over the
  integers: @{text solve_linear} is specified in @{file VWZ_Solver.thy} over the
  reduced field, exactly as the sampler's arithmetic is.

  The rows are built with @{text "X2b<^sup>T>"} and @{text "X2a<^sup>T>"}, which is
the form @{file VWZ_KeyGen.thy}'s @{text psi_of} evaluates and therefore the
form the sampler actually implements; @{text M2} would be the same numbers via
@{text "u2 = X2a . w2"} but not the same rows.

  The proof is the bilinear identity of @{file VWZ_Transpose.thy},
  @{text "dot (matvec (transpose A) u) v = dot u (matvec A v)"}, applied to the
  row that the membership gives, plus the homogeneous corollary of
  @{text solve_linear}.  Nothing about the hash, the trapdoor or the security
  argument is assumed.\<close>

lemma T2_D6:
  "finite Za \<Longrightarrow> finite Zb \<Longrightarrow>
   is_rect (X2a_of m s) \<Longrightarrow> is_rect (X2b_of m s) \<Longrightarrow>
   length v = n_cols (X2a_of m s) \<Longrightarrow> length v = n_cols (X2b_of m s) \<Longrightarrow>
   i \<in> Zset (map int (hash_target k msg)) (x1_of (sk :: skey)) \<Longrightarrow>
   (i \<in> Za - Zb \<or> i \<in> Zb - Za) \<Longrightarrow>
   solve_linear (rows_u2_of (X2a_of m s) (X2b_of m s) (sk_lam_a sk) (sk_lam_b sk) Za Zb)
                (replicate (n_rows (rows_u2_of (X2a_of m s) (X2b_of m s) (sk_lam_a sk) (sk_lam_b sk) Za Zb)) 0)
     = Some v \<Longrightarrow>
   fq (P2b (sk_lam_b sk) (X2b_of m s) v i) = 0 \<or>
   fq (P2a (sk_lam_a sk) (X2a_of m s) v i) = 0"
proof -
  assume fina: "finite Za" and finb: "finite Zb"
     and rectA: "is_rect (X2a_of m s)" and rectB: "is_rect (X2b_of m s)"
     and lenvA: "length v = n_cols (X2a_of m s)"
     and lenvB: "length v = n_cols (X2b_of m s)"
     and zi: "i \<in> Zset (map int (hash_target k msg)) (x1_of (sk :: skey))"
     and side: "i \<in> Za - Zb \<or> i \<in> Zb - Za"
     and sol: "solve_linear (rows_u2_of (X2a_of m s) (X2b_of m s) (sk_lam_a sk) (sk_lam_b sk) Za Zb)
                (replicate (n_rows (rows_u2_of (X2a_of m s) (X2b_of m s) (sk_lam_a sk) (sk_lam_b sk) Za Zb)) 0)
                  = Some v"
  have ball: "\<forall>r \<in> set (rows_u2_of (X2a_of m s) (X2b_of m s) (sk_lam_a sk) (sk_lam_b sk) Za Zb).
              fq (dot r v) = 0"
    using sol by (rule solve_linear_zero_rows)
  show "fq (P2b (sk_lam_b sk) (X2b_of m s) v i) = 0 \<or>
        fq (P2a (sk_lam_a sk) (X2a_of m s) v i) = 0"
  proof (cases "i \<in> Za - Zb")
    case True
    have mset: "i \<in> set (sorted_list_of_set (Za - Zb))"
      using True fina by (simp add: set_sorted_list_of_set)
    define u where uu: "u = vand (sk_lam_b sk ! i) (n_rows (X2b_of m s))"
    have rowmem: "matvec (transpose (X2b_of m s)) u
        \<in> set (rows_u2_of (X2a_of m s) (X2b_of m s) (sk_lam_a sk) (sk_lam_b sk) Za Zb)"
      unfolding rows_u2_of_def using mset uu by simp
    have h0: "fq (dot (matvec (transpose (X2b_of m s)) u) v) = 0"
      using rowmem ball by blast
    have idt: "dot (matvec (transpose (X2b_of m s)) u) v
        = dot u (matvec (X2b_of m s) v)"
      by (rule dot_matvec_transpose[OF rectB]) (simp_all add: uu vand_def lenvB)
    have "fq (P2b (sk_lam_b sk) (X2b_of m s) v i) = 0"
      using h0 idt unfolding P2b_def using uu by simp
    then show ?thesis by simp
  next
    case False
    with side have zb: "i \<in> Zb - Za" by blast
    have mset: "i \<in> set (sorted_list_of_set (Zb - Za))"
      using zb finb by (simp add: set_sorted_list_of_set)
    define w where ww: "w = vand (sk_lam_a sk ! i) (n_rows (X2a_of m s))"
    have rowmem: "matvec (transpose (X2a_of m s)) w
        \<in> set (rows_u2_of (X2a_of m s) (X2b_of m s) (sk_lam_a sk) (sk_lam_b sk) Za Zb)"
      unfolding rows_u2_of_def using mset ww by simp
    have h0: "fq (dot (matvec (transpose (X2a_of m s)) w) v) = 0"
      using rowmem ball by blast
    have idt: "dot (matvec (transpose (X2a_of m s)) w) v
        = dot w (matvec (X2a_of m s) v)"
      by (rule dot_matvec_transpose[OF rectA]) (simp_all add: ww vand_def lenvA)
    have "fq (P2a (sk_lam_a sk) (X2a_of m s) v i) = 0"
      using h0 idt unfolding P2a_def using ww by simp
    then show ?thesis by simp
  qed
qed

subsection \<open>T2 :: D1 -- verifier correctness\<close>

lemma T2_D1_correctness:
  "\<exists>w2 w3. Sign sk msg = (w2, w3) \<and> Eval pk w2 w3 = hash_target k msg"
  sorry

section \<open>T3 -- security / probabilistic / parser (subjects TODO(define))\<close>

subsection \<open>T3 :: B1 -- distinct_lam returns n pairwise-distinct values in [1, q)\<close>

text \<open>Restated against the state-passing sampler.  The earlier wording asked a
  list-valued @{text distinct_lam} for @{text n} points unconditionally; no such
  function exists, because rejection sampling terminates with probability 1
  rather than by construction.  The guard below is the algorithm's own failure
  signal, and @{text distinct_lam_partial_correct} discharges this form.
  The unconditional claim would need a measure-theoretic termination proof and
  is not asserted anywhere in this session.\<close>

lemma T3_B1:
  "fst (distinct_lam n seed) \<noteq> [] \<Longrightarrow>
   length (fst (distinct_lam n seed)) = n \<and>
   distinct (fst (distinct_lam n seed)) \<and>
   set (fst (distinct_lam n seed)) \<subseteq> {1..<3329}"
  unfolding distinct_lam_def
  by (rule distinct_lam_fuel_correct)

subsection \<open>T3 :: C1 -- weight(target) = k + 1\<close>

text \<open>@{text "hash_target"} has a body now (see @{file VWZ_Fq3329.thy}): the
  support is drawn from the pool of all positions by a partial Fisher-Yates
  walk, one removal per step, and the target is the indicator of that support.
  What the body buys is that the sparsity is a consequence of the selection
  rather than an assumption, and that the only uninterpreted object left is
  @{text digest} -- the XOF.  Nothing here claims it is a hash.

  Both bookkeeping facts are proved in @{file VWZ_Target.thy} and the lemma
  below is a one-line consequence.  The walk keeps the pool's length, set and
  distinctness (each a rewrite, since it only ever swaps a pair of positions),
  so its first @{text "k + 1"} entries exist and are distinct positions inside
  @{text "[0, par_n k)"}; the indicator of such a support is then a weight
  count, proved by induction on the range with @{text remove1} on the positive
  branch.  The first version of this was blocked on list bookkeeping and
  reverted rather than left half-proved; the second version moved the
  invariants into a separate theory and they went through.

  One premise is genuine and is kept.  The walk consumes one digest word per
  step, so @{text "k + 1"} words must be available.  Without that hypothesis
  the claim is false -- a short digest yields a shorter support -- and no
  definition can repair it, because the words come from the XOF.\<close>

lemma T3_C1:
  "length (digest k msg) \<ge> k + 1 \<Longrightarrow> weight (hash_target k msg) = k + 1"
  by (rule hash_target_weight)

subsection \<open>T3 :: C3 -- the raw reduction is biased for q = 3329\<close>

text \<open>Restated.  The v0 wording, @{text "unbiased N"} with @{text N} free and
  @{text unbiased} an uninterpreted constant, was a statement about nothing: it
  could be neither proved nor refuted, and making it true would have required
  inventing a predicate to fit.  The content of Sec 5.1 is a negative result
  about the modulus the protocol actually uses: @{text 3329} does not divide
  @{text "2 ^ 32"}, so reducing a 32-bit word modulo @{text q} is biased.  That
  is exactly the reason the sampler rejects and redraws.

  Machine-checked arithmetic: @{text "2 ^ 32 = 3329 * 1290167 + 1353"}, so the
  first @{text 1353} residues have @{text 1290168} preimages and the remaining
  ones have @{text 1290167}.  The discrepancy is small but real, and it is a
  property of the modulus rather than of an implementation.\<close>

lemma T3_C3: "\<not> unbiased 3329"
proof -
  have rest: "(2 :: nat) ^ 32 = 3329 * 1290167 + 1353" by simp
  have mod: "(2 :: nat) ^ 32 mod 3329 = 1353"
    using rest by simp
  show ?thesis
  proof
    assume "unbiased 3329"
    then have dvd: "3329 dvd (2 :: nat) ^ 32" by (simp add: unbiased_def)
    then have "(2 :: nat) ^ 32 mod 3329 = 0" by (rule dvd_imp_mod_0)
    with mod show False by simp
  qed
qed

subsection \<open>T3 :: D8 -- adaptor always succeeds (EMPIRICAL, not a theorem)\<close>

text \<open>v0 marks D8 as empirical: it may be false for adversarial targets.  It is
  retained as a typed stub only; it is NOT counted as a provable obligation and
  no bounded enumeration is offered here.\<close>

lemma T3_D8_empirical:
  "\<forall>msg. \<exists>w2 w3. Sign sk msg = (w2, w3)"
  sorry

subsection \<open>T3 :: E1 -- pk parser totality\<close>

text \<open>This one closes, and it is worth being blunt about how little that means: for
  ANY @{typ "nat list \<Rightarrow> nat list option"}, totality in this sense is
  definitional -- the statement asks only that a total HOL function returns
  either @{const None} or @{const Some}.  Since the last round @{text parse_pk}
  does have a body (the alias of @{text deser_pk}), but that changes nothing
  here: the content of Sec 8.3 is the length rule and the round trip, and the
  length rule is exercised by @{text T3_E2}, the round trip by T1-A.\<close>

lemma T3_E1_parse_pk_total:
  "\<forall>bs. parse_pk bs = None \<or> (\<exists>v. parse_pk bs = Some v)"
proof (intro allI)
  fix bs
  show "parse_pk bs = None \<or> (\<exists>v. parse_pk bs = Some v)"
    by (cases "parse_pk bs") simp_all
qed

subsection \<open>T3 :: E2 -- length mismatch is rejected\<close>

text \<open>This one has real content: it uses the body of @{text accepts_len}, not a
  case distinction on an option.  The argument is the length clause of the
  predicate.  If the verifier accepted @{text bs}, then
  @{text "length bs = 1 + 4 * par_m (hd bs)"} and @{text "hd bs = k"} (the key
  field has to agree with the head of the pk vector, and that head is @{text k}
  because the vector is a non-empty replicate).  Hence the accepted length is
  exactly @{text "1 + 4 * par_m k"}, which is the length the premise excludes.\<close>

lemma T3_E2:
  "\<forall>k bs. length bs \<noteq> 1 + 4 * par_m k \<longrightarrow>
     \<not> accepts_len (replicate (1 + 2 * (par_n k * (par_m k * par_m k))) k) bs"
proof (intro allI impI)
  fix k :: nat and bs :: "nat list"
  let ?N = "1 + 2 * (par_n k * (par_m k * par_m k))"
  assume hlen: "length bs \<noteq> 1 + 4 * par_m k"
  show "\<not> accepts_len (replicate ?N k) bs"
  proof
    assume acc: "accepts_len (replicate ?N k) bs"
    have Npos: "?N \<noteq> 0" by simp
    have hpk: "hd (replicate ?N k) = k"
      using Npos by (cases ?N) simp_all
    from acc have hhd: "hd (replicate ?N k) = hd bs"
      and hlen2: "length bs = 1 + 4 * par_m (hd bs)"
      by (auto simp: accepts_len_def)
    have hbs: "hd bs = k" using hhd hpk by simp
    have "length bs = 1 + 4 * par_m k" using hlen2 hbs by simp
    with hlen show False by simp
  qed
qed

subsection \<open>T3 :: E3b -- general rejection soundness (CONJECTURAL per spec Sec 10.1)\<close>

text \<open>v0 formalization-plan Sec 10.1 declares general rejection soundness not
  provable as stated.  The stub is kept for bookkeeping only and is explicitly
  NOT claimed.\<close>

lemma T3_E3b_conjectural:
  "\<forall>msg sig. Verify pk msg sig \<longrightarrow>
     (\<exists>w2 w3. Eval pk w2 w3 = hash_target k msg)"
  sorry

subsection \<open>T3 :: E4 -- signature parser totality\<close>

text \<open>Same shape as E1, same caveat: totality of a function into
  @{typ "nat list option"} is a case distinction, not a property of a parser.
  It closes; nothing about the signature format is thereby known.\<close>

lemma T3_E4_parse_sig_total:
  "\<forall>bs. parse_sig bs = None \<or> (\<exists>v. parse_sig bs = Some v)"
proof (intro allI)
  fix bs
  show "parse_sig bs = None \<or> (\<exists>v. parse_sig bs = Some v)"
    by (cases "parse_sig bs") simp_all
qed

end
