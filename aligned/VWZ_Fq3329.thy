(*  Title:      VWZ_Fq3329.thy
    SPDX-License-Identifier: Apache-2.0

    VWZ A3 -- definition layer (aligned rewrite), part 1 of 2.

    Anchor: HOL-Number_Theory.Residues.
      q = 3329 is prime; the base field is the prime residue ring
      `residue_ring (int 3329)`, used inside the locale `residues_prime 3329`
      (which supplies a `field` instance for free).

    Road-tested facts (see plans/vwz-a3-isabelle/_diag):
      * `field (ZMod 3329)` does NOT go through directly -- the residue-ring
        route is the one that works.
      * the sublocale-exported lemmas (res_carrier_eq, res_add_eq, ...) do not
        rewrite our goals under `simp add:`; unfolding `residue_ring_def`
        directly does, so that is what we use below.
      * `Fq3329.is_field` does apply by `rule`.

    Convention: every protocol object whose body is not yet formalised is
    introduced with `consts` and tagged TODO(define).  Spec references are to
    fibemate-vwz-specification_20260906.md.
*)
theory VWZ_Fq3329
  imports "HOL-Number_Theory.Residues"
begin

section \<open>The prime residue ring for q = 3329\<close>

lemma prime_3329: "prime (3329::nat)" by eval

interpretation Fq3329: residues_prime 3329 "residue_ring (int 3329)"
  by unfold_locales (rule prime_3329)

abbreviation Fq :: "int ring" where "Fq \<equiv> residue_ring (int 3329)"

lemma Fq_carrier: "carrier Fq = {0..3328}"
  by (simp add: residue_ring_def)

lemma Fq_card: "card (carrier Fq) = 3329"
  by (simp add: residue_ring_def)

lemma Fq_is_field: "field Fq"
  by (rule Fq3329.is_field)

lemma Fq_add_eq: "x \<oplus>\<^bsub>Fq\<^esub> y = (x + y) mod 3329"
  by (simp add: residue_ring_def)

lemma Fq_mult_eq: "x \<otimes>\<^bsub>Fq\<^esub> y = (x * y) mod 3329"
  by (simp add: residue_ring_def)

lemma Fq_zero_eq: "\<zero>\<^bsub>Fq\<^esub> = 0"
  by (simp add: residue_ring_def)

lemma Fq_one_eq: "\<one>\<^bsub>Fq\<^esub> = 1"
  by (simp add: residue_ring_def)

section \<open>Instance parameters (spec Sec 1.2)\<close>

definition par_n :: "nat \<Rightarrow> nat" where "par_n k = 2 * k + 2"
definition par_m :: "nat \<Rightarrow> nat" where "par_m k = 2 * k + 1"
definition par_w :: "nat \<Rightarrow> nat" where "par_w k = k + 1"

lemma par_n_eq_par_m_plus_1: "par_n k = par_m k + 1"
  unfolding par_n_def par_m_def by arith

lemma par_w_eq_half_n: "2 * par_w k = par_n k"
  unfolding par_w_def par_n_def by arith

section \<open>Serialization primitives (spec Sec 8)\<close>

definition le1 :: "nat \<Rightarrow> nat list" where "le1 x = [x mod 256]"

definition u16le :: "nat \<Rightarrow> nat list" where
  "u16le x = [x mod 256, (x div 256) mod 256]"

lemma u16le_len [simp]: "length (u16le x) = 2"
  by (simp add: u16le_def)

lemma le1_len [simp]: "length (le1 x) = 1"
  by (simp add: le1_def)

lemma u16le_concat_len [simp]: "length (concat (map u16le xs)) = 2 * length xs"
  by (induction xs) (auto simp: u16le_def)

definition ser_pk :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "ser_pk k psi = le1 k @ concat (map u16le psi)"

definition ser_sig :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "ser_sig k w = le1 k @ concat (map u16le w)"

lemma ser_pk_len [simp]: "length (ser_pk k psi) = 1 + 2 * length psi"
  by (simp add: ser_pk_def)

lemma ser_sig_len [simp]: "length (ser_sig k w) = 1 + 2 * length w"
  by (simp add: ser_sig_def)

section \<open>Protocol objects (bodies deferred)\<close>

text \<open>Each object below is an <em>uninterpreted</em> constant: its mathematical
  content is not yet formalised.  They exist so that the T0 obligations have a
  well-typed subject; bodies follow the spec sections named in the TODO tags.\<close>

consts SeedRng :: "nat \<Rightarrow> nat list"
        \<comment> \<open>TODO(define): spec Sec 3.1 -- 64-bit LCG state stream\<close>

consts distinct_lam :: "nat list \<Rightarrow> nat \<Rightarrow> nat list"
        \<comment> \<open>TODO(define): spec Sec 3.2 -- pairwise-distinct evaluation points\<close>

consts KeyGen :: "nat \<Rightarrow> nat list \<Rightarrow> (nat list \<times> nat list)"
        \<comment> \<open>TODO(define): spec Sec 3 -- (k, seed) |-> (pk, sk)\<close>

consts hash_target :: "nat \<Rightarrow> nat list \<Rightarrow> nat list"
        \<comment> \<open>TODO(define): spec Sec 5 -- (k, msg) |-> sparse target t (via H)\<close>

consts Eval :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list"
        \<comment> \<open>TODO(define): spec Sec 4 -- (pk, w2, w3) |-> t\<close>

consts Sign :: "nat list \<Rightarrow> nat list \<Rightarrow> (nat list \<times> nat list)"
        \<comment> \<open>TODO(define): spec Sec 6 -- (sk, msg) |-> (w2, w3)\<close>

consts Verify :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
        \<comment> \<open>TODO(define): spec Sec 7 -- (pk, msg, sig) |-> bool\<close>

consts sample_below :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
        \<comment> \<open>TODO(define): spec Sec 5.1 -- rejection-sampling reader\<close>

consts nullspace :: "nat list list \<Rightarrow> nat list list"
        \<comment> \<open>TODO(define): spec Sec 6.4.1 -- RREF nullspace basis\<close>

consts solve_linear :: "nat list list \<Rightarrow> nat list \<Rightarrow> nat list option"
        \<comment> \<open>TODO(define): spec Sec 6.4.3 -- Gauss-Jordan linear solve\<close>

end
