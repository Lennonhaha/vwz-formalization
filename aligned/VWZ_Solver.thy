(*  Title:      VWZ_Solver.thy
    SPDX-License-Identifier: Apache-2.0

    Spec 6.4.3 -- the linear solve, specified rather than implemented.

    Two things are fixed here, both of them corrections of earlier wording.

    (1) Domain.  `solve_linear` used to be declared over `nat` in
    VWZ_Fq3329.thy, while every matrix in this session is an `int list list`
    holding residues in [0, 3329).  Every call site had to spell out
    `map (map nat)` / `map nat` / `map int` just to cross the boundary, which
    hid the fact that the two sides were talking about the same objects.  It is
    now `mat => int list => int list option`, and the coercions are gone.

    (2) Semantics.  "Solves A x = b" here means `fq (dot r x) = b!i` for every
    row r, i.e. the system is solved modulo 3329 -- NOT `dot r x = b!i` in the
    integers.  This is not a weakening for convenience: the reduction in
    VWZ_RREF scales rows by `invmod p` and every row operation wraps through
    `fq`, so the object it produces is a reduced matrix over F_3329 whose
    entries happen to be integers.  Asserting integer equality would repeat the
    mismatch that made T2_B3 false in the first place.

    What is NOT here: an algorithm.  `solve_linear` is a specification --
    it returns *some* solution when one exists, via Hilbert choice, and `None`
    otherwise.  It is therefore not executable, and the Gauss-Jordan back
    substitution that the spec describes (with its free-variable assignment) is
    still open work.  The point of this file is that the obligations which
    mention the solver can now be stated about a defined object with a proved
    semantics, instead of about an uninterpreted constant.
*)

theory VWZ_Solver
  imports VWZ_RREF
begin

section \<open>Spec 6.4.3 -- what it means to solve the system over F_3329\<close>

text \<open>@{text solves} is the whole semantics: the candidate has the width of the
  matrix, and every row equation holds after reduction.  Writing it as a
  predicate keeps the definition of @{text solve_linear} to one line and makes
  the two derived facts below immediate.\<close>

definition solves :: "mat \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> bool" where
  "solves A b v = (length v = n_cols A \<and> map (\<lambda>r. fq (dot r v)) A = b)"

definition solve_linear :: "mat \<Rightarrow> int list \<Rightarrow> int list option" where
  "solve_linear A b =
     (if (\<exists>v. solves A b v) then Some (SOME v. solves A b v) else None)"

text \<open>The soundness direction is the one the obligations use: whatever the
  solver hands back really does satisfy every row equation.  It is proved from
  the definition of @{text solves} alone, so it stays true if the body is later
  replaced by a real algorithm -- only the definition of @{text solves} has to
  survive that replacement.\<close>

lemma solve_linear_sound:
  "solve_linear A b = Some v \<Longrightarrow> solves A b v"
proof -
  assume h: "solve_linear A b = Some v"
  have ex: "\<exists>v. solves A b v"
    using h unfolding solve_linear_def by (auto split: if_split_asm)
  have some: "solves A b (SOME v. solves A b v)"
    using ex by (rule someI_ex)
  from h have "v = (SOME v. solves A b v)"
    unfolding solve_linear_def by (auto split: if_split_asm)
  with some show ?thesis by simp
qed

lemma solve_linear_complete:
  "(\<exists>v. solves A b v) \<Longrightarrow> \<exists>v. solve_linear A b = Some v"
  unfolding solve_linear_def by (auto split: if_split_asm)

lemma solve_linear_none:
  "solve_linear A b = None \<Longrightarrow> \<not> (\<exists>v. solves A b v)"
  unfolding solve_linear_def by (auto split: if_split_asm)

text \<open>The two projections that obligations actually consume.  They are stated
  separately so that a proof can rewrite one row without unfolding the map.\<close>

lemma solves_length: "solves A b v \<Longrightarrow> length v = n_cols A"
  by (simp add: solves_def)

lemma solves_entry:
  "solves A b v \<Longrightarrow> i < n_rows A \<Longrightarrow> fq (dot (A ! i) v) = b ! i"
proof -
  assume s: "solves A b v" and i: "i < n_rows A"
  have eq: "map (\<lambda>r. fq (dot r v)) A = b" using s by (simp add: solves_def)
  have len: "i < length A" using i by (simp add: n_rows_def)
  have h1: "fq (dot (A ! i) v) = (map (\<lambda>r. fq (dot r v)) A) ! i"
    using len by (simp add: nth_map)
  have h2: "(map (\<lambda>r. fq (dot r v)) A) ! i = b ! i" using eq by simp
  from h1 h2 show "fq (dot (A ! i) v) = b ! i" by simp
qed

lemma solves_zero_entry:
  "solves A b v \<Longrightarrow> i < n_rows A \<Longrightarrow> b ! i = 0 \<Longrightarrow> fq (dot (A ! i) v) = 0"
  using solves_entry by auto

lemma solve_linear_zero_rows:
  "solve_linear A (replicate (n_rows A) 0) = Some v \<Longrightarrow>
   \<forall>r \<in> set A. fq (dot r v) = 0"
proof -
  assume h: "solve_linear A (replicate (n_rows A) 0) = Some v"
  have s: "solves A (replicate (n_rows A) 0) v" by (rule solve_linear_sound[OF h])
  show "\<forall>r \<in> set A. fq (dot r v) = 0"
  proof
    fix r
    assume rA: "r \<in> set A"
    then obtain i where i: "i < length A" "r = A ! i" by (auto simp add: set_conv_nth)
    have irow: "i < n_rows A" using i(1) by (simp add: n_rows_def)
    have hrow: "fq (dot (A ! i) v) = (replicate (n_rows A) 0) ! i"
      using s irow by (rule solves_entry)
    have hz: "(replicate (n_rows A) 0) ! i = 0" using irow by (simp add: nth_replicate)
    from hrow hz i(2) show "fq (dot r v) = 0" by simp
  qed
qed

end
