(*  Title:      VWZ_KeyGen.thy
    SPDX-License-Identifier: Apache-2.0

    Key generation, part 1: the deterministic draws that Sec 3.2 and 3.3 are
    built on.

    Scope, stated up front because it is easy to over-read:

      * This file defines the sampling *algorithms* and proves what they return
        -- partial correctness, not termination.
      * Rejection sampling terminates with probability 1, not by construction,
        so no unconditional "returns n points" theorem is proved here.  The
        guarantee is conditional on a non-empty result, which is exactly what
        the algorithm provides.
      * The ledger's T3_B1 is left as it is.  Weakening an obligation so that it
        becomes provable is the one move this repository is supposed to resist;
        the conditional form is proved here instead, as a supporting result.
*)
theory VWZ_KeyGen
  imports VWZ_Fq3329
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

end
