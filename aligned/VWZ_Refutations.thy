(*  Title:      VWZ_Refutations.thy
    SPDX-License-Identifier: Apache-2.0

    Machine-checked refutations of statements that are in the ledger but are
    not provable as written.

    Why a separate file: the obligation counter counts every `lemma` in
    VWZ_ObligationsAligned.thy.  A refutation is evidence that a statement is
    wrong, not an obligation to prove something, so it must not be counted as
    one -- otherwise closing a defect raises the "lemmas" number and the ledger
    starts measuring the wrong thing.

    Each entry here should name the ledger lemma it refutes and say which
    hypothesis is missing.
*)
theory VWZ_Refutations
  imports VWZ_ObligationsAligned
begin

section \<open>Refutation of T2_B7 as stated\<close>

text \<open>T2_B7 claims @{text "mat_rank (psi_slice pk i) = 2"} for every key and
  index, and the repaired version adds @{text "i < length (pk_psi pk)"}.  That
  premise is necessary but not sufficient: the key below has the right shape
  and the index is in range, and the slice is zero, so the rank is 0.

  What the statement is missing is a hypothesis on @{text pk} itself -- that it
  is in the image of @{text KeyGen}.  Until @{text KeyGen} has a body there is
  no such hypothesis to write, which is why T2_B7 is recorded as a defect in
  the statement rather than as proof debt.\<close>

lemma T2_B7_counterexample:
  "0 < length (pk_psi \<lparr>pk_k = 1, pk_psi = [[[0,0],[0,0]]]\<rparr>)
   \<and> mat_rank (psi_slice \<lparr>pk_k = 1, pk_psi = [[[0,0],[0,0]]]\<rparr> 0) = 0"
  by eval

text \<open>The same fact, stated as the negation of the repaired obligation, so the
  contradiction is explicit rather than inferred by the reader.\<close>

lemma T2_B7_refuted:
  "\<not> (\<forall>(pk::pkey) i. i < length (pk_psi pk) \<longrightarrow>
        mat_rank (psi_slice pk i) = 2)"
proof
  assume h: "\<forall>(pk::pkey) i. i < length (pk_psi pk) \<longrightarrow>
                mat_rank (psi_slice pk i) = 2"
  have a: "mat_rank (psi_slice \<lparr>pk_k = 1, pk_psi = [[[0,0],[0,0]]]\<rparr> 0) = 2"
    using h by simp
  have b: "mat_rank (psi_slice \<lparr>pk_k = 1, pk_psi = [[[0,0],[0,0]]]\<rparr> 0) = 0"
    using T2_B7_counterexample by simp
  from a b show False by simp
qed

end
