# VWZ specification: defects found by machine

This document lists the places where the VWZ obligations, as written, are **not
true**, and gives for each one the machine-checked evidence.  It is meant to be
read by the author of the specification and to serve as an appendix to a paper:
the claim is not that the protocol is broken, but that the *statements* were.

Method, applied uniformly:

1. formalise the obligation exactly as written, with no silent strengthening;
2. if it cannot be proved, look for an instance that makes it false and check
   that instance in Isabelle/HOL;
3. only then restate, and record both the original wording and the reason.

The obligation ledger (`tools/count-obligations.cjs`) counts only the statements
in `aligned/VWZ_ObligationsAligned.thy`.  Refutations live in
`aligned/VWZ_Refutations.thy` and are **not** counted as obligations, so closing
a defect never improves the ledger — it can only shrink it by making a statement
provable.

Build: `isabelle build -D aligned` with Isabelle2025-2, session `VWZ_A3_Aligned`.
Current state: **56 lemmas, 6 `sorry`, 0 proof-position `sorry` outside the ledger in the `VWZ_A3_Aligned` session.** Scaffolding and control sessions (`skeleton/`, `neg/`, `smoke/`) are excluded by design and are not claimed as proved — `skeleton/VWZ_A3_Skeleton.thy` alone holds 37 one-line `lemma … sorry` placeholders. The counting rule is stated in `docs/case-study/PAPER.md` §3.1.

---

## 1. T2_B3 — arithmetic domain mismatch (`Z` vs `F_q`)

**Original claim.** The bridge between the key-generation row operation and
matrix algebra:

```
invertible (X2a_of m s) ∧ ...
```

with `invertible` the two-sided inverse over the integers.

**Why it is false.** `add_row_mult` reduces every entry modulo 3329, while
`mat_mult` computes an unreduced integer dot product.  Left-multiplying by the
elementary matrix and performing the row operation therefore differ by a
reduction, and the reduced matrices are not invertible over `Z` at all.

**Machine evidence** (`aligned/VWZ_Probe.thy`):

```
probe_mult:   mat_mult (row_add_matrix 2 0 1 1) [[1,3328],[0,1]] = [[1,3329],[0,1]]
probe_rowop:  add_row_mult [[1,3328],[0,1]] 0 1 1              = [[1,0],[0,1]]
```

Already after two row additions the integer determinant of the result is
`-998699`, which is `1` modulo `q` but not a unit in `Z`.  A matrix with that
determinant has no integer inverse, so the obligation cannot be true in the
stated domain.

**Resolution (closed).** The obligation now lives over `F_q`: `mat_mult_mod` is
the dot product followed by `fq`, and `invertible_mod A` asks for a witness `B`
of the right shape whose two products are **congruent** (`cong_q_mat`) to the
identity.  Congruence rather than equality is forced by the fact that
`mat_mult_mod X (id_mat m) = map (map fq) X`, which equals `X` only when `X` is
already reduced, while a witness is arbitrary.  `T2_B3` is proved in this form.

**Lesson.** An algebraic identity about a modular implementation must be stated
in the modular ring.  The mismatch was invisible in prose and immediate in
Isabelle.

---

## 2. T2_D4 — dimension convention (row nullity vs column nullity)

**Original claim.** `dim (nullspace (rows3)) ≥ k - 1` for `k ≥ 2`, with the
nullity read as `dim_nullspace A = n_rows A - mat_rank A`.

**Why it is false.** `rows3` is a `(k + 2) x (2k + 1)` system.  The row-count
reading gives `k + 2 - rank`, and asking that to be `≥ k - 1` means
`rank ≤ 3` for *every* such system — which is not the case, and is not what the
sampler needs either.

**Correct statement.** The quantity the argument needs is the nullity of the
column map, `nullity A = n_cols A - mat_rank A = 2k + 1 - rank`, which is
`≥ k - 1` as soon as `rank ≤ k + 2`, i.e. as soon as reduction preserves the row
count.  For square matrices the two readings agree, which is why the earlier
two-by-two and three-by-three lemmas were unaffected.

**Resolution (closed).** `nullity` was added next to `dim_nullspace` (not in
place of it, because the row-count reading is the right one on square inputs),
`rows3_of` was given the body of Sec 6.4.1 with the four arguments it needs, and
`T2_D4` is proved in the column reading.

**Lesson.** "Dimension of the nullspace" is ambiguous for a non-square system;
the specification did not say which nullspace.

---

## 3. T2_B7 — a missing rank premise

**Original claim.** `mat_rank (psi_slice pk i) = 2` for every key `pk` and index
`i` in range.

**Why it is false.** `i < length (pk_psi pk)` is a shape condition on the key
record; it says nothing about the slice.  A key of the right shape whose slice
is the zero matrix has rank 0.

**Machine evidence** (`aligned/VWZ_Refutations.thy`):

```
T2_B7_counterexample: 0 < length (pk_psi <|pk_k = 1, pk_psi = [[[0,0],[0,0]]]|>)
                    ∧ mat_rank (psi_slice <|...|> 0) = 0
T2_B7_refuted:        ¬ (∀ pk i. i < length (pk_psi pk) ⟶ mat_rank (psi_slice pk i) = 2)
```

**Repaired statement (in the ledger).** Three premises, each corresponding to
something the original silently assumed:

1. `pk` is a key `KeyGen` can emit, so the slice has the shape of a sum of two
   outer products rather than being an arbitrary matrix;
2. the slice is non-degenerate, stated as the existence of a non-zero `2 x 2`
   minor — for a sum of two outer products this is what "the two drawn vectors
   are not parallel" amounts to;
3. the index is in range.

**Status: closed (2026-10-24).** The repaired statement is proved, and not by
the route the closing note of `aligned/VWZ_Rank.thy` anticipated.  The rank
theory ended up needing no row-operation or minor-invariance development at all:

- **upper half.** A slice entry is `(x0 * (ua!i2 * va!i3 + ub!i2 * vb!i3)) mod
  3329`, so row `i2` of the slice is the combination `(x0 * ua!i2) * va +
  (x0 * ub!i2) * vb`.  `rows_in_span_psi_slice_of` records that the rows lie in
  the span of two vectors and `mat_rank_psi_slice_of_le_two` feeds it to
  `mat_rank_le_two_of_rows_in_span` (the staircase/`rref` argument of
  `VWZ_Rank.thy`), giving `mat_rank ≤ 2`.  Because `map2` truncates, the
  spanning vectors are prefixes of length `min |va| |vb|`, so no length
  hypothesis on the factors is needed;
- **lower half.** The minor premise of the repaired statement *is* `minor2` of
  the slice modulo 3329, so `rank_ge_two_of_nonzero_minor` gives `2 ≤ mat_rank`
  once `is_rect` is known (now hypothesis-free);
- the two halves sandwich the rank, and `T2_B7` is `mat_rank = 2`.

The four items the file used to list were resolved in a different shape than the
note expected, and none of them is needed for this obligation:
`rref_step` was replaced by the residue-form undo lemmas,
`minors_invariant_under_row_ops` was proved forward in `VWZ_ModAlgebra.thy` and
backward through `minors_zero_rref_undo`, `rank_le_one_imp_minors_vanish` and
`rank_ge_two_of_nonzero_minor` were proved in `VWZ_Rank.thy`, and the product
bound `mat_rank (mat_mult A B) ≤ n_cols A` was replaced by the span argument
above, with `rank_outer_sum_le_two` as the one-line corollary.  The unrepaired
statement stays false (`T2_B7_refuted`), which is why the ledger statement keeps
the non-zero-minor premise.

**Lesson.** "The slice is rank 2" is a statement about the sampler, not about
the record shape.  The well-formedness hypothesis was missing from the prose —
and the repair that worked was the structural one (rows lie in a two-vector
span), not the most general rank theory.

---

## 4. T2_D5 — the target bit forced to be message-independent

**Original claim.**

```
i ∈ Sset (map int (hash_target k msg)) (x1_of sk)
  ⟹ Eval pk w2 w3 ! i = hash_target k msg ! i
```

with `pk`, `w2`, `w3`, `k` and `msg` all free.

**Why it is false.** `Eval` is typed

```
Eval :: nat list ⇒ nat list ⇒ nat list ⇒ nat list
```

so it never receives `k` and never receives `msg`.  Two instances of the
obligation with the *same* `Eval` arguments but different messages give the same
term on the left and two different target bits on the right.  The obligation
therefore asserts that the target bit at a support index is the same for every
message — i.e. that the target does not depend on the message it is derived
from.

**Machine evidence** (`aligned/VWZ_Refutations.thy`):

```
T2_D5_forces_target_independence:
  i ∈ Sset (map int (hash_target k1 msg1)) (x1_of sk) ⟹
  i ∈ Sset (map int (hash_target k2 msg2)) (x1_of sk) ⟹
  hash_target k1 msg1 ! i = hash_target k2 msg2 ! i
```

The proof instantiates the obligation twice at `Eval [] [] []` and chains the
two equations.  The derivation itself uses no hypothesis about `digest`; the
contradiction is with the body of `hash_target`, so this is a defect in the
wording, not a cryptographic difficulty.

**What the statement is missing.**

1. a body for `Sign` (`sk, msg ↦ (w2, w3)`), so that the witnesses can be tied
   to the message at all;
2. the linkage premises: `pk` is the signer's key, and the two witnesses are the
   ones `Sign` produced for *this* message;
3. an `Eval` that consumes the digest — otherwise no argument can make the
   evaluation depend on the target.

**Status: open (blocked), and it does not sit on the main line.** `T2_D5` keeps
its `sorry` and is tagged as a defect in the statement.  Two things are worth
stating precisely.

First, no *computational* counterexample can exist while the statement is
written against the uninterpreted constant: `Eval` is declared with `consts` in
`aligned/VWZ_Fq3329.thy` and has no body, while the protocol's real evaluation
is the separate definition `eval :: pkey ⇒ int list ⇒ int list ⇒ int list` in
`aligned/VWZ_Protocol.thy`.  So the evidence is necessarily the conditional
derivation above, and its conclusion is a statement about `hash_target`, which
*does* have a body (`aligned/VWZ_Fq3329.thy`) and derives its support from
`digest k msg`.  A target that is a function of the message cannot be
message-independent at a shared support index, so the obligation is false as
written.

Second, nothing else depends on it: outside `aligned/VWZ_Refutations.thy` no
lemma uses `T2_D5`, so discharging or restating it cannot move any other
obligation.  It is one of the six registered `sorry`s, counted by the ledger,
and it will stay that way until `Sign` has a body and the linkage premises can
be written down — a protocol-semantics decision that changes the security
argument, so it is deliberately not invented here.

**Lesson.** A correctness statement whose left-hand side does not mention the
message cannot say anything about a message-dependent target.  Formalisation
found this in one type signature.

---

## Summary

| Obligation | Defect | Machine evidence | Status |
|---|---|---|---|
| `T2_B3` | stated over `Z`, implementation is over `F_q` | `probe_mult`, `probe_rowop` (`VWZ_Probe.thy`) | closed after restatement over `F_q` |
| `T2_D4` | row nullity used for a non-square system | arithmetic: `k+2-rank ≥ k-1` needs `rank ≤ 3` | closed after switching to column nullity |
| `T2_B7` | rank-2 claim without a well-formedness premise | `T2_B7_counterexample`, `T2_B7_refuted` | closed: restated with a non-zero-minor premise, then proved via the two-vector span (`#23`, `#24`) |
| `T2_D5` | target bit forced independent of the message | `T2_D5_forces_target_independence` | open, blocked on `Sign` semantics; no other lemma uses it |

Three of the four are closed.  Of the closed ones, two were closed by restating
into a domain where the machinery already existed (`T2_B3` over `F_q`, `T2_D4`
in the column reading) and one by finding the right structural argument rather
than the most general theory (`T2_B7`).  The remaining one needs a modelling
decision (`Sign`) and is isolated: nothing consumes it, so the gap cannot hide
inside another proof.

## Reproducing

```
isabelle build -D aligned -o document=false     # RC=0, ~35 s on this machine
node tools/count-obligations.cjs                # 56 lemmas, 6 sorry, outside 0
```

`VWZ_Refutations.thy` is built as part of the session, so every refutation quoted
here is re-checked on every build.
