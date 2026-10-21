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
Current state: **56 lemmas, 7 `sorry`, 0 `sorry` outside the ledger.**

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

**Status: open, and honestly so.** The repaired statement is true but not yet
proved: it needs a rank theory that this development does not have.
`aligned/VWZ_Rank.thy` supplies the first layer (outer-product shapes, entry
formulas, and `mat_rank (zero_mat m n) = 0` proved through `rref`), and the
closing note of that file lists the four missing pieces:

- `rref_step`: each row operation is left multiplication by an invertible matrix;
- `minors_invariant_under_row_ops`: "every `2 x 2` minor vanishes" is preserved
  by row swaps, unit row scalings and row additions;
- `rank_le_one_imp_minors_vanish`: reduced form with at most one non-zero row
  has no non-zero minor;
- `mat_rank (mat_mult A B) ≤ n_cols A`, i.e. rank ≤ number of pivot columns,
  which is what bounds the rank of a sum of two outer products.

**Lesson.** "The slice is rank 2" is a statement about the sampler, not about
the record shape.  The well-formedness hypothesis was missing from the prose.

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
two equations.  No hypothesis about `digest` is used, so this is a defect in the
wording, not a cryptographic difficulty.

**What the statement is missing.**

1. a body for `Sign` (`sk, msg ↦ (w2, w3)`), so that the witnesses can be tied
   to the message at all;
2. the linkage premises: `pk` is the signer's key, and the two witnesses are the
   ones `Sign` produced for *this* message;
3. an `Eval` that consumes the digest — otherwise no argument can make the
   evaluation depend on the target.

**Status: open (blocked).** `T2_D5` keeps its `sorry` and is tagged as a defect
in the statement.  Modelling `Sign` is a protocol-semantics decision that changes
the security argument, so it is deliberately not invented here.

**Lesson.** A correctness statement whose left-hand side does not mention the
message cannot say anything about a message-dependent target.  Formalisation
found this in one type signature.

---

## Summary

| Obligation | Defect | Machine evidence | Status |
|---|---|---|---|
| `T2_B3` | stated over `Z`, implementation is over `F_q` | `probe_mult`, `probe_rowop` (`VWZ_Probe.thy`) | closed after restatement over `F_q` |
| `T2_D4` | row nullity used for a non-square system | arithmetic: `k+2-rank ≥ k-1` needs `rank ≤ 3` | closed after switching to column nullity |
| `T2_B7` | rank-2 claim without a well-formedness premise | `T2_B7_counterexample`, `T2_B7_refuted` | restated; open pending rank theory |
| `T2_D5` | target bit forced independent of the message | `T2_D5_forces_target_independence` | open; blocked on `Sign` semantics |

Two of the four are closed because the corrected statement is provable with the
machinery already present.  The other two are open for two different reasons —
one needs mathematics (a rank theory), one needs a modelling decision
(`Sign`) — and in neither case is the gap papered over.

## Reproducing

```
isabelle build -D aligned -o document=false     # RC=0, ~15 s
node tools/count-obligations.cjs                # 56 lemmas, 7 sorry, outside 0
```

`VWZ_Refutations.thy` is built as part of the session, so every refutation quoted
here is re-checked on every build.
