# Machine-checked specification defects in a post-quantum construction

**A case study in literal-first formalisation**

Object version: `vwz-formalization@d984b77` (2026-10-24) · Isabelle2025-2 · 20 theories ·
56 ledger obligations, 6 registered `sorry`, 0 outside the ledger

---

## Abstract

We formalised the algebraic core of a post-quantum construction in Isabelle/HOL under a
single discipline: **transcribe the specification literally, and allow restatement only
after the machine rejects the original sentence.** The result is not a security proof.
It is a list of four places where the specification, as written, does not mean what it
was intended to mean: an arithmetic domain mismatch, a dimension-convention mismatch,
a missing rank premise, and a definition whose free variables force two different
messages to produce the same target bits. Three are now closed; the fourth is false as
stated, has no consumer anywhere in the development, and cannot be repaired without a
modelling decision that we deliberately did not take.

The methodological claim is modest but testable: a proof assistant is useful *before*
implementation, as a machine that converts "looks right" into "decided false", and the
value of the exercise depends on keeping the ledger of what is actually proved honest.

## 1. Why literal-first

Formalising a cryptographic construction invites a quiet form of cheating: when a
statement will not go through, one adjusts the statement until it does. Each individual
adjustment looks reasonable; collectively they destroy the evidential value, because the
machine then certifies a sentence nobody wrote.

We therefore fixed an ordering rule at the start:

1. transcribe the statement as written, with the same quantifiers and the same domains;
2. if it fails, try to **refute** it (a witness, or a derivation of a contradiction from
   it);
3. only then restate, and record the restatement as a **defect against the
   specification**, not as a proof convenience.

This produces two kinds of output: proved obligations, and a defect register. The
register is the more interesting artefact.

## 2. Object and transcription

- **Object**: the algebraic skeleton of VWZ — the field `F_3329`, matrix and modular
  algebra, the key-generation pipeline, the slice matrices that carry the public key,
  and the target/hash side.
- **Transcription**: `aligned/*.thy`, 20 theory files. This is what the machine checks.
  There is no claim that it is a faithful copy of any particular PDF; fidelity is an
  assumption of the exercise, and the statements are quoted in `VWZ_DEFECTS.md` so a
  reader can check them against the source independently.
- **Two kinds of uninterpreted material** matter for reading the results:
  - `Eval` (`aligned/VWZ_Fq3329.thy:201`) is a bare `consts` with type
    `nat list => nat list => nat list => nat list`. It has no body.
  - `hash_target` (`aligned/VWZ_Fq3329.thy:195`) **does** have a body, derived from
    `digest k msg`.

The asymmetry between those two is what makes Result B a logical refutation rather than
a computed one.

## 3. Method: a ledger, three gates

### 3.1 The ledger

Obligations are grouped by what they depend on, not by file:

| Section | Scope | Lemmas | `sorry` |
|---|---|---:|---:|
| T0 | purely formal rewriting (target: 0) | 17 | 0 |
| T1-A | algebraic axioms | 16 | 0 |
| T1-D | definition-dependent obligations | 5 | 2 |
| T2 | linear algebra / matrices | 10 | 2 |
| T3 | security / probabilistic / parser (`TODO(define)` subjects) | 8 | 2 |
| **Total** | | **56** | **6** |

`tools/count-obligations.cjs` counts every `lemma` in the obligations file and asserts
that **every `sorry` proof step is registered**; at `d984b77` it reports
`6 (ledger: 6, outside: 0)`. The repository contains 582 lemmas in total; the difference
is supporting infrastructure, and is reported rather than hidden.

Two of the six open obligations are in T3, on subjects that are still uninterpreted
constants — i.e. they are blocked on modelling, not on mathematics.

### 3.2 Gates

- **Build gate**: `isabelle build -b -c -D aligned` → RC=0, 33-41 s on the author's
  machine (range across rounds; a single round is not a benchmark).
- **Encoding gate**: `.github/scripts/check-encoding.cjs` over tracked text files — no BOM, no
  NUL, no U+FFFD, no private-use characters. It also refuses to report a pass when it
  scanned nothing, so a wrong working directory cannot look green.
- **Ledger gate**: the count above, run after every change, plus a CI workflow that
  compares the totals literally.

### 3.3 The `quick_and_dirty` question

`quick_and_dirty` lets `sorry` through and is convenient during development; a green
build under it proves almost nothing. For the `T2_B7` work we ran a dependency-chain
check with the option **off**:

1. copy `aligned/` outside the repository;
2. remove `quick_and_dirty` from `ROOT`;
3. replace the six registered `sorry`s with `oops`;
4. build the obligations file under a fresh theory name (`VWZ_LedgerCheck`).

Result: RC=0 in ~35 s. That rules out hidden `sorry`/`Skip_Proof` **in the chain**. It is
not a full proof-term audit, and we do not present it as one — see §7.

## 4. Result A — `T2_B7`: false as written, true after repair, and proved

### 4.1 The statement as written

Conditioned only on the index being in range, `T2_B7` asserted that a slice matrix of
the public key has rank 2.

### 4.2 The refutation

`T2_B7_counterexample` (`aligned/VWZ_Refutations.thy`) takes a public key whose slice is
the zero 2x2 matrix. The index is in range; the rank is 0. The original statement is
therefore false, and no amount of proof effort could have closed it.

The refutation lives outside the obligation file on purpose: the ledger counts every
`lemma` in that file, and a refutation is evidence that a statement is wrong, not proof
debt. Mixing the two would corrupt the accounting.

### 4.3 The repair

Add a **non-zero 2x2 minor** premise. This is exactly the missing hypothesis: rank 2
means "some 2x2 minor does not vanish", and the original statement silently assumed it.

### 4.4 The proof

The proved statement is `aligned/VWZ_ObligationsAligned.thy:790`.

- **Upper bound.** Each row of the slice is `(x0 * ua!i) * va + (x0 * ub!i) * vb`
  (`psi_slice_of_row`), i.e. a combination of two fixed vectors. A matrix whose rows lie
  in the span of two vectors has rank at most 2:
  `rows_in_span_psi_slice_of` → `mat_rank_psi_slice_of_le_two` →
  `mat_rank_le_two_of_rows_in_span`. The construction truncates to the shorter of the
  two spanning vectors, so the bound needs **no** length hypothesis — an earlier plan
  that tried to prove equal lengths was abandoned as unnecessary.
- **Lower bound.** `rank_ge_two_of_nonzero_minor` turns the non-zero minor into
  `2 <= mat_rank`. The rectangle hypothesis needed by the minor lemma is supplied by
  `is_rect_psi_slice_of`, which holds without premises.
- **Conclusion.** `rank <= 2` and `2 <= rank` meet at `rank = 2`.

Four work items that had been listed as prerequisites for this obligation
(`rref_step`, `minors_invariant_under_row_ops`, `rank_le_one_imp_minors_vanish`, and a
product-dimension bound) turned out to be **superseded rather than proved**: the
residue-form undo lemma replaces the first, the forward direction of the second is
proved in `VWZ_ModAlgebra.thy` and the reverse direction goes through
`minors_zero_rref_undo`, the third is subsumed by `rank_ge_two_of_nonzero_minor`, and
the product bound is replaced by the span argument plus the one-line corollary
`rank_outer_sum_le_two`. This is recorded because "we proved the four things we said we
needed" would have been false.

## 5. Result B — `T2_D5`: false as written, and not a break

### 5.1 The statement

For every index in the support of `hash_target k msg`, the corresponding bit of
`Eval pk w2 w3` equals the corresponding bit of `hash_target k msg`. All of `pk`, `w2`,
`w3`, `k`, `msg` are universally quantified; **`Eval` never receives `k` or `msg`**.

### 5.2 Why there is no computed counterexample

`Eval` is `consts`, not a definition. Until it has a body there is nothing to compute,
so the only available refutation is logical. This distinction matters: a computed
witness is a much stronger artefact than a conditional derivation, and we should not
pretend to have one.

### 5.3 The derivation

`T2_D5_forces_target_independence` (`aligned/VWZ_Refutations.thy`) instantiates the lemma
twice at the same `Eval [] [] []` with two different `(k, msg)` pairs, and concludes
that the two targets agree bit-for-bit on any shared support index. Since `hash_target`
is defined from `digest k msg`, that contradicts what the definition is for: a support
derived from the message cannot be message-independent.

No hypothesis about `digest` is used. The contradiction comes from the shape of the
statement — free `k`, `msg` that never reach `Eval` — not from any property of the hash.

### 5.4 Why it is not a vulnerability

- `Eval` has no body in this development, so nothing executes.
- **No other proof consumes `T2_D5`.** Grep finds the name only in the obligations file,
  the refutation file and documentation. It moves no other obligation, so closing it
  (or not) cannot change any other result.
- A repair is a **modelling decision**: give `Sign` a body, add premises linking
  `w2, w3` to `fst/snd` of that body, and — if `Eval` is to depend on the message —
  change its type. That is a change to the object of study, not a proof task, and it
  would pull the distribution of `w2, w3` into the security argument. We left it open
  and documented it.

## 6. The two closed restatements

- **`T2_B3`** — arithmetic domain mismatch: the statement mixed integer arithmetic with
  arithmetic in `F_q`. Closed by restating on the correct domain.
- **`T2_D4`** — dimension convention: the statement used row nullity where the
  construction needs column nullity. Closed by restating with the right convention.

Neither required new mathematics; both required noticing that the sentence said
something other than intended. That is the characteristic failure mode this exercise is
designed to catch.

## 7. Limits and threats to validity

1. **Transcription fidelity.** The machine checks our sentences. If the transcription
   differs from the source, the result is about the transcription.
2. **Uninterpreted constants.** `Eval` and the T3 subjects are uninterpreted. Results
   that mention them are conditional on their intended semantics.
3. **Ledger ≠ correctness.** 56 obligations, 6 registered `sorry`: the ledger says what
   is owed and what is paid, not that the construction is correct.
4. **`quick_and_dirty=false` is a chain check.** Replacing registered `sorry`s with
   `oops` rules out hidden `sorry`s in the compiled chain; it is not a full independent
   proof-term audit, and we do not claim one.
5. **No extraction, no implementation link.** Nothing here says a compiled
   implementation refines these definitions.
6. **No security claim.** No theorem here is a security statement about the
   construction.

## 8. Engineering notes that made the numbers trustworthy

These are unglamorous and were decisive:

- **Literal first, restate later**, with the restatement recorded as a defect.
- **A ledger that is checked mechanically**, and a CI gate that compares the totals
  literally — so a change in the `sorry` count cannot silently pass.
- **Refutations outside the ledger**, so "this statement is false" never counts as
  "proof debt paid".
- **Encoding gate** on every tracked text file (no BOM, no NUL, no U+FFFD, no
  private-use characters), because mojibake in comments has repeatedly produced
  silently wrong tooling elsewhere.
- **No global `declare`** and a short blacklist of rewrite rules kept out of `simp`
  (`mod_add_eq`, `mod_mult_eq` reverse-rewrite against `fq_idem` and hang the simplifier;
  letting `min` into the simp set normalises it to `if`, which breaks the `zip`/`map`
  side conditions).
- **Re-measure, never extrapolate.** Every number quoted here was read from the tree at
  `d984b77`, not carried over from an earlier round.

## 9. Reproduction

```bash
isabelle build -b -c -D aligned        # RC=0, 33-41 s
node tools/count-obligations.cjs       # 56 lemmas, 6 sorry, outside 0
node .github/scripts/check-encoding.cjs          # tracked text files clean
```

Dependency chain with the option off: copy `aligned/` outside the repo, drop
`quick_and_dirty` from `ROOT`, replace registered `sorry`s with `oops`, build → RC=0
(~35 s).

## 10. Provenance of the numbers in this document

| Figure | Value | Where measured |
|---|---|---|
| object version | `d984b77` | `git rev-parse HEAD` |
| theory files | 20 | `count-obligations.cjs` |
| repository lemmas | 582 | `count-obligations.cjs` |
| ledger | 56 lemmas / 6 `sorry` / outside 0 | `count-obligations.cjs` |
| build | RC=0, 33-41 s | `isabelle build -b -c -D aligned` |
| chain check, `quick_and_dirty` off | RC=0, ~35 s | copy of `aligned/` outside the repo |

If you are reading this at a later commit, re-run the three commands before quoting any
of it.
