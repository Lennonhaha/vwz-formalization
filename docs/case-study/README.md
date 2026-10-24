# Case study: what a proof assistant found in a post-quantum construction

This directory is a self-contained write-up of one result: a machine-checked
formalisation of the algebraic core of a post-quantum construction (called VWZ
throughout this repository) turned up **four defects in the specification**, of which
three are now closed and one remains open and isolated.

The point of the exercise is not "we verified a cipher". It is narrower and, we think,
more useful: **a proof assistant can turn a sentence that looks right into a sentence
the machine decides is false, before anyone builds on it.**

## 1. Object under study

- Development: `aligned/` in this repository.
- Object version: **commit `d984b77`** (2026-10-24). Every number below was measured at
  that commit; later commits may move them.
- What is machine-checked is **our transcription** of the construction into Isabelle/HOL
  (`aligned/*.thy`), not a PDF or a published reference implementation. Statements are
  transcribed as written first; restatement is allowed only after the machine rejects
  the original (see §4).
- 20 theory files, 565,865 bytes, 582 lemmas in the repository (of which 56 are ledger
  obligations — the rest is supporting infrastructure).

## 2. The obligation ledger

`tools/count-obligations.cjs` classifies every obligation and asserts that **no `sorry`
exists outside the ledger**:

| Section | Scope | Lemmas | `sorry` |
|---|---|---:|---:|
| T0 | purely formal rewriting (target: 0) | 17 | 0 |
| T1-A | algebraic axioms | 16 | 0 |
| T1-D | definition-dependent obligations | 5 | 2 |
| T2 | linear algebra / matrices | 10 | 2 |
| T3 | security / probabilistic / parser (`TODO(define)` subjects) | 8 | 2 |
| **Total** | | **56** | **6** |

Verification gate output at `d984b77`:

```
TOTAL                56 lemmas, 6 sorry
sorry proof steps     6  (ledger: 6, outside: 0)
OK: every sorry proof step is an obligation in the ledger.
```

The six remaining `sorry`s are **registered debt with a documented reason**, not
accidents. Two of them sit in T3 on subjects that are still uninterpreted constants.

## 3. The four defects

| Defect | Kind | Status |
|---|---|---|
| `T2_B3` | arithmetic domain mismatch (`Z` vs `F_q`) | closed by restatement |
| `T2_D4` | dimension convention (row nullity vs column nullity) | closed by restatement |
| `T2_B7` | missing rank premise — statement false as written | **repaired and proved** |
| `T2_D5` | target bit forced to be message-independent | **refuted as written, open, zero consumers** |

Details for all four, including the exact statements, live in
[`VWZ_DEFECTS.md`](../../VWZ_DEFECTS.md).

## 4. Result A — `T2_B7`: a missing premise, then a proof

As written, `T2_B7` claimed that a certain slice matrix has rank 2 conditioned only on
an index being in range. That is false, and the refutation is a two-line witness
(`aligned/VWZ_Refutations.thy`, `T2_B7_counterexample`): take a public key whose slice
is the zero 2x2 matrix — the index is in range, the rank is 0.

The repaired statement adds exactly what was missing: a **non-zero 2x2 minor**. It is
now proved (`aligned/VWZ_ObligationsAligned.thy`, `T2_B7`), and the proof route is
worth recording because it is structural rather than heroic:

- **rank ≤ 2**: every row of the slice is a combination of two fixed vectors
  (`rows_in_span_psi_slice_of`), and any matrix whose rows lie in a two-vector span has
  rank at most 2 (`mat_rank_psi_slice_of_le_two`, resting on
  `mat_rank_le_two_of_rows_in_span`). Because the construction truncates to the shorter
  of the two spanning vectors, no length hypothesis is needed.
- **rank ≥ 2**: a non-zero minor of order 2 forces rank at least 2
  (`rank_ge_two_of_nonzero_minor`).

Merged as PRs #23 (span bound) and #24 (discharge of `T2_B7`).

## 5. Result B — `T2_D5`: false as stated, but not a break

As written, `T2_D5` says that a target bit computed by `Eval pk w2 w3` equals the
corresponding bit of `hash_target k msg` for every index in the support — with `pk`,
`w2`, `w3`, `k` and `msg` all universally quantified, and **`Eval` never receives `k`
or `msg`**.

`Eval` is an uninterpreted constant (`aligned/VWZ_Fq3329.thy:201`,
`nat list => nat list => nat list => nat list`), so no computed counterexample is
possible: the failure has to be logical. And it is.
`T2_D5_forces_target_independence` (`aligned/VWZ_Refutations.thy`) instantiates the
lemma twice at `Eval [] [] []` and derives that two targets built from **different
messages** must agree bit-for-bit on any shared support index. `hash_target`, by
contrast, has a body (`aligned/VWZ_Fq3329.thy:195`) derived from `digest k msg`, so the
conclusion contradicts its intended meaning.

What this is and is not:

- It **is** a specification defect: the sentence cannot hold for the reason it was
  written for.
- It is **not** a break of the construction: `Eval` has no body here, and
  **no other proof in the development consumes `T2_D5`** — grep finds it only in the
  obligation file, the refutation file and documentation. It moves no other obligation.
- Restating it is a **modelling decision, not a proof task**: it needs a body for
  `Sign` and premises linking `w2, w3` to that body. We deliberately did not invent
  that semantics, because doing so changes the security argument.

## 6. Boundaries — what this does not claim

1. **No security claim.** Every theorem here is about the transcribed formulas. Nothing
   here says the construction is secure, or that an implementation is correct.
2. **`T2_D5` is a specification defect, not a vulnerability.** It has no consumer and no
   executable semantics in this development.
3. **Transcription fidelity is an assumption.** The machine checks the sentences we
   wrote; if a sentence was mistranscribed, the machine cannot know.
4. **The ledger is not functional correctness.** 56 obligations with 6 registered
   `sorry`s is a bookkeeping discipline, not "everything is proved".
5. **`quick_and_dirty=false` is not a full proof-term check.** Our dependency-chain
   check (below) removes the option and replaces the six registered `sorry`s with
   `oops`; that rules out hidden `sorry`/`Skip_Proof` in the chain. It is not a
   statement that every proof term has been independently re-checked.

## 7. Reproducing

Requires Isabelle2025-2 and Node.js (only for the audit scripts).

```bash
# full build of the development
isabelle build -b -c -D aligned          # RC=0, 33-41 s on the author's machine

# obligation ledger: expect 56 lemmas / 6 sorry / outside 0
node tools/count-obligations.cjs

# encoding gate (tracked text files: no BOM, no NUL, no U+FFFD, no private-use chars)
node .github/scripts/check-encoding.cjs
```

Dependency-chain check with `quick_and_dirty` off (the method used for `T2_B7`):

1. copy `aligned/` outside the repository;
2. drop `quick_and_dirty` from `ROOT`;
3. replace the six registered `sorry`s with `oops` and build the obligations file under
   a fresh theory name;
4. `isabelle build` → RC=0 in ~35 s, i.e. the chain containing the new proofs compiles
   without hidden `sorry`s.

## 8. Where things are

| Path | What |
|---|---|
| `aligned/VWZ_ObligationsAligned.thy` | the 56 obligations; `T2_B7` (line ~790) proved, `T2_D5` (line ~902) registered `sorry` |
| `aligned/VWZ_Refutations.thy` | witnesses and reductio derivations; outside the ledger on purpose |
| `aligned/VWZ_Rank.thy` | span/rank toolkit behind `T2_B7` |
| `aligned/VWZ_Fq3329.thy` | field, `hash_target` (body), `Eval` (uninterpreted) |
| `VWZ_DEFECTS.md` | the four defects in full, with statements and status |
| `docs/papers/engineering-verification-pqc/` | longer Chinese write-up (`main-zh.tex`) |

> **Caution before citing the paper draft:** its abstract still reports *7 unclosed
> obligations* and a *~16 s* build. Both predate PRs #24/#25; the current figures are
> **6** and **33-41 s**. Regenerate the PDF before publishing it alongside this case
> study.

## 9. Versioning and citation

Archived at DOI [`10.5281/zenodo.23622795`](https://doi.org/10.5281/zenodo.23622795) (tag `v1.0.1`,
concept DOI `10.5281/zenodo.23622177`, record <https://zenodo.org/records/23622795>). The
earlier version, tag `v1.0.0`, stays citable at `10.5281/zenodo.23622178`; the two differ only
in `LICENSE` (v1.0.0 archived the GPLv3 text, v1.0.1 the Apache-2.0 text that the sources and
README declare). The machine-checked
artefact is the git tree, so the tag is the meaningful version identifier; the archived
zip is a `git archive` snapshot of it, and a rendered PDF is a convenience copy.
