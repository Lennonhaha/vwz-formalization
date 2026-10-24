# v1.0.0 — release notes (DRAFT, not published)

> **Status: draft for review. No tag has been created, no deposit has been made.**
> Publishing is a separate, irreversible step that needs an explicit go-ahead.

## Summary

This release packages the case study in `docs/case-study/`: what a proof assistant found
in the specification of the VWZ construction, and what was done about it.

The short version: formalising the algebraic core in Isabelle/HOL under a
**literal-first** rule (transcribe as written, restate only after the machine rejects the
original) surfaced **four specification defects**. Three are closed. One is false as
written, has no consumer anywhere in the development, and cannot be repaired without a
modelling decision that we deliberately did not take.

Nothing here is a security claim about the construction, and nothing here says an
implementation is correct.

## Artefact and provenance

- Repository: `Lennonhaha/vwz-formalization`, default branch `main`, GPL-3.0.
- **Object version for every number in this release: `d984b77`** (2026-10-24,
  `docs: settle T2_D5 and retire the rank work list (#25)`).
- `aligned/` — 20 theory files, 582 lemmas in the repository, **56 ledger obligations
  with 6 registered `sorry`, 0 outside the ledger**.
- The proposed tag target is the commit that adds `docs/case-study/` (a documentation-only
  commit; it does not touch `aligned/`, so the numbers above stay valid at the tag).

## What is in this release

| File | Contents |
|---|---|
| `docs/case-study/README.md` | short version: object, ledger, two headline results, boundaries, reproduction |
| `docs/case-study/PAPER.md` | long version: method, proofs, limits, engineering notes, provenance table |
| `docs/case-study/RELEASE-v1.0.0.md` | this file |
| `docs/case-study/zenodo-deposit.DRAFT.json` | Zenodo metadata, prepared but not submitted |

## Headline result A — `T2_B7`: a missing premise

- **As written**: rank 2 conditioned only on the index being in range. **False.**
- **Refutation**: `T2_B7_counterexample` in `aligned/VWZ_Refutations.thy` (zero 2x2 slice
  at an in-range index).
- **Repair**: add a non-zero 2x2 minor premise.
- **Proof**: `T2_B7` in `aligned/VWZ_ObligationsAligned.thy` (~line 790).
  - rank ≤ 2 via `psi_slice_of_row` → `rows_in_span_psi_slice_of` →
    `mat_rank_psi_slice_of_le_two` → `mat_rank_le_two_of_rows_in_span`;
  - rank ≥ 2 via `rank_ge_two_of_nonzero_minor`, with the rectangle hypothesis from
    `is_rect_psi_slice_of`;
  - the "no length hypothesis" property comes from truncation to the shorter spanning
    vector; the one-line corollary is `rank_outer_sum_le_two`.
- **Honest footnote**: the four work items originally listed as prerequisites
  (`rref_step`, `minors_invariant_under_row_ops`, `rank_le_one_imp_minors_vanish`,
  product-dimension bound) were **superseded, not proved** — recorded in
  `aligned/VWZ_Rank.thy`.

## Headline result B — `T2_D5`: false as written, and not a break

- **As written**: `Eval pk w2 w3` must agree with `hash_target k msg` on the support, with
  `k`, `msg` universally quantified — while `Eval` never receives `k` or `msg`.
- **Why no computed counterexample**: `Eval` is an uninterpreted constant
  (`aligned/VWZ_Fq3329.thy:201`), so the refutation is logical, not computational.
- **Derivation**: `T2_D5_forces_target_independence` in `aligned/VWZ_Refutations.thy`
  instantiates the statement twice at `Eval [] [] []` and forces two different messages to
  produce identical target bits; `hash_target` (`aligned/VWZ_Fq3329.thy:195`) has a body
  derived from `digest k msg`.
- **Scope**: no consumer anywhere in the development; it moves no other obligation.
  Closing it requires giving `Sign` a body and adding linkage premises — a modelling
  decision, left open on purpose.

## Closed restatements

- `T2_B3` — arithmetic domain mismatch (integers vs `F_q`).
- `T2_D4` — dimension convention (row nullity vs column nullity).

## Ledger

| Section | Scope | Lemmas | `sorry` |
|---|---|---:|---:|
| T0 | purely formal rewriting (target: 0) | 17 | 0 |
| T1-A | algebraic axioms | 16 | 0 |
| T1-D | definition-dependent obligations | 5 | 2 |
| T2 | linear algebra / matrices | 10 | 2 |
| T3 | security / probabilistic / parser (`TODO(define)` subjects) | 8 | 2 |
| **Total** | | **56** | **6** |

## Reproducing

```bash
isabelle build -b -c -D aligned        # RC=0, 33-41 s
node tools/count-obligations.cjs       # 56 lemmas, 6 sorry, outside 0
node .github/scripts/check-encoding.cjs          # tracked text files: no BOM, no NUL, no U+FFFD, no PUA
```

`quick_and_dirty` off (chain check used for `T2_B7`): copy `aligned/` outside the repo,
drop the option from `ROOT`, replace the six registered `sorry`s with `oops`, build
(~35 s, RC=0). This rules out hidden `sorry`/`Skip_Proof` in the chain; it is **not** a
full proof-term audit.

## Boundaries

1. No security claim: every theorem is about the transcribed formulas.
2. `T2_D5` is a specification defect, not a vulnerability (no consumer, no executable
   semantics here).
3. Transcription fidelity is an assumption of the exercise.
4. The ledger records what is owed and paid, not functional correctness.
5. No extraction, no implementation link.

## Caution before citing the paper draft

`docs/papers/engineering-verification-pqc/main-zh.tex` still reports **7 unclosed
obligations** and a **~16 s** build. Both numbers predate PRs #24/#25. Current figures:
**6** and **33-41 s**. That file is deliberately unchanged in this release; do not quote
its abstract as current.

## Publication checklist (for the person who says go)

1. Confirm the release commit and re-run the three commands above at that commit.
2. `git tag -s v1.0.0 <commit>` and push the tag.
3. Submit `zenodo-deposit.DRAFT.json` **after** the tag exists — the `related_identifiers`
   URL points at `/tree/v1.0.0`.
4. Only after Zenodo mints the DOI: add the DOI to the README, then (optionally) to the
   paper draft in the same edit that fixes its two stale numbers.
