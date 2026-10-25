# VWZ Formalization

Machine-checked proofs for the **VWZ** construction (Kyber-style, over the prime
field `F_3329`), developed in **Isabelle/HOL**.

> 📄 **Paper:** [VWZ 形式化验证与规范缺陷分析 (v1.0.0-paper)](https://github.com/Lennonhaha/vwz-formalization/releases/tag/v1.0.0-paper)
> — nine-page Chinese manuscript: four specification defects found by machine, and the
> obligation ledger (56 lemmas, 7 unresolved proofs, 0 outside the ledger).
> Source: [`docs/papers/engineering-verification-pqc/`](docs/papers/engineering-verification-pqc/).

This repository is deliberately separate from the FIBEMATE business
repositories: formal methods artifacts have a different build toolchain
(Isabelle), a different release cadence, and a much larger footprint than the
product code. Keeping them apart keeps both sides honest.
Status, known gaps, and how to contribute: [docs/ANNOUNCEMENT-EN.md](https://github.com/Lennonhaha/fibemate/blob/main/docs/ANNOUNCEMENT-EN.md) · [contributor guide](https://github.com/Lennonhaha/fibemate/blob/main/docs/CONTRIBUTORS-GUIDE.md).


## Status

The formalization is **work in progress**. Proof obligations are tracked in
tiers; the counts below are generated, not asserted.

| Session | Content | Lemmas | `sorry` |
|---|---|---|---|
| `VWZ_A3_Aligned` | Definition layers + obligation inventory | 56 | 7 |

Rank, nullity and inversion are no longer uninterpreted. `VWZ_RREF.thy` defines
a fuel-parameterised Gauss-Jordan reduction and derives
`mat_rank A = length (filter (\<lambda>r. \<not> all_zero_row r) (rref A))`,
`dim_nullspace A = n_rows A - mat_rank A`, and `mat_inv A` by reducing `[A | I]`.
Fuel makes the recursion structural, so no termination proof is needed.
Correctness of the reduction (that it reaches a normal form, that `mat_rank` is
the field rank, that `mat_inv` is a two-sided inverse) is **not** claimed; seven
`eval` lemmas check that the definitions compute on concrete matrices.

`M2` and `M3` are now spelled as spec Sec 3.4 spells them (`X2b * X2a^-1`), so
`T2_B5` closes by unfolding. That is transcription, not proof, and it is
recorded as such.

`solve_linear` is a defined object now, not an uninterpreted constant, but it is
a **specification**: it returns some solution of `A x = b` over F_3329 when one
exists (Hilbert choice) and `None` otherwise, so it is not executable and the
Gauss-Jordan back substitution the spec describes is still open. What is
proved about it is the semantics (`solve_linear_sound`, the `None` case, the row
projections, and the homogeneous corollary that a solution of `A x = 0` reduces
every row to zero). The two systems that T2_D6 needs are kept apart in
`VWZ_Rows3.thy`: `rows3_of` is the *u3* system, `rows_u2_of` the *u2* system.
`VWZ_Transpose.thy` supplies the bilinear identity
`dot (matvec (transpose A) u) v = dot u (matvec A v)` by exchanging the two sums
(`swap_idx`), and that identity is what lets `T2_D6` close against the rows the
sampler really builds.

The generator is no longer a single opaque constant, though it is not a
replacement yet. `VWZ_Fq3329` now carries the Sec 3.1 LCG as a state machine on
`nat` reduced modulo `2^64` (exact, since `nat` does not overflow, and no
`Word_Lib` needed), together with `next_u16_mod` -- including the 32-bit
truncation *before* the modular reduction, which the spec makes normative for
byte compatibility. `VWZ_KeyGen` defines `draw_list` and a fuel-counted
`distinct_lam_fuel`, and proves partial correctness: if it returns anything, it
returns `n` pairwise-distinct points in `[1, q)`.

`SeedRng` is now a state transition, `nat => nat * nat`: it returns the value
and the next state, and the stream is its iteration. The earlier signature
`nat => nat list` could not express an unbounded stream, which is what
rejection sampling needs. `distinct_lam n s` is the same sampler under a
generous fuel bound (`8 * n + 8` rounds), so it returns a pair even when it
fails, and `[]` is the failure signal the spec's retry logic expects.

What is *not* proved is termination of rejection sampling: it stops with
probability 1, not by construction, and this session has no measure theory.
T3_B1 was restated against the state-passing sampler and now carries that
failure guard explicitly; the restated form is discharged by
`distinct_lam_partial_correct`. The unconditional "always returns n points"
claim is nowhere asserted — it was asking a list-valued function for a
property the algorithm cannot have.

### T3: two parsers, a weight, and the index split

`T3_E1`, `T3_E2` and `T3_E4` are closed, taking the ledger from 15 to 12; `T3_C3` then took it to 11. The
split is recorded honestly: E1 and E4 are option-case splits with almost no
information content (a total function into an option returns `None` or `Some`),
while E2 has substance -- an accepted length forces `hd bs = k`, which contradicts
the stated premise. `T3_C3` is now closed as a negative result: `unbiased m` is
defined as `m dvd 2 ^ 32` (exact uniformity of a 32-bit reduction), and `3329`
does not divide `2 ^ 32` -- which is precisely why the sampler rejects.

Three names on that path are no longer uninterpreted: `parse_pk` / `parse_sig` are
the existing `deser_pk` / `deser_sig` (spec Sec 8.3), and `weight` is a real
filter. `Sset` / `Zset` are the zero / non-zero split of `adapted_of` over
`(t, x1)`; the split needs the secret `x1`, which a signature taking only the
message could not express, so the two obligations were restated and that
restatement is recorded in the file.

`rows3_of` no longer stays uninterpreted either: `VWZ_Rows3.thy` builds it from
`vand`, `matvec` and `transpose` exactly as Sec 6.4.1 lists it. `hash_target` has
a body too: the support comes out of a partial Fisher-Yates walk that swaps a
pair of positions in place at every step (`fy_fuel` / `swap_at` in
`VWZ_Fq3329.thy`), and the target is the indicator of that support. The only
uninterpreted object left on that path is `digest`, the XOF, and nothing claims
it is a hash. `T3_C1` is closed: `VWZ_Target.thy` proves that the walk keeps the
pool's length, set and distinctness, so the first `k + 1` entries exist and are
distinct positions in range, and that the indicator of such a support has Hamming
weight equal to its length. It keeps the hypothesis that the digest supplies
`k + 1` words, without which the claim is simply false.

### One obligation is still a defect in the specification, not proof debt

`T2_D5` is marked **TODO(defect / restatement)**.  It is not a gap in a proof: it
is a statement that is false as written, and it was refuted by machine before
anything was restated.  `T2_B7` was in the same class and is now closed.

- `T2_B7` (`VWZ_Refutations.thy`, `T2_B7_counterexample` and `T2_B7_refuted`):
  `mat_rank (psi_slice pk i) = 2` needs the key to be in the image of `KeyGen` and
  the slice to have a non-zero `2 x 2` minor. A key of the right shape with a zero
  slice has rank 0. The repaired statement is in the ledger and is **proved**: rows
  of a slice lie in the span of two vectors (`rows_in_span_psi_slice_of`), which
  bounds the rank by 2, and the minor premise supplies the other inequality.
- `T2_D5` (`VWZ_Refutations.thy`, `T2_D5_forces_target_independence`): `Eval` is
  typed so that it never receives `k` or `msg`, while `pk`, `w2` and `w3` are
  free. The obligation therefore forces the target bit at a support index to be
  the same for every message, while `hash_target` derives its support from
  `digest k msg`. It stays open until `Sign` has a body and the linkage premises
  can be written down. Nothing else in the development uses it, so it cannot
  hide an error inside another proof.

`VWZ_DEFECTS.md` collects all four specification defects found this way
(`T2_B3`, `T2_D4`, `T2_B7`, `T2_D5`) with their machine evidence and status;
three of the four are now closed.

### Key generation now has a body

`KeyGen` was the last uninterpreted name on the critical path. It is now a definition (`VWZ_KeyGen.thy`):

- `random_invertible_matrix m s` runs the Sec 3.3 loop exactly `m * m` times from `id_mat m`,
  drawing `i`, then `j` (both consumed even when `i = j`), then the factor, and
  applying `add_row_mult`. No fuel is invented: the round count is structural.
- `mats_of m s` draws the four matrices in the order Sec 3.3 fixes (`X2a, X2b, X3a, X3b`),
  and `X2a_of` / `X2b_of` / `X3a_of` / `X3b_of` are views on it, not extra draws.
- `KeyGen k seed` follows the draw order the spec makes normative (lambdas, then
  matrices, then `x1`), builds `psi` slice by slice with `map2` over the two
  outer-product factors, and fills the secret record with the Sec 3.6 fields,
  using `mat_inv` / `mat_mult` from `VWZ_RREF`.

T2_D4 is closed too, and it was also a restatement rather than a proof attempt.
`rows3_of` now has the body Sec 6.4.1 lists (Vandermonde rows in the secret
`lambda_c` for `Za`, and `M3^T` rows for `Zb`), so the lemma takes the four
arguments the body needs; and the count runs over `nullity A = n_cols A - mat_rank A`,
not `dim_nullspace A = n_rows A - mat_rank A`.  For a `(k+2) x (2k+1)` system the
row-count reading gives `k+2-rank`, which cannot bound `k-1` from below at all --
it would need `rank <= 3` for every such system.  The column nullity gives
`2k+1-rank >= k-1` from `rank <= k+2`, i.e. from the reduction preserving the row
count.  Both readings agree on square matrices, so the earlier square lemmas are
untouched; `nullity` was added next to `dim_nullspace` rather than redefining it.

What was open, T2_B3, is now closed over `F_q`, and the restatement was forced by
two facts that the first plan got wrong.  First, the bridge as stated is false:
`add_row_mult` reduces entries modulo `q` while `mat_mult` does not, so
left-multiplying by an elementary matrix differs from the row operation by a
reduction.  `VWZ_Probe.thy` exhibits the mismatch, and two row additions already
yield an integer determinant far from a unit -- these matrices are not invertible
over the integers at all.  The obligation therefore lives over `F_q`:
`mat_mult_mod` is the dot product followed by `fq`, and `invertible_mod` asks for
a witness whose two products are congruent (`cong_q_mat`) to the identity.
Congruence rather than equality is required because `B * I` is `map (map fq) B`,
which equals `B` only for reduced matrices, and a witness is arbitrary.

The proof runs in layers.  `mat_mult_mod_assoc` supplies associativity of the
modular product; `mat_mult_mod_row_add` transfers one row addition, under the
invariant that entries stay in `[0, q)`, which the generator preserves because it
starts from `id_mat` and only adds positive multiples; `mat_mult_mod_elem_inverse`
gives the explicit elementary inverse `row_add_matrix m i j (-f)`; `inv_step`
therefore shows that a row addition preserves `invertible_mod`; and `rim_iter_inv`
inducts over the fuel, so the four matrices that `mats_of` produces are invertible
modulo `q`.  No determinant is needed anywhere, and the statement is not assumed:
the old `sorry` is gone.
`VWZ_A3_Aligned` is the only session that carries obligations. The remaining
sessions are scaffolding:
- `smoke` — field and invariant smoke tests
- `skeleton` — early skeleton, kept for provenance

`neg/` holds a **negative control**: a deliberately false statement. It is
intentionally *not* listed in `ROOTS`, because a negative control must fail.
Run it on its own to confirm the toolchain really rejects falsehoods:

```bash
isabelle build -D neg   # expected: FAILED
```

## Layout

```
ROOTS                          session registry
aligned/                       the obligation-carrying session
  ROOT
  VWZ_Fq3329.thy               F_3329 as `residue_ring (int 3329)`, parameters, encoders, Sec 3.1 LCG
  VWZ_KeyGen.thy               draws, Sec 3.3 matrix generator, psi, and KeyGen
  VWZ_Matrix.thy               matrix layer: rows, cols, det (Laplace), row ops
  VWZ_Protocol.thy             protocol records and decoders
  VWZ_Aux.thy                  auxiliary lemmas (determinants, zero rows, T2_B2 support)
  VWZ_RREF.thy                 elementary row operations, fuel-counted Gauss-Jordan, rank / nullity / inverse
  VWZ_ObligationsAligned.thy   the obligation inventory, tiered T0..T3
  VWZ_Refutations.thy          machine-checked refutations of ledger statements that are false as written
skeleton/  smoke/  neg/        scaffolding sessions
tools/count.cjs                lemma / sorry counter (source of the table above)
ALIGNED-NOTES.md               working notes: what is proved, what is assumed, why
```

## Building

Requires **Isabelle2025-2** (or a compatible release).

```bash
isabelle build -D .
```

Expected output: three sessions `Finished`, exit code `0`.

To force a clean rebuild (recommended before trusting a green result):

```bash
isabelle build -c -D .
```

A successful build prints `Finished VWZ_A3_Aligned` and exits `0`.

### Environment notes

Two environment traps cost real time and are recorded here so they are not
rediscovered:

- `prime n by simp` can hang pathologically on this development. Use `by eval`.
- `isabelle build` prints `theory X 100%` for **every** theory, including ones
  that then fail. The progress line is not a success signal; check for an error
  block after the `by`.

## Honesty policy

- `sorry` counts are reported as they are. A tier is never described as
  "complete" because its easy half is done.
- Obligations whose subjects are still undefined constants are marked
  `TODO(define)` rather than proved against a placeholder.
- A definitional unfolding is not an obligation and is not counted as one; such
  lemmas live outside the ledger file, which is why the ledger count did not
  move when `mat_rank` got a body.
- `T2_B7` was recorded with a defect in its *statement*, not just a missing
  proof: `pk` ranges over every `pkey`, so once `psi_slice` is defined the
  claim is false for a slice that happens to be zero. A well-formedness
  hypothesis was missing and was noted rather than silently added on the
  obligation's behalf; with the non-zero-minor premise the statement is now
  proved (`#23`, `#24`).
- That is not a matter of opinion: `VWZ_Refutations.thy` proves the negation of
  the repaired statement, with a key of the right shape, an index in range, and
  rank 0. Refutations live outside the ledger file so they are not counted as
  obligations.
- Two obligations are explicitly **not** counted as provable: one is empirical
  (`T3_D8`), one is declared unprovable in the specification (`T3_E3b`).
- `T2_D5` is still recorded as a defect in the statement, and it is the only one
  left open. `VWZ_Refutations.thy` proves that the obligation forces the target
  bit at a support index to be message-independent, because `Eval` receives
  neither `k` nor `msg` while `pk`, `w2` and `w3` stay free — and `hash_target`
  does depend on `digest k msg`. Restating it needs a body for `Sign` and the
  linkage premises, so the `sorry` stays and is tagged as a defect. No other
  lemma uses it.
- All four defects and their evidence are collected in `VWZ_DEFECTS.md`.

## Citation

The machine-checked artefact is versioned by tag; the write-up is archived with a DOI.

Software (the Isabelle development):

- Version DOI (v1.0.1): [`10.5281/zenodo.23622795`](https://doi.org/10.5281/zenodo.23622795)
- Previous version (v1.0.0): [`10.5281/zenodo.23622178`](https://doi.org/10.5281/zenodo.23622178)
- Concept DOI (all versions): [`10.5281/zenodo.23622177`](https://doi.org/10.5281/zenodo.23622177)
- Records: <https://zenodo.org/records/23622795> (v1.0.1) and <https://zenodo.org/records/23622178> (v1.0.0)
- Object version for every number quoted in the write-up: `d984b77`

Write-up (technical note, Chinese):

- DOI: [`10.5281/zenodo.23632173`](https://doi.org/10.5281/zenodo.23632173)
- Concept DOI: [`10.5281/zenodo.23632172`](https://doi.org/10.5281/zenodo.23632172)
- Record: <https://zenodo.org/records/23632173>
- Source: `docs/papers/engineering-verification-pqc/main-zh.tex`; the deposit carries both the
  compiled PDF and that LaTeX source. The note states the full Isabelle route for the closed
  obligations (including the two-dimensional span bound behind `T2_B7`) and the analysis of
  `T2_D5`. It is a separate work with its own concept DOI, not a version of the software deposit.

Each deposit holds a `git archive` snapshot of its tag: `vwz-formalization-1.0.1.zip`
(705,989 bytes) and `vwz-formalization-1.0.0.zip` (713,177 bytes). The two versions differ
only in `LICENSE`: v1.0.0 archived the GPLv3 text while the README and every Isabelle source
header declared Apache-2.0; v1.0.1 archives the canonical Apache-2.0 text.

## License

Apache-2.0. See `LICENSE`.
