# VWZ Formalization

Machine-checked proofs for the **VWZ** construction (Kyber-style, over the prime
field `F_3329`), developed in **Isabelle/HOL**.

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
| `VWZ_A3_Aligned` | Definition layers + obligation inventory | 56 | 11 |

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

`hash_target` and `rows3_of` stay uninterpreted on purpose. A hash needs a digest
function this session does not have, and `rows3` needs the secret `lambda_c`,
`M3` and the split point; a placeholder that ignored them would turn the lemmas
into statements about a made-up matrix.

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

What is still open is T2_B3: that the four generated matrices are invertible.
The definitions make the claim well-posed, and the reason it is true (row
additions only, so determinant 1) is visible in the code.  The algebraic
foundation the bridge needs now exists: `VWZ_MatAlgebra` proves the exchange of
summation order (`swap_idx`), the index form of a product entry (`entry_mult`),
and associativity of `mat_mult` in the square case (`mat_mult_assoc_square`).
The row-operation bridge turned out not to be missing but false as stated:
`add_row_mult` reduces entries modulo `q`, while `mat_mult` does not, so
left-multiplying by an elementary matrix differs from the row operation by one
reduction (machine-checked in `VWZ_Probe`). T2_B3 is therefore in restatement
over `F_q`, and it stays `sorry` until that lands.

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
- `T2_B7` is recorded with a defect in its *statement*, not just a missing
  proof: `pk` ranges over every `pkey`, so once `psi_slice` is defined the
  claim is false for a slice that happens to be zero. A well-formedness
  hypothesis is missing and is noted rather than silently added on the
  obligation's behalf.
- That is not a matter of opinion: `VWZ_Refutations.thy` proves the negation of
  the repaired statement, with a key of the right shape, an index in range, and
  rank 0. Refutations live outside the ledger file so they are not counted as
  obligations.
- Two obligations are explicitly **not** counted as provable: one is empirical
  (`T3_D8`), one is declared unprovable in the specification (`T3_E3b`).

## License

Apache-2.0. See `LICENSE`.
