# VWZ Formalization

Machine-checked proofs for the **VWZ** construction (Kyber-style, over the prime
field `F_3329`), developed in **Isabelle/HOL**.

This repository is deliberately separate from the FIBEMATE business
repositories: formal methods artifacts have a different build toolchain
(Isabelle), a different release cadence, and a much larger footprint than the
product code. Keeping them apart keeps both sides honest.

## Status

The formalization is **work in progress**. Proof obligations are tracked in
tiers; the counts below are generated, not asserted.

| Session | Content | Lemmas | `sorry` |
|---|---|---|---|
| `VWZ_A3_Aligned` | Definition layers + obligation inventory | 56 | 16 |

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

What is *not* proved is termination of rejection sampling, and that gap is
visible in the type. `SeedRng` is declared `nat => nat list`, a finite list,
while the algorithm needs an unbounded stream; the definitions therefore use
the state-passing form and the constant is left in place until that type is
changed. T3_B1 stays unconditional in the ledger and stays `sorry`; weakening
it until it became provable would have been the wrong kind of progress.

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
  VWZ_KeyGen.thy               draws and distinct evaluation points, with partial correctness
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
