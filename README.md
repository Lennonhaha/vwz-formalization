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
| `VWZ_A3_Aligned` | Definition layers + obligation inventory | 56 | 18 |

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
  VWZ_Fq3329.thy               F_3329 as `residue_ring (int 3329)`, parameters, encoders
  VWZ_Matrix.thy               matrix layer: rows, cols, det (Laplace), row ops
  VWZ_Protocol.thy             protocol records and decoders
  VWZ_Aux.thy                  auxiliary lemmas (determinants, zero rows, i = 0 branch)
  VWZ_ObligationsAligned.thy   the obligation inventory, tiered T0..T3
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
- Two obligations are explicitly **not** counted as provable: one is empirical
  (`T3_D8`), one is declared unprovable in the specification (`T3_E3b`).

## License

Apache-2.0. See `LICENSE`.
