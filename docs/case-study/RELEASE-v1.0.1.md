# v1.0.1 — release notes

> **Status: published 2026-10-25.** Tag `v1.0.1` = `c06c9bb`; archived at DOI
> [`10.5281/zenodo.23622795`](https://doi.org/10.5281/zenodo.23622795)
> (concept DOI `10.5281/zenodo.23622177`, record <https://zenodo.org/records/23622795>).

## Why this version exists

`v1.0.0` archived a tree whose `LICENSE` file carried the **GNU GPL v3** text, while the README
said "Apache-2.0. See `LICENSE`." and all 19 Isabelle theory files carried
`SPDX-License-Identifier: Apache-2.0`. Both the file and the headers date from the first commit
(`cc297ca`), so the contradiction had been in the repository from the start; publishing the DOI
made it visible, because Zenodo reads the licence from the `LICENSE` file.

Version 1.0.1 resolves it in favour of Apache-2.0 — the licence the sources and the README
already declared, and the one the neighbouring tool and benchmark repositories use.

## What changed

| | v1.0.0 (tag `4f81346`) | v1.0.1 (tag `c06c9bb`) |
|---|---|---|
| `LICENSE` | GPLv3 text, 33,779 bytes | canonical Apache-2.0 text, 11,358 bytes, sha256 `cfc7749b…` |
| Everything else | — | unchanged |

No theory, proof, or measurement changed. The ledger is the same: **56 obligations, 6 registered
`sorry`, 0 outside**; 20 Isabelle theories, 582 lemmas (tracked-file counts). All numbers in the
write-ups remain those of commit `d984b77`.

## Provenance

| | |
|---|---|
| Tag | `v1.0.1` → commit `c06c9bb` (annotated tag object) |
| Archive | `vwz-formalization-1.0.1.zip`, 705,989 bytes, md5 `afcf39e8536c10285ed4ecd33f51ec52` |
| Version DOI | `10.5281/zenodo.23622795` |
| Concept DOI | `10.5281/zenodo.23622177` (unchanged; resolves to the latest version) |
| Previous version | `v1.0.0`, `4f81346`, DOI `10.5281/zenodo.23622178` — stays published and citable |

## Verification

```
git archive v1.0.1 → zip → LICENSE 11,358 B, sha256 cfc7749b…, no "GNU GENERAL PUBLIC LICENSE"
node .github/scripts/check-encoding.cjs  → 36 tracked text files OK
node tools/count-obligations.cjs         → 56 ledger lemmas, 6 sorry, outside 0
```

The Zenodo record for this version declares `apache2.0` (legacy id for Apache License 2.0) and
points its `isSupplementTo` identifier at `tree/v1.0.1`. The v1.0.0 record keeps `gpl-3.0`, which
is what its own archive contains.
