# Verification record

## Toolchain

- **Lean:** 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), x86_64 Linux.
- **Mathlib:** `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- **Compile flags:** `-j1 -M12288 -DmaxHeartbeats=800000`.

## Strict kernel replay

The checker is [`checker/IndependentFVLTReplay436.lean`](checker/IndependentFVLTReplay436.lean), sha256 `c5d0b3ca719c36ea6939e0108469fe3597e9906c6fa7892f4f45481e055f548f`. It runs as `lean --run IndependentFVLTReplay436.lean <Module>`. It replays every constant of the target module through the kernel, reusing the compiled dependencies (`fullDependencyReplay = false`), and reports axioms, partial constants and unsafe constants.

| Module | Source sha256 | Compile | Replay | Constants | Partial / unsafe | Axioms | Verdict |
|---|---|---:|---:|---:|---:|---|---|
| `Verified` | `297cc745…b084536` | 293.54 s | 1,527.82 s | 3,325 | 0 / 0 | propext, Classical.choice, Quot.sound | **PASS** |
| `CoherentEnergyMeasure` | `581ccf72…40a903` | 8.48 s | 28.05 s | 168 | 0 / 0 | the same | **PASS** |
| `CoherentEnergyRHBridge` | `572e70e7…150695a5`* | 1.77 s | 6.97 s | 9 | 0 / 0 | the same | **PASS** |

\* The full source hashes are in `../SHA256SUMS.txt`.

**Log hashes:**
- `strict436_Verified.log`: `b0c7089a…f1b20de2`
- `strict436_CoherentEnergyMeasure.log`: `0abc105a…4140f69`
- `strict436_CoherentEnergyRHBridge.log`: `df87a68c…150695a5`

The logs are the checker's JSON output. Each lists every audited declaration with its axioms.

## Statement review

- **Read against the paper's definitions and theorems:**
  - the principal equivalences in `Verified`;
  - the definitions and headline statements of `CoherentEnergyMeasure` and `CoherentEnergyRHBridge`.
- **Covered by the kernel replay only:** internal lemmas.
- **Not read one by one:** about 1,000 auxiliary theorems in `Verified`, outside the principal equivalences.

## Finite controls (historical)

Before the measure side was formalised, the October 2026 construction was checked by exact rational arithmetic at B = 91: 9,291 checks over 578 configurations, with cutoffs up to X = 1000.
- Its inputs were `HANDOFF_FORMULAS.json` (`105847a3…`) and `CHECK_RESULTS.json` (`c88a6d10…`).
- Its checker was `check_growth.py` (`73084c1d…`).
- These are not included here, because the checker depends on its original bundle. The identity they checked is now proved in Lean for every B ≥ 1.

## Build check from this repository

On 2026-11-23 this repository was built from a fresh copy with `lake exe cache get`, then `lake build`.
- **Result:** "Build completed successfully (4087 jobs)", exit code 0, 0 errors, 2 min 30 s.
- **Warnings:** 514, all from linters (for example unused tactics); none is a proof error.
- **Timings:** `Verified` 147 s, `CoherentEnergyMeasure` 7.8 s, `CoherentEnergyRHBridge` 1.8 s.
- **Mathlib:** the pinned commit came from the public Mathlib cache.
- **Log:** [`lake_build_fresh.log`](lake_build_fresh.log), sha256 `6a0046e7f271f7972d8a3f505b86799e25d97d6fed950682efecef12c269c185`.
- **Pins:** `lake-manifest.json` records the exact revision of Mathlib and of each of its dependencies.

This build checks that the sources compile. The kernel replays above check the proof terms and axioms.

## The PDF

`paper/paper.pdf` (full edition v0.3.3.2) was built on 2026-11-23 from `paper/paper.tex` (sha256 `4e35827c…f6e7dde1`) with Tectonic 0.17.0, the official x86_64 Linux release, whose archive sha256 was checked against the release's published digest.
- **Result:** exit code 0; 15 pages; 0 overfull and 0 underfull boxes; no undefined references.
- **TeX log:** [`tectonic_paper.log`](tectonic_paper.log), sha256 `8d5dd331…4cf24518`.
- **PDF:** sha256 `e7e6d3bdd6ca3b428232047b4743acac856da1561080870bdb5c462c5c3579da`.

`paper/simple/simple.pdf` (simplified edition v0.1.4) was built the same way: 4 pages, 0 overfull and 0 underfull boxes.

## Independent checks

Three further checks, run on commit `b633d91` and re-run in full on `2d60e22`, are recorded in [`independent_checks/INDEPENDENT_CHECKS.md`](independent_checks/INDEPENDENT_CHECKS.md):
- **Statement pins:** `StatementPins.lean` restates seven headline results using definitions written from scratch in plain Mathlib, and proves them. All compile with standard axioms only.
- **`leanchecker`:** Lean's own replay of all four modules. PASS.
- **`nanoda`:** an independent Rust kernel. It re-checked the full dependency closure of the pins, 64,601 declarations including Mathlib, with no errors and only the standard axioms. PASS.
