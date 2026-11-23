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
