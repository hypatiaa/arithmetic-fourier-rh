# Independent checks (2026-11-23)

These checks were first run on a fresh clone of commit `b633d91` plus `StatementPins.lean`, and re-run in full on commit `2d60e22`, which narrowed the header comment of `StatementPins.lean`. Both runs used Lean 4.35.0 and the pinned Mathlib. They add two kinds of evidence to the replay records in `../VERIFICATION.md`:

- **Different checkers:** Lean's own `leanchecker`, and `nanoda`, a type checker written separately in Rust.
- **The statements:** `StatementPins.lean` checks what the theorems say, not only whether their proofs are valid.

## 1. Statement pins (`StatementPins.lean`, sha256 `af9f8ee7…a494e2`)

**What the file does.**
- It defines from scratch, using only Mathlib, the Mertens function, saphir's scalar S_B, the weights j(r), the energy, the Poisson measure ν and the polynomial D_{X,B}. No definition from this repository is used.
- It states seven results with those definitions and Mathlib's `_root_.RiemannHypothesis` and `riemannZeta`, and proves each from the repository's theorem:

| Pin | Statement |
|---|---|
| `pin_inverse` | M(n) = Σ_{k ≤ n} [gcd(k,B)=1] μ(k)/k · S_B(⌊n/k⌋) |
| `pin_energy_identity` | ∫ ‖D_{X,B}‖² dν = Σ_{r ≤ X, (r,B)=1} j(r) S_B(⌊X/r⌋)², for B ≥ 1 |
| `pin_rh_iff_energy` | RH ⇔ ∀δ>0 ∃C≥0 ∀X≥1, energy ≤ C·X^{1+δ} |
| `pin_rh_iff_norm` | RH ⇔ ∀δ>0 ∃C≥0 ∀X≥1, ∫ ‖D_{X,B}‖² dν ≤ C·X^{1+δ}, for B ≥ 1 |
| `pin_rh_iff_one_sided` | RH ⇔ ∀ε>0 ∃C≥0, eventually σ·S_B(n) ≥ −C·n^{1/2+ε} (σ = ±1) |
| `pin_strip_iff_scalar` | no zeros of ζ on Re s > a ⇔ ∀ε>0, \|S_B(n)\| ≤ C·n^{a+ε} (½ ≤ a < 1) |
| `pin_rh_iff_mertens` | RH ⇔ ∀ε>0, Σ_{n ≤ ⌊x⌋} μ(n) = O(x^{1/2+ε}) |

**Result:**
- All seven compile, and `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for each.
- The independently written ν and D_{X,B} are equal to the repository's by `rfl`, that is, definitionally.

**What this buys.** Each pin states a headline result independently in Mathlib terms, and Lean checks that the development proves that statement.

## 2. Lean's `leanchecker`

```
lake env leanchecker Verified CoherentEnergyMeasure CoherentEnergyRHBridge StatementPins
```

**Result:** exit code 0 in 32 s, with no errors. Log: [`leanchecker.log`](leanchecker.log).

`leanchecker` ships with Lean 4.35.0. It replays every declaration of the named modules through Lean's kernel. This is a second replay route besides our own checker (`../checker/IndependentFVLTReplay436.lean`).

## 3. `nanoda`, an independent Rust kernel

```
lake env leanexport StatementPins -- <the seven pins>     # 468 MB export
nanoda_bin nanoda_config.json
```

**Result:** "Checked 64601 declarations with no errors", exit code 0, 41 s. Log: [`nanoda.log`](nanoda.log).

**Configuration** ([`nanoda_config.json`](nanoda_config.json)): only `propext`, `Classical.choice` and `Quot.sound` are permitted. Any other axiom actually used would have stopped the check.

**Scope.** The export holds the full dependency closure of the seven pins: every declaration they use, from this repository and from Mathlib and Lean's core.
- Theorems of `Verified` that the pins do not depend on are outside that closure. They are covered by the two kernel replays above.
- A first attempt exported the entire environment (3.1 GB). nanoda ran out of memory on it (28 GB), so that run was inconclusive. It is not counted as either a pass or a failure.

**The statements as nanoda reads them.** [`nanoda_pp.txt`](nanoda_pp.txt) has nanoda's own pretty-print of the four main pins and three definitions. For example:

```
theorem StatementPins.pin_rh_iff_norm :
  forall {B : Nat}, LE.le (OfNat.ofNat 1) B → Iff RiemannHypothesis
    (forall (δ : Real), LT.lt (OfNat.ofNat 0) δ → Exists (fun (C : Real) =>
      And (LE.le (OfNat.ofNat 0) C) (forall (X : Nat), LE.le (OfNat.ofNat 1) X → LE.le
        (MeasureTheory.integral StatementPins.nu (fun θ => ‖StatementPins.poly B X θ‖ ^ 2))
        (C * X ^ (1 + δ)))))
```

(The last three lines are abbreviated here; the file has the exact text.)

## Hashes

- `leanchecker.log` (re-check of `2d60e22`): `abf1f26a45f0db26d37769a7ae484aaf98420dd64edec67ee8e865833816b3a4`
- `nanoda.log` (re-check of `2d60e22`): `be83c8a8d1de29daa994d68159ffcf34a1413d729f80b84d13495a922bb350d7`
- `nanoda_pp.txt`: `3243262a576fd6d398572263fe213eafd10f2d5a6bf9984bcf1f84a3389b7816`
- the export (not shipped, 468 MB): `1813ece96f59b0ab3fe50baac34a93a9a1b22cfc1fbb37ca136e15e84a59cb64`

## Re-check after the comment change (commit `2d60e22`)

`StatementPins.lean` changed only in its header comment: sha256 `33e38ace…7604225` became `af9f8ee7d80e58c608db3c7adbc17ca15292e8487fc33cd7c4c2e23439a494e2`. The whole chain was re-run on a fresh clone of that commit:
- **`lake build`:** 4,089 jobs, exit 0; all seven pins report only `propext`, `Classical.choice` and `Quot.sound`.
- **`leanchecker`:** all four modules, exit 0.
- **`leanexport` of the seven pins:** byte-identical to the first run, sha256 `1813ece9…a59cb64`, 468,107,587 bytes. A comment change leaves every declaration unchanged, and the identical export shows that directly.
- **`nanoda`:** "Checked 64601 declarations with no errors", exit 0. Its statement printout is identical to the first run (`3243262a…`).

The logs in this folder are from the re-check.
