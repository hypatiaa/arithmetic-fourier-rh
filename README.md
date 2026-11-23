# Arithmetic Fourier energy and the Riemann Hypothesis, in Lean 4

saphir's arithmetic Fourier instrument for the Möbius function, and a Lean 4 / Mathlib formalisation of its equivalences with the Riemann Hypothesis.

## The construction

- **Phasors.** Each prime p gets a unit phasor z_p. Set Z(n) = ∏ z_p^{v_p(n)}.
- **The polynomial.** A Möbius divisor lift with an inclusion–exclusion window modulo B gives a trigonometric polynomial D_{X,B}.
- **The measure.** Under the product Poisson measure with radius 1/p on each prime's circle, the modes Ψ_r = ∏ (z_p^a − p^{−1} z_p^{a−1}) are orthogonal, with ‖Ψ_r‖² = j(r) = ∏_{p|r} (1 − p^{−2}).
- **The energy.** The squared norm of D_{X,B} is a positive sum of squares of a single scalar:

  ‖D_{X,B}‖²_ν = Σ_{r ≤ X, (r,B)=1} j(r) · S_B(⌊X/r⌋)²,  with S_B(t) = Σ_{k ≤ t, (k,B)=1} M(t/k)/k.

## What Lean proves

All of the following are kernel-checked with no `sorry`, and use only `propext`, `Classical.choice` and `Quot.sound`. Strict replay records are in [`verification/`](verification/).

Three independent routes check this:
- **Kernel replay:** our own replay checker, and Lean's `leanchecker`.
- **An independent kernel:** `nanoda`, written in Rust, re-checked the 64,601 declarations behind the headline results.
- **Statement pins:** each pin in [`StatementPins.lean`](StatementPins.lean) states a headline result independently in Mathlib terms, and Lean checks that the development proves that statement.

- **Exact inversion, for every modulus B.** S_B and the Mertens function M determine each other; M = O(n^θ) ⇔ S_B = O(n^θ).
  - `g_convolution_h`, `S_from_M`, `M_from_S`, `M_power_bound_iff_S`
- **The energy identity, for every B ≥ 1.** The Poisson measure gives Gram kernel gcd(d,e)²/(de); the Ψ_r are orthogonal; and ∫ ‖D_{X,B}‖² dν equals the energy above.
  - `innerNu_Z`, `innerNu_Psi`, `norm_sq_D_eq_energy`, `norm_sq_D_eq_coherent_energy`
- **The RH equivalence.** RH ⇔ for every δ > 0, ‖D_{X,B}‖²_ν ≤ C_δ X^{1+δ} for all X ≥ 1. There is the same statement for every zero-free half-plane Re s > a, and the same with the energy sum in place of the norm.
  - `coherent_energy_measure_growth_iff_RH`, `coherent_energy_growth_iff_RH`, `fixed_strip_iff_coherent_energy_measure_power`
- **One sign is enough.** For either fixed sign σ: RH ⇔ eventually σ·S_B(n) ≥ −C_ε n^{1/2+ε}, for every ε > 0.
  - `rh_iff_one_sided_fourier_scalar`
- **The classical Mertens criterion, both directions.**
  - `mertens_cancellation_iff_RH`

**What this is not.** Every result is an equivalence or an identity. No growth bound is proved: the estimate ‖D_{X,B}‖²_ν ≪ X^{1+δ} is exactly as hard as RH.

The ζ function and `RiemannHypothesis` are Mathlib's own definitions.

Some modules take Ingham's zero-density estimate as an explicit hypothesis (`ZetaDensityPremise`). The results above do not use it.

## Layout

| Path | Contents |
|---|---|
| `Verified.lean` | the main development: 1,074 theorems, assembled from 335 fragments |
| `CoherentEnergyMeasure.lean` | the Poisson measure and the energy identity |
| `CoherentEnergyRHBridge.lean` | identification with `Verified` and the measure-norm RH criteria |
| `fragments/` | the 335 source fragments, plus `assemble.py`, which rebuilds `Verified.lean` exactly |
| `paper/` | the write-up (Markdown, LaTeX, HTML) |
| `verification/` | compile and strict replay logs, the replay checker, and `VERIFICATION.md` |
| `scripts/verify_release.py` | checks this release's hashes, replay verdicts and the reassembly |

## Build

The project uses Lean 4.35.0 with Mathlib pinned in `lakefile.toml`.

```
lake exe cache get
lake build
```

To check the release files without Lean: `python scripts/verify_release.py`.

## Credits

- **saphir:** the arithmetic Fourier construction (prime phasors, the Möbius lift and window, the Poisson measure, the modes Ψ_r, the scalar S_B and its inverse, and the energy identity), and the direction of the work.
- **The formalisation:** Codex wrote the main Lean development. Gemini formalised the measure modules and assembled the release. Claude (Fable and Opus) did the independent compilation, the statement audits and the prior-art review. The write-up gives the details.
- **Prior art:**
  - The Poisson Gram kernel gcd(d,e)²/(de) belongs to the GCD-sum literature: Aistleitner–Berkes–Seip, JEMS 2015, and earlier work of Hedenmalm, Lindqvist, Seip and Hilberdink.
  - The two-sided and one-sided criteria are in the lineage of Mertens, Landau and Littlewood.
  - See the write-up, §7.

## Licence

- Lean sources and scripts: Apache License 2.0 ([`LICENSE`](LICENSE)).
- The write-up in `paper/`: Creative Commons Attribution 4.0 ([`LICENSE-DOCS.md`](LICENSE-DOCS.md)).

No external peer review is implied.
