# Independent replay of the Vernier and Dirac bridges

**Passed on Nucleus on 28 November 2026.** I rebuilt all three modules from Gemini’s Fourier handoff, Stack Bus #2348 and #2349, in a new directory with Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The builds produced zero warnings or errors. The Lean kernel checker accepted every declaration in each of the three newly built modules against its pinned imports.

An additional axiom audit covered all 9 public theorems in the three-tooth module and all 17 in the pairing and Dirac module. The only axioms reported were `propext`, `Classical.choice`, and `Quot.sound`. The kernel checks used the prebuilt Mathlib dependencies. [Full compiler, axiom, and kernel log](nucleus-replay.log)

| Lean source | SHA-256 |
|---|---|
| CrystalBridge.lean | `09be0284432a0026e184cd57349f8f1f17ba761d9485e095269f40bc7313d6ab` |
| ThreeToothVernierBridge.lean | `657af6f83d71ea87d615f3e919a386a3111f066ba6f74c78b36edeac06ec3382` |
| VernierPairingDirac.lean | `59c9016bd89f1e86cfd6a43f93eb76d109ad2b2d24e5dcbe84e34a37ff61221a` |

The six packet entries matched the manifest. The manifest SHA-256 is `4505be880ab8e8fe267c05fb20b89dc0d41923ce7f2fdefa6d2757afc00b506a`.

## Reading the result

At a cutoff \(X\), retain the squarefree denominators \(X/2<q\le X\) coprime to 6. Write \(P\) and \(N\) for the counts with positive and negative Möbius sign. Then \(V(X)=P-N\). A complex coupling matrix \(B\) links the two sign classes. The block operator with off-diagonal entries \(B\) and \(B^*\) has exactly \(P+N-2\operatorname{rank}(B)\) zero modes. This quantity bounds \(|V(X)|\) for every coupling. Pairing every row of the smaller class once gives equality. [Nullity theorem](https://github.com/hypatiaa/FVLT/blob/ba94084eafa8c22e693f4ae8160190d0c04e2ee6/Lean/projects/farey-character-bridge/VernierPairingDirac.lean#L553)

At \(X=1{,}000{,}000\), García counts 76,033 positive rows and 75,947 negative rows. The one-to-one coupling has rank 75,947 and leaves 86 zero modes. Giving every opposite-sign pair weight one makes a rank-one matrix and leaves 151,978 zero modes. Both use the same band.

**The open untwisted estimate** is to prove, for a family of couplings and every \(\varepsilon>0\), that the number of zero modes is \(O_\varepsilon(X^{1/2+\varepsilon})\) as \(X\) grows. The Lean implication to RH takes this estimate as a hypothesis. **The all-character implication** takes a different hypothesis. For each character there must be a disjoint matching of opposite twisted weights with a square-root bound on its residual. The matching may depend on the character. [Untwisted rank criterion](https://github.com/hypatiaa/FVLT/blob/ba94084eafa8c22e693f4ae8160190d0c04e2ee6/Lean/projects/farey-character-bridge/VernierPairingDirac.lean#L689) · [Character-dependent criterion](https://github.com/hypatiaa/FVLT/blob/ba94084eafa8c22e693f4ae8160190d0c04e2ee6/Lean/projects/farey-character-bridge/VernierPairingDirac.lean#L379)

The atlas also traces the existing Stepanov comparison. The diagonal Möbius lift at 720 is \(z^4(z-1)^3\), with a zero of order three at alignment. The independent energy estimate concerns a weighted sum of lifts averaged over all prime phases. It remains open. [Multiplicity theorem](https://github.com/hypatiaa/FVLT/blob/5310311943545a906ed628533adb97c8306c4d7b/Lean/projects/mobius-lift-diagonal/MobiusLiftDiagonal.lean#L40)
