# Condensed Targets for TQFTs: A Lean 4 Investigation

This repository contains the paper and a synchronized Lean 4 formalization of
categorical ingredients for placing topological field theories in condensed or
liquid settings. It does not yet formalize a geometric TQFT.

**Status: proof-placeholder-free.** 12 Lean source files, approximately 4,700
lines, no executable proof-admission placeholders, and no custom axioms. Every
listed formal result is machine-checked against Mathlib v4.28.0.

## Building

```bash
lake exe cache get
lake build
```

The repository's `Build Lean 4` workflow runs the full `lake build` target.

## Files

| File | Content |
|------|---------|
| `LiquidTQFT.lean` | Abstract TQFT framework, transfer theorem, monoidal `CondensedAb` |
| `MonoidalViaLocalization.lean` | Symmetric monoidal structure via localization |
| `BanachEmbedding.lean` | `SemiNormedGrp -> CondensedAb`: faithfulness and finite-limit preservation |
| `FullnessCounterexample.lean` | Presheaf-level functor: faithful but not full |
| `SheafFullnessCounterexample.lean` | Non-fullness for the sheaf-level embedding |
| `EmbeddingProfile.lean` | Failure to reflect isomorphisms and preserve epimorphisms |
| `Cob2.lean` | Base Frobenius presentation and ordinary interpretation functor |
| `DijkgraafWitten.lean` | Rank-`n` diagonal Frobenius datum and torus/genus-word evaluations |
| `Cob2Monoidal.lean` | Lawful monoidal quotient and strong monoidal interpretation |
| `Cob2Symmetric.lean` | Symmetric quotient and strong braided monoidal interpretation |
| `DijkgraafWittenSymmetric.lean` | Base-to-symmetric functor bridge, packaged diagonal theory, and transported torus/genus evaluations |
| `Ribbon.lean` | Balanced/ribbon categories, quantum trace, dimension, and S-pairing |

## Machine-checked results

- `CondensedAb` carries Mathlib's symmetric monoidal structure via
  `Sheaf.monoidalCategory`.
- `AbstractTQFT.transfer`: braided monoidal functors preserve TQFT structure.
- The realization `semiNormedGrpToCondensedAb : SemiNormedGrp -> CondensedAb`
  is additive, faithful, and left exact, but not full, not conservative, and
  not right exact; every negative clause has an explicit counterexample.
- `SemiNormedGrp.hasFiniteProducts`.
- A base combinatorial Frobenius presentation and its interpretation in any
  braided monoidal target.
- A rank-`n` diagonal commutative Frobenius datum on `Fin n -> ℤ`; its torus
  and every connected genus word in the defined family act by multiplication
  by `n` on the monoidal unit.
- A strengthened lawful monoidal quotient with a strong monoidal
  interpretation.
- A symmetric monoidal quotient imposing swap naturality, involutivity, and
  both hexagons; every commutative Frobenius datum in a symmetric target gives
  a strong braided monoidal interpretation, packaged as `toSymmetricTQFT2d`.
- The composite base-to-symmetric quotient functor recovers the original
  interpretation for every commutative Frobenius datum in a symmetric target.
- `frobZnSymmetricTQFT n` packages the diagonal datum on the symmetric
  quotient; `symmetricTorus` and every `symmetricGenus g` map to
  `(n : ℤ) • 𝟙`, hence evaluate at `1` to `n`.
- In every ribbon category, quantum trace is cyclic, quantum dimension is
  multiplicative under tensor product, and the S-pairing is symmetric.

## Important scope limits

- The tensor product on `CondensedAb` is the ambient sheaf tensor, not the
  liquid tensor product; no exactness of tensoring is claimed.
- `Cob2.lean` remains the ordinary base quotient. `Cob2Monoidal.lean` and
  `Cob2Symmetric.lean` close its algebraic interchange and braiding gaps, but
  no normal-form theorem, universal classification property, or equivalence
  with geometric oriented bordisms is claimed.
- The diagonal model is a finite-state Frobenius toy theory on an algebraic
  presentation. Its closed classes are now transported through the symmetric
  quotient, but they are not thereby geometric surface invariants, and the
  model is not the conventional finite-group/cocycle Dijkgraaf-Witten
  state-sum construction.
- `Ribbon.lean` supplies abstract input-side ribbon identities; it does not
  construct a modular tensor category or Reshetikhin-Turaev invariant.
- Results are universe-local in Mathlib's condensed conventions.

## Repository relationship

This repository mirrors the Lean sources used by the paper. The canonical
implementation repository is
[`Liquid-TQFT-CMCM-cont.`](https://github.com/seanm27lol/Liquid-TQFT-CMCM-cont.),
with the synchronized results based on commit `820dfa3`.

## Attribution

The symmetric monoidal structure on `CondensedAb` relies on Mathlib
infrastructure built by Joël Riou and Dagur Asgeirsson. Formal verification
was assisted by Aristotle (Harmonic) and ANT/OAI

## License

MIT
