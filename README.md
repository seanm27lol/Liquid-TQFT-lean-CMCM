# Liquid TQFT: Formally Verified Categorical Foundations

A Lean 4 formalization investigating condensed abelian groups (Clausen-Scholze)
as a target category for topological quantum field theories.

## Building

```
lake exe cache get
lake build
```

Requires Lean 4 with Mathlib v4.28.0.

## Files

| File | Content |
|------|---------|
| `LiquidTQFT.lean` | Abstract TQFT framework, transfer theorem, monoidal CondensedAb |
| `MonoidalViaLocalization.lean` | Symmetric monoidal structure via localization (Riou-Asgeirsson) |
| `BanachEmbedding.lean` | Sheaf-level embedding SemiNormedGrp -> CondensedAb, faithfulness |
| `FullnessCounterexample.lean` | Presheaf-level embedding: faithful but not full (machine-checked) |
| `Cob2.lean` | Commutative Frobenius algebras, 2d cobordism category |

## Status

5 active files. 5 sorries (2 in BanachEmbedding, 3 in Cob2). 0 custom axioms.

## Key Results

- `MonoidalCategory CondensedAb` (sorry-free, via `Sheaf.monoidalCategory`)
- `AbstractTQFT.transfer` (sorry-free)
- `semiNormedGrpToCondensedAb : SemiNormedGrp -> CondensedAb` (sorry-free)
- Sheaf-level embedding is faithful (sorry-free)
- Presheaf-level embedding is faithful but **not full**, both machine-checked (sorry-free)
- `CommFrobeniusAlgebra` and `Cob2Category` (sorry-free)
- `SemiNormedGrp.hasFiniteProducts` (sorry-free, new to Mathlib)

## Attribution

The symmetric monoidal structure on CondensedAb relies entirely on Mathlib
infrastructure built by Joel Riou and Dagur Asgeirsson.

## Citation

Co-authored-by: Aristotle (Harmonic). Synthesis and prompt engineering by Claude (Anthropic).

## License

MIT
