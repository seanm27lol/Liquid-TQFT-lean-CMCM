# Liquid TQFT: Formally Verified Categorical Foundations

A Lean 4 formalization investigating liquid vector spaces (Clausen-Scholze)
as a target category for topological quantum field theories.

(check out cool scholze comment in recent quanta magazine article about condensed math, same idea?? ;)
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
| `BanachEmbedding.lean` | Embedding SemiNormedGrp -> CondensedAb, faithfulness, fullness disproof |
| `Cob2.lean` | Commutative Frobenius algebras, 2d cobordism category |

## Status

4 active files. 3 sorries (2 in BanachEmbedding, 1 in Cob2). 0 custom axioms.

## Key Results

- `MonoidalCategory CondensedAb` (sorry-free, via `Sheaf.monoidalCategory`)
- `AbstractTQFT.transfer` (sorry-free)
- `semiNormedGrpToCondensedAb : SemiNormedGrp -> CondensedAb` (sorry-free)
- `semiNormedGrpToCondensedAb_faithful` (sorry-free)
- Fullness of embedding **disproved** for SemiNormedGrp (counterexample found)
- `CommFrobeniusAlgebra` and `Cob2Category` (sorry-free)
- `SemiNormedGrp.hasFiniteProducts` (sorry-free, new to Mathlib)

## Attribution

The symmetric monoidal structure on CondensedAb relies entirely on Mathlib
infrastructure built by Joel Riou and Dagur Asgeirsson.

## Citation

```
Co-authored-by: Aristotle (Harmonic)
```

Synthesis and prompt engineering by Claude (Anthropic).

## License

MIT
