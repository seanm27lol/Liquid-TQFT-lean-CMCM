# Liquid TQFT: Formally Verified Categorical Foundations

A Lean 4 formalization investigating liquid vector spaces (Clausen-Scholze)
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
| `MonoidalViaLocalization.lean` | Sorry-free symmetric monoidal structure via localization |
| `CondensedMonoidal.lean` | Manual construction (superseded, retained for analysis) |
| `BanachEmbedding.lean` | Embedding SemiNormedGrp -> CondensedAb, faithfulness, fullness disproof |
| `Cob2.lean` | Commutative Frobenius algebras, 2d cobordism category |

## Key Results

- `MonoidalCategory CondensedAb` (sorry-free, 6 lines)
- `AbstractTQFT.transfer` (sorry-free)
- `semiNormedGrpToCondensedAb : SemiNormedGrp -> CondensedAb` (sorry-free)
- `CommFrobeniusAlgebra` and `Cob2Category` (sorry-free)
- Fullness of embedding **disproved** for SemiNormedGrp (counterexample found)

## Citation

```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

Synthesis and prompt engineering by Claude (Anthropic).
