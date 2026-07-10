# Condensed Targets for TQFTs: A Lean 4 Investigation

This repository explores categorical ingredients that may be useful when placing
infinite-dimensional field theories in condensed or liquid settings. It is not
yet a formalization of a geometric topological quantum field theory.

## Building

```bash
lake exe cache get
lake build
```

The project is pinned to Lean 4 and Mathlib v4.28.0.

## Machine-checked results

- `CondensedAb` carries Mathlib's symmetric monoidal structure via
  `Sheaf.monoidalCategory`.
- `AbstractTQFT.transfer` proves composition of braided monoidal functors. The
  structure is categorical scaffolding rather than a standard Atiyah-Segal TQFT.
- `semiNormedGrpToCondensedAb : SemiNormedGrp ⥤ CondensedAb` is constructed and
  is faithful.
- The same sheaf-level functor is **not full**, witnessed by the continuous,
  unbounded summation map on `ℕ →₀ ℤ` with the sup norm.
- `SemiNormedGrp` is given finite products using finite Pi types with the sup norm.
- Commutative Frobenius algebra data and an ordinary quotient presentation
  category are defined.

## Important scope limits

- Ordinary TQFT gluing is functorial composition of bordisms; it does not require
  short exact sequences or an abelian target. Exactness may matter in additional
  derived or analytic constructions, none of which is proved here.
- The object named `Cob2Category` is currently only an ordinary category. The
  monoidal structure, symmetric coherence, geometric completeness, and free
  universal property of the actual 2-dimensional bordism category remain open.
- The repository proves a symmetric monoidal structure on `CondensedAb`, not an
  unrestricted exactness theorem for its tensor product and not the Liquid Tensor
  Experiment.
- `CondensedAb` forgets scalar linearity. In particular, a complex-linear source
  category cannot be full in `CondensedAb`; a scalar-sensitive condensed-module
  target would be needed.

## Incomplete declarations

There are 5 `sorry` placeholders across three declarations: two preservation
instances in `BanachEmbedding.lean`, and the three fields of
`CommFrobeniusData.toCob2Functor` in `Cob2.lean`. There are no explicit custom
`axiom` declarations. Any theorem depending on those placeholders should be
reported as conditional or incomplete.

See [`MATHEMATICAL_STATUS.md`](MATHEMATICAL_STATUS.md) for the detailed claim audit.

## Files

| File | Content |
|---|---|
| `LiquidTQFT.lean` | Braided monoidal scaffolding, transfer, and `CondensedAb` instances |
| `MonoidalViaLocalization.lean` | Instantiation of Riou-Asgeirsson Mathlib infrastructure |
| `BanachEmbedding.lean` | Sheaf-level functor and faithfulness; two incomplete limit-preservation instances |
| `FullnessCounterexample.lean` | Presheaf-level faithful-but-not-full counterexample |
| `SheafFullnessCounterexample.lean` | Sheaf-level non-fullness theorem |
| `Cob2.lean` | Frobenius data and an incomplete presentation related to 2d cobordisms |

## Attribution

The symmetric monoidal structure on `CondensedAb` relies entirely on Mathlib
infrastructure built by Joël Riou and Dagur Asgeirsson. Formal proof search was
assisted by Aristotle (Harmonic), with synthesis and prompt engineering by
Claude (Anthropic).

## License

MIT
