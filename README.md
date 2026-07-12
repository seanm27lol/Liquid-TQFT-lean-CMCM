# Condensed Targets for TQFTs: A Lean 4 Investigation

This repository explores categorical ingredients that may be useful when placing
infinite-dimensional field theories in condensed or liquid settings. It is not
yet a formalization of a geometric topological quantum field theory.

**Status: the formalization is complete and sorry-free.** 7 files, approximately
2250 lines of Lean 4, 0 sorry placeholders, 0 custom axioms. Every stated result
is machine-checked. Last audited against the source: this revision.

[needs to be updated ;)]

## Building

```bash
lake exe cache get
lake build
```

The project is pinned to Lean 4 and Mathlib v4.28.0. Pull requests are checked by
the repository's `Build Lean 4` workflow, which runs the full `lake build` target.

## Files

| File | Content |
|------|---------|
| `LiquidTQFT.lean` | Abstract TQFT framework, transfer theorem, monoidal CondensedAb |
| `MonoidalViaLocalization.lean` | Symmetric monoidal structure via localization (Riou-Asgeirsson) |
| `BanachEmbedding.lean` | Embedding SemiNormedGrp -> CondensedAb: faithfulness, finite products, equalizers |
| `FullnessCounterexample.lean` | Presheaf-level functor: faithful but not full |
| `SheafFullnessCounterexample.lean` | Non-fullness for the sheaf-level embedding itself |
| `EmbeddingProfile.lean` | Does not reflect isomorphisms; does not preserve epimorphisms |
| `Cob2.lean` | Commutative Frobenius data, presentation quotient, induced functor |

## Machine-checked results

- `CondensedAb` carries Mathlib's symmetric monoidal structure via
  `Sheaf.monoidalCategory` (assembling infrastructure due to Joel Riou and
  Dagur Asgeirsson).
- `AbstractTQFT.transfer`: braided monoidal functors preserve TQFT structure.
- An embedding functor `semiNormedGrpToCondensedAb : SemiNormedGrp -> CondensedAb`,
  with no such connection previously packaged in Mathlib v4.28.0.
- A complete structural profile of this embedding, every clause machine-checked:
  **additive, faithful, and left exact (preserves all finite limits), but not
  full, not conservative, and not right exact.** Witnesses: an unbounded
  continuous additive map (summation on finitely supported integer sequences,
  whose sup-norm topology is discrete); two discrete norms on the same group;
  a discrete-to-euclidean quotient admitting no local lifts.
- `SemiNormedGrp.hasFiniteProducts` (not previously in Mathlib).
- Commutative Frobenius data, a combinatorial quotient category presented by the
  Frobenius generators and equations, and the functor it receives from any
  commutative Frobenius datum.

## Important scope limits

- The tensor product formalized on `CondensedAb` is the ambient sheaf tensor,
  not the liquid tensor product; no exactness of tensoring is claimed.
- The `Cob2` quotient imposes the category axioms and Frobenius equations only;
  tensor interchange, monoidal coherence on morphisms, and braiding naturality
  are not imposed, so it is a preliminary presentation, coarser than a full
  presentation of the 2-dimensional cobordism category, and the induced functor
  is an ordinary (not symmetric monoidal) functor.
- Results are universe-local in Mathlib's condensed conventions.
- No specific physical TQFT is constructed.

See `MATHEMATICAL_STATUS.md` for the claim-by-claim audit.

## Attribution

The symmetric monoidal structure on CondensedAb relies entirely on Mathlib
infrastructure built by Joel Riou and Dagur Asgeirsson. Formal verification
assisted by Aristotle (Harmonic); synthesis and prompt engineering by Claude
(Anthropic).

## License

MIT
