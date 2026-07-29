# Condensed Targets for TQFTs: A Lean 4 Investigation

This repository contains the paper and a synchronized Lean 4 formalization of
categorical ingredients for placing topological field theories in condensed or
liquid settings. It does not yet formalize a geometric TQFT.

**Status: proof-placeholder-free.** At the checkpoint documented here, the
canonical implementation comprises 15,082 lines across 40 Lean source
files—39 under `RequestProject` plus `Ribbon.lean`—with no executable
proof-admission placeholders and no custom axioms. Every listed formal result
is machine-checked against Mathlib v4.28.0.

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
| `DijkgraafWittenDisconnected.lean` | Tensor-product evaluations for disconnected closed presentation words |
| `Cob2Canonical.lean` | Canonical Frobenius generator and reconstruction of the symmetric algebraic source |
| `Cob2Spider.lean` | Ordered connected spiders and their positive-boundary composition law |
| `Cob2Permutation.lean`, `Cob2BoundaryPermutations.lean` | Derived adjacent-boundary permutation identities |
| `Cob2SpiderPermutations.lean`, `Cob2SpiderPermutationWords.lean`, `Cob2SpiderPermutationInvariance.lean`, `Cob2FinitePermutationWords.lean` | Arbitrary-position adjacent swaps, finite swap words, existence of a representative for every finite boundary permutation, and spider absorption |
| `Cob2NormalForm.lean` | Component/genus surface codes modulo component relabeling |
| `Cob2SurfaceComposition.lean`, `Cob2SurfaceGraphBound.lean` | Descended code composition, Euler bound, and connected regression |
| `Cob2SurfaceCategory.lean` | Unit and associativity laws for graph gluing and the `SurfaceNFObj` category |
| `Cob2SurfaceMonoidal.lean`, `Cob2SurfaceMonoidalCoherence.lean` | Disjoint-union bifunctor, interchange, associativity, and unit coherence for surface codes |
| `Cob2SurfaceSignature.lean`, `Cob2ConnectedReification.lean` | Ordinary signature functor from the original Cob2 quotient, connected-spider reification, and genus injectivity |
| `Cob2SurfaceWiring.lean` | Genus-zero boundary wirings and their compatibility with gluing and reindexing |
| `Cob2SurfaceSymmetric.lean` | Lawful symmetric monoidal structure on `SurfaceNFObj`, with block-swap braiding |
| `Cob2SurfaceSignatureSymmetric.lean` | Symmetric-relation soundness and strong braided surface-signature semantics |
| `Cob2Universal.lean`, `Cob2UniversalEquivalence.lean`, `Cob2UniversalConverse.lean` | Evaluation/interpretation functors, both reconstruction isomorphisms, and the commutative-Frobenius universal equivalence |
| `Cob2OrdinaryShadow.lean` | Conditional composition-and-reconstruction interface for ordinary shadows of supplied strong braided theories |
| `FiniteDiagonalFrobenius.lean` | Finite-labelled diagonal Frobenius data, cardinality-valued genus words, and relabeling isomorphisms |
| `Cob2GeometricPrelude.lean` | Unoriented smooth one-manifolds, surfaces with boundary, boundary-parametrized single cobordisms, and the cylinder boundary calculation |
| `Cob2OrientedGeometricPrelude.lean` | Locally compatible tangent orientations, reversal, diffeomorphism preservation, and oriented carriers |
| `Cob2GeometricCylinder.lean` | Smooth embedded endpoint parametrization and packaged boundary-parametrized cylinder cobordism |
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
- The arity-one object of the symmetric algebraic source carries its canonical
  commutative Frobenius datum. Interpreting this datum reconstructs the
  identity source functor, including as a bundled braided monoidal
  isomorphism.
- The chosen ordered spiders satisfy the positive-boundary composition law
  `spider a b g ≫ spider b c h = spider a c (g + (b - 1) + h)`.
- Every permutation of a finite incoming or outgoing boundary has at least one
  adjacent-swap word representative, and a noncomputably chosen representative
  is absorbed by every ordered connected spider on that boundary.
- `SurfaceNF` records finitely many components, incident input/output circles,
  and a genus for each component, modulo relabeling. Its finite multigraph
  gluing operation descends to the quotient; the verified Euler bound prevents
  truncation in the cycle-rank genus term, and composing connected codes across
  `b > 0` adds exactly `b - 1` handles.
- Graph gluing satisfies both unit laws and associativity, so the wrapped
  normal forms `SurfaceNFObj` form a category. Disjoint union is a bifunctor
  compatible with composition and identities, with proved associativity and
  empty-code unit equations. Boundary equivalences are represented by
  genus-zero cylinder wirings whose gluing action is the expected external
  boundary reindexing.
- `SurfaceNFObj` carries a lawful symmetric monoidal structure: tensor is
  disjoint union, the coherence maps are the verified arity transports, and
  the braiding is the block-swap wiring.
- Every raw Cob2 word has a component/genus signature, the nine original
  commutative-Frobenius equations are sound for it, and the signature descends
  to an ordinary functor `Cob2Cat ⥤ SurfaceNFObj`.
- The same signature respects the strengthened monoidal and symmetric
  relations and therefore descends to a strong braided monoidal functor from
  `Cob2SymmetricObj` to `SurfaceNFObj`.
- Every canonical connected code is the signature of its ordered spider,
  including closed and one-sided cases, and connected codes at fixed boundary
  arities have injective genus parameters.
- Evaluation at the generating circle and Frobenius interpretation are
  functors between strong braided functors out of the symmetric algebraic
  source and commutative Frobenius data. Both reconstruction natural
  isomorphisms are proved, yielding an equivalence of these categories.
- The geometric prelude bundles closed smooth one-manifolds, compact smooth
  surfaces with boundary, and single unoriented cobordisms whose full boundary
  is smoothly parametrized. It also constructs the cylinder carrier and proves
  the formula for its model-theoretic boundary.
- The orientation layer defines tangent orientations as pointwise module
  orientations locally compatible in tangent-bundle trivializations, proves
  reversal involutive, and records preservation under diffeomorphisms.
- For every stored closed smooth one-manifold \(M\), the two endpoint
  inclusions into \(M\times[0,1]\) form a smooth manifold embedding onto the
  full model boundary and package an honest `cylinderCobordism M`.
- `frobZnSymmetricTQFT n` packages the diagonal datum on the symmetric
  quotient; `symmetricTorus` and every `symmetricGenus g` map to
  `(n : ℤ) • 𝟙`, hence evaluate at `1` to `n`.
- More generally, for a commutative ring `R` and finite label type `ι`, the
  diagonal function algebra `ι → R` is a commutative Frobenius datum whose
  connected genus words act by `Fintype.card ι`; permutations of `ι` induce
  Frobenius isomorphisms and interpreted monoidal natural automorphisms.
- Given an explicit chain of supplied strong braided monoidal theories,
  `OrdinaryShadowBridge` composes them, evaluates the result at the generating
  circle, and applies the algebraic reconstruction theorem. This is a
  conditional interface, not a construction or equivalence theorem for
  quantum geometric Langlands or a quantum Fourier--Mukai transform.
- In every ribbon category, quantum trace is cyclic, quantum dimension is
  multiplicative under tensor product, and the S-pairing is symmetric.

## Important scope limits

- The tensor product on `CondensedAb` is the ambient sheaf tensor, not the
  liquid tensor product; no exactness of tensoring is claimed.
- `Cob2.lean` remains the ordinary base quotient. `Cob2Monoidal.lean` and
  `Cob2Symmetric.lean` close its algebraic interchange and braiding gaps.
  The resulting universal equivalence is a theorem about this algebraic
  generators-and-relations source, not about geometric bordisms.
- Finite boundary permutations are representable by adjacent-swap words, but
  representation independence is not proved and the chosen representatives
  are not a categorical group action.
- The `SurfaceNF` category now has lawful monoidal and symmetric instances,
  and the signature is strong braided on the symmetric algebraic quotient.
  This proves sound combinatorial semantics, not that the signature is full,
  faithful, essentially surjective, or an equivalence. No theorem gives a
  complete or unique normal form for every arbitrary presentation word.
- The geometric layer now has locally compatible tangent orientations and a
  verified boundary-parametrized cylinder. It does not construct the boundary
  as a manifold with an induced orientation, distinguish incoming reversal
  from outgoing preservation, provide collars or smooth gluing, prove the
  cylinder is a categorical identity, form a quotient by diffeomorphisms or a
  geometric cobordism category, or compare with the algebraic source.
- The diagonal model is a finite-state Frobenius toy theory on an algebraic
  presentation. Its closed classes are now transported through the symmetric
  quotient, but they are not thereby geometric surface invariants, and the
  model is not the conventional finite-group/cocycle Dijkgraaf-Witten
  state-sum construction.
- The finite-labelled extension computes label cardinality and relabeling
  symmetries only. It does not identify labels with gauge fields or establish
  a finite-group state-sum, Fourier--Mukai, or Langlands correspondence.
- The ordinary-shadow comparison assumes all three strong braided functors as
  input. It proves the resulting algebraic reconstruction and does not supply
  geometric comparison, decategorification, or duality functors.
- `Ribbon.lean` supplies abstract input-side ribbon identities; it does not
  construct a modular tensor category or Reshetikhin-Turaev invariant.
- Results are universe-local in Mathlib's condensed conventions.

## Repository relationship

This repository mirrors the Lean sources used by the paper. The canonical
implementation repository is
[`Liquid-TQFT-CMCM-cont.`](https://github.com/seanm27lol/Liquid-TQFT-CMCM-cont.).
The documentation here records its current algebraic checkpoint; the repository
revision, rather than an embedded stale hash, is authoritative.
## Cool Videos

https://youtu.be/uVZYogrffzI?is=eARtZfZ8D-Ru6Yb-
awesome video about Frobenius Algebra and 2d TQFT :)
## Attribution

The symmetric monoidal structure on `CondensedAb` relies on Mathlib
infrastructure built by Joël Riou and Dagur Asgeirsson. Formal verification
was assisted by Aristotle (Harmonic), Claude (Anthropic), and OpenAI Codex.

## License

MIT
