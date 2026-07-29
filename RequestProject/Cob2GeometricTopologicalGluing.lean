import RequestProject.Cob2GeometricBoundaryCollar
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Topological gluing along a parametrized cobordism seam

This file constructs the canonical topological pushout underlying the composition of two
boundary-parametrized cobordisms.  For chosen-collared oriented cobordisms `W : M ⟶ N` and
`V : N ⟶ P`, the outgoing copy of `N` in `W` and the incoming copy of `N` in `V` give a span in
`TopCat`.  Its pushout is the topological carrier obtained by identifying precisely that seam.

The construction records the two canonical maps into the pushout, proves their pointwise agreement
on the seam, packages the outer boundary map, and exposes the pushout descent and uniqueness
principles.  It also proves that the two chosen half-collars have the same zero slice after mapping
into the pushout.  The incoming and outgoing boundary-orientation conventions cancel on the common
seam.

This is a genuine topological gluing object and a necessary precursor to geometric composition.
Its compactness is proved below.  It is not yet promoted to a
`CompactSmoothSurfaceWithBoundary`: this file does not prove that the pushout is Hausdorff, second
countable, locally Euclidean with boundary, or equipped with a compatible smooth structure.
Consequently it does not define smooth cobordism composition, prove the cylinder identity or
associativity up to diffeomorphism, form a geometric bordism category, or compare that category
with the algebraic presentation.
-/

open Set
open CategoryTheory
open CategoryTheory.Limits
open scoped Manifold ContDiff Topology

namespace Cob2GeometricPrelude

noncomputable section

namespace ParametrizedSmoothCobordism

variable {M N : ClosedSmoothOneManifold}

/-- The incoming parametrized boundary, regarded as a continuous map of topological spaces. -/
noncomputable def incomingBoundaryTopMap (W : ParametrizedSmoothCobordism M N) :
    TopCat.of M.M ⟶ TopCat.of W.W :=
  TopCat.ofHom
    ⟨fun x => W.boundaryMap (Sum.inl x),
      W.boundaryMap_contMDiff.continuous.comp continuous_inl⟩

/-- The outgoing parametrized boundary, regarded as a continuous map of topological spaces. -/
noncomputable def outgoingBoundaryTopMap (W : ParametrizedSmoothCobordism M N) :
    TopCat.of N.M ⟶ TopCat.of W.W :=
  TopCat.ofHom
    ⟨fun x => W.boundaryMap (Sum.inr x),
      W.boundaryMap_contMDiff.continuous.comp continuous_inr⟩

@[simp]
theorem incomingBoundaryTopMap_apply (W : ParametrizedSmoothCobordism M N) (x : M.M) :
    W.incomingBoundaryTopMap x = W.boundaryMap (Sum.inl x) :=
  rfl

@[simp]
theorem outgoingBoundaryTopMap_apply (W : ParametrizedSmoothCobordism M N) (x : N.M) :
    W.outgoingBoundaryTopMap x = W.boundaryMap (Sum.inr x) :=
  rfl

/-- The incoming boundary leg is injective. -/
theorem incomingBoundaryTopMap_injective (W : ParametrizedSmoothCobordism M N) :
    Function.Injective W.incomingBoundaryTopMap :=
  W.boundaryMap_isSmoothEmbedding.isEmbedding.injective.comp Sum.inl_injective

/-- The outgoing boundary leg is injective. -/
theorem outgoingBoundaryTopMap_injective (W : ParametrizedSmoothCobordism M N) :
    Function.Injective W.outgoingBoundaryTopMap :=
  W.boundaryMap_isSmoothEmbedding.isEmbedding.injective.comp Sum.inr_injective

/-- The incoming boundary leg is a closed topological embedding. -/
theorem incomingBoundaryTopMap_isClosedEmbedding (W : ParametrizedSmoothCobordism M N) :
    Topology.IsClosedEmbedding W.incomingBoundaryTopMap :=
  ⟨W.boundaryMap_isSmoothEmbedding.isEmbedding.comp Topology.IsEmbedding.inl,
    (isCompact_range W.incomingBoundaryTopMap.hom.continuous).isClosed⟩

/-- The outgoing boundary leg is a closed topological embedding. -/
theorem outgoingBoundaryTopMap_isClosedEmbedding (W : ParametrizedSmoothCobordism M N) :
    Topology.IsClosedEmbedding W.outgoingBoundaryTopMap :=
  ⟨W.boundaryMap_isSmoothEmbedding.isEmbedding.comp Topology.IsEmbedding.inr,
    (isCompact_range W.outgoingBoundaryTopMap.hom.continuous).isClosed⟩

end ParametrizedSmoothCobordism

namespace CollaredOrientedParametrizedSmoothCobordism

variable {M N P : OrientedClosedSmoothOneManifold}

/-- The underlying boundary-parametrized cobordism of a collared oriented cobordism. -/
abbrev underlying
    (W : CollaredOrientedParametrizedSmoothCobordism M N) :
    ParametrizedSmoothCobordism
      M.toClosedSmoothOneManifold N.toClosedSmoothOneManifold :=
  W.toOrientedParametrizedSmoothCobordism.toParametrizedSmoothCobordism

/--
The topological carrier obtained by gluing the outgoing boundary of `W` to the incoming boundary
of `V` using their common stored parametrization by `N`.
-/
noncomputable def topologicalGluingCarrier
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) : TopCat :=
  pushout W.underlying.outgoingBoundaryTopMap V.underlying.incomingBoundaryTopMap

/-- The canonical map from the left surface into its topological gluing carrier. -/
noncomputable def topologicalGluingInl
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    TopCat.of W.underlying.W ⟶ W.topologicalGluingCarrier V :=
  pushout.inl _ _

/-- The canonical map from the right surface into its topological gluing carrier. -/
noncomputable def topologicalGluingInr
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    TopCat.of V.underlying.W ⟶ W.topologicalGluingCarrier V :=
  pushout.inr _ _

/--
The underlying pushout cocone in `Type`.  It is exposed separately so that the exact
identification behavior of the topological pushout can be read from Mathlib's concrete type-level
pushout.
-/
noncomputable def topologicalGluingUnderlyingCocone
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    PushoutCocone
      ((forget TopCat).map W.underlying.outgoingBoundaryTopMap)
      ((forget TopCat).map V.underlying.incomingBoundaryTopMap) :=
  (pushout.cocone
    W.underlying.outgoingBoundaryTopMap
    V.underlying.incomingBoundaryTopMap).map (forget TopCat)

/-- The underlying type-level cocone of the topological gluing is a pushout. -/
private noncomputable def topologicalGluingUnderlyingIsColimit
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    IsColimit (W.topologicalGluingUnderlyingCocone V) :=
  isColimitOfHasPushoutOfPreservesColimit
    (forget TopCat)
    W.underlying.outgoingBoundaryTopMap
    V.underlying.incomingBoundaryTopMap

/-- The canonical inclusion of the left surface into the topological pushout is injective. -/
theorem topologicalGluingInl_injective
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    Function.Injective (W.topologicalGluingInl V) := by
  exact CategoryTheory.Limits.Types.pushoutCocone_inr_injective_of_isColimit
    (PushoutCocone.flipIsColimit (W.topologicalGluingUnderlyingIsColimit V))
    V.underlying.incomingBoundaryTopMap_injective

/-- The canonical inclusion of the right surface into the topological pushout is injective. -/
theorem topologicalGluingInr_injective
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    Function.Injective (W.topologicalGluingInr V) := by
  exact CategoryTheory.Limits.Types.pushoutCocone_inr_injective_of_isColimit
    (W.topologicalGluingUnderlyingIsColimit V)
    W.underlying.outgoingBoundaryTopMap_injective

/--
A point from the left and a point from the right have the same image in the pushout exactly when
they are the corresponding images of one point of the parametrized seam.  Thus there are no
unintended cross-piece identifications.
-/
theorem topologicalGluingInl_eq_inr_iff
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (w : W.underlying.W) (v : V.underlying.W) :
    W.topologicalGluingInl V w = W.topologicalGluingInr V v ↔
      ∃ x : N.toClosedSmoothOneManifold.M,
        W.underlying.boundaryMap (Sum.inr x) = w ∧
          V.underlying.boundaryMap (Sum.inl x) = v := by
  exact CategoryTheory.Limits.Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
    (W.topologicalGluingUnderlyingIsColimit V)
    W.underlying.outgoingBoundaryTopMap_injective
    w v

/-- The seam point accounting for a cross-piece equality is unique. -/
theorem topologicalGluingInl_eq_inr_iff_existsUnique
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (w : W.underlying.W) (v : V.underlying.W) :
    W.topologicalGluingInl V w = W.topologicalGluingInr V v ↔
      ∃! x : N.toClosedSmoothOneManifold.M,
        W.underlying.boundaryMap (Sum.inr x) = w ∧
          V.underlying.boundaryMap (Sum.inl x) = v := by
  constructor
  · intro h
    obtain ⟨x, hxW, hxV⟩ := (W.topologicalGluingInl_eq_inr_iff V w v).mp h
    refine ⟨x, ⟨hxW, hxV⟩, ?_⟩
    intro y hy
    exact W.underlying.outgoingBoundaryTopMap_injective
      (hy.1.trans hxW.symm)
  · rintro ⟨x, ⟨hxW, hxV⟩, _⟩
    exact (W.topologicalGluingInl_eq_inr_iff V w v).mpr
      ⟨x, hxW, hxV⟩

/-- The topological gluing carrier is compact. -/
theorem topologicalGluingCarrier_isCompact
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    IsCompact (Set.univ : Set (W.topologicalGluingCarrier V)) := by
  have hW : IsCompact (Set.range (W.topologicalGluingInl V)) :=
    isCompact_range (W.topologicalGluingInl V).hom.continuous
  have hV : IsCompact (Set.range (W.topologicalGluingInr V)) :=
    isCompact_range (W.topologicalGluingInr V).hom.continuous
  rw [← show
    Set.range (W.topologicalGluingInl V) ∪
        Set.range (W.topologicalGluingInr V) =
      Set.univ by
    ext z
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    exact CategoryTheory.Limits.Types.eq_or_eq_of_isPushout
      (IsPushout.of_isColimit (W.topologicalGluingUnderlyingIsColimit V)) z]
  exact hW.union hV

/-- The two canonical maps identify the corresponding points of the parametrized seam. -/
@[simp]
theorem topologicalGluing_seam
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (x : N.toClosedSmoothOneManifold.M) :
    W.topologicalGluingInl V (W.underlying.boundaryMap (Sum.inr x)) =
      W.topologicalGluingInr V (V.underlying.boundaryMap (Sum.inl x)) := by
  exact CategoryTheory.congr_fun
    (pushout.condition :
      W.underlying.outgoingBoundaryTopMap ≫ W.topologicalGluingInl V =
        V.underlying.incomingBoundaryTopMap ≫ W.topologicalGluingInr V)
    x

/--
The unglued incoming boundary of `W` and outgoing boundary of `V`, mapped into the topological
pushout.
-/
noncomputable def topologicalGluingOuterBoundary
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    TopCat.of
        (M.toClosedSmoothOneManifold.M ⊕ P.toClosedSmoothOneManifold.M) ⟶
      W.topologicalGluingCarrier V :=
  TopCat.ofHom
    ⟨Sum.elim
        (fun x =>
          W.topologicalGluingInl V
            (W.underlying.boundaryMap (Sum.inl x)))
        (fun x =>
          W.topologicalGluingInr V
            (V.underlying.boundaryMap (Sum.inr x))),
      (W.topologicalGluingInl V).hom.continuous.comp
          (W.underlying.boundaryMap_contMDiff.continuous.comp continuous_inl) |>.sumElim
        ((W.topologicalGluingInr V).hom.continuous.comp
          (V.underlying.boundaryMap_contMDiff.continuous.comp continuous_inr))⟩

@[simp]
theorem topologicalGluingOuterBoundary_inl
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (x : M.toClosedSmoothOneManifold.M) :
    W.topologicalGluingOuterBoundary V (Sum.inl x) =
      W.topologicalGluingInl V (W.underlying.boundaryMap (Sum.inl x)) :=
  rfl

@[simp]
theorem topologicalGluingOuterBoundary_inr
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (x : P.toClosedSmoothOneManifold.M) :
    W.topologicalGluingOuterBoundary V (Sum.inr x) =
      W.topologicalGluingInr V (V.underlying.boundaryMap (Sum.inr x)) :=
  rfl

/--
The two unglued boundary families remain distinct and injectively parametrized in the topological
pushout.
-/
theorem topologicalGluingOuterBoundary_injective
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    Function.Injective (W.topologicalGluingOuterBoundary V) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          apply congrArg Sum.inl
          exact Sum.inl_injective
            (W.underlying.boundaryMap_isSmoothEmbedding.isEmbedding.injective
              (W.topologicalGluingInl_injective V h))
      | inr y =>
          obtain ⟨z, hz, _⟩ :=
            (W.topologicalGluingInl_eq_inr_iff V
              (W.underlying.boundaryMap (Sum.inl x))
              (V.underlying.boundaryMap (Sum.inr y))).mp h
          have :=
            W.underlying.boundaryMap_isSmoothEmbedding.isEmbedding.injective hz
          contradiction
  | inr x =>
      cases y with
      | inl y =>
          obtain ⟨z, hz, _⟩ :=
            (W.topologicalGluingInl_eq_inr_iff V
              (W.underlying.boundaryMap (Sum.inl y))
              (V.underlying.boundaryMap (Sum.inr x))).mp h.symm
          have :=
            W.underlying.boundaryMap_isSmoothEmbedding.isEmbedding.injective hz
          contradiction
      | inr y =>
          apply congrArg Sum.inr
          exact Sum.inr_injective
            (V.underlying.boundaryMap_isSmoothEmbedding.isEmbedding.injective
              (W.topologicalGluingInr_injective V h))

/--
A pair of continuous maps out of the two pieces which agree on the seam descends to the
topological gluing carrier.
-/
noncomputable def topologicalGluingDesc
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    {T : TopCat}
    (f : TopCat.of W.underlying.W ⟶ T)
    (g : TopCat.of V.underlying.W ⟶ T)
    (h :
      W.underlying.outgoingBoundaryTopMap ≫ f =
        V.underlying.incomingBoundaryTopMap ≫ g) :
    W.topologicalGluingCarrier V ⟶ T :=
  pushout.desc f g h

@[simp, reassoc]
theorem topologicalGluingInl_desc
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    {T : TopCat}
    (f : TopCat.of W.underlying.W ⟶ T)
    (g : TopCat.of V.underlying.W ⟶ T)
    (h :
      W.underlying.outgoingBoundaryTopMap ≫ f =
        V.underlying.incomingBoundaryTopMap ≫ g) :
    W.topologicalGluingInl V ≫ W.topologicalGluingDesc V f g h = f := by
  exact pushout.inl_desc _ _ _

@[simp, reassoc]
theorem topologicalGluingInr_desc
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    {T : TopCat}
    (f : TopCat.of W.underlying.W ⟶ T)
    (g : TopCat.of V.underlying.W ⟶ T)
    (h :
      W.underlying.outgoingBoundaryTopMap ≫ f =
        V.underlying.incomingBoundaryTopMap ≫ g) :
    W.topologicalGluingInr V ≫ W.topologicalGluingDesc V f g h = g := by
  exact pushout.inr_desc _ _ _

/-- Continuous maps out of the topological gluing carrier are determined on its two pieces. -/
@[ext]
theorem topologicalGluing_hom_ext
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    {T : TopCat}
    {f g : W.topologicalGluingCarrier V ⟶ T}
    (hW : W.topologicalGluingInl V ≫ f = W.topologicalGluingInl V ≫ g)
    (hV : W.topologicalGluingInr V ≫ f = W.topologicalGluingInr V ≫ g) :
    f = g :=
  pushout.hom_ext hW hV

/--
After passage to the pushout, the outgoing half-collar of `W` and incoming half-collar of `V`
have the same zero slice.
-/
@[simp]
theorem topologicalGluing_collar_zero
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (x : N.toClosedSmoothOneManifold.M) :
    W.topologicalGluingInl V
        (W.collar.collarMap (Sum.inr x, (⊥ : Set.Icc (0 : ℝ) 1))) =
      W.topologicalGluingInr V
        (V.collar.collarMap (Sum.inl x, (⊥ : Set.Icc (0 : ℝ) 1))) := by
  rw [W.collar.collarMap_zero, V.collar.collarMap_zero]
  exact W.topologicalGluing_seam V x

/--
The stored outgoing orientation of the left cobordism is the negative of the stored incoming
orientation of the right cobordism along their common parametrized seam.
-/
theorem seam_boundary_orientations_cancel
    (M N P : OrientedClosedSmoothOneManifold)
    (x : N.toClosedSmoothOneManifold.M) :
    orientedBoundaryOrientationAt M N (Sum.inr x) =
      -orientedBoundaryOrientationAt N P (Sum.inl x) := by
  change N.orientation.orientationAt x = - -N.orientation.orientationAt x
  exact (neg_neg (N.orientation.orientationAt x)).symm

end CollaredOrientedParametrizedSmoothCobordism

end

end Cob2GeometricPrelude
