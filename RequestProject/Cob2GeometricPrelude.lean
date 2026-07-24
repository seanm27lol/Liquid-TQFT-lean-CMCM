import Mathlib.Geometry.Manifold.Bordism
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# A geometric prelude for two-dimensional cobordisms

This file records the smallest geometric substrate needed before one can define a
two-dimensional cobordism category.  It bundles compact smooth one-manifolds, compact smooth
surfaces with boundary, and a boundary parametrization by a disjoint union of one-manifolds.
It also constructs the carrier of the cylinder and computes its model-theoretic boundary.

The definitions here are deliberately **unoriented**.  They do not define a bordism category,
composition by gluing, collars, a quotient by diffeomorphisms, or an equivalence with the
algebraic generators-and-relations category used elsewhere in this project.  In particular, the
cylinder carrier below is not promoted to an identity morphism: doing that honestly belongs with
the missing smooth gluing and boundary-parametrization infrastructure.
-/

open Set
open scoped Manifold ContDiff

namespace Cob2GeometricPrelude

universe u

noncomputable section

/-! ## The one-dimensional and surface models -/

/-- The Euclidean tangent space used for smooth one-manifolds. -/
abbrev LineTangentSpace := EuclideanSpace ℝ (Fin 1)

/-- The chart target used for smooth one-manifolds without boundary. -/
abbrev LineModelSpace := EuclideanSpace ℝ (Fin 1)

/-- The half-space chart target used for the interval direction of a surface with boundary. -/
abbrev HalfLineModelSpace := EuclideanHalfSpace 1

/-- The tangent space of the product model for a two-dimensional surface with boundary. -/
abbrev SurfaceTangentSpace := LineTangentSpace × LineTangentSpace

/-- The chart target of the product model for a two-dimensional surface with boundary. -/
abbrev SurfaceModelSpace := ModelProd LineModelSpace HalfLineModelSpace

/-- The product model with corners used for smooth surfaces with boundary. -/
abbrev surfaceModel :
    ModelWithCorners ℝ SurfaceTangentSpace SurfaceModelSpace :=
  (𝓡 1).prod (𝓡∂ 1)

/-! ## Bundled closed one-manifolds -/

/--
A compact smooth one-manifold without model boundary.

The absence of model boundary follows from using the boundaryless Euclidean model `𝓡 1`.
Hausdorffness and second countability are stored explicitly because they are part of the usual
manifold hypotheses needed by later geometric constructions.
-/
structure ClosedSmoothOneManifold where
  /-- The underlying type. -/
  M : Type u
  /-- The topology on the underlying type. -/
  [topologicalSpace : TopologicalSpace M]
  /-- The smooth atlas, modelled on the Euclidean line. -/
  [chartedSpace : ChartedSpace LineModelSpace M]
  /-- Smooth one-manifold regularity. -/
  [isManifold : IsManifold (𝓡 1) ∞ M]
  /-- Compactness of the closed one-manifold. -/
  [compactSpace : CompactSpace M]
  /-- Hausdorffness of the underlying topology. -/
  [t2Space : T2Space M]
  /-- Second countability of the underlying topology. -/
  [secondCountableTopology : SecondCountableTopology M]

namespace ClosedSmoothOneManifold

instance (M : ClosedSmoothOneManifold) : TopologicalSpace M.M :=
  M.topologicalSpace

instance (M : ClosedSmoothOneManifold) : ChartedSpace LineModelSpace M.M :=
  M.chartedSpace

instance (M : ClosedSmoothOneManifold) : IsManifold (𝓡 1) ∞ M.M :=
  M.isManifold

instance (M : ClosedSmoothOneManifold) : CompactSpace M.M :=
  M.compactSpace

instance (M : ClosedSmoothOneManifold) : T2Space M.M :=
  M.t2Space

instance (M : ClosedSmoothOneManifold) : SecondCountableTopology M.M :=
  M.secondCountableTopology

/-- A stored closed one-manifold has no model boundary. -/
instance (M : ClosedSmoothOneManifold) : BoundarylessManifold (𝓡 1) M.M := by
  infer_instance

end ClosedSmoothOneManifold

/-! ## Bundled compact surfaces with boundary -/

/-- A compact smooth surface modelled on a line times a half-line. -/
structure CompactSmoothSurfaceWithBoundary where
  /-- The underlying type. -/
  W : Type u
  /-- The topology on the underlying type. -/
  [topologicalSpace : TopologicalSpace W]
  /-- The product-half-space smooth atlas. -/
  [chartedSpace : ChartedSpace SurfaceModelSpace W]
  /-- Smooth surface-with-boundary regularity. -/
  [isManifold : IsManifold surfaceModel ∞ W]
  /-- Compactness of the surface. -/
  [compactSpace : CompactSpace W]
  /-- Hausdorffness of the underlying topology. -/
  [t2Space : T2Space W]
  /-- Second countability of the underlying topology. -/
  [secondCountableTopology : SecondCountableTopology W]

namespace CompactSmoothSurfaceWithBoundary

instance (W : CompactSmoothSurfaceWithBoundary) : TopologicalSpace W.W :=
  W.topologicalSpace

instance (W : CompactSmoothSurfaceWithBoundary) : ChartedSpace SurfaceModelSpace W.W :=
  W.chartedSpace

instance (W : CompactSmoothSurfaceWithBoundary) : IsManifold surfaceModel ∞ W.W :=
  W.isManifold

instance (W : CompactSmoothSurfaceWithBoundary) : CompactSpace W.W :=
  W.compactSpace

instance (W : CompactSmoothSurfaceWithBoundary) : T2Space W.W :=
  W.t2Space

instance (W : CompactSmoothSurfaceWithBoundary) : SecondCountableTopology W.W :=
  W.secondCountableTopology

end CompactSmoothSurfaceWithBoundary

/-! ## Boundary-parametrized cobordism data -/

/--
An unoriented compact smooth surface whose entire model boundary is parametrized by the disjoint
union of two closed smooth one-manifolds.

Smoothness and smooth embeddedness are separate fields.  In Mathlib v4.28.0,
`Manifold.IsSmoothEmbedding.contMDiff` is not yet implemented, so neither condition is silently
derived from the other.
-/
structure ParametrizedSmoothCobordism
    (M N : ClosedSmoothOneManifold) extends CompactSmoothSurfaceWithBoundary where
  /-- The parametrization of the incoming and outgoing boundary components. -/
  boundaryMap : M.M ⊕ N.M → W
  /-- The boundary parametrization is smooth. -/
  boundaryMap_contMDiff : ContMDiff (𝓡 1) surfaceModel ∞ boundaryMap
  /-- The boundary parametrization is a smooth embedding. -/
  boundaryMap_isSmoothEmbedding :
    Manifold.IsSmoothEmbedding (𝓡 1) surfaceModel ∞ boundaryMap
  /-- The parametrization has image exactly the model-theoretic boundary of the surface. -/
  boundaryMap_range : Set.range boundaryMap = surfaceModel.boundary W

namespace ParametrizedSmoothCobordism

instance {M N : ClosedSmoothOneManifold} (W : ParametrizedSmoothCobordism M N) :
    TopologicalSpace W.W :=
  W.topologicalSpace

instance {M N : ClosedSmoothOneManifold} (W : ParametrizedSmoothCobordism M N) :
    ChartedSpace SurfaceModelSpace W.W :=
  W.chartedSpace

instance {M N : ClosedSmoothOneManifold} (W : ParametrizedSmoothCobordism M N) :
    IsManifold surfaceModel ∞ W.W :=
  W.isManifold

instance {M N : ClosedSmoothOneManifold} (W : ParametrizedSmoothCobordism M N) :
    CompactSpace W.W :=
  W.compactSpace

instance {M N : ClosedSmoothOneManifold} (W : ParametrizedSmoothCobordism M N) :
    T2Space W.W :=
  W.t2Space

instance {M N : ClosedSmoothOneManifold} (W : ParametrizedSmoothCobordism M N) :
    SecondCountableTopology W.W :=
  W.secondCountableTopology

end ParametrizedSmoothCobordism

/-! ## The cylinder carrier -/

/-- The underlying compact smooth surface with boundary of the cylinder on `M`. -/
noncomputable def cylinderCarrier (M : ClosedSmoothOneManifold) :
    CompactSmoothSurfaceWithBoundary where
  W := M.M × Set.Icc (0 : ℝ) 1

/--
The model boundary of `M × [0,1]` is exactly the union of its two endpoint copies of `M`.

This is the geometric calculation needed before the endpoint inclusions can be packaged as a
parametrized cylinder.
-/
theorem cylinder_boundary (M : ClosedSmoothOneManifold) :
    surfaceModel.boundary (cylinderCarrier M).W =
      Set.prod (Set.univ : Set M.M) ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1)) := by
  exact boundary_product (I := 𝓡 1)

end

end Cob2GeometricPrelude
