import RequestProject.Cob2OrientedGeometricPrelude
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Boundary topology, collars, and orientation compatibility

This file adds a precise boundary-and-collar substrate to the geometric cobordism prelude.
The stored boundary parametrization of a `ParametrizedSmoothCobordism` is first promoted to an
honest homeomorphism onto the model-theoretic boundary as a topological subspace.  A boundary
collar is then recorded as smooth product-neighborhood data: its zero slice is the given boundary
parametrization, its full map is a topological embedding, and it is a local diffeomorphism along
the zero slice.  The latter condition implies that the collar image really contains a neighborhood
of every boundary point.

For oriented cobordisms, the file fixes the two-dimensional boundary-first, inward-normal
convention.  Incoming boundary orientations are reversed, outgoing orientations are retained, and
the collar differential is required to transport the resulting product orientation to the stored
surface orientation.

All collar assertions here are fields of bundled data.  This file does not prove that every compact
surface admits such a collar, construct a collar for the cylinder, give the model-theoretic boundary
subtype a smooth-manifold structure, construct an induced boundary orientation without chosen
collar data, glue surfaces, define composition or identity laws, form a bordism category, or compare
geometric cobordisms with the algebraic generators-and-relations categories elsewhere in the
project.
-/

open Set
open scoped Manifold ContDiff Topology

namespace Cob2GeometricPrelude

noncomputable section

/-! ## The parametrized boundary as a topological subspace -/

/--
The stored boundary parametrization is a homeomorphism onto the model-theoretic boundary as a
topological subspace.

This does not equip the boundary subtype with a smooth-manifold structure.
-/
noncomputable def ParametrizedSmoothCobordism.boundaryHomeomorph
    {M N : ClosedSmoothOneManifold}
    (W : ParametrizedSmoothCobordism M N) :
    M.M ⊕ N.M ≃ₜ surfaceModel.boundary W.W :=
  W.boundaryMap_isSmoothEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr W.boundaryMap_range)

@[simp]
theorem ParametrizedSmoothCobordism.boundaryHomeomorph_apply
    {M N : ClosedSmoothOneManifold}
    (W : ParametrizedSmoothCobordism M N) (x : M.M ⊕ N.M) :
    (W.boundaryHomeomorph x : W.W) = W.boundaryMap x :=
  rfl

/-! ## Smooth collar data -/

/--
A smooth product collar of the full parametrized boundary of `W`.

The local-diffeomorphism condition is imposed only along the zero slice.  Together with the global
topological embedding, this captures a genuine smooth collar neighborhood without requiring the
artificial far endpoint of the compact collar parameter to map to the model boundary.
-/
structure ParametrizedSmoothCobordism.BoundaryCollar
    {M N : ClosedSmoothOneManifold}
    (W : ParametrizedSmoothCobordism M N) where
  /-- The collar map from the parametrized boundary times a compact inward parameter. -/
  collarMap : (M.M ⊕ N.M) × Set.Icc (0 : ℝ) 1 → W.W
  /-- The zero slice of the collar is the stored boundary parametrization. -/
  collarMap_zero :
    ∀ x, collarMap (x, (⊥ : Set.Icc (0 : ℝ) 1)) = W.boundaryMap x
  /-- The collar map is smooth on its full compact parameter domain. -/
  collarMap_contMDiff :
    ContMDiff surfaceModel surfaceModel ∞ collarMap
  /-- The collar map is a topological embedding. -/
  collarMap_isEmbedding :
    Topology.IsEmbedding collarMap
  /-- Along the zero slice, the collar map is a smooth local diffeomorphism. -/
  collarMap_isLocalDiffeomorphAt_zero :
    ∀ x, IsLocalDiffeomorphAt surfaceModel surfaceModel ∞
      collarMap (x, (⊥ : Set.Icc (0 : ℝ) 1))

namespace ParametrizedSmoothCobordism.BoundaryCollar

variable {M N : ClosedSmoothOneManifold}
    {W : ParametrizedSmoothCobordism M N}

/-- The image of a collar contains a neighborhood of every parametrized boundary point. -/
theorem range_mem_nhds (c : W.BoundaryCollar) (x : M.M ⊕ N.M) :
    Set.range c.collarMap ∈ 𝓝 (W.boundaryMap x) := by
  rw [← c.collarMap_zero x]
  obtain ⟨Φ, hx, heq⟩ :=
    c.collarMap_isLocalDiffeomorphAt_zero x
  have hzero : c.collarMap (x, (⊥ : Set.Icc (0 : ℝ) 1)) =
      Φ (x, (⊥ : Set.Icc (0 : ℝ) 1)) := heq hx
  rw [hzero]
  refine Filter.mem_of_superset (Φ.open_target.mem_nhds (Φ.map_source hx)) ?_
  intro y hy
  refine ⟨Φ.invFun y, ?_⟩
  exact (heq (Φ.map_target hy)).trans (Φ.right_inv hy)

end ParametrizedSmoothCobordism.BoundaryCollar

/-! ## The boundary-first, inward-normal orientation convention -/

/--
The product orientation on the two-dimensional tangent model obtained by putting an oriented
boundary tangent first and the positive inward collar parameter second.
-/
def boundaryFirstInwardOrientation
    (o : Orientation ℝ LineTangentSpace (Fin 1)) :
    Orientation ℝ SurfaceTangentSpace (Fin 2) :=
  let b : Module.Basis (Fin 1) ℝ LineTangentSpace :=
    o.someBasis (by simp [LineTangentSpace])
  let positiveInward : Module.Basis (Fin 1) ℝ LineTangentSpace :=
    PiLp.basisFun 2 ℝ (Fin 1)
  ((b.prod positiveInward).reindex finSumFinEquiv).orientation

/--
The oriented boundary family of an oriented cobordism: incoming components are reversed and
outgoing components retain their stored orientation.
-/
def orientedBoundaryOrientationAt
    (M N : OrientedClosedSmoothOneManifold) :
    (x : M.toClosedSmoothOneManifold.M ⊕ N.toClosedSmoothOneManifold.M) →
      Orientation ℝ LineTangentSpace (Fin 1) :=
  Sum.elim
    (fun x => -M.orientation.orientationAt x)
    (fun x => N.orientation.orientationAt x)

/-! ## Oriented and collared cobordism data -/

/-- A boundary-parametrized smooth surface carrying source, target, and surface orientations. -/
structure OrientedParametrizedSmoothCobordism
    (M N : OrientedClosedSmoothOneManifold) where
  /-- The underlying boundary-parametrized smooth cobordism. -/
  toParametrizedSmoothCobordism :
    ParametrizedSmoothCobordism
      M.toClosedSmoothOneManifold N.toClosedSmoothOneManifold
  /-- The chosen smooth tangent orientation of the surface. -/
  orientation :
    CompactSmoothSurfaceOrientation
      toParametrizedSmoothCobordism.toCompactSmoothSurfaceWithBoundary

namespace OrientedParametrizedSmoothCobordism

variable {M N : OrientedClosedSmoothOneManifold}
    (W : OrientedParametrizedSmoothCobordism M N)

/-- A collar of the full parametrized boundary of an oriented cobordism. -/
abbrev BoundaryCollar :=
  W.toParametrizedSmoothCobordism.BoundaryCollar

/--
The collar satisfies the standard oriented-cobordism boundary convention when its differential
transports the reversed incoming and unchanged outgoing boundary orientations, followed by the
positive inward direction, to the stored surface orientation.
-/
def BoundaryCollar.IsOrientationCompatible (c : W.BoundaryCollar) : Prop :=
  ∀ x,
    Orientation.map (Fin 2)
        ((c.collarMap_isLocalDiffeomorphAt_zero x).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv
        (boundaryFirstInwardOrientation (orientedBoundaryOrientationAt M N x)) =
      W.orientation.orientationAt
        (c.collarMap (x, (⊥ : Set.Icc (0 : ℝ) 1)))

end OrientedParametrizedSmoothCobordism

/--
An oriented boundary-parametrized cobordism equipped with a genuine smooth collar and the standard
incoming/outgoing boundary-orientation convention.
-/
structure CollaredOrientedParametrizedSmoothCobordism
    (M N : OrientedClosedSmoothOneManifold) where
  /-- The oriented boundary-parametrized cobordism. -/
  toOrientedParametrizedSmoothCobordism :
    OrientedParametrizedSmoothCobordism M N
  /-- A chosen smooth product collar of its full parametrized boundary. -/
  collar :
    ParametrizedSmoothCobordism.BoundaryCollar
      toOrientedParametrizedSmoothCobordism.toParametrizedSmoothCobordism
  /-- The collar realizes the standard incoming/outgoing orientation convention. -/
  collar_orientation_compatible :
    OrientedParametrizedSmoothCobordism.BoundaryCollar.IsOrientationCompatible
      toOrientedParametrizedSmoothCobordism collar

end

end Cob2GeometricPrelude
