import RequestProject.Cob2GeometricPrelude
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Orientation

/-!
# Oriented geometric data for two-dimensional cobordisms

This file adds the first orientation-sensitive layer to the geometric prelude.  An orientation is
a choice of orientation in every tangent space which is locally constant after transport through
a tangent-bundle trivialization.  We record orientation reversal, preservation by a smooth
diffeomorphism, and oriented versions of the one- and two-dimensional carriers already defined in
`Cob2GeometricPrelude`.

These definitions are deliberately only geometric **data**.  They do not construct an induced
orientation on the boundary of a surface, distinguish incoming from outgoing boundary
orientations, provide collars or smooth gluing, define an oriented bordism category, or prove an
equivalence with the algebraic generators-and-relations category used elsewhere in this project.
In particular, no classification of smooth oriented surfaces or diffeomorphism/gluing invariance
is asserted here.
-/

open Set
open scoped Manifold Bundle ContDiff Topology

namespace Cob2GeometricPrelude

universe u v w

noncomputable section

/-! ## Smooth orientations of tangent bundles -/

/--
A smooth-manifold orientation expressed as a locally constant family of orientations of tangent
spaces.

Local constancy is tested in a tangent-bundle trivialization at each point.  This avoids pretending
that tangent spaces at different points are definitionally the same while requiring exactly the
usual compatibility of their orientations in local coordinates.
-/
structure SmoothTangentOrientation
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] (ι : Type*) where
  /-- The chosen orientation of each tangent space. -/
  orientationAt : (x : M) → Orientation ℝ (TangentSpace I x) ι
  /--
  In a tangent-bundle trivialization, the chosen tangent-space orientations are locally constant.
  -/
  locally_constant :
    ∀ x : M,
      ∃ (U : Set M) (_hUx : U ∈ 𝓝 x)
        (hU : U ⊆ (trivializationAt E (TangentSpace I) x).baseSet),
        ∀ (y : M) (hy : y ∈ U),
          Orientation.map ι
              ((trivializationAt E (TangentSpace I) x).linearEquivAt ℝ y (hU hy))
              (orientationAt y) =
            Orientation.map ι
              ((trivializationAt E (TangentSpace I) x).linearEquivAt ℝ x
                (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x))
              (orientationAt x)

namespace SmoothTangentOrientation

variable
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I 1 M] {ι : Type*}

/-- Two smooth tangent orientations are equal when their pointwise orientations are equal. -/
@[ext]
theorem ext {o o₂ : SmoothTangentOrientation I (M := M) ι}
    (h : o.orientationAt = o₂.orientationAt) : o = o₂ := by
  cases o
  cases o₂
  cases h
  rfl

/-- Reverse every tangent-space orientation. -/
def reverse (o : SmoothTangentOrientation I (M := M) ι) :
    SmoothTangentOrientation I (M := M) ι where
  orientationAt x := -o.orientationAt x
  locally_constant x := by
    obtain ⟨U, hUx, hU, h⟩ := o.locally_constant x
    refine ⟨U, hUx, hU, ?_⟩
    intro y hy
    simpa only [Orientation.map_neg] using congrArg Neg.neg (h y hy)

/-- Reversing an orientation twice recovers the original orientation. -/
@[simp]
theorem reverse_reverse (o : SmoothTangentOrientation I (M := M) ι) :
    o.reverse.reverse = o := by
  ext x
  exact neg_neg (o.orientationAt x)

section Diffeomorph

variable
    {E' : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type v} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {N : Type w} [TopologicalSpace N] [ChartedSpace H' N]
    [IsManifold J ∞ N] [IsManifold I ∞ M]

/--
A smooth diffeomorphism preserves two chosen orientations when its differential transports the
chosen source orientation to the chosen target orientation at every point.
-/
def PreservesDiffeomorph
    (oM : SmoothTangentOrientation I (M := M) ι)
    (oN : SmoothTangentOrientation J (M := N) ι)
    (Φ : M ≃ₘ^∞⟮I, J⟯ N) : Prop :=
  ∀ x,
    Orientation.map ι
        (Φ.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
        (oM.orientationAt x) =
      oN.orientationAt (Φ x)

end Diffeomorph

end SmoothTangentOrientation

/-! ## Oriented one-manifold and surface carriers -/

/-- A smooth tangent orientation on a stored closed one-manifold. -/
abbrev ClosedSmoothOneManifoldOrientation (M : ClosedSmoothOneManifold) :=
  SmoothTangentOrientation (𝓡 1) (M := M.M) (Fin 1)

/-- A smooth tangent orientation on a stored compact surface with boundary. -/
abbrev CompactSmoothSurfaceOrientation (W : CompactSmoothSurfaceWithBoundary) :=
  SmoothTangentOrientation surfaceModel (M := W.W) (Fin 2)

/-- A closed smooth one-manifold together with a smooth tangent orientation. -/
structure OrientedClosedSmoothOneManifold where
  /-- The underlying closed smooth one-manifold. -/
  toClosedSmoothOneManifold : ClosedSmoothOneManifold
  /-- Its chosen smooth tangent orientation. -/
  orientation : ClosedSmoothOneManifoldOrientation toClosedSmoothOneManifold

/-- A compact smooth surface with boundary together with a smooth tangent orientation. -/
structure OrientedCompactSmoothSurfaceWithBoundary where
  /-- The underlying compact smooth surface with boundary. -/
  toCompactSmoothSurfaceWithBoundary : CompactSmoothSurfaceWithBoundary
  /-- Its chosen smooth tangent orientation. -/
  orientation :
    CompactSmoothSurfaceOrientation toCompactSmoothSurfaceWithBoundary

end

end Cob2GeometricPrelude
