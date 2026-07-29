import RequestProject.Cob2OrientedGeometricPrelude

/-!
# The endpoint parametrization of the geometric cylinder

This file isolates the next geometric calculation for two-dimensional cobordisms.  For a stored
closed smooth one-manifold `M`, it defines the two endpoint inclusions into `M × [0,1]` and proves
that their coproduct is smooth, is a manifold immersion, is a topological embedding, and has image
exactly the model-theoretic boundary of the cylinder carrier.  These results package the carrier
as an honest `ParametrizedSmoothCobordism`.

Mathlib v4.28.0 does not provide product-with-a-constant or coproduct closure theorems for
`Manifold.IsImmersion`, so the immersion proof is carried out directly in the canonical sum and
product charts.  This still does not construct collars, smooth gluing, identity laws in a
cobordism category, or an orientation compatible with the incoming and outgoing boundary.
-/

open Set
open scoped Manifold ContDiff

namespace Cob2GeometricPrelude

noncomputable section

/-! ## Endpoint inclusions -/

/-- The incoming and outgoing endpoint copies of `M` inside its cylinder carrier. -/
def cylinderBoundaryMap (M : ClosedSmoothOneManifold) :
    M.M ⊕ M.M → (cylinderCarrier M).W :=
  Sum.elim (fun x => (x, ⊥)) (fun x => (x, ⊤))

/-- The cylinder endpoint parametrization is smooth. -/
theorem cylinderBoundaryMap_contMDiff (M : ClosedSmoothOneManifold) :
    ContMDiff (𝓡 1) surfaceModel ∞ (cylinderBoundaryMap M) := by
  apply ContMDiff.sumElim
  · exact contMDiff_id.prodMk contMDiff_const
  · exact contMDiff_id.prodMk contMDiff_const

/-- The cylinder endpoint parametrization is a topological embedding. -/
theorem cylinderBoundaryMap_isEmbedding (M : ClosedSmoothOneManifold) :
    Topology.IsEmbedding (cylinderBoundaryMap M) := by
  let f : M.M → (cylinderCarrier M).W := fun x => (x, ⊥)
  let g : M.M → (cylinderCarrier M).W := fun x => (x, ⊤)
  have hf : Topology.IsEmbedding f := isEmbedding_prodMkLeft ⊥
  have hg : Topology.IsEmbedding g := isEmbedding_prodMkLeft ⊤
  have hfc : IsClosed (Set.range f) :=
    (isCompact_range hf.continuous).isClosed
  have hgc : IsClosed (Set.range g) :=
    (isCompact_range hg.continuous).isClosed
  rw [show cylinderBoundaryMap M = Sum.elim f g by rfl]
  apply hf.sumElim hg
  · rw [hfc.closure_eq]
    rw [Set.disjoint_left]
    intro z hz_f hz_g
    obtain ⟨x, rfl⟩ := hz_f
    obtain ⟨y, hxy⟩ := hz_g
    have : (⊤ : Set.Icc (0 : ℝ) 1) = ⊥ := congrArg Prod.snd hxy
    norm_num at this
  · rw [hgc.closure_eq]
    rw [Set.disjoint_left]
    intro z hz_f hz_g
    obtain ⟨x, rfl⟩ := hz_f
    obtain ⟨y, hxy⟩ := hz_g
    have : (⊤ : Set.Icc (0 : ℝ) 1) = ⊥ := congrArg Prod.snd hxy
    norm_num at this

/-- The cylinder endpoint parametrization covers exactly the model-theoretic boundary. -/
theorem cylinderBoundaryMap_range (M : ClosedSmoothOneManifold) :
    Set.range (cylinderBoundaryMap M) =
      surfaceModel.boundary (cylinderCarrier M).W := by
  rw [cylinder_boundary]
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    cases x with
    | inl x =>
        exact ⟨Set.mem_univ x, Set.mem_insert (⊥ : Set.Icc (0 : ℝ) 1) {⊤}⟩
    | inr x =>
        exact ⟨Set.mem_univ x, Set.mem_insert_of_mem ⊥ (Set.mem_singleton ⊤)⟩
  · intro hz
    rcases z with ⟨x, t⟩
    change x ∈ (Set.univ : Set M.M) ∧
      t ∈ ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1)) at hz
    rcases hz with ⟨_, hz⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr x, rfl⟩

/--
The cylinder endpoint parametrization is a manifold immersion.

The single global complement is the interval-direction tangent line.  On each summand, the
canonical sum chart and product chart identify the map with `y ↦ (y, 0)`; the endpoint-coordinate
calculations are `IccLeftChart_extend_bot` and `IccRightChart_extend_top`.
-/
theorem cylinderBoundaryMap_isImmersion (M : ClosedSmoothOneManifold) :
    Manifold.IsImmersion (𝓡 1) surfaceModel ∞ (cylinderBoundaryMap M) := by
  rw [Manifold.IsImmersion]
  refine ⟨LineTangentSpace, by infer_instance, by infer_instance, ?_⟩
  intro p
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (cylinderBoundaryMap_contMDiff M).continuous.continuousAt
    (ContinuousLinearEquiv.refl ℝ SurfaceTangentSpace)
    (chartAt LineModelSpace p)
    (chartAt SurfaceModelSpace (cylinderBoundaryMap M p))
    (mem_chart_source LineModelSpace p)
    (mem_chart_source SurfaceModelSpace (cylinderBoundaryMap M p))
    (IsManifold.chart_mem_maximalAtlas p)
    (IsManifold.chart_mem_maximalAtlas (cylinderBoundaryMap M p))
  intro y hy
  cases p with
  | inl x =>
      simp_all [cylinderBoundaryMap]
      rw [ChartedSpace.sum_chartAt_inl] at hy ⊢
      constructor
      · simpa [OpenPartialHomeomorph.lift_openEmbedding_symm,
          prodChartedSpace_chartAt] using
          (chartAt LineModelSpace x).right_inv hy
      · change
          (chartAt HalfLineModelSpace (⊥ : Set.Icc (0 : ℝ) 1)).extend
              (𝓡∂ 1) ⊥ = 0
        rw [show chartAt HalfLineModelSpace (⊥ : Set.Icc (0 : ℝ) 1) =
          IccLeftChart 0 1 by
            exact Icc_chartedSpaceChartAt_of_le_top (by norm_num)]
        exact IccLeftChart_extend_bot
  | inr x =>
      simp_all [cylinderBoundaryMap]
      rw [ChartedSpace.sum_chartAt_inr] at hy ⊢
      constructor
      · simpa [OpenPartialHomeomorph.lift_openEmbedding_symm,
          prodChartedSpace_chartAt] using
          (chartAt LineModelSpace x).right_inv hy
      · change
          (chartAt HalfLineModelSpace (⊤ : Set.Icc (0 : ℝ) 1)).extend
              (𝓡∂ 1) ⊤ = 0
        rw [show chartAt HalfLineModelSpace (⊤ : Set.Icc (0 : ℝ) 1) =
          IccRightChart 0 1 by
            exact Icc_chartedSpaceChartAt_of_top_le (by norm_num)]
        exact IccRightChart_extend_top

/-- The cylinder endpoint parametrization is a smooth manifold embedding. -/
theorem cylinderBoundaryMap_isSmoothEmbedding (M : ClosedSmoothOneManifold) :
    Manifold.IsSmoothEmbedding (𝓡 1) surfaceModel ∞ (cylinderBoundaryMap M) :=
  ⟨cylinderBoundaryMap_isImmersion M, cylinderBoundaryMap_isEmbedding M⟩

/-! ## The boundary-parametrized cylinder -/

/--
The geometric cylinder on a closed smooth one-manifold, with its two endpoint copies as incoming
and outgoing boundary parametrizations.

This is verified boundary-parametrized surface data.  No claim is made here that it is an identity
for a cobordism composition: that requires a separately constructed smooth gluing operation and
its unit law.
-/
noncomputable def cylinderCobordism (M : ClosedSmoothOneManifold) :
    ParametrizedSmoothCobordism M M where
  toCompactSmoothSurfaceWithBoundary := cylinderCarrier M
  boundaryMap := cylinderBoundaryMap M
  boundaryMap_contMDiff := cylinderBoundaryMap_contMDiff M
  boundaryMap_isSmoothEmbedding := cylinderBoundaryMap_isSmoothEmbedding M
  boundaryMap_range := cylinderBoundaryMap_range M

end

end Cob2GeometricPrelude
