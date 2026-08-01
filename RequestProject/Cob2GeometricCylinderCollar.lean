import RequestProject.Cob2GeometricCylinder
import RequestProject.Cob2GeometricBoundaryCollar
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# An explicit two-ended collar for the geometric cylinder

This file equips `cylinderCobordism M` with concrete smooth boundary-collar
data.  The incoming branch sends `(x, t)` to `(x, t / 3)` and the outgoing
branch sends it to `(x, 1 - t / 3)`.  Their closed images are disjoint, and
explicit partial inverses prove the required local-diffeomorphism statements
along both zero slices.

The result supplies `BoundaryCollar` data for the verified cylinder.  It does
not prove the separate incoming/outgoing orientation-compatibility predicate,
a general collar-existence theorem, smooth seam gluing, or the cylinder
identity law for a geometric cobordism category.
-/

open Set
open scoped Manifold ContDiff Topology

namespace Cob2GeometricPrelude

noncomputable section

def collarShrinkLeft (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 (by norm_num) ((t : ℝ) / 3)

def collarShrinkRight (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 (by norm_num) (1 - (t : ℝ) / 3)

@[simp] theorem collarShrinkLeft_val (t : Set.Icc (0 : ℝ) 1) :
    (collarShrinkLeft t : ℝ) = (t : ℝ) / 3 := by
  rw [collarShrinkLeft, Set.projIcc_of_mem]
  constructor <;> linarith [t.2.1, t.2.2]

@[simp] theorem collarShrinkRight_val (t : Set.Icc (0 : ℝ) 1) :
    (collarShrinkRight t : ℝ) = 1 - (t : ℝ) / 3 := by
  rw [collarShrinkRight, Set.projIcc_of_mem]
  constructor <;> linarith [t.2.1, t.2.2]

theorem collarShrinkLeft_contMDiff :
    ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersEuclideanHalfSpace 1) ∞ collarShrinkLeft := by
  apply (contMDiffOn_projIcc (x := (0 : ℝ)) (y := 1)).comp_contMDiff
      (I := modelWithCornersEuclideanHalfSpace 1) (I' := modelWithCornersSelf ℝ ℝ)
  · exact (contMDiff_subtype_coe_Icc (x := (0 : ℝ)) (y := 1)).div_const 3
  · intro t
    constructor <;> dsimp <;> linarith [t.2.1, t.2.2]

theorem collarShrinkRight_contMDiff :
    ContMDiff (modelWithCornersEuclideanHalfSpace 1)
      (modelWithCornersEuclideanHalfSpace 1) ∞ collarShrinkRight := by
  apply (contMDiffOn_projIcc (x := (0 : ℝ)) (y := 1)).comp_contMDiff
      (I := modelWithCornersEuclideanHalfSpace 1) (I' := modelWithCornersSelf ℝ ℝ)
  · exact contMDiff_const.sub
      ((contMDiff_subtype_coe_Icc (x := (0 : ℝ)) (y := 1)).div_const 3)
  · intro t
    constructor <;> dsimp <;> linarith [t.2.1, t.2.2]

section Distrib

variable
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [TopologicalSpace G] (J : ModelWithCorners 𝕜 F G)
    {M M' P : Type*}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace M'] [ChartedSpace H M']
    [TopologicalSpace P] [ChartedSpace G P]

/-- Smooth counterpart of the topological distributivity homeomorphism. -/
def sumProdDistribDiffeomorph (n : WithTop ℕ∞) :
    ((M ⊕ M') × P) ≃ₘ^n⟮I.prod J, I.prod J⟯ ((M × P) ⊕ (M' × P)) where
  toEquiv := Equiv.sumProdDistrib M M' P
  contMDiff_toFun := by
    intro p
    rcases p with ⟨x, z⟩
    cases x with
    | inl x =>
        let f : (M ⊕ M') × P → (M × P) ⊕ (M' × P) := fun q =>
          Sum.inl (Sum.elim id (fun _ => x) q.1, q.2)
        have hf : ContMDiff (I.prod J) (I.prod J) n f := by
          apply ContMDiff.inl.comp
          exact (((contMDiff_id.sumElim contMDiff_const).comp contMDiff_fst).prodMk
            contMDiff_snd)
        apply hf.contMDiffAt.congr_of_eventuallyEq
        filter_upwards [((isOpen_range_inl.preimage continuous_fst).mem_nhds
          ⟨x, rfl⟩)] with q hq
        rcases q with ⟨q, t⟩
        obtain ⟨q, rfl⟩ := hq
        rfl
    | inr x =>
        let f : (M ⊕ M') × P → (M × P) ⊕ (M' × P) := fun q =>
          Sum.inr (Sum.elim (fun _ => x) id q.1, q.2)
        have hf : ContMDiff (I.prod J) (I.prod J) n f := by
          apply ContMDiff.inr.comp
          exact (((contMDiff_const.sumElim contMDiff_id).comp contMDiff_fst).prodMk
            contMDiff_snd)
        apply hf.contMDiffAt.congr_of_eventuallyEq
        filter_upwards [((isOpen_range_inr.preimage continuous_fst).mem_nhds
          ⟨x, rfl⟩)] with q hq
        rcases q with ⟨q, t⟩
        obtain ⟨q, rfl⟩ := hq
        rfl
  contMDiff_invFun := by
    apply ContMDiff.sumElim
    · exact (ContMDiff.inl.comp contMDiff_fst).prodMk contMDiff_snd
    · exact (ContMDiff.inr.comp contMDiff_fst).prodMk contMDiff_snd

end Distrib

def cylinderCollarMap (M : ClosedSmoothOneManifold) :
    (M.M ⊕ M.M) × Set.Icc (0 : ℝ) 1 → (cylinderCarrier M).W :=
  Sum.elim
      (fun p : M.M × Set.Icc (0 : ℝ) 1 => (p.1, collarShrinkLeft p.2))
      (fun p : M.M × Set.Icc (0 : ℝ) 1 => (p.1, collarShrinkRight p.2)) ∘
    sumProdDistribDiffeomorph (modelWithCornersSelf ℝ LineModelSpace)
      (modelWithCornersEuclideanHalfSpace 1) ∞

@[simp] theorem cylinderCollarMap_inl (M : ClosedSmoothOneManifold)
    (x : M.M) (t : Set.Icc (0 : ℝ) 1) :
    cylinderCollarMap M (Sum.inl x, t) = (x, collarShrinkLeft t) := rfl

@[simp] theorem cylinderCollarMap_inr (M : ClosedSmoothOneManifold)
    (x : M.M) (t : Set.Icc (0 : ℝ) 1) :
    cylinderCollarMap M (Sum.inr x, t) = (x, collarShrinkRight t) := rfl

theorem cylinderCollarMap_contMDiff (M : ClosedSmoothOneManifold) :
    ContMDiff surfaceModel surfaceModel ∞ (cylinderCollarMap M) := by
  change ContMDiff surfaceModel surfaceModel ∞
    ((Sum.elim
      (fun p : M.M × Set.Icc (0 : ℝ) 1 => (p.1, collarShrinkLeft p.2))
      (fun p : M.M × Set.Icc (0 : ℝ) 1 => (p.1, collarShrinkRight p.2))) ∘
      sumProdDistribDiffeomorph (modelWithCornersSelf ℝ LineModelSpace)
        (modelWithCornersEuclideanHalfSpace 1) ∞)
  apply (ContMDiff.sumElim
    (contMDiff_fst.prodMk (collarShrinkLeft_contMDiff.comp contMDiff_snd))
    (contMDiff_fst.prodMk (collarShrinkRight_contMDiff.comp contMDiff_snd))).comp
  exact (sumProdDistribDiffeomorph (modelWithCornersSelf ℝ LineModelSpace)
    (modelWithCornersEuclideanHalfSpace 1) ∞).contMDiff

theorem cylinderCollarMap_injective (M : ClosedSmoothOneManifold) :
    Function.Injective (cylinderCollarMap M) := by
  rintro ⟨x, s⟩ ⟨y, t⟩ h
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          apply Prod.ext
          · exact congrArg (fun z => Sum.inl z.1) h
          · apply Subtype.ext
            have hst := congrArg (fun z => (z.2 : ℝ)) h
            simp only [cylinderCollarMap_inl, collarShrinkLeft_val] at hst
            linarith
      | inr y =>
          have h' := congrArg (fun z => (z.2 : ℝ)) h
          simp only [cylinderCollarMap_inl, cylinderCollarMap_inr,
            collarShrinkLeft_val, collarShrinkRight_val] at h'
          linarith [s.2.2, t.2.2]
  | inr x =>
      cases y with
      | inl y =>
          have h' := congrArg (fun z => (z.2 : ℝ)) h
          simp only [cylinderCollarMap_inl, cylinderCollarMap_inr,
            collarShrinkLeft_val, collarShrinkRight_val] at h'
          linarith [s.2.2, t.2.2]
      | inr y =>
          apply Prod.ext
          · exact congrArg (fun z => Sum.inr z.1) h
          · apply Subtype.ext
            have hst := congrArg (fun z => (z.2 : ℝ)) h
            simp only [cylinderCollarMap_inr, collarShrinkRight_val] at hst
            linarith

theorem cylinderCollarMap_isEmbedding (M : ClosedSmoothOneManifold) :
    Topology.IsEmbedding (cylinderCollarMap M) :=
  ((cylinderCollarMap_contMDiff M).continuous.isClosedEmbedding
    (cylinderCollarMap_injective M)).isEmbedding

def collarExpandLeft (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 (by norm_num) (3 * (t : ℝ))

theorem collarExpandLeft_val_of_lt (t : Set.Icc (0 : ℝ) 1)
    (ht : (t : ℝ) < 1 / 3) :
    (collarExpandLeft t : ℝ) = 3 * (t : ℝ) := by
  rw [collarExpandLeft, Set.projIcc_of_mem]
  constructor <;> linarith [t.2.1]

noncomputable def cylinderCollarLeftPartial (M : ClosedSmoothOneManifold) :
    PartialDiffeomorph surfaceModel surfaceModel
      ((M.M ⊕ M.M) × Set.Icc (0 : ℝ) 1) (cylinderCarrier M).W ∞ where
  toPartialEquiv :=
    { toFun := cylinderCollarMap M
      invFun := fun q => (Sum.inl q.1, collarExpandLeft q.2)
      source := {p | p.1 ∈ Set.range (Sum.inl : M.M → M.M ⊕ M.M) ∧ (p.2 : ℝ) < 1}
      target := {q | (q.2 : ℝ) < 1 / 3}
      map_source' := by
        rintro ⟨a, t⟩ ⟨⟨x, rfl⟩, ht⟩
        simp only [Set.mem_setOf_eq, cylinderCollarMap_inl, collarShrinkLeft_val]
        linarith
      map_target' := by
        intro q hq
        change (q.2 : ℝ) < 1 / 3 at hq
        constructor
        · exact ⟨q.1, rfl⟩
        · rw [collarExpandLeft_val_of_lt q.2 hq]
          linarith
      left_inv' := by
        rintro ⟨a, t⟩ ⟨⟨x, rfl⟩, ht⟩
        change (Sum.inl x, collarExpandLeft (collarShrinkLeft t)) = (Sum.inl x, t)
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          rw [collarExpandLeft_val_of_lt]
          · simp only [collarShrinkLeft_val]
            ring
          · simp only [collarShrinkLeft_val]
            linarith
      right_inv' := by
        intro q hq
        change (q.2 : ℝ) < 1 / 3 at hq
        change (q.1, collarShrinkLeft (collarExpandLeft q.2)) = q
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          rw [collarShrinkLeft_val, collarExpandLeft_val_of_lt q.2 hq]
          ring }
  open_source := by
    exact (isOpen_range_inl.preimage continuous_fst).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
  open_target :=
    isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
  contMDiffOn_toFun := (cylinderCollarMap_contMDiff M).contMDiffOn
  contMDiffOn_invFun := by
    have hreal : ContMDiff surfaceModel (modelWithCornersSelf ℝ ℝ) ∞
        (fun q : (cylinderCarrier M).W => 3 * (q.2 : ℝ)) :=
      contMDiff_const.mul
        (contMDiff_subtype_coe_Icc.comp contMDiff_snd)
    have hexpand : ContMDiffOn surfaceModel
        (modelWithCornersEuclideanHalfSpace 1) ∞
        (fun q : (cylinderCarrier M).W => collarExpandLeft q.2)
        {q | (q.2 : ℝ) < 1 / 3} := by
      apply (contMDiffOn_projIcc (x := (0 : ℝ)) (y := 1)).comp hreal.contMDiffOn
      intro q hq
      change (q.2 : ℝ) < 1 / 3 at hq
      constructor <;> dsimp
      · linarith [q.2.2.1]
      · linarith
    exact (ContMDiff.inl.comp_contMDiffOn contMDiffOn_fst).prodMk hexpand

theorem cylinderCollarMap_isLocalDiffeomorphAt_inl_zero
    (M : ClosedSmoothOneManifold) (x : M.M) :
    IsLocalDiffeomorphAt surfaceModel surfaceModel ∞ (cylinderCollarMap M)
      (Sum.inl x, (⊥ : Set.Icc (0 : ℝ) 1)) := by
  exact (cylinderCollarLeftPartial M).isLocalDiffeomorphAt _ _ _
    ⟨⟨x, rfl⟩, by norm_num⟩

def collarExpandRight (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 (by norm_num) (3 * (1 - (t : ℝ)))

theorem collarExpandRight_val_of_gt (t : Set.Icc (0 : ℝ) 1)
    (ht : 2 / 3 < (t : ℝ)) :
    (collarExpandRight t : ℝ) = 3 * (1 - (t : ℝ)) := by
  rw [collarExpandRight, Set.projIcc_of_mem]
  constructor <;> linarith [t.2.2]

noncomputable def cylinderCollarRightPartial (M : ClosedSmoothOneManifold) :
    PartialDiffeomorph surfaceModel surfaceModel
      ((M.M ⊕ M.M) × Set.Icc (0 : ℝ) 1) (cylinderCarrier M).W ∞ where
  toPartialEquiv :=
    { toFun := cylinderCollarMap M
      invFun := fun q => (Sum.inr q.1, collarExpandRight q.2)
      source := {p | p.1 ∈ Set.range (Sum.inr : M.M → M.M ⊕ M.M) ∧ (p.2 : ℝ) < 1}
      target := {q | 2 / 3 < (q.2 : ℝ)}
      map_source' := by
        rintro ⟨a, t⟩ ⟨⟨x, rfl⟩, ht⟩
        simp only [Set.mem_setOf_eq, cylinderCollarMap_inr, collarShrinkRight_val]
        linarith
      map_target' := by
        intro q hq
        change 2 / 3 < (q.2 : ℝ) at hq
        constructor
        · exact ⟨q.1, rfl⟩
        · rw [collarExpandRight_val_of_gt q.2 hq]
          linarith [q.2.2]
      left_inv' := by
        rintro ⟨a, t⟩ ⟨⟨x, rfl⟩, ht⟩
        change (Sum.inr x, collarExpandRight (collarShrinkRight t)) = (Sum.inr x, t)
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          rw [collarExpandRight_val_of_gt]
          · simp only [collarShrinkRight_val]
            ring
          · simp only [collarShrinkRight_val]
            linarith
      right_inv' := by
        intro q hq
        change 2 / 3 < (q.2 : ℝ) at hq
        change (q.1, collarShrinkRight (collarExpandRight q.2)) = q
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          rw [collarShrinkRight_val, collarExpandRight_val_of_gt q.2 hq]
          ring }
  open_source := by
    exact (isOpen_range_inr.preimage continuous_fst).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
  open_target :=
    isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)
  contMDiffOn_toFun := (cylinderCollarMap_contMDiff M).contMDiffOn
  contMDiffOn_invFun := by
    have hreal : ContMDiff surfaceModel (modelWithCornersSelf ℝ ℝ) ∞
        (fun q : (cylinderCarrier M).W => 3 * (1 - (q.2 : ℝ))) :=
      contMDiff_const.mul
        (contMDiff_const.sub (contMDiff_subtype_coe_Icc.comp contMDiff_snd))
    have hexpand : ContMDiffOn surfaceModel
        (modelWithCornersEuclideanHalfSpace 1) ∞
        (fun q : (cylinderCarrier M).W => collarExpandRight q.2)
        {q | 2 / 3 < (q.2 : ℝ)} := by
      apply (contMDiffOn_projIcc (x := (0 : ℝ)) (y := 1)).comp hreal.contMDiffOn
      intro q hq
      change 2 / 3 < (q.2 : ℝ) at hq
      constructor <;> dsimp
      · linarith [q.2.2.2]
      · linarith
    exact (ContMDiff.inr.comp_contMDiffOn contMDiffOn_fst).prodMk hexpand

theorem cylinderCollarMap_isLocalDiffeomorphAt_inr_zero
    (M : ClosedSmoothOneManifold) (x : M.M) :
    IsLocalDiffeomorphAt surfaceModel surfaceModel ∞ (cylinderCollarMap M)
      (Sum.inr x, (⊥ : Set.Icc (0 : ℝ) 1)) := by
  exact (cylinderCollarRightPartial M).isLocalDiffeomorphAt _ _ _
    ⟨⟨x, rfl⟩, by norm_num⟩

noncomputable def cylinderBoundaryCollar (M : ClosedSmoothOneManifold) :
    (cylinderCobordism M).BoundaryCollar where
  collarMap := cylinderCollarMap M
  collarMap_zero := by
    intro x
    cases x with
    | inl x =>
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp [collarShrinkLeft, cylinderCobordism, cylinderBoundaryMap]
    | inr x =>
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp [collarShrinkRight, cylinderCobordism, cylinderBoundaryMap]
  collarMap_contMDiff := cylinderCollarMap_contMDiff M
  collarMap_isEmbedding := cylinderCollarMap_isEmbedding M
  collarMap_isLocalDiffeomorphAt_zero := by
    intro x
    cases x with
    | inl x => exact cylinderCollarMap_isLocalDiffeomorphAt_inl_zero M x
    | inr x => exact cylinderCollarMap_isLocalDiffeomorphAt_inr_zero M x

end

end Cob2GeometricPrelude
