import RequestProject.Cob2GeometricTopologicalGluing
import Mathlib.Topology.Separation.Regular

/-!
# Hausdorffness of the topological cobordism gluing

This file proves that the `TopCat` pushout used to glue two chosen-collared oriented
cobordisms along their common parametrized boundary is Hausdorff.

The proof exposes the canonical quotient map from the disjoint union of the two compact
Hausdorff surface carriers.  Its kernel is exactly the union of the two diagonals and the two
graphs of the seam identification, hence is closed.  A general compact-Hausdorff
closed-kernel quotient lemma then separates distinct quotient points.

This establishes only the Hausdorff separation property of the already constructed
topological pushout.  It does not prove second countability, a local Euclidean-with-boundary
structure, compatibility with a smooth atlas, or any categorical composition law for smooth
cobordisms.
-/

open Set Function Topology
open CategoryTheory CategoryTheory.Limits
open scoped Manifold ContDiff Topology

universe u v

namespace Cob2GeometricPrelude

noncomputable section

/--
A quotient of a compact Hausdorff space is Hausdorff when its kernel relation is closed.

The kernel hypothesis first makes the quotient map closed: the saturation of a closed subset
is the second projection of a closed subset of the compact square.  Normality of the compact
Hausdorff source then separates two closed fibers, and closedness of the quotient map turns the
resulting saturated complements into disjoint neighborhoods downstairs.
-/
theorem t2Space_of_compact_closed_kernel_quotient
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y]
    (q : X → Y) (hq : IsQuotientMap q)
    (hker : IsClosed {p : X × X | q p.1 = q p.2}) :
    T2Space Y := by
  have hq_closed : IsClosedMap q := by
    intro s hs
    apply hq.isClosed_preimage.mp
    let R : Set (X × X) :=
      {p | p.1 ∈ s ∧ q p.1 = q p.2}
    have hR : IsClosed R := by
      exact (hs.preimage continuous_fst).inter hker
    have hRcompact : IsCompact R := hR.isCompact
    have hsaturate : Prod.snd '' R = q ⁻¹' (q '' s) := by
      ext x
      constructor
      · rintro ⟨p, ⟨hps, hpq⟩, rfl⟩
        exact ⟨p.1, hps, hpq⟩
      · rintro ⟨z, hzs, hzq⟩
        exact ⟨(z, x), ⟨hzs, hzq⟩, rfl⟩
    rw [← hsaturate]
    exact (hRcompact.image continuous_snd).isClosed
  refine ⟨fun y₁ y₂ hne => ?_⟩
  obtain ⟨x₁, rfl⟩ := hq.surjective y₁
  obtain ⟨x₂, rfl⟩ := hq.surjective y₂
  let F₁ : Set X := {x | q x = q x₁}
  let F₂ : Set X := {x | q x = q x₂}
  have hF₁ : IsClosed F₁ := by
    let e₁ : X → X × X := fun x => (x, x₁)
    have he₁ : Continuous e₁ := continuous_id.prodMk continuous_const
    have heq : e₁ ⁻¹' {p : X × X | q p.1 = q p.2} = F₁ := by
      ext x
      simp [e₁, F₁]
    rw [← heq]
    exact hker.preimage he₁
  have hF₂ : IsClosed F₂ := by
    let e₂ : X → X × X := fun x => (x, x₂)
    have he₂ : Continuous e₂ := continuous_id.prodMk continuous_const
    have heq : e₂ ⁻¹' {p : X × X | q p.1 = q p.2} = F₂ := by
      ext x
      simp [e₂, F₂]
    rw [← heq]
    exact hker.preimage he₂
  have hFdisj : Disjoint F₁ F₂ := by
    refine Set.disjoint_left.2 ?_
    intro x hx₁ hx₂
    apply hne
    exact hx₁.symm.trans hx₂
  obtain ⟨U, V, hUopen, hVopen, hF₁U, hF₂V, hUV⟩ :=
    normal_separation hF₁ hF₂ hFdisj
  refine ⟨(q '' Uᶜ)ᶜ, (q '' Vᶜ)ᶜ,
    (hq_closed Uᶜ hUopen.isClosed_compl).isOpen_compl,
    (hq_closed Vᶜ hVopen.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
  · intro hx
    obtain ⟨z, hzU, hzq⟩ := hx
    exact hzU (hF₁U hzq)
  · intro hx
    obtain ⟨z, hzV, hzq⟩ := hx
    exact hzV (hF₂V hzq)
  · refine Set.disjoint_left.2 ?_
    intro y hyU hyV
    obtain ⟨x, rfl⟩ := hq.surjective y
    have hxU : x ∈ U := by
      by_contra hx
      exact hyU ⟨x, hx, rfl⟩
    have hxV : x ∈ V := by
      by_contra hx
      exact hyV ⟨x, hx, rfl⟩
    exact Set.disjoint_left.1 hUV hxU hxV

namespace CollaredOrientedParametrizedSmoothCobordism

variable {M N P : OrientedClosedSmoothOneManifold}

private noncomputable def hausdorffGluingUnderlyingIsColimit
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    IsColimit (W.topologicalGluingUnderlyingCocone V) :=
  isColimitOfHasPushoutOfPreservesColimit
    (forget TopCat)
    W.underlying.outgoingBoundaryTopMap
    V.underlying.incomingBoundaryTopMap

/--
The canonical map from the disjoint union of the two surface carriers to their topological
pushout.
-/
noncomputable def topologicalGluingQuotient
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    W.underlying.W ⊕ V.underlying.W → W.topologicalGluingCarrier V :=
  Sum.elim (W.topologicalGluingInl V) (W.topologicalGluingInr V)

/-- The canonical gluing quotient map is continuous. -/
theorem topologicalGluingQuotient_continuous
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    Continuous (W.topologicalGluingQuotient V) :=
  (W.topologicalGluingInl V).hom.continuous.sumElim
    (W.topologicalGluingInr V).hom.continuous

/-- The canonical gluing quotient map is surjective. -/
theorem topologicalGluingQuotient_surjective
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    Surjective (W.topologicalGluingQuotient V) := by
  intro z
  obtain ⟨w, rfl⟩ | ⟨v, rfl⟩ :=
    CategoryTheory.Limits.Types.eq_or_eq_of_isPushout
      (IsPushout.of_isColimit (W.hausdorffGluingUnderlyingIsColimit V)) z
  · exact ⟨Sum.inl w, rfl⟩
  · exact ⟨Sum.inr v, rfl⟩

/--
The topology on the pushout is precisely the quotient topology induced by the canonical map
from the disjoint union.
-/
theorem topologicalGluingQuotient_isQuotientMap
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    IsQuotientMap (W.topologicalGluingQuotient V) := by
  refine isQuotientMap_iff.2
    ⟨W.topologicalGluingQuotient_surjective V, fun s => ?_⟩
  constructor
  · exact fun hs => hs.preimage (W.topologicalGluingQuotient_continuous V)
  · intro hs
    have hpieces := isOpen_sum_iff.1 hs
    apply TopCat.isOpen_iff_of_isColimit
      (pushout.cocone
        W.underlying.outgoingBoundaryTopMap
        V.underlying.incomingBoundaryTopMap)
      (pushout.isColimit _ _)
      s |>.2
    rintro (_ | ⟨(_ | _)⟩)
    · rw [PushoutCocone.condition_zero]
      change IsOpen
        ((W.underlying.outgoingBoundaryTopMap ≫ W.topologicalGluingInl V) ⁻¹' s)
      simpa [topologicalGluingQuotient] using
        hpieces.1.preimage W.underlying.outgoingBoundaryTopMap.hom.continuous
    · exact hpieces.1
    · exact hpieces.2

/--
The kernel of the gluing quotient is closed.

It is exactly the union of the left and right diagonals with the two directed graphs of the
common seam parametrization.  Each of these four sets is a compact range in the Hausdorff
square of the disjoint union.
-/
theorem topologicalGluingQuotient_kernel_isClosed
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    IsClosed
      {p : (W.underlying.W ⊕ V.underlying.W) ×
          (W.underlying.W ⊕ V.underlying.W) |
        W.topologicalGluingQuotient V p.1 =
          W.topologicalGluingQuotient V p.2} := by
  let LL : Set ((W.underlying.W ⊕ V.underlying.W) ×
      (W.underlying.W ⊕ V.underlying.W)) :=
    Set.range (fun w : W.underlying.W => (Sum.inl w, Sum.inl w))
  let LR : Set ((W.underlying.W ⊕ V.underlying.W) ×
      (W.underlying.W ⊕ V.underlying.W)) :=
    Set.range (fun x : N.toClosedSmoothOneManifold.M =>
      (Sum.inl (W.underlying.outgoingBoundaryTopMap x),
        Sum.inr (V.underlying.incomingBoundaryTopMap x)))
  let RL : Set ((W.underlying.W ⊕ V.underlying.W) ×
      (W.underlying.W ⊕ V.underlying.W)) :=
    Set.range (fun x : N.toClosedSmoothOneManifold.M =>
      (Sum.inr (V.underlying.incomingBoundaryTopMap x),
        Sum.inl (W.underlying.outgoingBoundaryTopMap x)))
  let RR : Set ((W.underlying.W ⊕ V.underlying.W) ×
      (W.underlying.W ⊕ V.underlying.W)) :=
    Set.range (fun v : V.underlying.W => (Sum.inr v, Sum.inr v))
  have hLL : IsCompact LL := by
    exact isCompact_range (continuous_inl.prodMk continuous_inl)
  have hLR : IsCompact LR := by
    exact isCompact_range
      ((continuous_inl.comp
          W.underlying.outgoingBoundaryTopMap.hom.continuous).prodMk
        (continuous_inr.comp
          V.underlying.incomingBoundaryTopMap.hom.continuous))
  have hRL : IsCompact RL := by
    exact isCompact_range
      ((continuous_inr.comp
          V.underlying.incomingBoundaryTopMap.hom.continuous).prodMk
        (continuous_inl.comp
          W.underlying.outgoingBoundaryTopMap.hom.continuous))
  have hRR : IsCompact RR := by
    exact isCompact_range (continuous_inr.prodMk continuous_inr)
  have hkernel :
      {p : (W.underlying.W ⊕ V.underlying.W) ×
          (W.underlying.W ⊕ V.underlying.W) |
        W.topologicalGluingQuotient V p.1 =
          W.topologicalGluingQuotient V p.2} =
        LL ∪ LR ∪ RL ∪ RR := by
    ext p
    rcases p with ⟨a, b⟩
    cases a with
    | inl w =>
        cases b with
        | inl w' =>
            simp only [Set.mem_setOf_eq, Set.mem_union,
              topologicalGluingQuotient, Sum.elim_inl, LL, LR, RL, RR]
            constructor
            · intro h
              left
              left
              left
              exact ⟨w, by
                rw [Prod.mk.injEq, Sum.inl.injEq, Sum.inl.injEq]
                exact ⟨rfl, W.topologicalGluingInl_injective V h⟩⟩
            · rintro (((⟨z, h⟩ | ⟨_, h⟩) | ⟨_, h⟩) | ⟨_, h⟩)
              · exact congrArg (W.topologicalGluingInl V)
                  ((by simpa using (Prod.mk.inj h).1 : z = w).symm.trans
                    (by simpa using (Prod.mk.inj h).2 : z = w'))
              · simp at h
              · simp at h
              · simp at h
        | inr v =>
            simp only [Set.mem_setOf_eq, Set.mem_union,
              topologicalGluingQuotient, Sum.elim_inl, Sum.elim_inr,
              LL, LR, RL, RR]
            constructor
            · intro h
              left
              left
              right
              obtain ⟨x, hxw, hxv⟩ :=
                (W.topologicalGluingInl_eq_inr_iff V w v).mp h
              exact ⟨x, by
                rw [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq]
                exact ⟨hxw, hxv⟩⟩
            · rintro (((⟨_, h⟩ | ⟨x, h⟩) | ⟨_, h⟩) | ⟨_, h⟩)
              · simp at h
              · exact (W.topologicalGluingInl_eq_inr_iff V w v).mpr
                  ⟨x, (by simpa using (Prod.mk.inj h).1),
                    (by simpa using (Prod.mk.inj h).2)⟩
              · simp at h
              · simp at h
    | inr v =>
        cases b with
        | inl w =>
            simp only [Set.mem_setOf_eq, Set.mem_union,
              topologicalGluingQuotient, Sum.elim_inl, Sum.elim_inr,
              LL, LR, RL, RR]
            constructor
            · intro h
              left
              right
              obtain ⟨x, hxw, hxv⟩ :=
                (W.topologicalGluingInl_eq_inr_iff V w v).mp h.symm
              exact ⟨x, by
                rw [Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq]
                exact ⟨hxv, hxw⟩⟩
            · rintro (((⟨_, h⟩ | ⟨_, h⟩) | ⟨x, h⟩) | ⟨_, h⟩)
              · simp at h
              · simp at h
              · exact ((W.topologicalGluingInl_eq_inr_iff V w v).mpr
                  ⟨x, (by simpa using (Prod.mk.inj h).2),
                    (by simpa using (Prod.mk.inj h).1)⟩).symm
              · simp at h
        | inr v' =>
            simp only [Set.mem_setOf_eq, Set.mem_union,
              topologicalGluingQuotient, Sum.elim_inr,
              LL, LR, RL, RR]
            constructor
            · intro h
              right
              exact ⟨v, by
                rw [Prod.mk.injEq, Sum.inr.injEq, Sum.inr.injEq]
                exact ⟨rfl, W.topologicalGluingInr_injective V h⟩⟩
            · rintro (((⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩) | ⟨z, h⟩)
              · simp at h
              · simp at h
              · simp at h
              · exact congrArg (W.topologicalGluingInr V)
                  ((by simpa using (Prod.mk.inj h).1 : z = v).symm.trans
                    (by simpa using (Prod.mk.inj h).2 : z = v'))
  rw [hkernel]
  exact (((hLL.union hLR).union hRL).union hRR).isClosed

/--
The topological pushout obtained by gluing two compact chosen-collared oriented cobordisms
along their common parametrized boundary is Hausdorff.
-/
theorem topologicalGluingCarrier_t2Space
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    T2Space (W.topologicalGluingCarrier V) :=
  t2Space_of_compact_closed_kernel_quotient
    (W.topologicalGluingQuotient V)
    (W.topologicalGluingQuotient_isQuotientMap V)
    (W.topologicalGluingQuotient_kernel_isClosed V)

end CollaredOrientedParametrizedSmoothCobordism

end

end Cob2GeometricPrelude
