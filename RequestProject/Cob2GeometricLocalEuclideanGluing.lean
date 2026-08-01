import RequestProject.Cob2GeometricSecondCountableGluing
import Mathlib.Topology.Piecewise

/-!
# Local Euclidean structure on the topological cobordism gluing

This file equips the canonical compact Hausdorff, second-countable topological
pushout of two chosen-collared oriented cobordisms with charts modelled on
`SurfaceModelSpace`.  Away from the seam, its charts are transported through
the canonical inclusions of the two original surfaces.  At the seam, the two
chosen half-collars are joined into a signed collar with parameter interval
`[-1,1]`; this map is proved to be a local homeomorphism along its zero slice.

The resulting `topologicalGluingChartedSpace` and
`topologicalGluingCarrier_isManifold_zero` establish only the topological
(`C⁰`) local-Euclidean-with-boundary layer.  They do not prove smooth
compatibility of chart transitions, construct a smooth atlas on the glued
carrier, define smooth cobordism composition, or prove identity and
associativity laws.
-/

open Set
open CategoryTheory
open scoped Manifold ContDiff Topology

namespace Cob2GeometricPrelude

noncomputable section

namespace CollaredOrientedParametrizedSmoothCobordism

variable {M N P : OrientedClosedSmoothOneManifold}

def outgoingCollarDomain (M N : OrientedClosedSmoothOneManifold) :
    Set ((M.toClosedSmoothOneManifold.M ⊕ N.toClosedSmoothOneManifold.M) ×
      Set.Icc (0 : ℝ) 1) :=
  Prod.fst ⁻¹' Set.range Sum.inr

def incomingCollarDomain (N P : OrientedClosedSmoothOneManifold) :
    Set ((N.toClosedSmoothOneManifold.M ⊕ P.toClosedSmoothOneManifold.M) ×
      Set.Icc (0 : ℝ) 1) :=
  Prod.fst ⁻¹' Set.range Sum.inl

theorem outgoingCollarDomain_isOpen
    (M N : OrientedClosedSmoothOneManifold) :
    IsOpen (outgoingCollarDomain M N) :=
  isOpen_range_inr.preimage continuous_fst

theorem incomingCollarDomain_isOpen
    (N P : OrientedClosedSmoothOneManifold) :
    IsOpen (incomingCollarDomain N P) :=
  isOpen_range_inl.preimage continuous_fst

def outgoingHalfCollarRange
    (W : CollaredOrientedParametrizedSmoothCobordism M N) : Set W.underlying.W :=
  W.collar.collarMap '' outgoingCollarDomain M N

def incomingHalfCollarRange
    (V : CollaredOrientedParametrizedSmoothCobordism N P) : Set V.underlying.W :=
  V.collar.collarMap '' incomingCollarDomain N P

theorem outgoingHalfCollarRange_mem_nhds
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (x : N.toClosedSmoothOneManifold.M) :
    outgoingHalfCollarRange W ∈
      nhds (W.underlying.boundaryMap (Sum.inr x)) := by
  let p :
      (M.toClosedSmoothOneManifold.M ⊕ N.toClosedSmoothOneManifold.M) ×
        Set.Icc (0 : ℝ) 1 :=
    (Sum.inr x, ⊥)
  have hrange : Set.range W.collar.collarMap ∈
      nhds (W.collar.collarMap p) := by
    simpa [p, W.collar.collarMap_zero] using
      W.collar.range_mem_nhds (Sum.inr x)
  have hmap := W.collar.collarMap_isEmbedding.map_nhds_of_mem p hrange
  rw [← W.collar.collarMap_zero (Sum.inr x), ← hmap]
  rw [Filter.mem_map]
  change W.collar.collarMap ⁻¹'
      (W.collar.collarMap '' outgoingCollarDomain M N) ∈ nhds p
  rw [Set.preimage_image_eq _ W.collar.collarMap_isEmbedding.injective]
  exact (outgoingCollarDomain_isOpen M N).mem_nhds ⟨x, rfl⟩

theorem incomingHalfCollarRange_mem_nhds
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (x : N.toClosedSmoothOneManifold.M) :
    incomingHalfCollarRange V ∈
      nhds (V.underlying.boundaryMap (Sum.inl x)) := by
  let p :
      (N.toClosedSmoothOneManifold.M ⊕ P.toClosedSmoothOneManifold.M) ×
        Set.Icc (0 : ℝ) 1 :=
    (Sum.inl x, ⊥)
  have hrange : Set.range V.collar.collarMap ∈
      nhds (V.collar.collarMap p) := by
    simpa [p, V.collar.collarMap_zero] using
      V.collar.range_mem_nhds (Sum.inl x)
  have hmap := V.collar.collarMap_isEmbedding.map_nhds_of_mem p hrange
  rw [← V.collar.collarMap_zero (Sum.inl x), ← hmap]
  rw [Filter.mem_map]
  change V.collar.collarMap ⁻¹'
      (V.collar.collarMap '' incomingCollarDomain N P) ∈ nhds p
  rw [Set.preimage_image_eq _ V.collar.collarMap_isEmbedding.injective]
  exact (incomingCollarDomain_isOpen N P).mem_nhds ⟨x, rfl⟩

abbrev SignedCollarParameter := Set.Icc (-1 : ℝ) 1

def signedNegativePart (t : SignedCollarParameter) : Set.Icc (0 : ℝ) 1 :=
  ⟨max (-t.1) 0, le_max_right _ _, max_le (by linarith [t.2.1]) zero_le_one⟩

def signedPositivePart (t : SignedCollarParameter) : Set.Icc (0 : ℝ) 1 :=
  ⟨max t.1 0, le_max_right _ _, max_le t.2.2 zero_le_one⟩

theorem signedNegativePart_continuous : Continuous signedNegativePart := by
  apply Continuous.subtype_mk
  fun_prop

theorem signedPositivePart_continuous : Continuous signedPositivePart := by
  apply Continuous.subtype_mk
  fun_prop

@[simp] theorem signedNegativePart_zero :
    signedNegativePart (⟨0, by norm_num⟩ : SignedCollarParameter) = ⊥ := by
  ext
  simp [signedNegativePart]

@[simp] theorem signedPositivePart_zero :
    signedPositivePart (⟨0, by norm_num⟩ : SignedCollarParameter) = ⊥ := by
  ext
  simp [signedPositivePart]

theorem signedNegativePart_coe_of_nonpos (t : SignedCollarParameter)
    (ht : (t : ℝ) ≤ 0) :
    (signedNegativePart t : ℝ) = -t := by
  simp [signedNegativePart, max_eq_left (neg_nonneg.mpr ht)]

theorem signedPositivePart_coe_of_nonneg (t : SignedCollarParameter)
    (ht : 0 ≤ (t : ℝ)) :
    (signedPositivePart t : ℝ) = t := by
  simp [signedPositivePart, max_eq_left ht]

def signedCollarMap
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    N.toClosedSmoothOneManifold.M × SignedCollarParameter →
      W.topologicalGluingCarrier V :=
  fun p =>
    if (p.2 : ℝ) ≤ 0 then
      W.topologicalGluingInl V
        (W.collar.collarMap (Sum.inr p.1, signedNegativePart p.2))
    else
      W.topologicalGluingInr V
        (V.collar.collarMap (Sum.inl p.1, signedPositivePart p.2))

@[simp] theorem signedCollarMap_zero
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (x : N.toClosedSmoothOneManifold.M) :
    signedCollarMap W V (x, ⟨0, by norm_num⟩) =
      W.topologicalGluingInl V (W.underlying.boundaryMap (Sum.inr x)) := by
  simp [signedCollarMap, W.collar.collarMap_zero]

theorem signedCollarMap_continuous
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    Continuous (signedCollarMap W V) := by
  let f : N.toClosedSmoothOneManifold.M × SignedCollarParameter →
      W.topologicalGluingCarrier V := fun p =>
    W.topologicalGluingInl V
      (W.collar.collarMap (Sum.inr p.1, signedNegativePart p.2))
  let g : N.toClosedSmoothOneManifold.M × SignedCollarParameter →
      W.topologicalGluingCarrier V := fun p =>
    W.topologicalGluingInr V
      (V.collar.collarMap (Sum.inl p.1, signedPositivePart p.2))
  change Continuous (fun p => if (p.2 : ℝ) ≤ 0 then f p else g p)
  apply continuous_if_le (continuous_subtype_val.comp continuous_snd) continuous_const
  · exact ((W.topologicalGluingInl V).hom.continuous.comp
      W.collar.collarMap_contMDiff.continuous).comp
        ((continuous_inr.comp continuous_fst).prodMk
          (signedNegativePart_continuous.comp continuous_snd)) |>.continuousOn
  · exact ((W.topologicalGluingInr V).hom.continuous.comp
      V.collar.collarMap_contMDiff.continuous).comp
        ((continuous_inl.comp continuous_fst).prodMk
          (signedPositivePart_continuous.comp continuous_snd)) |>.continuousOn
  · intro p hp
    rcases p with ⟨x, t⟩
    have hp0 : t = (⟨0, by norm_num⟩ : SignedCollarParameter) := by
      ext
      exact hp
    subst hp0
    dsimp [f, g]
    simpa [W.collar.collarMap_zero, V.collar.collarMap_zero] using
      W.topologicalGluing_seam V x

theorem signedCollarMap_injective
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    Function.Injective (signedCollarMap W V) := by
  intro p q hpq
  by_cases hp : (p.2 : ℝ) ≤ 0
  · by_cases hq : (q.2 : ℝ) ≤ 0
    · have hcollar := W.collar.collarMap_isEmbedding.injective
          (W.topologicalGluingInl_injective V
            (by simpa [signedCollarMap, hp, hq] using hpq))
      have hx : p.1 = q.1 := by
        simpa using congrArg (fun z => z.1) hcollar
      have htneg : (signedNegativePart p.2 : ℝ) =
          (signedNegativePart q.2 : ℝ) := by
        exact congrArg (fun z => (z.2 : ℝ)) hcollar
      have ht : p.2 = q.2 := by
        apply Subtype.ext
        rw [signedNegativePart_coe_of_nonpos p.2 hp,
          signedNegativePart_coe_of_nonpos q.2 hq] at htneg
        linarith
      exact Prod.ext hx ht

    · have hcross :
          W.topologicalGluingInl V
              (W.collar.collarMap (Sum.inr p.1, signedNegativePart p.2)) =
            W.topologicalGluingInr V
              (V.collar.collarMap (Sum.inl q.1, signedPositivePart q.2)) := by
          simpa [signedCollarMap, hp, hq] using hpq
      obtain ⟨z, hzW, hzV⟩ :=
        (W.topologicalGluingInl_eq_inr_iff V _ _).mp hcross
      have hVparams := V.collar.collarMap_isEmbedding.injective
        (hzV.symm.trans (V.collar.collarMap_zero (Sum.inl z)).symm)
      have hnormal : (signedPositivePart q.2 : ℝ) = 0 := by
        simpa using congrArg (fun z => (z.2 : ℝ)) hVparams
      rw [signedPositivePart_coe_of_nonneg q.2 (le_of_not_ge hq)] at hnormal
      exact (hq (by linarith)).elim
  · by_cases hq : (q.2 : ℝ) ≤ 0
    · have hcross :
          W.topologicalGluingInl V
              (W.collar.collarMap (Sum.inr q.1, signedNegativePart q.2)) =
            W.topologicalGluingInr V
              (V.collar.collarMap (Sum.inl p.1, signedPositivePart p.2)) := by
          simpa [signedCollarMap, hp, hq] using hpq.symm
      obtain ⟨z, hzW, hzV⟩ :=
        (W.topologicalGluingInl_eq_inr_iff V _ _).mp hcross
      have hVparams := V.collar.collarMap_isEmbedding.injective
        (hzV.symm.trans (V.collar.collarMap_zero (Sum.inl z)).symm)
      have hnormal : (signedPositivePart p.2 : ℝ) = 0 := by
        simpa using congrArg (fun z => (z.2 : ℝ)) hVparams
      rw [signedPositivePart_coe_of_nonneg p.2 (le_of_not_ge hp)] at hnormal
      exact (hp (by linarith)).elim
    · have hcollar := V.collar.collarMap_isEmbedding.injective
          (W.topologicalGluingInr_injective V
            (by simpa [signedCollarMap, hp, hq] using hpq))
      have hx : p.1 = q.1 := by
        simpa using congrArg (fun z => z.1) hcollar
      have htpos : (signedPositivePart p.2 : ℝ) =
          (signedPositivePart q.2 : ℝ) := by
        exact congrArg (fun z => (z.2 : ℝ)) hcollar
      have ht : p.2 = q.2 := by
        apply Subtype.ext
        rw [signedPositivePart_coe_of_nonneg p.2 (le_of_not_ge hp),
          signedPositivePart_coe_of_nonneg q.2 (le_of_not_ge hq)] at htpos
        exact htpos
      exact Prod.ext hx ht

theorem signedCollarMap_isClosedEmbedding
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    Topology.IsClosedEmbedding (signedCollarMap W V) := by
  letI : T2Space (W.topologicalGluingCarrier V) :=
    W.topologicalGluingCarrier_t2Space V
  exact (signedCollarMap_continuous W V).isClosedEmbedding
    (signedCollarMap_injective W V)

theorem topologicalGluingInl_outgoingHalfCollar_mem_signedRange
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    {w : W.underlying.W} (hw : w ∈ outgoingHalfCollarRange W) :
    W.topologicalGluingInl V w ∈ Set.range (signedCollarMap W V) := by
  rcases hw with ⟨p, hp, rfl⟩
  obtain ⟨x, hx⟩ := hp
  have hx' : p.1 = Sum.inr x := hx.symm
  rcases p with ⟨b, t⟩
  dsimp only at hx'
  subst b
  let s : SignedCollarParameter :=
    ⟨-(t : ℝ), by constructor <;> linarith [t.2.1, t.2.2]⟩
  refine ⟨(x, s), ?_⟩
  have hs : (s : ℝ) ≤ 0 := by dsimp [s]; linarith [t.2.1]
  simp only [signedCollarMap, hs, if_pos]
  have hn : signedNegativePart s = t := by
    apply Subtype.ext
    rw [signedNegativePart_coe_of_nonpos s hs]
    simp [s]
  rw [hn]

theorem topologicalGluingInr_incomingHalfCollar_mem_signedRange
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    {v : V.underlying.W} (hv : v ∈ incomingHalfCollarRange V) :
    W.topologicalGluingInr V v ∈ Set.range (signedCollarMap W V) := by
  rcases hv with ⟨p, hp, rfl⟩
  obtain ⟨x, hx⟩ := hp
  have hx' : p.1 = Sum.inl x := hx.symm
  rcases p with ⟨b, t⟩
  dsimp only at hx'
  subst b
  let s : SignedCollarParameter :=
    ⟨(t : ℝ), by constructor <;> linarith [t.2.1, t.2.2]⟩
  by_cases ht : (t : ℝ) = 0
  · have ht' : t = (⊥ : Set.Icc (0 : ℝ) 1) := Subtype.ext ht
    subst t
    refine ⟨(x, ⟨0, by norm_num⟩), ?_⟩
    simpa [signedCollarMap, V.collar.collarMap_zero] using
      W.topologicalGluing_collar_zero V x
  · have hspos : 0 < (s : ℝ) := by
      dsimp [s]
      exact lt_of_le_of_ne t.2.1 (Ne.symm ht)
    refine ⟨(x, s), ?_⟩
    simp only [signedCollarMap]
    rw [if_neg (not_le.mpr hspos)]
    have hn : signedPositivePart s = t := by
      apply Subtype.ext
      rw [signedPositivePart_coe_of_nonneg s hspos.le]
    rw [hn]

theorem signedCollarMap_range_mem_nhds
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (x : N.toClosedSmoothOneManifold.M) :
    Set.range (signedCollarMap W V) ∈
      nhds (signedCollarMap W V (x, ⟨0, by norm_num⟩)) := by
  letI : T2Space (W.topologicalGluingCarrier V) :=
    W.topologicalGluingCarrier_t2Space V
  obtain ⟨OW, hOWsub, hOWopen, hxOW⟩ :=
    mem_nhds_iff.mp (outgoingHalfCollarRange_mem_nhds W x)
  obtain ⟨OV, hOVsub, hOVopen, hxOV⟩ :=
    mem_nhds_iff.mp (incomingHalfCollarRange_mem_nhds V x)
  let q := W.topologicalGluingQuotient V
  let A : Set (W.underlying.W ⊕ V.underlying.W) :=
    Sum.inl '' OW ∪ Sum.inr '' OV
  have hAopen : IsOpen A := by
    exact (isOpenMap_inl OW hOWopen).union (isOpenMap_inr OV hOVopen)
  have hqclosed : IsClosedMap q :=
    (W.topologicalGluingQuotient_continuous V).isClosedMap
  have hKopen : IsOpen (kernImage q A) :=
    (isClosedMap_iff_kernImage.mp hqclosed) hAopen
  let seam := W.topologicalGluingInl V
    (W.underlying.boundaryMap (Sum.inr x))
  have hseamK : seam ∈ kernImage q A := by
    intro y hy
    cases y with
    | inl w =>
        change W.topologicalGluingInl V w =
          W.topologicalGluingInl V
            (W.underlying.boundaryMap (Sum.inr x)) at hy
        have hw : w = W.underlying.boundaryMap (Sum.inr x) :=
          W.topologicalGluingInl_injective V hy
        left
        refine ⟨W.underlying.boundaryMap (Sum.inr x), hxOW, ?_⟩
        exact congrArg Sum.inl hw.symm
    | inr v =>
        change W.topologicalGluingInr V v =
          W.topologicalGluingInl V
            (W.underlying.boundaryMap (Sum.inr x)) at hy
        have hy' : W.topologicalGluingInr V v =
            W.topologicalGluingInr V
              (V.underlying.boundaryMap (Sum.inl x)) :=
          hy.trans (W.topologicalGluing_seam V x)
        have hv : v = V.underlying.boundaryMap (Sum.inl x) :=
          W.topologicalGluingInr_injective V hy'
        right
        exact ⟨V.underlying.boundaryMap (Sum.inl x), hxOV,
          congrArg Sum.inr hv.symm⟩
  have hKnhds : kernImage q A ∈ nhds seam := hKopen.mem_nhds hseamK
  have hKsub : kernImage q A ⊆ Set.range (signedCollarMap W V) := by
    intro z hz
    obtain ⟨y, rfl⟩ := W.topologicalGluingQuotient_surjective V z
    have hyA : y ∈ A := hz rfl
    rcases hyA with ⟨w, hw, rfl⟩ | ⟨v, hv, rfl⟩
    · simpa [q, topologicalGluingQuotient] using
        (topologicalGluingInl_outgoingHalfCollar_mem_signedRange
          W V (hOWsub hw))
    · simpa [q, topologicalGluingQuotient] using
        (topologicalGluingInr_incomingHalfCollar_mem_signedRange
          W V (hOVsub hv))
  have : Set.range (signedCollarMap W V) ∈ nhds seam :=
    Filter.mem_of_superset hKnhds hKsub
  rw [signedCollarMap_zero W V x]
  exact this

example : ChartedSpace SurfaceModelSpace
    (N.toClosedSmoothOneManifold.M × SignedCollarParameter) := by
  letI : Fact ((-1 : ℝ) < 1) := ⟨by norm_num⟩
  infer_instance

theorem exists_localChart_of_embedding_range_mem_nhds
    {X Y H : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace H] [ChartedSpace H X]
    (f : X → Y) (x : X) (hf : Topology.IsEmbedding f)
    (hrange : Set.range f ∈ nhds (f x)) :
    ∃ e : OpenPartialHomeomorph Y H, f x ∈ e.source := by
  have hlocal : IsLocalHomeomorphOn f ({x} : Set X) := by
    rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    let U : Set X := f ⁻¹' interior (Set.range f)
    have hxint : f x ∈ interior (Set.range f) :=
      mem_interior_iff_mem_nhds.mpr hrange
    have hUnhds : U ∈ nhds x :=
      (isOpen_interior.preimage hf.continuous).mem_nhds hxint
    refine ⟨U, hUnhds, ?_⟩
    refine ⟨hf.comp Topology.IsEmbedding.subtypeVal, ?_⟩
    rw [Set.range_restrict, Set.image_preimage_eq_inter_range]
    rw [inter_eq_left.mpr interior_subset]
    exact isOpen_interior
  obtain ⟨e, hxe, heq⟩ := hlocal x (Set.mem_singleton x)
  let c : OpenPartialHomeomorph Y H := e.symm.trans (chartAt H x)
  refine ⟨c, ?_⟩
  change f x ∈ e.symm.source ∩ e.symm ⁻¹' (chartAt H x).source
  constructor
  · rw [heq]
    exact e.map_source hxe
  · change e.symm (f x) ∈ (chartAt H x).source
    rw [heq, e.left_inv hxe]
    exact mem_chart_source H x

theorem exists_signedSeamChart
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (x : N.toClosedSmoothOneManifold.M) :
    ∃ e : OpenPartialHomeomorph (W.topologicalGluingCarrier V)
        SurfaceModelSpace,
      W.topologicalGluingInl V
          (W.underlying.boundaryMap (Sum.inr x)) ∈ e.source := by
  letI : Fact ((-1 : ℝ) < 1) := ⟨by norm_num⟩
  let p : N.toClosedSmoothOneManifold.M × SignedCollarParameter :=
    (x, ⟨0, by norm_num⟩)
  have h := exists_localChart_of_embedding_range_mem_nhds
    (H := SurfaceModelSpace)
    (signedCollarMap W V) p
    (signedCollarMap_isClosedEmbedding W V).isEmbedding
    (signedCollarMap_range_mem_nhds W V x)
  simpa [p, signedCollarMap_zero W V x] using h

theorem topologicalGluingInl_isClosedEmbedding
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    Topology.IsClosedEmbedding (W.topologicalGluingInl V) := by
  letI : T2Space (W.topologicalGluingCarrier V) :=
    W.topologicalGluingCarrier_t2Space V
  exact (W.topologicalGluingInl V).hom.continuous.isClosedEmbedding
    (W.topologicalGluingInl_injective V)

theorem topologicalGluingInr_isClosedEmbedding
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    Topology.IsClosedEmbedding (W.topologicalGluingInr V) := by
  letI : T2Space (W.topologicalGluingCarrier V) :=
    W.topologicalGluingCarrier_t2Space V
  exact (W.topologicalGluingInr V).hom.continuous.isClosedEmbedding
    (W.topologicalGluingInr_injective V)

theorem topologicalGluingInl_range_mem_nhds_of_not_seam
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (w : W.underlying.W)
    (hw : w ∉ Set.range W.underlying.outgoingBoundaryTopMap) :
    Set.range (W.topologicalGluingInl V) ∈
      nhds (W.topologicalGluingInl V w) := by
  letI : T2Space (W.topologicalGluingCarrier V) :=
    W.topologicalGluingCarrier_t2Space V
  let O : Set W.underlying.W :=
    (Set.range W.underlying.outgoingBoundaryTopMap)ᶜ
  let q := W.topologicalGluingQuotient V
  let A : Set (W.underlying.W ⊕ V.underlying.W) := Sum.inl '' O
  have hOopen : IsOpen O :=
    W.underlying.outgoingBoundaryTopMap_isClosedEmbedding.isClosed_range.isOpen_compl
  have hAopen : IsOpen A := isOpenMap_inl O hOopen
  have hqclosed : IsClosedMap q :=
    (W.topologicalGluingQuotient_continuous V).isClosedMap
  have hKopen : IsOpen (kernImage q A) :=
    (isClosedMap_iff_kernImage.mp hqclosed) hAopen
  have hpointK : W.topologicalGluingInl V w ∈ kernImage q A := by
    intro y hy
    cases y with
    | inl w' =>
        change W.topologicalGluingInl V w' =
          W.topologicalGluingInl V w at hy
        have hww : w' = w := W.topologicalGluingInl_injective V hy
        refine ⟨w, ?_, congrArg Sum.inl hww.symm⟩
        exact hw
    | inr v =>
        change W.topologicalGluingInr V v =
          W.topologicalGluingInl V w at hy
        obtain ⟨x, hxW, hxV⟩ :=
          (W.topologicalGluingInl_eq_inr_iff V w v).mp hy.symm
        exact (hw ⟨x, hxW⟩).elim
  have hKnhds : kernImage q A ∈ nhds (W.topologicalGluingInl V w) :=
    hKopen.mem_nhds hpointK
  apply Filter.mem_of_superset hKnhds
  intro z hz
  obtain ⟨y, rfl⟩ := W.topologicalGluingQuotient_surjective V z
  have hyA : y ∈ A := hz rfl
  rcases hyA with ⟨w', hw', rfl⟩
  exact ⟨w', rfl⟩

theorem topologicalGluingInr_range_mem_nhds_of_not_seam
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (v : V.underlying.W)
    (hv : v ∉ Set.range V.underlying.incomingBoundaryTopMap) :
    Set.range (W.topologicalGluingInr V) ∈
      nhds (W.topologicalGluingInr V v) := by
  letI : T2Space (W.topologicalGluingCarrier V) :=
    W.topologicalGluingCarrier_t2Space V
  let O : Set V.underlying.W :=
    (Set.range V.underlying.incomingBoundaryTopMap)ᶜ
  let q := W.topologicalGluingQuotient V
  let A : Set (W.underlying.W ⊕ V.underlying.W) := Sum.inr '' O
  have hOopen : IsOpen O :=
    V.underlying.incomingBoundaryTopMap_isClosedEmbedding.isClosed_range.isOpen_compl
  have hAopen : IsOpen A := isOpenMap_inr O hOopen
  have hqclosed : IsClosedMap q :=
    (W.topologicalGluingQuotient_continuous V).isClosedMap
  have hKopen : IsOpen (kernImage q A) :=
    (isClosedMap_iff_kernImage.mp hqclosed) hAopen
  have hpointK : W.topologicalGluingInr V v ∈ kernImage q A := by
    intro y hy
    cases y with
    | inr v' =>
        change W.topologicalGluingInr V v' =
          W.topologicalGluingInr V v at hy
        have hvv : v' = v := W.topologicalGluingInr_injective V hy
        refine ⟨v, ?_, congrArg Sum.inr hvv.symm⟩
        exact hv
    | inl w =>
        change W.topologicalGluingInl V w =
          W.topologicalGluingInr V v at hy
        obtain ⟨x, hxW, hxV⟩ :=
          (W.topologicalGluingInl_eq_inr_iff V w v).mp hy
        exact (hv ⟨x, hxV⟩).elim
  have hKnhds : kernImage q A ∈ nhds (W.topologicalGluingInr V v) :=
    hKopen.mem_nhds hpointK
  apply Filter.mem_of_superset hKnhds
  intro z hz
  obtain ⟨y, rfl⟩ := W.topologicalGluingQuotient_surjective V z
  have hyA : y ∈ A := hz rfl
  rcases hyA with ⟨v', hv', rfl⟩
  exact ⟨v', rfl⟩

theorem exists_topologicalGluingInlChart_of_not_seam
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (w : W.underlying.W)
    (hw : w ∉ Set.range W.underlying.outgoingBoundaryTopMap) :
    ∃ e : OpenPartialHomeomorph (W.topologicalGluingCarrier V)
        SurfaceModelSpace,
      W.topologicalGluingInl V w ∈ e.source :=
  exists_localChart_of_embedding_range_mem_nhds
    (W.topologicalGluingInl V) w
    (topologicalGluingInl_isClosedEmbedding W V).isEmbedding
    (topologicalGluingInl_range_mem_nhds_of_not_seam W V w hw)

theorem exists_topologicalGluingInrChart_of_not_seam
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (v : V.underlying.W)
    (hv : v ∉ Set.range V.underlying.incomingBoundaryTopMap) :
    ∃ e : OpenPartialHomeomorph (W.topologicalGluingCarrier V)
        SurfaceModelSpace,
      W.topologicalGluingInr V v ∈ e.source :=
  exists_localChart_of_embedding_range_mem_nhds
    (W.topologicalGluingInr V) v
    (topologicalGluingInr_isClosedEmbedding W V).isEmbedding
    (topologicalGluingInr_range_mem_nhds_of_not_seam W V v hv)

theorem exists_topologicalGluingChart
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P)
    (z : W.topologicalGluingCarrier V) :
    ∃ e : OpenPartialHomeomorph (W.topologicalGluingCarrier V)
        SurfaceModelSpace, z ∈ e.source := by
  obtain ⟨y, hy⟩ := W.topologicalGluingQuotient_surjective V z
  subst z
  cases y with
  | inl w =>
      by_cases hw : w ∈ Set.range W.underlying.outgoingBoundaryTopMap
      · obtain ⟨x, hx⟩ := hw
        obtain ⟨e, he⟩ := exists_signedSeamChart W V x
        refine ⟨e, ?_⟩
        change W.topologicalGluingInl V w ∈ e.source
        rw [← hx]
        exact he
      · simpa [topologicalGluingQuotient] using
          exists_topologicalGluingInlChart_of_not_seam W V w hw
  | inr v =>
      by_cases hv : v ∈ Set.range V.underlying.incomingBoundaryTopMap
      · obtain ⟨x, hx⟩ := hv
        obtain ⟨e, he⟩ := exists_signedSeamChart W V x
        refine ⟨e, ?_⟩
        change W.topologicalGluingInr V v ∈ e.source
        rw [← hx]
        change W.topologicalGluingInr V
          (V.underlying.boundaryMap (Sum.inl x)) ∈ e.source
        rw [← W.topologicalGluing_seam V x]
        exact he
      · simpa [topologicalGluingQuotient] using
          exists_topologicalGluingInrChart_of_not_seam W V v hv

noncomputable def topologicalGluingChartedSpace
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    ChartedSpace SurfaceModelSpace (W.topologicalGluingCarrier V) where
  atlas := Set.range fun z => Classical.choose (exists_topologicalGluingChart W V z)
  chartAt z := Classical.choose (exists_topologicalGluingChart W V z)
  mem_chart_source z := Classical.choose_spec (exists_topologicalGluingChart W V z)
  chart_mem_atlas z := ⟨z, rfl⟩

theorem topologicalGluingCarrier_isManifold_zero
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    letI : ChartedSpace SurfaceModelSpace (W.topologicalGluingCarrier V) :=
      topologicalGluingChartedSpace W V
    IsManifold surfaceModel 0 (W.topologicalGluingCarrier V) := by
  infer_instance

end CollaredOrientedParametrizedSmoothCobordism
end
end Cob2GeometricPrelude
