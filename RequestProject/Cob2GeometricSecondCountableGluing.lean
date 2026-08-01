import RequestProject.Cob2GeometricHausdorffGluing
import Mathlib.Topology.Compactness.Bases

/-!
# Second countability of the topological cobordism gluing

This file proves that the compact Hausdorff `TopCat` pushout used to glue two
chosen-collared oriented cobordisms is second countable.

The general argument starts with a continuous surjection from a compact
second-countable space to a Hausdorff space.  Such a map is closed.  Finite
subcovers of its compact fibers then turn finite unions of a countable source
basis into a countable basis downstairs.

Applied to the canonical quotient from the disjoint union of the two surface
carriers, this equips the already constructed gluing carrier with the remaining
global countability property expected of a surface.  It does not construct
local Euclidean charts, a manifold-with-boundary structure, a compatible
smooth atlas, or a smooth cobordism composition law.
-/

open Set
open TopologicalSpace

universe u v

namespace Cob2GeometricPrelude

noncomputable section

/--
A continuous surjective image of a compact second-countable space in a
Hausdorff space is second countable.

The countable candidate basis consists of kernel images of finite unions of
elements of a countable source basis.  Closedness of the map makes these
kernel images open, while compactness of each fiber supplies the finite
subcover needed for the neighborhood-basis property.
-/
theorem secondCountableTopology_of_compact_surjective
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hsurj : Function.Surjective f) :
    SecondCountableTopology Y := by
  classical
  let B : Set (Set Y) :=
    Set.range fun s : Finset (countableBasis X) =>
      kernImage f (⋃ b ∈ s, (b : Set X))
  have hclosed : IsClosedMap f := hf.isClosedMap
  have hBopen : ∀ U ∈ B, IsOpen U := by
    rintro U ⟨s, rfl⟩
    rw [isClosedMap_iff_kernImage] at hclosed
    apply hclosed
    exact isOpen_biUnion fun b _ => isOpen_of_mem_countableBasis b.2
  have hBbasis : IsTopologicalBasis B := by
    apply isTopologicalBasis_of_isOpen_of_nhds hBopen
    intro y U hyU hU
    have hfiberCompact : IsCompact (f ⁻¹' ({y} : Set Y)) :=
      (isClosed_singleton.preimage hf).isCompact
    have hchoice :
        ∀ x : f ⁻¹' ({y} : Set Y),
          ∃ b : countableBasis X,
            x.1 ∈ (b : Set X) ∧ (b : Set X) ⊆ f ⁻¹' U := by
      intro x
      have hxU : x.1 ∈ f ⁻¹' U := by
        have hxy : f x.1 ∈ ({y} : Set Y) := x.2
        change f x.1 = y at hxy
        change f x.1 ∈ U
        rw [hxy]
        exact hyU
      obtain ⟨b, hb, hxb, hbU⟩ :=
        (isBasis_countableBasis X).exists_subset_of_mem_open
          hxU (hU.preimage hf)
      exact ⟨⟨b, hb⟩, hxb, hbU⟩
    choose bOf hbOf_mem hbOf_sub using hchoice
    have hcover :
        f ⁻¹' ({y} : Set Y) ⊆
          ⋃ x : f ⁻¹' ({y} : Set Y), (bOf x : Set X) := by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hbOf_mem ⟨x, hx⟩⟩
    obtain ⟨t, ht⟩ :=
      hfiberCompact.elim_finite_subcover
        (fun x : f ⁻¹' ({y} : Set Y) => (bOf x : Set X))
        (fun x => isOpen_of_mem_countableBasis (bOf x).2)
        hcover
    let s : Finset (countableBasis X) := t.image bOf
    refine
      ⟨kernImage f (⋃ b ∈ s, (b : Set X)), ⟨s, rfl⟩, ?_, ?_⟩
    · intro x hxy
      have hxcover := ht (by simpa using hxy)
      rcases mem_iUnion.mp hxcover with ⟨q, hq⟩
      rcases mem_iUnion.mp hq with ⟨hqt, hxq⟩
      exact mem_iUnion.mpr
        ⟨bOf q, mem_iUnion.mpr
          ⟨by simpa [s] using Finset.mem_image_of_mem bOf hqt, hxq⟩⟩
    · intro z hz
      obtain ⟨x, hxz⟩ := hsurj z
      have hx : x ∈ ⋃ b ∈ s, (b : Set X) := hz hxz
      rcases mem_iUnion.mp hx with ⟨b, hb⟩
      rcases mem_iUnion.mp hb with ⟨hbs, hxb⟩
      obtain ⟨q, hqt, hqb⟩ := Finset.mem_image.mp hbs
      subst b
      exact hxz ▸ hbOf_sub q hxb
  exact hBbasis.secondCountableTopology (countable_range _)

namespace CollaredOrientedParametrizedSmoothCobordism

variable {M N P : OrientedClosedSmoothOneManifold}

/--
The topological pushout obtained by gluing two compact chosen-collared
oriented cobordisms along their common parametrized boundary is second
countable.
-/
theorem topologicalGluingCarrier_secondCountable
    (W : CollaredOrientedParametrizedSmoothCobordism M N)
    (V : CollaredOrientedParametrizedSmoothCobordism N P) :
    SecondCountableTopology (W.topologicalGluingCarrier V) := by
  letI : T2Space (W.topologicalGluingCarrier V) :=
    W.topologicalGluingCarrier_t2Space V
  exact
    secondCountableTopology_of_compact_surjective
      (W.topologicalGluingQuotient V)
      (W.topologicalGluingQuotient_continuous V)
      (W.topologicalGluingQuotient_surjective V)

end CollaredOrientedParametrizedSmoothCobordism

end

end Cob2GeometricPrelude
