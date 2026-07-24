import RequestProject.Cob2BoundaryPermutations

/-!
# Arbitrary boundary-adjacent invariance for ordered Cob2 spiders

The ordered multiplication and comultiplication combs were previously known
to absorb the first adjacent transposition.  This file proves reassociation
lemmas comparing their left- and right-recursive presentations, then uses
them to absorb an adjacent transposition after any number of leading wires.

The associator transports of the wrapped-arity source are handled explicitly:
they are exposed as raw equality transports and discharged by the quotient's
category relations.  No new presentation relation is introduced.

This supplies invariance under every individual adjacent boundary
transposition.  It does not yet bundle a full finite-permutation action or
prove an arbitrary-word spider normal form, and it makes no geometric-bordism
claim.
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace Cob2SpiderPermutations

open Cob2Spider Cob2Permutation Cob2BoundaryPermutations

private lemma merge_append_one (n : ℕ) :
    merge (n + 1) =
      (merge n ⊗ₘ 𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
        Cob2Symmetric.mul := by
  cases n with
  | zero =>
      change
        𝟙 (⟨1⟩ : Cob2SymmetricObj) =
          (Cob2Symmetric.unit ⊗ₘ
            𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
              Cob2Symmetric.mul
      simpa using
        Cob2Symmetric.canonicalFrobenius.unit_mul.symm
  | succ n =>
      simp

private lemma associator_one_hom_comp (n : ℕ) {Z : Cob2SymmetricObj}
    (f :
      ((⟨1⟩ : Cob2SymmetricObj) ⊗
        ((⟨n⟩ : Cob2SymmetricObj) ⊗
          (⟨1⟩ : Cob2SymmetricObj))) ⟶ Z) :
    (α_ (⟨1⟩ : Cob2SymmetricObj)
      (⟨n⟩ : Cob2SymmetricObj)
      (⟨1⟩ : Cob2SymmetricObj)).hom ≫ f = f := by
  rw [Cob2Symmetric.associator_hom_class]
  unfold cob2αm
  rw [Cob2Symmetric.class_eqToMor]
  generalize_proofs h
  cases h
  obtain ⟨w⟩ := f
  exact Quotient.sound
    (.monoidal (.old (.id_comp w)))

private lemma comp_associator_one_hom (n : ℕ) {W : Cob2SymmetricObj}
    (f :
      W ⟶
        (((⟨1⟩ : Cob2SymmetricObj) ⊗
          (⟨n⟩ : Cob2SymmetricObj)) ⊗
            (⟨1⟩ : Cob2SymmetricObj))) :
    f ≫
      (α_ (⟨1⟩ : Cob2SymmetricObj)
        (⟨n⟩ : Cob2SymmetricObj)
        (⟨1⟩ : Cob2SymmetricObj)).hom = f := by
  rw [Cob2Symmetric.associator_hom_class]
  unfold cob2αm
  rw [Cob2Symmetric.class_eqToMor]
  generalize_proofs h
  cases h
  obtain ⟨w⟩ := f
  exact Quotient.sound
    (.monoidal (.old (.comp_id w)))

lemma merge_prepend (n : ℕ) :
    merge (1 + n) =
      (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ merge n) ≫
        Cob2Symmetric.mul := by
  induction n with
  | zero =>
      change
        𝟙 (⟨1⟩ : Cob2SymmetricObj) =
          ((𝟙 (⟨1⟩ : Cob2SymmetricObj)) ⊗ₘ
            Cob2Symmetric.unit) ≫ Cob2Symmetric.mul
      simpa using
        Cob2Symmetric.canonicalFrobenius.mul_unit.symm
  | succ n ih =>
      have hleft :
          merge (1 + (n + 1)) =
            (merge (1 + n) ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
                Cob2Symmetric.mul := by
        simpa only [Nat.add_assoc] using
          merge_append_one (1 + n)
      rw [hleft]
      rw [ih]
      rw [merge_append_one n]
      have hmul :
          (Cob2Symmetric.mul ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
                Cob2Symmetric.mul =
            (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              Cob2Symmetric.mul) ≫
                Cob2Symmetric.mul := by
        have h :=
          Cob2Symmetric.canonicalFrobenius.mul_assoc'
        change
          (Cob2Symmetric.mul ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
                Cob2Symmetric.mul =
            (α_ (⟨1⟩ : Cob2SymmetricObj)
              (⟨1⟩ : Cob2SymmetricObj)
              (⟨1⟩ : Cob2SymmetricObj)).hom ≫
                (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                  Cob2Symmetric.mul) ≫
                    Cob2Symmetric.mul at h
        exact h.trans
          (associator_one_hom_comp 1
            ((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              Cob2Symmetric.mul) ≫
                Cob2Symmetric.mul))
      have hinterchange_left :
          (((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ merge n) ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
            (Cob2Symmetric.mul ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj))) =
            (((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ merge n) ≫
                Cob2Symmetric.mul) ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj)) := by
        rw [Cob2Symmetric.cob2Symmetric_interchange]
        simp
      have hq :
          ((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ merge n) ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj)) =
            𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              (merge n ⊗ₘ
                𝟙 (⟨1⟩ : Cob2SymmetricObj)) := by
        have h :=
          Cob2Symmetric.cob2Symmetric_associator_naturality
            (𝟙 (⟨1⟩ : Cob2SymmetricObj))
            (merge n)
            (𝟙 (⟨1⟩ : Cob2SymmetricObj))
        change
          (((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ merge n) ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
            (α_ (⟨1⟩ : Cob2SymmetricObj)
              (⟨1⟩ : Cob2SymmetricObj)
              (⟨1⟩ : Cob2SymmetricObj)).hom) =
            (α_ (⟨1⟩ : Cob2SymmetricObj)
              (⟨n⟩ : Cob2SymmetricObj)
              (⟨1⟩ : Cob2SymmetricObj)).hom ≫
              (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                (merge n ⊗ₘ
                  𝟙 (⟨1⟩ : Cob2SymmetricObj))) at h
        exact
          (comp_associator_one_hom 1
            ((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ merge n) ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj))).symm |>.trans <|
            h |>.trans <|
              associator_one_hom_comp n
                (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                  (merge n ⊗ₘ
                    𝟙 (⟨1⟩ : Cob2SymmetricObj)))
      have hinterchange_right :
          ((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              (merge n ⊗ₘ
                𝟙 (⟨1⟩ : Cob2SymmetricObj))) ≫
            (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              Cob2Symmetric.mul)) =
            𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              ((merge n ⊗ₘ
                𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
                  Cob2Symmetric.mul) := by
        rw [Cob2Symmetric.cob2Symmetric_interchange]
        simp
      rw [← hinterchange_left]
      simp only [Category.assoc]
      rw [hmul]
      rw [hq]
      rw [← Category.assoc]
      exact congrArg
        (fun q => q ≫ Cob2Symmetric.mul)
        hinterchange_right

private lemma split_append_one (n : ℕ) :
    split (n + 1) =
      Cob2Symmetric.comul ≫
        (split n ⊗ₘ 𝟙 (⟨1⟩ : Cob2SymmetricObj)) := by
  cases n with
  | zero =>
      change
        𝟙 (⟨1⟩ : Cob2SymmetricObj) =
          Cob2Symmetric.comul ≫
            (Cob2Symmetric.counit ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj))
      simpa using
        Cob2Symmetric.canonicalFrobenius.counit_comul.symm
  | succ n =>
      simp

lemma split_prepend (n : ℕ) :
    split (1 + n) =
      Cob2Symmetric.comul ≫
        (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ split n) := by
  induction n with
  | zero =>
      change
        𝟙 (⟨1⟩ : Cob2SymmetricObj) =
          Cob2Symmetric.comul ≫
            (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              Cob2Symmetric.counit)
      simpa using
        Cob2Symmetric.canonicalFrobenius.comul_counit.symm
  | succ n ih =>
      have hleft :
          split (1 + (n + 1)) =
            Cob2Symmetric.comul ≫
              (split (1 + n) ⊗ₘ
                𝟙 (⟨1⟩ : Cob2SymmetricObj)) := by
        simpa only [Nat.add_assoc] using
          split_append_one (1 + n)
      rw [hleft]
      rw [ih]
      rw [split_append_one n]
      have hinterchange_left :
          (Cob2Symmetric.comul ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
            ((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ split n) ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj)) =
            (Cob2Symmetric.comul ≫
                (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ split n)) ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj) := by
        rw [Cob2Symmetric.cob2Symmetric_interchange]
        simp
      have hinterchange_right :
          (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              Cob2Symmetric.comul) ≫
            (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              (split n ⊗ₘ
                𝟙 (⟨1⟩ : Cob2SymmetricObj))) =
            𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              (Cob2Symmetric.comul ≫
                (split n ⊗ₘ
                  𝟙 (⟨1⟩ : Cob2SymmetricObj))) := by
        rw [Cob2Symmetric.cob2Symmetric_interchange]
        simp
      have hcoassoc :
          Cob2Symmetric.comul ≫
              (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                Cob2Symmetric.comul) =
            Cob2Symmetric.comul ≫
              (Cob2Symmetric.comul ⊗ₘ
                𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
                  (α_ (⟨1⟩ : Cob2SymmetricObj)
                    (⟨1⟩ : Cob2SymmetricObj)
                    (⟨1⟩ : Cob2SymmetricObj)).hom := by
        exact
          Cob2Symmetric.canonicalFrobenius.comul_coassoc'
      have hnat :
          ((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ split n) ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
            (α_ (⟨1⟩ : Cob2SymmetricObj)
              (⟨n⟩ : Cob2SymmetricObj)
              (⟨1⟩ : Cob2SymmetricObj)).hom =
            (α_ (⟨1⟩ : Cob2SymmetricObj)
              (⟨1⟩ : Cob2SymmetricObj)
              (⟨1⟩ : Cob2SymmetricObj)).hom ≫
              (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                (split n ⊗ₘ
                  𝟙 (⟨1⟩ : Cob2SymmetricObj))) := by
        exact
          Cob2Symmetric.cob2Symmetric_associator_naturality
            (𝟙 (⟨1⟩ : Cob2SymmetricObj))
            (split n)
            (𝟙 (⟨1⟩ : Cob2SymmetricObj))
      rw [← hinterchange_left]
      rw [← hinterchange_right]
      slice_rhs 1 2 => rw [hcoassoc]
      slice_rhs 3 4 => rw [← hnat]
      have ht :=
        comp_associator_one_hom n
          (Cob2Symmetric.comul ≫
            (Cob2Symmetric.comul ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
                ((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ split n) ⊗ₘ
                  𝟙 (⟨1⟩ : Cob2SymmetricObj)))
      simpa only [Category.assoc] using ht.symm

theorem adjacentSwap_merge (i k : ℕ) :
    adjacentSwap i k ≫ merge (boundaryArity i k) =
      merge (boundaryArity i k) := by
  induction i with
  | zero =>
      simpa using firstAdjacentSwap_merge k
  | succ i ih =>
      rw [adjacentSwap_succ]
      change
        (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ adjacentSwap i k) ≫
            merge (1 + boundaryArity i k) =
          merge (1 + boundaryArity i k)
      have hp := merge_prepend (boundaryArity i k)
      have hinterchange :
          (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ adjacentSwap i k) ≫
              (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                merge (boundaryArity i k)) =
            𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              (adjacentSwap i k ≫
                merge (boundaryArity i k)) := by
        rw [Cob2Symmetric.cob2Symmetric_interchange]
        simp
      calc
        _ =
            (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ adjacentSwap i k) ≫
              ((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                merge (boundaryArity i k)) ≫
                  Cob2Symmetric.mul) :=
            congrArg
              (fun q =>
                (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ adjacentSwap i k) ≫ q)
              hp
        _ =
            ((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ adjacentSwap i k) ≫
              (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                merge (boundaryArity i k))) ≫
                  Cob2Symmetric.mul := by
            rw [Category.assoc]
        _ =
            (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              (adjacentSwap i k ≫
                merge (boundaryArity i k))) ≫
                  Cob2Symmetric.mul :=
            congrArg
              (fun q => q ≫ Cob2Symmetric.mul)
              hinterchange
        _ =
            (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              merge (boundaryArity i k)) ≫
                Cob2Symmetric.mul := by rw [ih]
        _ = _ := hp.symm

theorem split_adjacentSwap (i k : ℕ) :
    split (boundaryArity i k) ≫ adjacentSwap i k =
      split (boundaryArity i k) := by
  induction i with
  | zero =>
      simpa using split_firstAdjacentSwap k
  | succ i ih =>
      rw [adjacentSwap_succ]
      change
        split (1 + boundaryArity i k) ≫
            (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ adjacentSwap i k) =
          split (1 + boundaryArity i k)
      have hp := split_prepend (boundaryArity i k)
      have hinterchange :
          (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              split (boundaryArity i k)) ≫
            (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ adjacentSwap i k) =
            𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              (split (boundaryArity i k) ≫
                adjacentSwap i k) := by
        rw [Cob2Symmetric.cob2Symmetric_interchange]
        simp
      calc
        _ =
            (Cob2Symmetric.comul ≫
              (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                split (boundaryArity i k))) ≫
                  (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                    adjacentSwap i k) :=
            congrArg
              (fun q =>
                q ≫
                  (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                    adjacentSwap i k))
              hp
        _ =
            Cob2Symmetric.comul ≫
              ((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                split (boundaryArity i k)) ≫
                  (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                    adjacentSwap i k)) := by
            rw [Category.assoc]
        _ =
            Cob2Symmetric.comul ≫
              (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                (split (boundaryArity i k) ≫
                  adjacentSwap i k)) :=
            congrArg
              (fun q => Cob2Symmetric.comul ≫ q)
              hinterchange
        _ =
            Cob2Symmetric.comul ≫
              (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
                split (boundaryArity i k)) := by rw [ih]
        _ = _ := hp.symm

end Cob2SpiderPermutations
