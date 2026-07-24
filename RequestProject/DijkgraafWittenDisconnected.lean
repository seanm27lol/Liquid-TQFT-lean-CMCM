import RequestProject.DijkgraafWittenSymmetric

/-!
# Disconnected closed-word evaluations for the diagonal finite-state theory

This file forms finite disjoint unions of the already defined connected
genus words by using the tensor operation in the algebraic cobordism
presentation.  For the rank-`n` diagonal Frobenius datum, every connected
component contributes the scalar `n`, so a list with `k` components evaluates
to `n ^ k`.

The result is transported through the symmetric quotient and stated through
the underlying functor of the packaged strong monoidal, braided theory.  It is
still a computation for specified algebraic presentation words: no connected
normal-form theorem, classification of smooth surfaces, or equivalence with
the geometric oriented bordism category is asserted.
-/

open CategoryTheory MonoidalCategory
open ModuleCat.MonoidalCategory

noncomputable section

namespace DijkgraafWitten

/-- Tensor the connected genus words in a list.  The empty list is the empty
closed word, represented by the identity of arity zero. -/
def disconnectedGenusWord : List ℕ → Cob2Mor 0 0
  | [] => .id 0
  | g :: gs => .tensor (genusWord g) (disconnectedGenusWord gs)

@[simp]
theorem disconnectedGenusWord_nil :
    disconnectedGenusWord [] = .id 0 := rfl

@[simp]
theorem disconnectedGenusWord_cons (g : ℕ) (gs : List ℕ) :
    disconnectedGenusWord (g :: gs) =
      .tensor (genusWord g) (disconnectedGenusWord gs) := rfl

/-- The ordinary quotient class of a specified finite disjoint union. -/
def disconnectedGenus (gs : List ℕ) : Cob2Hom 0 0 :=
  ⟦disconnectedGenusWord gs⟧

/-- The same specified finite disjoint union transported to the symmetric
algebraic quotient. -/
def symmetricDisconnectedGenus (gs : List ℕ) :
    (⟨0⟩ : Cob2SymmetricObj) ⟶ (⟨0⟩ : Cob2SymmetricObj) :=
  Cob2.toSymmetricQuotient.map (disconnectedGenus gs)

@[simp]
theorem symmetricDisconnectedGenus_eq_mk (gs : List ℕ) :
    symmetricDisconnectedGenus gs =
      (⟦disconnectedGenusWord gs⟧ :
        (⟨0⟩ : Cob2SymmetricObj) ⟶ (⟨0⟩ : Cob2SymmetricObj)) := rfl

/-- Evaluation at `1` multiplies the contribution `n` from each listed
connected component. -/
theorem interpret_disconnectedGenusWord_one (n : ℕ) (gs : List ℕ) :
    (frobZn n).interpret (disconnectedGenusWord gs)
        ((1 : ℤ) : 𝟙_ (ModuleCat ℤ)) =
      (n : ℤ) ^ gs.length := by
  induction gs with
  | nil =>
      simp [disconnectedGenusWord]
  | cons g gs ih =>
      simp only [disconnectedGenusWord, CommFrobeniusData.interpret_tensor,
        CommFrobeniusData.powAdd_zero, Iso.symm_hom, Iso.symm_inv,
        ModuleCat.comp_apply]
      change
        (ρ_ (𝟙_ (ModuleCat ℤ))).hom
            (((frobZn n).interpret (genusWord g) ⊗ₘ
                (frobZn n).interpret (disconnectedGenusWord gs))
              ((ρ_ (𝟙_ (ModuleCat ℤ))).inv (1 : ℤ))) =
          (n : ℤ) ^ (g :: gs).length
      rw [ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
        ModuleCat.MonoidalCategory.tensorHom_tmul,
        ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
      have hg :
          (frobZn n).interpret (genusWord g)
              ((1 : ℤ) : 𝟙_ (ModuleCat ℤ)) =
            (n : ℤ) := by
        exact Z_genus n g
      rw [hg, ih]
      simp [pow_succ]

/-- The ordinary interpretation of a disconnected genus list is the scalar
`n ^ numberOfComponents` on the monoidal unit. -/
theorem Z_disconnected_eq_smul_id (n : ℕ) (gs : List ℕ) :
    (frobZn n).toCob2Functor.map (disconnectedGenus gs) =
      ((n : ℤ) ^ gs.length) • 𝟙 (𝟙_ (ModuleCat ℤ)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  refine (interpret_disconnectedGenusWord_one n gs).trans ?_
  change (n : ℤ) ^ gs.length = (n : ℤ) ^ gs.length * 1
  simp

/-- Headline disconnected computation through the packaged symmetric theory. -/
theorem Z_disconnected_symmetric_eq_smul_id (n : ℕ) (gs : List ℕ) :
    (frobZnSymmetricTQFT n).Z.map (symmetricDisconnectedGenus gs) =
      ((n : ℤ) ^ gs.length) • 𝟙 (𝟙_ (ModuleCat ℤ)) := by
  change (frobZn n).interpret (disconnectedGenusWord gs) =
    ((n : ℤ) ^ gs.length) • 𝟙 (𝟙_ (ModuleCat ℤ))
  exact Z_disconnected_eq_smul_id n gs

/-- Evaluation-at-one form of the packaged disconnected computation. -/
theorem Z_disconnected_symmetric (n : ℕ) (gs : List ℕ) :
    ((frobZnSymmetricTQFT n).Z.map (symmetricDisconnectedGenus gs)).hom
        ((1 : ℤ) : 𝟙_ (ModuleCat ℤ)) =
      (n : ℤ) ^ gs.length := by
  change (frobZn n).interpret (disconnectedGenusWord gs)
      ((1 : ℤ) : 𝟙_ (ModuleCat ℤ)) =
    (n : ℤ) ^ gs.length
  exact interpret_disconnectedGenusWord_one n gs

/-- For this particular diagonal theory, evaluations of the specified
disconnected words depend only on the number of connected components, not on
their listed genera. -/
theorem Z_disconnected_symmetric_eq_of_length_eq
    (n : ℕ) {gs hs : List ℕ} (h : gs.length = hs.length) :
    (frobZnSymmetricTQFT n).Z.map (symmetricDisconnectedGenus gs) =
      (frobZnSymmetricTQFT n).Z.map (symmetricDisconnectedGenus hs) := by
  rw [Z_disconnected_symmetric_eq_smul_id,
    Z_disconnected_symmetric_eq_smul_id, h]

end DijkgraafWitten
