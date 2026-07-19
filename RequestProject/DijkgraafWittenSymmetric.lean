import RequestProject.DijkgraafWitten
import RequestProject.Cob2Symmetric

/-!
# The diagonal finite-state theory on the symmetric algebraic quotient

This file transports the torus and connected genus-word computations from
`DijkgraafWitten.lean` through the lawful symmetric quotient constructed in
`Cob2Symmetric.lean`.  The resulting evaluations are stated through the
underlying functor of a packaged strong monoidal, braided algebraic theory
between symmetric categories.  The package records `Functor.Monoidal` and
`Functor.Braided`; it does not have a separately named `Functor.Symmetric`
field.

The source remains an algebraic generators-and-relations presentation.  No
equivalence with the geometric oriented bordism category, classification of
smooth surfaces, or diffeomorphism/gluing invariance is asserted here.
Despite the historical filename, the concrete model is the diagonal rank-`n`
finite-state Frobenius theory, not the conventional finite-group/cocycle
Dijkgraaf--Witten state-sum construction.
-/

open CategoryTheory MonoidalCategory
open ModuleCat.MonoidalCategory

noncomputable section

namespace Cob2

/-- The canonical ordinary functor from the original quotient to the symmetric quotient. -/
def toSymmetricQuotient : Cob2Cat ⥤ Cob2SymmetricObj :=
  Cob2.toMonoidalQuotient ⋙ Cob2Monoidal.toSymmetricQuotient

@[simp]
theorem toSymmetricQuotient_obj (n : Cob2Cat) :
    toSymmetricQuotient.obj n = (⟨n⟩ : Cob2SymmetricObj) := rfl

@[simp]
theorem toSymmetricQuotient_map_mk {a b : ℕ} (w : Cob2Mor a b) :
    toSymmetricQuotient.map (⟦w⟧ : Cob2Hom a b) =
      (⟦w⟧ : (⟨a⟩ : Cob2SymmetricObj) ⟶ (⟨b⟩ : Cob2SymmetricObj)) := rfl

end Cob2

namespace CommFrobeniusData

/-- Interpreting after both quotient maps recovers the original ordinary interpretation. -/
theorem toCob2SymmetricFunctor_comp_fromCob2
    {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C]
    (A : CommFrobeniusData C) :
    Cob2.toSymmetricQuotient ⋙ A.toCob2SymmetricFunctor =
      A.toCob2Functor := by
  unfold Cob2.toSymmetricQuotient
  rw [CategoryTheory.Functor.assoc,
    A.toCob2SymmetricFunctor_comp_toSymmetricQuotient,
    A.toCob2MonoidalFunctor_comp_toMonoidalQuotient]

/-- The symmetric and ordinary interpretations agree on every raw representative. -/
theorem toCob2SymmetricFunctor_map_mk_eq_toCob2Functor_map_mk
    {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C]
    (A : CommFrobeniusData C) {a b : ℕ} (w : Cob2Mor a b) :
    A.toCob2SymmetricFunctor.map
        (⟦w⟧ : (⟨a⟩ : Cob2SymmetricObj) ⟶ (⟨b⟩ : Cob2SymmetricObj)) =
      A.toCob2Functor.map (⟦w⟧ : Cob2Hom a b) := rfl

end CommFrobeniusData

namespace DijkgraafWitten

/-- The rank-`n` diagonal datum in the `TQFT2d` package over the symmetric quotient. -/
noncomputable def frobZnSymmetricTQFT (n : ℕ) :
    TQFT2d Cob2SymmetricObj (ModuleCat ℤ) :=
  (frobZn n).toSymmetricTQFT2d

/-- The torus presentation class transported from the original to the symmetric quotient. -/
def symmetricTorus :
    (⟨0⟩ : Cob2SymmetricObj) ⟶ (⟨0⟩ : Cob2SymmetricObj) :=
  Cob2.toSymmetricQuotient.map torus

/-- The connected genus-`g` presentation class transported to the symmetric quotient. -/
def symmetricGenus (g : ℕ) :
    (⟨0⟩ : Cob2SymmetricObj) ⟶ (⟨0⟩ : Cob2SymmetricObj) :=
  Cob2.toSymmetricQuotient.map (⟦genusWord g⟧ : Cob2Hom 0 0)

@[simp]
theorem symmetricTorus_eq_mk :
    symmetricTorus =
      (⟦torusWord⟧ : (⟨0⟩ : Cob2SymmetricObj) ⟶ (⟨0⟩ : Cob2SymmetricObj)) := rfl

@[simp]
theorem symmetricGenus_eq_mk (g : ℕ) :
    symmetricGenus g =
      (⟦genusWord g⟧ : (⟨0⟩ : Cob2SymmetricObj) ⟶ (⟨0⟩ : Cob2SymmetricObj)) := rfl

/-- The one-handle member of the symmetric genus family is the symmetric torus class. -/
theorem symmetricGenus_one : symmetricGenus 1 = symmetricTorus := by
  unfold symmetricGenus symmetricTorus
  rw [genusWord_one]

/-- The packaged concrete theory recovers the original interpretation after quotienting. -/
theorem frobZnSymmetricTQFT_comp_fromCob2 (n : ℕ) :
    Cob2.toSymmetricQuotient ⋙ (frobZnSymmetricTQFT n).Z =
      (frobZn n).toCob2Functor := by
  exact CommFrobeniusData.toCob2SymmetricFunctor_comp_fromCob2 (frobZn n)

/-- The symmetric torus class acts by multiplication by `n` on the monoidal unit. -/
theorem Z_torus_symmetric_eq_smul_id (n : ℕ) :
    (frobZnSymmetricTQFT n).Z.map symmetricTorus =
      (n : ℤ) • 𝟙 (𝟙_ (ModuleCat ℤ)) := by
  change (frobZn n).interpret torusWord =
    (n : ℤ) • 𝟙 (𝟙_ (ModuleCat ℤ))
  exact Z_torus_eq_smul_id n

/-- Every transported genus class in the defined family acts by multiplication by `n`. -/
theorem Z_genus_symmetric_eq_smul_id (n g : ℕ) :
    (frobZnSymmetricTQFT n).Z.map (symmetricGenus g) =
      (n : ℤ) • 𝟙 (𝟙_ (ModuleCat ℤ)) := by
  change (frobZn n).interpret (genusWord g) =
    (n : ℤ) • 𝟙 (𝟙_ (ModuleCat ℤ))
  exact Z_genus_eq_smul_id n g

/-- The underlying module morphism for the symmetric torus evaluates at `1` to `n`. -/
theorem Z_torus_symmetric (n : ℕ) :
    ((frobZnSymmetricTQFT n).Z.map symmetricTorus).hom
        ((1 : ℤ) : 𝟙_ (ModuleCat ℤ)) =
      (n : ℤ) := by
  change (frobZn n).interpret torusWord (1 : ℤ) = (n : ℤ)
  exact Z_torus n

/-- The module morphism for each transported genus class evaluates at `1` to `n`. -/
theorem Z_genus_symmetric (n g : ℕ) :
    ((frobZnSymmetricTQFT n).Z.map (symmetricGenus g)).hom
        ((1 : ℤ) : 𝟙_ (ModuleCat ℤ)) =
      (n : ℤ) := by
  change (frobZn n).interpret (genusWord g) (1 : ℤ) = (n : ℤ)
  exact Z_genus n g

end DijkgraafWitten
