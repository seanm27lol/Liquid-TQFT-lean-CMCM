import RequestProject.Cob2Universal

/-!
# Reconstruction toward the algebraic universal property

This file proves the first reconstruction isomorphism for the algebraic
generators-and-relations source.  Interpreting a commutative Frobenius datum
as a strong braided functor and then evaluating that functor at the canonical
generator recovers the original datum naturally.

It also records the canonical objectwise comparison needed for the converse
reconstruction.  Turning that family into an isomorphism of strong braided
functors additionally requires its naturality for every presentation
morphism; no such converse or geometric bordism classification is claimed
here.
-/

open CategoryTheory MonoidalCategory

noncomputable section

universe v u

namespace CommFrobeniusData

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C]

/-- A structure-preserving morphism whose carrier map is invertible gives an
isomorphism of commutative Frobenius data. -/
noncomputable def isoOfHom {A B : CommFrobeniusData C}
    (f : A ⟶ B) [IsIso f.hom] : A ≅ B where
  hom := f
  inv :=
    { hom := inv f.hom
      map_mul := by
        rw [← cancel_mono f.hom]
        simp only [Category.assoc]
        rw [← f.map_mul]
        simp
      map_unit := by
        rw [← cancel_mono f.hom]
        simp [f.map_unit]
      map_comul := by
        rw [← cancel_epi f.hom]
        rw [← Category.assoc]
        rw [← f.map_comul]
        simp
      map_counit := by
        rw [← cancel_epi f.hom]
        simp [f.map_counit] }
  hom_inv_id := by
    apply Hom.ext
    simp
  inv_hom_id := by
    apply Hom.ext
    simp

end CommFrobeniusData

namespace Cob2Symmetric

open CategoryTheory.Functor.LaxMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C]

/-- The left unitor identifies the carrier obtained by interpreting and then
evaluating a Frobenius datum with its original carrier. -/
noncomputable def frobeniusReconstructionHom (A : CommFrobeniusData C) :
    evaluateAtGeneratorObj (interpretFrobeniusObj A) ⟶ A := by
  letI : A.toCob2SymmetricFunctor.Monoidal :=
    A.toCob2SymmetricFunctorMonoidal
  letI : A.toCob2SymmetricFunctor.Braided :=
    A.toCob2SymmetricFunctorBraided
  refine
    { hom := (λ_ A.X).hom
      map_mul := ?_
      map_unit := ?_
      map_comul := ?_
      map_counit := ?_ }
  · dsimp [evaluateAtGeneratorObj, interpretFrobeniusObj,
      CommFrobeniusData.mapByBraided, StrongBraidedFunctor.braided,
      StrongBraidedFunctor.monoidal,
      CategoryTheory.Functor.Monoidal.ofLaxMonoidal,
      CategoryTheory.Functor.CoreMonoidal.toMonoidal,
      CategoryTheory.Functor.CoreMonoidal.toLaxMonoidal,
      CategoryTheory.Functor.CoreMonoidal.ofLaxMonoidal,
      CommFrobeniusData.toCob2SymmetricFunctorMonoidal,
      CommFrobeniusData.toCob2SymmetricCore]
    simp only [Cob2Symmetric.mul]
    rw [CommFrobeniusData.toCob2SymmetricFunctor_map_mk]
    rw [show μ A.toCob2SymmetricFunctor
        (⟨1⟩ : Cob2SymmetricObj) (⟨1⟩ : Cob2SymmetricObj) =
          (A.powAdd 1 1).inv from rfl]
    dsimp [CommFrobeniusData.powAdd, CommFrobeniusData.interpret]
    monoidal
  · dsimp [evaluateAtGeneratorObj, interpretFrobeniusObj,
      CommFrobeniusData.mapByBraided, StrongBraidedFunctor.braided,
      StrongBraidedFunctor.monoidal,
      CategoryTheory.Functor.Monoidal.ofLaxMonoidal,
      CategoryTheory.Functor.CoreMonoidal.toMonoidal,
      CategoryTheory.Functor.CoreMonoidal.toLaxMonoidal,
      CategoryTheory.Functor.CoreMonoidal.ofLaxMonoidal,
      CommFrobeniusData.toCob2SymmetricFunctorMonoidal,
      CommFrobeniusData.toCob2SymmetricCore]
    simp only [Cob2Symmetric.unit]
    rw [CommFrobeniusData.toCob2SymmetricFunctor_map_mk]
    rw [show ε A.toCob2SymmetricFunctor = 𝟙 (𝟙_ C) from rfl]
    dsimp [CommFrobeniusData.interpret]
    simp
  · dsimp [evaluateAtGeneratorObj, interpretFrobeniusObj,
      CommFrobeniusData.mapByBraided, StrongBraidedFunctor.braided,
      StrongBraidedFunctor.monoidal,
      CategoryTheory.Functor.Monoidal.ofLaxMonoidal,
      CategoryTheory.Functor.CoreMonoidal.toMonoidal,
      CategoryTheory.Functor.CoreMonoidal.toOplaxMonoidal,
      CategoryTheory.Functor.CoreMonoidal.ofLaxMonoidal,
      CommFrobeniusData.toCob2SymmetricFunctorMonoidal,
      CommFrobeniusData.toCob2SymmetricCore]
    simp only [Cob2Symmetric.comul]
    rw [CommFrobeniusData.toCob2SymmetricFunctor_map_mk]
    have hδ :
        inv (μ A.toCob2SymmetricFunctor
          (⟨1⟩ : Cob2SymmetricObj) (⟨1⟩ : Cob2SymmetricObj)) =
            (A.powAdd 1 1).hom := by
      apply IsIso.inv_eq_of_hom_inv_id
      change (A.powAdd 1 1).inv ≫ (A.powAdd 1 1).hom =
        𝟙 (A.objPow 1 ⊗ A.objPow 1)
      simp
    rw [hδ]
    dsimp [CommFrobeniusData.powAdd, CommFrobeniusData.interpret]
    monoidal
  · dsimp [evaluateAtGeneratorObj, interpretFrobeniusObj,
      CommFrobeniusData.mapByBraided, StrongBraidedFunctor.braided,
      StrongBraidedFunctor.monoidal,
      CategoryTheory.Functor.Monoidal.ofLaxMonoidal,
      CategoryTheory.Functor.CoreMonoidal.toMonoidal,
      CategoryTheory.Functor.CoreMonoidal.toOplaxMonoidal,
      CategoryTheory.Functor.CoreMonoidal.ofLaxMonoidal,
      CommFrobeniusData.toCob2SymmetricFunctorMonoidal,
      CommFrobeniusData.toCob2SymmetricCore]
    simp only [Cob2Symmetric.counit]
    rw [CommFrobeniusData.toCob2SymmetricFunctor_map_mk]
    have hη :
        inv (ε A.toCob2SymmetricFunctor) = 𝟙 (𝟙_ C) := by
      apply IsIso.inv_eq_of_hom_inv_id
      change 𝟙 (𝟙_ C) ≫ 𝟙 (𝟙_ C) = 𝟙 (𝟙_ C)
      simp
    rw [hη]
    dsimp [CommFrobeniusData.interpret]
    exact (Category.comp_id ((λ_ A.X).hom ≫ A.counit)).symm

/-- Interpreting and evaluating a Frobenius datum recovers it up to the
canonical left-unitor isomorphism. -/
noncomputable def frobeniusReconstructionIso (A : CommFrobeniusData C) :
    evaluateAtGeneratorObj (interpretFrobeniusObj A) ≅ A := by
  letI : IsIso (frobeniusReconstructionHom A).hom := by
    dsimp [frobeniusReconstructionHom]
    infer_instance
  exact CommFrobeniusData.isoOfHom (frobeniusReconstructionHom A)

/-- The first reconstruction triangle of the algebraic universal property:
evaluation after interpretation is naturally isomorphic to the identity. -/
noncomputable def frobeniusReconstruction :
    interpretFrobenius ⋙ evaluateAtGenerator ≅
      𝟭 (CommFrobeniusData C) := by
  refine NatIso.ofComponents frobeniusReconstructionIso ?_
  intro A B f
  apply CommFrobeniusData.Hom.ext
  change
    InterpretFrobenius.powHom f 1 ≫ (λ_ B.X).hom =
      (λ_ A.X).hom ≫ f.hom
  dsimp [InterpretFrobenius.powHom]
  monoidal

/-- Objectwise comparison for the converse reconstruction.  At arity zero it
is the strong functor's unit comparison; at a successor it is built from the
previous comparison and the strong tensor comparison. -/
noncomputable def functorReconstructionObjIso
    (F : StrongBraidedFunctor Cob2SymmetricObj C) :
    (n : ℕ) →
      (evaluateAtGeneratorObj F).objPow n ≅
        F.obj.toFunctor.obj (⟨n⟩ : Cob2SymmetricObj) := by
  letI : F.obj.toFunctor.Braided := StrongBraidedFunctor.braided F
  intro n
  induction n with
  | zero => exact asIso (ε F.obj.toFunctor)
  | succ n ih =>
      exact tensorIso ih
          (Iso.refl (F.obj.toFunctor.obj (⟨1⟩ : Cob2SymmetricObj))) ≪≫
        asIso (μ F.obj.toFunctor
          (⟨n⟩ : Cob2SymmetricObj) (⟨1⟩ : Cob2SymmetricObj))

end Cob2Symmetric
