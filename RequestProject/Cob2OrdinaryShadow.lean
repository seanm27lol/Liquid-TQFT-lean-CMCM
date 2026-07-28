import RequestProject.Cob2UniversalConverse

/-!
# Ordinary shadows of categorified theories

This module isolates a purely algebraic comparison interface.  A chain of
strong braided monoidal theories may be composed with the verified symmetric
generators-and-relations source.  Evaluating the resulting ordinary
`ModuleCat`-valued (or otherwise symmetric-target-valued) theory on the
generating circle produces a commutative Frobenius datum, and the existing
universal-property theorem reconstructs the composite theory from that datum.

The construction does not supply any of the comparison functors occurring in
geometric or quantum Langlands, nor does it assert that such functors are
equivalences.  It also does not identify the algebraic source with a geometric
bordism category.  Those inputs must be constructed independently; this file
only records what follows once suitable strong braided monoidal functors have
been provided.
-/

open CategoryTheory

noncomputable section

universe vR vS vB vH vC uR uS uB uH uC

namespace TQFT2d

/-- Precomposition of an abstract braided-monoidal theory by a strong braided
monoidal functor. -/
def pullback
    {R : Type uR} [Category.{vR} R] [MonoidalCategory R] [BraidedCategory R]
    {S : Type uS} [Category.{vS} S] [MonoidalCategory S] [BraidedCategory S]
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    (F : R ⥤ S) [F.Monoidal] [F.Braided] (T : TQFT2d S C) :
    TQFT2d R C where
  Z := F ⋙ T.Z
  monoidal := by
    letI := T.monoidal
    infer_instance
  braided := by
    letI := T.monoidal
    letI := T.braided
    infer_instance

/-- Regard the data stored by `TQFT2d` as a bundled strong braided functor. -/
noncomputable def toStrongBraidedFunctor
    {S : Type uS} [Category.{vS} S] [MonoidalCategory S] [BraidedCategory S]
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    (T : TQFT2d S C) :
    Cob2Symmetric.StrongBraidedFunctor S C := by
  letI : T.Z.Monoidal := T.monoidal
  letI : T.Z.Braided := T.braided
  refine ⟨LaxBraidedFunctor.of T.Z, ?_⟩
  constructor
  · infer_instance
  · intro X Y
    infer_instance

@[simp]
theorem toStrongBraidedFunctor_toFunctor
    {S : Type uS} [Category.{vS} S] [MonoidalCategory S] [BraidedCategory S]
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
    (T : TQFT2d S C) :
    (T.toStrongBraidedFunctor).obj.toFunctor = T.Z := rfl

end TQFT2d

/-- Data needed to extract an ordinary symmetric-target shadow from a
categorified corridor.  Each field is an actual strong braided monoidal theory;
no existence or equivalence claim is built into the interface. -/
structure OrdinaryShadowBridge
    (B : Type uB) [Category.{vB} B] [MonoidalCategory B] [BraidedCategory B]
    (H : Type uH) [Category.{vH} H] [MonoidalCategory H] [BraidedCategory H]
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C] where
  /-- A realization of the algebraic symmetric surface presentation in the
  proposed Betti or de Rham sector. -/
  sourceComparison : TQFT2d Cob2SymmetricObj B
  /-- The selected sector of the categorified theory. -/
  sectorTheory : TQFT2d B H
  /-- A strong braided monoidal decategorification or realization functor. -/
  shadow : TQFT2d H C

namespace OrdinaryShadowBridge

variable
    {B : Type uB} [Category.{vB} B] [MonoidalCategory B] [BraidedCategory B]
    {H : Type uH} [Category.{vH} H] [MonoidalCategory H] [BraidedCategory H]
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The ordinary theory obtained by composing the three supplied strong
braided monoidal functors. -/
noncomputable def ordinaryComposite (D : OrdinaryShadowBridge B H C) :
    TQFT2d Cob2SymmetricObj C := by
  letI : D.sectorTheory.Z.Monoidal := D.sectorTheory.monoidal
  letI : D.sectorTheory.Z.Braided := D.sectorTheory.braided
  letI : D.shadow.Z.Monoidal := D.shadow.monoidal
  letI : D.shadow.Z.Braided := D.shadow.braided
  exact (D.sourceComparison.transfer D.sectorTheory.Z).transfer D.shadow.Z

/-- The commutative Frobenius datum seen by the ordinary shadow on the
generating circle. -/
noncomputable def ordinaryShadowFrobenius (D : OrdinaryShadowBridge B H C) :
    CommFrobeniusData C :=
  Cob2Symmetric.evaluateAtGeneratorObj D.ordinaryComposite.toStrongBraidedFunctor

/-- The verified algebraic reconstruction comparison: interpreting the
ordinary-shadow Frobenius datum recovers the composite strong braided functor. -/
noncomputable def ordinaryShadowComparisonIso (D : OrdinaryShadowBridge B H C) :
    Cob2Symmetric.interpretFrobeniusObj D.ordinaryShadowFrobenius ≅
      D.ordinaryComposite.toStrongBraidedFunctor :=
  Cob2Symmetric.functorReconstructionIso
    D.ordinaryComposite.toStrongBraidedFunctor

end OrdinaryShadowBridge
