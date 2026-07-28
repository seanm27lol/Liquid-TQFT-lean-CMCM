import RequestProject.Cob2SurfaceSignature
import RequestProject.Cob2SurfaceSymmetric
import RequestProject.Cob2Symmetric

/-!
# Surface signatures through the symmetric quotient

The finite component/genus signature of raw `Cob2Mor` words respects the
lawful monoidal and symmetric presentation relations.  It therefore descends
to the symmetric quotient and defines a strong braided monoidal functor into
the symmetric monoidal category of surface normal forms.

This is a combinatorial semantics for the algebraic presentation.  It does
not identify that presentation with a category of smooth bordisms.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

namespace Cob2NormalForm

open SurfaceNFMonoidal

namespace Cob2Mor

theorem signature_cob2αm (a b c : ℕ) :
    (signature (_root_.cob2αm a b c) :
      (⟨(a + b) + c⟩ : SurfaceNFObj) ⟶
        (⟨a + (b + c)⟩ : SurfaceNFObj)) =
      (α_ (⟨a⟩ : SurfaceNFObj) ⟨b⟩ ⟨c⟩).hom := by
  rw [_root_.cob2αm, signature_eqToMor]
  rfl

theorem signature_cob2αmInv (a b c : ℕ) :
    (signature (_root_.cob2αmInv a b c) :
      (⟨a + (b + c)⟩ : SurfaceNFObj) ⟶
        (⟨(a + b) + c⟩ : SurfaceNFObj)) =
      (α_ (⟨a⟩ : SurfaceNFObj) ⟨b⟩ ⟨c⟩).inv := by
  rw [_root_.cob2αmInv, signature_eqToMor]
  rfl

theorem signature_cob2Leftm (a : ℕ) :
    (signature (_root_.cob2Leftm a) :
      (⟨0 + a⟩ : SurfaceNFObj) ⟶ (⟨a⟩ : SurfaceNFObj)) =
      (λ_ (⟨a⟩ : SurfaceNFObj)).hom := by
  rw [_root_.cob2Leftm, signature_eqToMor]
  rfl

theorem signature_cob2Rightm (a : ℕ) :
    (signature (_root_.cob2Rightm a) :
      (⟨a + 0⟩ : SurfaceNFObj) ⟶ (⟨a⟩ : SurfaceNFObj)) =
      (ρ_ (⟨a⟩ : SurfaceNFObj)).hom := by
  rw [_root_.cob2Rightm, signature_eqToMor]
  rfl

/-- Every relation of the lawful monoidal presentation preserves the finite
surface signature. -/
theorem signature_cob2MonoidalRel_sound
    {a b : ℕ} {f g : _root_.Cob2Mor a b}
    (h : _root_.Cob2MonoidalRel f g) :
    signature f = signature g := by
  induction h with
  | old h => exact signature_cob2Rel_sound h
  | comp_congr _ _ ihf ihg => exact signature_comp_congr ihf ihg
  | tensor_congr _ _ ihf ihg => exact signature_tensor_congr ihf ihg
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihfg ihgh => exact ihfg.trans ihgh
  | tensor_id a c =>
      exact SurfaceNF.tensor_identity a c
  | interchange f₁ f₂ g₁ g₂ =>
      exact SurfaceNF.tensor_comp
        (signature f₁) (signature g₁)
        (signature f₂) (signature g₂)
  | associator_naturality f₁ f₂ f₃ =>
      simpa only [signature_comp, signature_tensor, signature_cob2αm]
        using
          (MonoidalCategory.associator_naturality
            (C := SurfaceNFObj)
            (signature f₁ :
              (⟨_⟩ : SurfaceNFObj) ⟶ ⟨_⟩)
            (signature f₂ :
              (⟨_⟩ : SurfaceNFObj) ⟶ ⟨_⟩)
            (signature f₃ :
              (⟨_⟩ : SurfaceNFObj) ⟶ ⟨_⟩))
  | leftUnitor_naturality f =>
      simpa only [signature_comp, signature_tensor, signature_id,
        signature_cob2Leftm]
        using
          (MonoidalCategory.leftUnitor_naturality
            (C := SurfaceNFObj)
            (signature f :
              (⟨_⟩ : SurfaceNFObj) ⟶ ⟨_⟩))
  | rightUnitor_naturality f =>
      simpa only [signature_comp, signature_tensor, signature_id,
        signature_cob2Rightm]
        using
          (MonoidalCategory.rightUnitor_naturality
            (C := SurfaceNFObj)
            (signature f :
              (⟨_⟩ : SurfaceNFObj) ⟶ ⟨_⟩))

/-- Every relation of the symmetric presentation preserves the finite
surface signature. -/
theorem signature_cob2SymmetricRel_sound
    {a b : ℕ} {f g : _root_.Cob2Mor a b}
    (h : _root_.Cob2SymmetricRel f g) :
    signature f = signature g := by
  induction h with
  | monoidal h => exact signature_cob2MonoidalRel_sound h
  | comp_congr _ _ ihf ihg => exact signature_comp_congr ihf ihg
  | tensor_congr _ _ ihf ihg => exact signature_tensor_congr ihf ihg
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihfg ihgh => exact ihfg.trans ihgh
  | swap_naturality f g =>
      simpa only [signature_comp, signature_tensor, signature_swap]
        using SurfaceNFMonoidal.swap_naturality
          (signature f) (signature g)
  | swap_involutive a b =>
      simpa only [signature_comp, signature_swap, signature_id]
        using SurfaceNFMonoidal.swap_involutive
          (⟨a⟩ : SurfaceNFObj) (⟨b⟩ : SurfaceNFObj)
  | hexagon_forward a b c =>
      simp only [signature_comp, signature_tensor, signature_swap,
        signature_id, signature_cob2αm]
      rw [SurfaceNF.comp_assoc, SurfaceNF.comp_assoc]
      simpa only [braiding_hom_eq_swap, CategoryStruct.comp,
        CategoryStruct.id, MonoidalCategoryStruct.whiskerLeft,
        MonoidalCategoryStruct.whiskerRight]
        using
          (BraidedCategory.hexagon_forward
            (⟨a⟩ : SurfaceNFObj) ⟨b⟩ ⟨c⟩)
  | hexagon_reverse a b c =>
      simp only [signature_comp, signature_tensor, signature_swap,
        signature_id, signature_cob2αmInv]
      rw [SurfaceNF.comp_assoc, SurfaceNF.comp_assoc]
      simpa only [braiding_hom_eq_swap, CategoryStruct.comp,
        CategoryStruct.id, MonoidalCategoryStruct.whiskerLeft,
        MonoidalCategoryStruct.whiskerRight]
        using
          (BraidedCategory.hexagon_reverse
            (⟨a⟩ : SurfaceNFObj) ⟨b⟩ ⟨c⟩)

end Cob2Mor

namespace Cob2Monoidal

/-- The finite surface signature on the lawful monoidal quotient. -/
def signature {X Y : _root_.Cob2MonoidalObj} :
    _root_.Cob2MonoidalHom X Y →
      SurfaceNF X.arity Y.arity :=
  Quotient.lift Cob2Mor.signature
    (fun _ _ h => Cob2Mor.signature_cob2MonoidalRel_sound h)

@[simp]
theorem signature_mk {a b : ℕ} (f : _root_.Cob2Mor a b) :
    signature
        (⟦f⟧ :
          _root_.Cob2MonoidalHom
            (⟨a⟩ : _root_.Cob2MonoidalObj) ⟨b⟩) =
      Cob2Mor.signature f :=
  rfl

end Cob2Monoidal

/-- Surface signatures as an ordinary functor from the lawful monoidal
quotient. -/
def surfaceSignatureMonoidalFunctor :
    _root_.Cob2MonoidalObj ⥤ SurfaceNFObj where
  obj X := ⟨X.arity⟩
  map f := Cob2Monoidal.signature f
  map_id _ := rfl
  map_comp f g := by
    induction f using Quotient.inductionOn with
    | _ f =>
        induction g using Quotient.inductionOn with
        | _ g => rfl

@[simp]
theorem surfaceSignatureMonoidalFunctor_map_mk
    {a b : ℕ} (f : _root_.Cob2Mor a b) :
    surfaceSignatureMonoidalFunctor.map
        (⟦f⟧ :
          (⟨a⟩ : _root_.Cob2MonoidalObj) ⟶ ⟨b⟩) =
      Cob2Mor.signature f :=
  rfl

namespace Cob2Symmetric

/-- The finite surface signature on the symmetric quotient. -/
def signature {X Y : _root_.Cob2SymmetricObj} :
    _root_.Cob2SymmetricHom X Y →
      SurfaceNF X.arity Y.arity :=
  Quotient.lift Cob2Mor.signature
    (fun _ _ h => Cob2Mor.signature_cob2SymmetricRel_sound h)

@[simp]
theorem signature_mk {a b : ℕ} (f : _root_.Cob2Mor a b) :
    signature
        (⟦f⟧ :
          _root_.Cob2SymmetricHom
            (⟨a⟩ : _root_.Cob2SymmetricObj) ⟨b⟩) =
      Cob2Mor.signature f :=
  rfl

end Cob2Symmetric

/-- The symmetric algebraic presentation evaluated by finite surface
component/genus signatures. -/
def surfaceSignatureSymmetricFunctor :
    _root_.Cob2SymmetricObj ⥤ SurfaceNFObj where
  obj X := ⟨X.arity⟩
  map f := Cob2Symmetric.signature f
  map_id _ := rfl
  map_comp f g := by
    induction f using Quotient.inductionOn with
    | _ f =>
        induction g using Quotient.inductionOn with
        | _ g => rfl

@[simp]
theorem surfaceSignatureSymmetricFunctor_map_mk
    {a b : ℕ} (f : _root_.Cob2Mor a b) :
    surfaceSignatureSymmetricFunctor.map
        (⟦f⟧ :
          (⟨a⟩ : _root_.Cob2SymmetricObj) ⟶ ⟨b⟩) =
      Cob2Mor.signature f :=
  rfl

/-- Passing from the monoidal quotient to the symmetric quotient does not
change the finite surface signature. -/
theorem surfaceSignatureSymmetricFunctor_comp_toSymmetricQuotient :
    _root_.Cob2Monoidal.toSymmetricQuotient ⋙
        surfaceSignatureSymmetricFunctor =
      surfaceSignatureMonoidalFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  induction f using Quotient.inductionOn
  rfl

/-- Passing from the original quotient to the lawful monoidal quotient does
not change the finite surface signature. -/
theorem surfaceSignatureMonoidalFunctor_comp_toMonoidalQuotient :
    _root_.Cob2.toMonoidalQuotient ⋙
        surfaceSignatureMonoidalFunctor =
      surfaceSignatureFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  induction f using Quotient.inductionOn
  rfl

/-- The surface-signature functor preserves the quotient tensor on the
nose. -/
theorem surfaceSignatureSymmetricFunctor_map_tensor
    {X₁ Y₁ X₂ Y₂ : _root_.Cob2SymmetricObj}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    surfaceSignatureSymmetricFunctor.map (f ⊗ₘ g) =
      (surfaceSignatureSymmetricFunctor.map f ⊗ₘ
        surfaceSignatureSymmetricFunctor.map g) := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  rfl

/-- Identity comparison isomorphisms package the strict preservation of unit
and tensor as a strong monoidal functor. -/
noncomputable def surfaceSignatureSymmetricCore :
    surfaceSignatureSymmetricFunctor.CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left := by
    intro X Y f X'
    obtain ⟨f⟩ := f
    simp
    rfl
  μIso_hom_natural_right := by
    intro X Y X' f
    obtain ⟨f⟩ := f
    simp
    rfl
  associativity := by
    intro X Y Z
    simp only [Iso.refl_hom, MonoidalCategory.id_whiskerRight,
      MonoidalCategory.whiskerLeft_id, Category.id_comp,
      Category.comp_id]
    rw [_root_.Cob2Symmetric.associator_hom_class,
      surfaceSignatureSymmetricFunctor_map_mk,
      Cob2Mor.signature_cob2αm]
    rfl
  left_unitality := by
    intro X
    simp only [Iso.refl_hom, MonoidalCategory.id_whiskerRight,
      Category.id_comp]
    rw [_root_.Cob2Symmetric.leftUnitor_hom_class,
      surfaceSignatureSymmetricFunctor_map_mk,
      Cob2Mor.signature_cob2Leftm]
    rfl
  right_unitality := by
    intro X
    simp only [Iso.refl_hom, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
    rw [_root_.Cob2Symmetric.rightUnitor_hom_class,
      surfaceSignatureSymmetricFunctor_map_mk,
      Cob2Mor.signature_cob2Rightm]
    rfl

/-- The finite surface-signature semantics is strong monoidal. -/
noncomputable def surfaceSignatureSymmetricFunctorMonoidal :
    surfaceSignatureSymmetricFunctor.Monoidal :=
  surfaceSignatureSymmetricCore.toMonoidal

/-- The descended functor sends the source braiding to the block-swap
braiding of surface normal forms. -/
theorem surfaceSignatureSymmetricFunctor_map_braiding
    (X Y : _root_.Cob2SymmetricObj) :
    surfaceSignatureSymmetricFunctor.map (β_ X Y).hom =
      (β_ (surfaceSignatureSymmetricFunctor.obj X)
        (surfaceSignatureSymmetricFunctor.obj Y)).hom := by
  change
    Cob2Mor.signature (.swap X.arity Y.arity) =
      SurfaceNF.swap X.arity Y.arity
  rfl

/-- The strong monoidal surface-signature semantics is braided. -/
noncomputable def surfaceSignatureSymmetricFunctorBraided :
    surfaceSignatureSymmetricFunctor.Braided := by
  letI : surfaceSignatureSymmetricFunctor.Monoidal :=
    surfaceSignatureSymmetricFunctorMonoidal
  refine { braided := ?_ }
  intro X Y
  change
    (surfaceSignatureSymmetricCore.μIso X Y).hom ≫
        Cob2Mor.signature (.swap X.arity Y.arity) =
      SurfaceNF.swap X.arity Y.arity ≫
        (surfaceSignatureSymmetricCore.μIso Y X).hom
  simp [surfaceSignatureSymmetricCore]

end Cob2NormalForm
