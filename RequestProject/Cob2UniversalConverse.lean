import RequestProject.Cob2UniversalEquivalence

/-!
# The converse reconstruction and the algebraic universal equivalence

This module completes the algebraic commutative-Frobenius universal
equivalence for the generators-and-relations category `Cob2SymmetricObj`.

Concretely, it supplies the converse reconstruction isomorphism: evaluating a
strong braided functor at the canonical Frobenius generator and interpreting
the resulting commutative Frobenius datum recovers the original functor,
naturally in the functor.  Combined with the already established
`frobeniusReconstruction`, this assembles the actual categorical equivalence
between the category of strong braided functors out of `Cob2SymmetricObj` and
the category of commutative Frobenius data.

Throughout, the strong braided functor category is represented as the full
subcategory of `LaxBraidedFunctor` objects whose unit comparison `ε` and
tensor comparison `μ` are invertible; its morphisms are the monoidal natural
transformations inherited from `LaxBraidedFunctor`.

This is a purely algebraic generators-and-relations universal property.  It
does **not** identify `Cob2SymmetricObj` with compact oriented smooth
bordisms, it does **not** classify smooth surfaces or construct boundary
diffeomorphisms, collars, or geometric gluing invariance, and it is
independent of the separate `SurfaceNF` category, signature, and connected
reification program.
-/

open CategoryTheory MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C]

namespace Cob2Symmetric

/-! ## Stage 1 — raw-word naturality of the converse comparison -/

/-- Compatibility of the objectwise comparison with the tensor-power
comparison `powAdd` and the strong tensorator `μ` of `F`. -/
theorem functorReconstruction_powAdd
    (F : StrongBraidedFunctor Cob2SymmetricObj C) (a c : ℕ) :
    ((evaluateAtGeneratorObj F).powAdd a c).hom ≫
        ((functorReconstructionObjIso F a).hom ⊗ₘ
          (functorReconstructionObjIso F c).hom) ≫
          μ F.obj.toFunctor (⟨a⟩ : Cob2SymmetricObj) (⟨c⟩ : Cob2SymmetricObj) =
      (functorReconstructionObjIso F (a + c)).hom := by
  letI : F.obj.toFunctor.Braided := StrongBraidedFunctor.braided F
  letI : F.obj.toFunctor.Monoidal := StrongBraidedFunctor.monoidal F
  have hRs : ∀ n, (functorReconstructionObjIso F (n+1)).hom =
      ((functorReconstructionObjIso F n).hom ⊗ₘ
          𝟙 (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))) ≫
        μ F.obj.toFunctor (⟨n⟩ : Cob2SymmetricObj) (⟨1⟩ : Cob2SymmetricObj) := fun _ => rfl
  induction c with
  | zero =>
      simp only [Nat.add_zero]
      have hR0 : (functorReconstructionObjIso F 0).hom = ε F.obj.toFunctor := rfl
      rw [hR0, CommFrobeniusData.powAdd_zero]
      rw [show μ F.obj.toFunctor (⟨a⟩ : Cob2SymmetricObj) (⟨0⟩ : Cob2SymmetricObj)
          = μ F.obj.toFunctor (⟨a⟩ : Cob2SymmetricObj) (𝟙_ Cob2SymmetricObj) from rfl]
      rw [tensorHom_ε_comp_μ]
      rw [show (ρ_ (⟨a⟩ : Cob2SymmetricObj)).inv = 𝟙 (⟨a⟩ : Cob2SymmetricObj) from rfl,
        F.obj.toFunctor.map_id]
      simp
  | succ c ih =>
      have hrhs : (functorReconstructionObjIso F (a+(c+1))).hom =
          ((functorReconstructionObjIso F (a+c)).hom ⊗ₘ
            𝟙 (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))) ≫
            μ F.obj.toFunctor (⟨a+c⟩ : Cob2SymmetricObj) (⟨1⟩ : Cob2SymmetricObj) := hRs (a+c)
      have hmu : μ F.obj.toFunctor (⟨a⟩:Cob2SymmetricObj) (⟨c+1⟩:Cob2SymmetricObj)
          = μ F.obj.toFunctor (⟨a⟩:Cob2SymmetricObj)
              ((⟨c⟩:Cob2SymmetricObj) ⊗ (⟨1⟩:Cob2SymmetricObj)) := rfl
      have hassoc := Functor.LaxMonoidal.associativity F.obj.toFunctor
        (⟨a⟩:Cob2SymmetricObj) (⟨c⟩:Cob2SymmetricObj) (⟨1⟩:Cob2SymmetricObj)
      rw [show F.obj.toFunctor.map (α_ (⟨a⟩:Cob2SymmetricObj) ⟨c⟩ ⟨1⟩).hom = 𝟙 _ from by
            rw [show (α_ (⟨a⟩:Cob2SymmetricObj) ⟨c⟩ ⟨1⟩).hom = 𝟙 _ from rfl]
            exact F.obj.toFunctor.map_id _] at hassoc
      rw [Category.comp_id] at hassoc
      rw [CommFrobeniusData.powAdd_succ, hRs c, hrhs, hmu, ← ih]
      simp only [Iso.trans_hom, whiskerRightIso_hom, MonoidalCategory.tensorHom_id,
        MonoidalCategory.comp_whiskerRight, Category.assoc]
      rw [show μ F.obj.toFunctor (⟨a+c⟩:Cob2SymmetricObj) (⟨1⟩:Cob2SymmetricObj)
          = μ F.obj.toFunctor ((⟨a⟩:Cob2SymmetricObj)⊗(⟨c⟩:Cob2SymmetricObj))
              (⟨1⟩:Cob2SymmetricObj) from rfl]
      rw [hassoc]
      simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_comp,
        MonoidalCategory.comp_whiskerRight, Category.assoc]
      simp only [MonoidalCategory.whisker_assoc, Category.assoc]
      monoidal

/-- The arity-one objectwise comparison is exactly the left unitor at `F ⟨1⟩`. -/
theorem functorReconstructionObjIso_one
    (F : StrongBraidedFunctor Cob2SymmetricObj C) :
    (functorReconstructionObjIso F 1).hom
      = (λ_ (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))).hom := by
  letI : F.obj.toFunctor.Braided := StrongBraidedFunctor.braided F
  letI : F.obj.toFunctor.Monoidal := StrongBraidedFunctor.monoidal F
  have hRs : (functorReconstructionObjIso F 1).hom =
      ((functorReconstructionObjIso F 0).hom ⊗ₘ
          𝟙 (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))) ≫
        μ F.obj.toFunctor (⟨0⟩ : Cob2SymmetricObj) (⟨1⟩ : Cob2SymmetricObj) := rfl
  have hR0 : (functorReconstructionObjIso F 0).hom = ε F.obj.toFunctor := rfl
  rw [hRs, hR0, Functor.LaxMonoidal.left_unitality F.obj.toFunctor (⟨1⟩:Cob2SymmetricObj)]
  rw [show F.obj.toFunctor.map (λ_ (⟨1⟩:Cob2SymmetricObj)).hom
      = 𝟙 (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj)) from by
        rw [show (λ_ (⟨1⟩:Cob2SymmetricObj)).hom = 𝟙 (⟨1⟩:Cob2SymmetricObj) from rfl]
        exact F.obj.toFunctor.map_id _]
  rw [MonoidalCategory.tensorHom_id]
  rw [show μ F.obj.toFunctor (𝟙_ Cob2SymmetricObj) (⟨1⟩:Cob2SymmetricObj)
        ≫ 𝟙 (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))
      = μ F.obj.toFunctor (𝟙_ Cob2SymmetricObj) (⟨1⟩:Cob2SymmetricObj) from Category.comp_id _]
  rfl

/-- Multiplication generator case of the converse naturality. -/
theorem functorReconstruction_interpret_mul
    (F : StrongBraidedFunctor Cob2SymmetricObj C) :
    (evaluateAtGeneratorObj F).interpret .μ ≫
        (functorReconstructionObjIso F 1).hom =
      (functorReconstructionObjIso F 2).hom ≫
        F.obj.toFunctor.map
          (⟦.μ⟧ : (⟨2⟩ : Cob2SymmetricObj) ⟶ (⟨1⟩ : Cob2SymmetricObj)) := by
  letI : F.obj.toFunctor.Braided := StrongBraidedFunctor.braided F
  letI : F.obj.toFunctor.Monoidal := StrongBraidedFunctor.monoidal F
  rw [show (functorReconstructionObjIso F 2).hom
        = ((functorReconstructionObjIso F 1).hom ⊗ₘ
              𝟙 (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))) ≫
            μ F.obj.toFunctor (⟨1⟩:Cob2SymmetricObj) (⟨1⟩:Cob2SymmetricObj) from rfl,
      functorReconstructionObjIso_one F,
      show (evaluateAtGeneratorObj F).interpret Cob2Mor.μ
        = ((λ_ (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))).hom
              ▷ F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))
            ≫ (μ F.obj.toFunctor (⟨1⟩:Cob2SymmetricObj) (⟨1⟩:Cob2SymmetricObj)
                ≫ F.obj.toFunctor.map (⟦Cob2Mor.μ⟧ : (⟨2⟩:Cob2SymmetricObj)⟶(⟨1⟩:Cob2SymmetricObj)))
            ≫ (λ_ (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))).inv from rfl]
  simp [MonoidalCategory.tensorHom_id]

/-- Unit generator case of the converse naturality. -/
theorem functorReconstruction_interpret_unit
    (F : StrongBraidedFunctor Cob2SymmetricObj C) :
    (evaluateAtGeneratorObj F).interpret .η ≫
        (functorReconstructionObjIso F 1).hom =
      (functorReconstructionObjIso F 0).hom ≫
        F.obj.toFunctor.map
          (⟦.η⟧ : (⟨0⟩ : Cob2SymmetricObj) ⟶ (⟨1⟩ : Cob2SymmetricObj)) := by
  letI : F.obj.toFunctor.Braided := StrongBraidedFunctor.braided F
  letI : F.obj.toFunctor.Monoidal := StrongBraidedFunctor.monoidal F
  rw [functorReconstructionObjIso_one F,
      show (functorReconstructionObjIso F 0).hom = ε F.obj.toFunctor from rfl,
      show (evaluateAtGeneratorObj F).interpret Cob2Mor.η
        = (ε F.obj.toFunctor
              ≫ F.obj.toFunctor.map (⟦Cob2Mor.η⟧ : (⟨0⟩:Cob2SymmetricObj)⟶(⟨1⟩:Cob2SymmetricObj)))
            ≫ (λ_ (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))).inv from rfl]
  simp

/-- Comultiplication generator case of the converse naturality. -/
theorem functorReconstruction_interpret_comul
    (F : StrongBraidedFunctor Cob2SymmetricObj C) :
    (evaluateAtGeneratorObj F).interpret .δ ≫
        (functorReconstructionObjIso F 2).hom =
      (functorReconstructionObjIso F 1).hom ≫
        F.obj.toFunctor.map
          (⟦.δ⟧ : (⟨1⟩ : Cob2SymmetricObj) ⟶ (⟨2⟩ : Cob2SymmetricObj)) := by
  letI : F.obj.toFunctor.Braided := StrongBraidedFunctor.braided F
  letI : F.obj.toFunctor.Monoidal := StrongBraidedFunctor.monoidal F
  rw [show (functorReconstructionObjIso F 2).hom
        = ((functorReconstructionObjIso F 1).hom ⊗ₘ
              𝟙 (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))) ≫
            μ F.obj.toFunctor (⟨1⟩:Cob2SymmetricObj) (⟨1⟩:Cob2SymmetricObj) from rfl,
      functorReconstructionObjIso_one F,
      show (evaluateAtGeneratorObj F).interpret Cob2Mor.δ
        = (λ_ (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))).hom
            ≫ (F.obj.toFunctor.map (⟦Cob2Mor.δ⟧ : (⟨1⟩:Cob2SymmetricObj)⟶(⟨2⟩:Cob2SymmetricObj))
                ≫ δ F.obj.toFunctor (⟨1⟩:Cob2SymmetricObj) (⟨1⟩:Cob2SymmetricObj))
            ≫ ((λ_ (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))).inv
                ▷ F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj)) from rfl]
  simp only [MonoidalCategory.tensorHom_id, Category.assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, Iso.inv_hom_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp, Functor.Monoidal.δ_μ]
  rw [show 𝟙 (F.obj.toFunctor.obj ((⟨1⟩:Cob2SymmetricObj)⊗(⟨1⟩:Cob2SymmetricObj)))
      = 𝟙 (F.obj.toFunctor.obj (⟨2⟩:Cob2SymmetricObj)) from rfl, Category.comp_id]

/-- Counit generator case of the converse naturality. -/
theorem functorReconstruction_interpret_counit
    (F : StrongBraidedFunctor Cob2SymmetricObj C) :
    (evaluateAtGeneratorObj F).interpret .ε ≫
        (functorReconstructionObjIso F 0).hom =
      (functorReconstructionObjIso F 1).hom ≫
        F.obj.toFunctor.map
          (⟦.ε⟧ : (⟨1⟩ : Cob2SymmetricObj) ⟶ (⟨0⟩ : Cob2SymmetricObj)) := by
  letI : F.obj.toFunctor.Braided := StrongBraidedFunctor.braided F
  letI : F.obj.toFunctor.Monoidal := StrongBraidedFunctor.monoidal F
  rw [functorReconstructionObjIso_one F,
      show (functorReconstructionObjIso F 0).hom = ε F.obj.toFunctor from rfl,
      show (evaluateAtGeneratorObj F).interpret Cob2Mor.ε
        = (λ_ (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))).hom
            ≫ (F.obj.toFunctor.map (⟦Cob2Mor.ε⟧ : (⟨1⟩:Cob2SymmetricObj)⟶(⟨0⟩:Cob2SymmetricObj))
                ≫ η F.obj.toFunctor) from rfl]
  rw [Category.assoc, Category.assoc, Functor.Monoidal.η_ε]
  rw [show (𝟙 (F.obj.toFunctor.obj (𝟙_ Cob2SymmetricObj)))
      = 𝟙 (F.obj.toFunctor.obj (⟨0⟩:Cob2SymmetricObj)) from rfl, Category.comp_id]

/-- Raw-word naturality of the converse comparison: interpreting a raw word
in the evaluated Frobenius datum intertwines the objectwise comparison with
the action of `F` on the corresponding quotient morphism. -/
theorem functorReconstruction_interpret_naturality
    (F : StrongBraidedFunctor Cob2SymmetricObj C)
    {a b : ℕ} (w : Cob2Mor a b) :
    (evaluateAtGeneratorObj F).interpret w ≫
        (functorReconstructionObjIso F b).hom =
      (functorReconstructionObjIso F a).hom ≫
        F.obj.toFunctor.map
          (⟦w⟧ :
            (⟨a⟩ : Cob2SymmetricObj) ⟶ (⟨b⟩ : Cob2SymmetricObj)) := by
  letI : F.obj.toFunctor.Braided := StrongBraidedFunctor.braided F
  letI : F.obj.toFunctor.Monoidal := StrongBraidedFunctor.monoidal F
  induction w with
  | id n =>
      simp only [CommFrobeniusData.interpret_id, Category.id_comp]
      rw [show (⟦Cob2Mor.id n⟧ : (⟨n⟩:Cob2SymmetricObj)⟶(⟨n⟩:Cob2SymmetricObj))
          = 𝟙 (⟨n⟩:Cob2SymmetricObj) from rfl,
        F.obj.toFunctor.map_id, Category.comp_id]
  | μ => exact functorReconstruction_interpret_mul F
  | η => exact functorReconstruction_interpret_unit F
  | δ => exact functorReconstruction_interpret_comul F
  | ε => exact functorReconstruction_interpret_counit F
  | comp p q ihp ihq =>
      simp only [CommFrobeniusData.interpret_comp, Category.assoc]
      rw [ihq, ← Category.assoc, ihp, Category.assoc, ← F.obj.toFunctor.map_comp]
      rfl
  | @tensor a b c d p q ihp ihq =>
      have hbd : ((evaluateAtGeneratorObj F).powAdd b d).inv ≫
            (functorReconstructionObjIso F (b+d)).hom
          = ((functorReconstructionObjIso F b).hom ⊗ₘ (functorReconstructionObjIso F d).hom)
              ≫ μ F.obj.toFunctor (⟨b⟩:Cob2SymmetricObj) (⟨d⟩:Cob2SymmetricObj) := by
        rw [← functorReconstruction_powAdd F b d, ← Category.assoc, Iso.inv_hom_id,
          Category.id_comp]
      simp only [CommFrobeniusData.interpret_tensor, Category.assoc]
      rw [hbd, MonoidalCategory.tensorHom_comp_tensorHom_assoc, ihp, ihq,
        ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc,
        Functor.LaxMonoidal.μ_natural, reassoc_of% (functorReconstruction_powAdd F a c)]
      rfl
  | swap a b =>
      have hba : ((evaluateAtGeneratorObj F).powAdd b a).inv ≫
            (functorReconstructionObjIso F (b+a)).hom
          = ((functorReconstructionObjIso F b).hom ⊗ₘ (functorReconstructionObjIso F a).hom)
              ≫ μ F.obj.toFunctor (⟨b⟩:Cob2SymmetricObj) (⟨a⟩:Cob2SymmetricObj) := by
        rw [← functorReconstruction_powAdd F b a, ← Category.assoc, Iso.inv_hom_id,
          Category.id_comp]
      simp only [CommFrobeniusData.interpret_swap, Category.assoc]
      rw [hba, ← BraidedCategory.braiding_naturality_assoc,
        ← Functor.LaxBraided.braided, reassoc_of% (functorReconstruction_powAdd F a b)]
      rfl

/-! ## Stage 2 — the converse reconstruction component -/

/-- The converse reconstruction isomorphism at a fixed strong braided functor:
interpreting the evaluated Frobenius datum recovers `F`. -/
noncomputable def functorReconstructionIso
    (F : StrongBraidedFunctor Cob2SymmetricObj C) :
    interpretFrobeniusObj (evaluateAtGeneratorObj F) ≅ F :=
  (IsStrongBraided Cob2SymmetricObj C).isoMk
    (LaxBraidedFunctor.isoOfComponents
      (fun X => functorReconstructionObjIso F X.arity)
      (by
        intro X Y f
        induction f using Quotient.inductionOn with
        | _ w => exact functorReconstruction_interpret_naturality F w)
      (by
        dsimp only
        rw [show (functorReconstructionObjIso F (𝟙_ Cob2SymmetricObj).arity).hom
              = ε F.obj.toFunctor from rfl,
          show ε (interpretFrobeniusObj (evaluateAtGeneratorObj F)).obj.toFunctor
              = 𝟙 (𝟙_ C) from rfl, Category.id_comp])
      (by
        intro X Y
        dsimp only
        rw [show (functorReconstructionObjIso F (X ⊗ Y).arity).hom
              = (functorReconstructionObjIso F (X.arity + Y.arity)).hom from rfl,
          show μ (interpretFrobeniusObj (evaluateAtGeneratorObj F)).obj.toFunctor X Y
              = ((evaluateAtGeneratorObj F).powAdd X.arity Y.arity).inv from rfl,
          ← functorReconstruction_powAdd F X.arity Y.arity, ← Category.assoc,
          Iso.inv_hom_id, Category.id_comp]))

@[simp]
theorem functorReconstructionIso_hom_app
    (F : StrongBraidedFunctor Cob2SymmetricObj C) (X : Cob2SymmetricObj) :
    (functorReconstructionIso F).hom.hom.hom.hom.app X =
      (functorReconstructionObjIso F X.arity).hom := rfl

/-! ## Stage 3 — naturality in the strong braided functor -/

/-- Arity-indexed component equation witnessing naturality of the converse
reconstruction in the strong braided functor. -/
theorem functorReconstruction_naturality_app
    {F G : StrongBraidedFunctor Cob2SymmetricObj C} (α : F ⟶ G) (n : ℕ) :
    InterpretFrobenius.powHom (evaluateAtGeneratorMap α) n ≫
        (functorReconstructionObjIso G n).hom =
      (functorReconstructionObjIso F n).hom ≫
        α.hom.hom.hom.app (⟨n⟩ : Cob2SymmetricObj) := by
  letI : F.obj.toFunctor.Braided := StrongBraidedFunctor.braided F
  letI : F.obj.toFunctor.Monoidal := StrongBraidedFunctor.monoidal F
  letI : G.obj.toFunctor.Braided := StrongBraidedFunctor.braided G
  letI : G.obj.toFunctor.Monoidal := StrongBraidedFunctor.monoidal G
  letI : (α.hom.hom.hom).IsMonoidal := α.hom.hom.isMonoidal
  induction n with
  | zero =>
      show 𝟙 _ ≫ ε G.obj.toFunctor
        = ε F.obj.toFunctor ≫ α.hom.hom.hom.app (𝟙_ Cob2SymmetricObj)
      rw [Category.id_comp]
      exact (NatTrans.IsMonoidal.unit (τ := α.hom.hom.hom)).symm
  | succ n ih =>
      rw [InterpretFrobenius.powHom_succ,
        show (functorReconstructionObjIso G (n+1)).hom
            = ((functorReconstructionObjIso G n).hom ⊗ₘ
                𝟙 (G.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))) ≫
              μ G.obj.toFunctor (⟨n⟩:Cob2SymmetricObj) (⟨1⟩:Cob2SymmetricObj) from rfl,
        show (functorReconstructionObjIso F (n+1)).hom
            = ((functorReconstructionObjIso F n).hom ⊗ₘ
                𝟙 (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))) ≫
              μ F.obj.toFunctor (⟨n⟩:Cob2SymmetricObj) (⟨1⟩:Cob2SymmetricObj) from rfl,
        show (evaluateAtGeneratorMap α).hom
            = α.hom.hom.hom.app (⟨1⟩:Cob2SymmetricObj) from rfl,
        show α.hom.hom.hom.app (⟨n+1⟩:Cob2SymmetricObj)
            = α.hom.hom.hom.app ((⟨n⟩:Cob2SymmetricObj) ⊗ (⟨1⟩:Cob2SymmetricObj)) from rfl]
      rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, ih]
      conv_rhs => rw [Category.assoc, NatTrans.IsMonoidal.tensor,
        MonoidalCategory.tensorHom_comp_tensorHom_assoc]
      rw [show α.hom.hom.hom.app (⟨1⟩:Cob2SymmetricObj)
            ≫ 𝟙 (G.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))
          = α.hom.hom.hom.app (⟨1⟩:Cob2SymmetricObj) from Category.comp_id _,
        show 𝟙 (F.obj.toFunctor.obj (⟨1⟩:Cob2SymmetricObj))
            ≫ α.hom.hom.hom.app (⟨1⟩:Cob2SymmetricObj)
          = α.hom.hom.hom.app (⟨1⟩:Cob2SymmetricObj) from Category.id_comp _]
      rfl

/-- The converse reconstruction triangle of the algebraic universal property:
evaluation followed by interpretation is naturally isomorphic to the identity
on strong braided functors. -/
noncomputable def functorReconstruction :
    evaluateAtGenerator ⋙ interpretFrobenius ≅
      𝟭 (StrongBraidedFunctor Cob2SymmetricObj C) := by
  refine NatIso.ofComponents functorReconstructionIso ?_
  intro F G α
  apply InducedCategory.hom_ext
  apply LaxBraidedFunctor.hom_ext
  ext X
  simpa using functorReconstruction_naturality_app α X.arity

/-! ## Stage 4 — the headline algebraic universal equivalence -/

/-- The algebraic commutative-Frobenius universal equivalence: strong braided
functors out of the generators-and-relations category `Cob2SymmetricObj` are
equivalent to commutative Frobenius data. -/
noncomputable def commFrobeniusUniversalEquivalence :
    StrongBraidedFunctor Cob2SymmetricObj C ≌ CommFrobeniusData C :=
  CategoryTheory.Equivalence.mk
    evaluateAtGenerator
    interpretFrobenius
    functorReconstruction.symm
    frobeniusReconstruction

@[simp]
theorem commFrobeniusUniversalEquivalence_functor :
    (commFrobeniusUniversalEquivalence (C := C)).functor = evaluateAtGenerator :=
  rfl

@[simp]
theorem commFrobeniusUniversalEquivalence_inverse :
    (commFrobeniusUniversalEquivalence (C := C)).inverse = interpretFrobenius :=
  rfl

end Cob2Symmetric
