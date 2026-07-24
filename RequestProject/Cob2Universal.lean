import RequestProject.Cob2Canonical

/-!
# Interfaces for the algebraic universal property

This file supplies the two categories that occur in the generators-and-relations
universal property of the symmetric algebraic source:

* commutative Frobenius data and structure-preserving morphisms;
* braided lax monoidal functors whose unit and tensor comparison maps are
  isomorphisms.

The second category is a full subcategory because Mathlib currently bundles
`LaxBraidedFunctor`, but not strong braided functors as a separate category.
No universal equivalence or comparison with geometric bordisms is asserted
here.
-/

open CategoryTheory MonoidalCategory

noncomputable section

universe v u v' u'

namespace CommFrobeniusData

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- A strong braided monoidal functor transports all of a commutative
Frobenius datum, including the two mixed Frobenius laws. -/
noncomputable def mapByBraided
    {D : Type u'} [Category.{v'} D]
    [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) [F.Braided] (A : CommFrobeniusData C) :
    CommFrobeniusData D where
  X := F.obj A.X
  mul := CategoryTheory.Functor.LaxMonoidal.μ F A.X A.X ≫ F.map A.mul
  unit := CategoryTheory.Functor.LaxMonoidal.ε F ≫ F.map A.unit
  comul := F.map A.comul ≫
    CategoryTheory.Functor.OplaxMonoidal.δ F A.X A.X
  counit := F.map A.counit ≫ CategoryTheory.Functor.OplaxMonoidal.η F
  mul_assoc' := by
    simp_rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
      CategoryTheory.Functor.LaxMonoidal.μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc,
      CategoryTheory.Functor.LaxMonoidal.μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, A.mul_assoc']
    simp
  unit_mul := by
    simp [← F.map_comp, A.unit_mul]
  mul_unit := by
    simp [← F.map_comp, A.mul_unit]
  comul_coassoc' := by
    simp_rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
      CategoryTheory.Functor.OplaxMonoidal.δ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp,
      CategoryTheory.Functor.OplaxMonoidal.δ_natural_right_assoc,
      ← F.map_comp_assoc, A.comul_coassoc', F.map_comp, Category.assoc,
      CategoryTheory.Functor.OplaxMonoidal.associativity]
  counit_comul := by
    simp_rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
      CategoryTheory.Functor.OplaxMonoidal.δ_natural_left_assoc,
      CategoryTheory.Functor.OplaxMonoidal.left_unitality,
      ← F.map_comp_assoc, A.counit_comul]
  comul_counit := by
    simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      CategoryTheory.Functor.OplaxMonoidal.δ_natural_right_assoc,
      CategoryTheory.Functor.OplaxMonoidal.right_unitality,
      ← F.map_comp_assoc, A.comul_counit]
  frobenius_left := by
    calc
      _ = CategoryTheory.Functor.LaxMonoidal.μ F A.X A.X ≫
          F.map ((A.X ◁ A.comul) ≫ (α_ A.X A.X A.X).inv ≫
            (A.mul ▷ A.X)) ≫
          CategoryTheory.Functor.OplaxMonoidal.δ F A.X A.X := by
        rw [F.map_comp, F.map_comp]
        simp only [CategoryTheory.Functor.Monoidal.map_whiskerLeft,
          CategoryTheory.Functor.Monoidal.map_associator_inv,
          CategoryTheory.Functor.Monoidal.map_whiskerRight]
        simp only [MonoidalCategory.whiskerLeft_comp,
          MonoidalCategory.comp_whiskerRight, Category.assoc,
          CategoryTheory.Functor.Monoidal.μ_δ_assoc,
          CategoryTheory.Functor.Monoidal.μ_δ, Category.comp_id]
      _ = CategoryTheory.Functor.LaxMonoidal.μ F A.X A.X ≫
          F.map (A.mul ≫ A.comul) ≫
          CategoryTheory.Functor.OplaxMonoidal.δ F A.X A.X := by
        rw [A.frobenius_left]
      _ = _ := by simp [F.map_comp, Category.assoc]
  frobenius_right := by
    calc
      _ = CategoryTheory.Functor.LaxMonoidal.μ F A.X A.X ≫
          F.map ((A.comul ▷ A.X) ≫ (α_ A.X A.X A.X).hom ≫
            (A.X ◁ A.mul)) ≫
          CategoryTheory.Functor.OplaxMonoidal.δ F A.X A.X := by
        rw [F.map_comp, F.map_comp]
        simp only [CategoryTheory.Functor.Monoidal.map_whiskerRight,
          CategoryTheory.Functor.Monoidal.map_associator,
          CategoryTheory.Functor.Monoidal.map_whiskerLeft]
        simp only [MonoidalCategory.whiskerLeft_comp,
          MonoidalCategory.comp_whiskerRight, Category.assoc,
          CategoryTheory.Functor.Monoidal.μ_δ_assoc,
          CategoryTheory.Functor.Monoidal.μ_δ, Category.comp_id]
      _ = CategoryTheory.Functor.LaxMonoidal.μ F A.X A.X ≫
          F.map (A.mul ≫ A.comul) ≫
          CategoryTheory.Functor.OplaxMonoidal.δ F A.X A.X := by
        rw [A.frobenius_right]
      _ = _ := by simp [F.map_comp, Category.assoc]
  mul_comm' := by
    rw [← CategoryTheory.Functor.LaxBraided.braided_assoc,
      ← F.map_comp, A.mul_comm']

/-- A morphism of commutative Frobenius data preserves all four structure
maps. -/
@[ext]
structure Hom (A B : CommFrobeniusData C) where
  hom : A.X ⟶ B.X
  map_mul : (hom ⊗ₘ hom) ≫ B.mul = A.mul ≫ hom := by cat_disch
  map_unit : A.unit ≫ hom = B.unit := by cat_disch
  map_comul : A.comul ≫ (hom ⊗ₘ hom) = hom ≫ B.comul := by cat_disch
  map_counit : hom ≫ B.counit = A.counit := by cat_disch

instance category : Category (CommFrobeniusData C) where
  Hom := Hom
  id A :=
    { hom := 𝟙 A.X
      map_mul := by simp
      map_unit := by simp
      map_comul := by simp
      map_counit := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      map_mul := by
        rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc, g.map_mul,
          ← Category.assoc, f.map_mul, Category.assoc]
      map_unit := by
        rw [← Category.assoc, f.map_unit, g.map_unit]
      map_comul := by
        rw [← MonoidalCategory.tensorHom_comp_tensorHom, ← Category.assoc, f.map_comul,
          Category.assoc, g.map_comul, ← Category.assoc]
      map_counit := by
        rw [Category.assoc, g.map_counit, f.map_counit] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

@[simp]
theorem id_hom (A : CommFrobeniusData C) :
    (𝟙 A : Hom A A).hom = 𝟙 A.X := rfl

@[simp]
theorem comp_hom {A B D : CommFrobeniusData C} (f : A ⟶ B) (g : B ⟶ D) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

end CommFrobeniusData

namespace Cob2Symmetric

open CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal

universe v₁ v₂ u₁ u₂

variable (S : Type u₁) [Category.{v₁} S] [MonoidalCategory S] [BraidedCategory S]
variable (C : Type u₂) [Category.{v₂} C] [MonoidalCategory C] [BraidedCategory C]

/-- A bundled lax braided functor is strong when its unit and tensor
comparison maps are isomorphisms. -/
def IsStrongBraided : ObjectProperty (LaxBraidedFunctor S C) :=
  fun F =>
    IsIso (ε F.toFunctor) ∧
      ∀ X Y, IsIso (μ F.toFunctor X Y)

/-- Strong braided functors, represented as the full subcategory of bundled
lax braided functors whose comparison maps are isomorphisms. -/
abbrev StrongBraidedFunctor :=
  (IsStrongBraided S C).FullSubcategory

namespace StrongBraidedFunctor

variable {S C}

/-- Recover the strong monoidal structure recorded propositionally by an
object of `StrongBraidedFunctor`. -/
noncomputable def monoidal
    (F : StrongBraidedFunctor S C) :
    F.obj.toFunctor.Monoidal := by
  letI : IsIso (ε F.obj.toFunctor) := F.property.1
  letI : ∀ X Y, IsIso (μ F.obj.toFunctor X Y) := F.property.2
  exact CategoryTheory.Functor.Monoidal.ofLaxMonoidal F.obj.toFunctor

/-- A strong bundled lax braided functor has the corresponding Mathlib
`Functor.Braided` structure. -/
noncomputable def braided
    (F : StrongBraidedFunctor S C) :
    F.obj.toFunctor.Braided :=
  { monoidal F with
    braided := F.obj.laxBraided.braided }

end StrongBraidedFunctor

section UniversalObjects

variable {C : Type u₂} [Category.{v₂} C] [MonoidalCategory C]
  [SymmetricCategory C]

/-- Evaluate a strong braided functor on the canonical Frobenius generator. -/
noncomputable def evaluateAtGeneratorObj
    (F : StrongBraidedFunctor Cob2SymmetricObj C) :
    CommFrobeniusData C := by
  letI : F.obj.toFunctor.Braided := StrongBraidedFunctor.braided F
  exact CommFrobeniusData.mapByBraided F.obj.toFunctor canonicalFrobenius

omit [SymmetricCategory C] in
private theorem oplaxTensor_naturality_of_isMonoidal
    {S : Type*} [Category S] [MonoidalCategory S]
    {F G : S ⥤ C} [F.Monoidal] [G.Monoidal]
    (α : F ⟶ G) [α.IsMonoidal] (X Y : S) :
    δ F X Y ≫ (α.app X ⊗ₘ α.app Y) =
      α.app (X ⊗ Y) ≫ δ G X Y := by
  rw [← cancel_mono (μ G X Y)]
  calc
    (δ F X Y ≫ (α.app X ⊗ₘ α.app Y)) ≫ μ G X Y =
        δ F X Y ≫
          ((α.app X ⊗ₘ α.app Y) ≫ μ G X Y) := Category.assoc _ _ _
    _ = δ F X Y ≫ (μ F X Y ≫ α.app (X ⊗ Y)) := by
      rw [NatTrans.IsMonoidal.tensor]
    _ = (δ F X Y ≫ μ F X Y) ≫ α.app (X ⊗ Y) :=
      (Category.assoc _ _ _).symm
    _ = α.app (X ⊗ Y) := by simp
    _ = α.app (X ⊗ Y) ≫ (δ G X Y ≫ μ G X Y) := by simp
    _ = (α.app (X ⊗ Y) ≫ δ G X Y) ≫ μ G X Y :=
      (Category.assoc _ _ _).symm

omit [SymmetricCategory C] in
private theorem oplaxUnit_naturality_of_isMonoidal
    {S : Type*} [Category S] [MonoidalCategory S]
    {F G : S ⥤ C} [F.Monoidal] [G.Monoidal]
    (α : F ⟶ G) [α.IsMonoidal] :
    α.app (𝟙_ S) ≫ η G = η F := by
  rw [← cancel_epi (ε F)]
  calc
    ε F ≫ (α.app (𝟙_ S) ≫ η G) =
        (ε F ≫ α.app (𝟙_ S)) ≫ η G :=
      (Category.assoc _ _ _).symm
    _ = ε G ≫ η G := by rw [NatTrans.IsMonoidal.unit]
    _ = 𝟙 (𝟙_ C) := Functor.Monoidal.ε_η G
    _ = ε F ≫ η F := (Functor.Monoidal.ε_η F).symm

/-- A monoidal natural transformation acts at the generator by a morphism of
commutative Frobenius data.  Preservation of comultiplication and counit uses
the inverse tensorator and unitor compatibilities derived above. -/
noncomputable def evaluateAtGeneratorMap
    {F G : StrongBraidedFunctor Cob2SymmetricObj C} (α : F ⟶ G) :
    evaluateAtGeneratorObj F ⟶ evaluateAtGeneratorObj G := by
  letI : F.obj.toFunctor.Braided := StrongBraidedFunctor.braided F
  letI : G.obj.toFunctor.Braided := StrongBraidedFunctor.braided G
  let τ : F.obj.toFunctor ⟶ G.obj.toFunctor := α.hom.hom.hom
  letI : τ.IsMonoidal := α.hom.hom.isMonoidal
  refine
    { hom := τ.app (⟨1⟩ : Cob2SymmetricObj)
      map_mul := ?_
      map_unit := ?_
      map_comul := ?_
      map_counit := ?_ }
  · dsimp [evaluateAtGeneratorObj, CommFrobeniusData.mapByBraided]
    rw [← Category.assoc, ← NatTrans.IsMonoidal.tensor]
    rw [Category.assoc, ← τ.naturality]
    simp only [Category.assoc]
  · dsimp [evaluateAtGeneratorObj, CommFrobeniusData.mapByBraided]
    rw [Category.assoc, τ.naturality]
    rw [← Category.assoc, NatTrans.IsMonoidal.unit]
  · dsimp [evaluateAtGeneratorObj, CommFrobeniusData.mapByBraided]
    rw [Category.assoc, oplaxTensor_naturality_of_isMonoidal]
    rw [← Category.assoc, τ.naturality]
    rw [Category.assoc]
  · dsimp [evaluateAtGeneratorObj, CommFrobeniusData.mapByBraided]
    rw [← Category.assoc, ← τ.naturality]
    rw [Category.assoc, oplaxUnit_naturality_of_isMonoidal]

/-- Evaluation at the generating circle, functorial on strong braided
functors and monoidal natural transformations. -/
noncomputable def evaluateAtGenerator :
    StrongBraidedFunctor Cob2SymmetricObj C ⥤ CommFrobeniusData C where
  obj := evaluateAtGeneratorObj
  map := evaluateAtGeneratorMap
  map_id F := by
    apply CommFrobeniusData.Hom.ext
    rfl
  map_comp α β := by
    apply CommFrobeniusData.Hom.ext
    rfl

/-- Interpret a commutative Frobenius datum as a strong braided functor.
This is the object map of the future interpretation functor. -/
noncomputable def interpretFrobeniusObj
    (A : CommFrobeniusData C) :
    StrongBraidedFunctor Cob2SymmetricObj C := by
  letI : A.toCob2SymmetricFunctor.Monoidal :=
    A.toCob2SymmetricFunctorMonoidal
  letI : A.toCob2SymmetricFunctor.Braided :=
    A.toCob2SymmetricFunctorBraided
  refine ⟨LaxBraidedFunctor.of A.toCob2SymmetricFunctor, ?_⟩
  constructor
  · infer_instance
  · intro X Y
    infer_instance

namespace InterpretFrobenius

variable {A B D : CommFrobeniusData C}

/-- The tensor power of a morphism of Frobenius data, in the same
right-associated convention as `CommFrobeniusData.objPow`. -/
def powHom (f : A ⟶ B) : (n : ℕ) → A.objPow n ⟶ B.objPow n
  | 0 => 𝟙 (𝟙_ C)
  | n + 1 => powHom f n ⊗ₘ f.hom

@[simp]
theorem powHom_zero (f : A ⟶ B) :
    powHom f 0 = 𝟙 (𝟙_ C) := rfl

@[simp]
theorem powHom_succ (f : A ⟶ B) (n : ℕ) :
    powHom f (n + 1) = powHom f n ⊗ₘ f.hom := rfl

@[simp]
theorem powHom_id (A : CommFrobeniusData C) (n : ℕ) :
    powHom (𝟙 A) n = 𝟙 (A.objPow n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [powHom_succ, CommFrobeniusData.id_hom, ih]
      change (𝟙 (A.objPow n) ⊗ₘ 𝟙 A.X) =
        𝟙 (A.objPow n ⊗ A.X)
      rw [MonoidalCategory.id_tensorHom_id]

theorem powHom_comp (f : A ⟶ B) (g : B ⟶ D) (n : ℕ) :
    powHom (f ≫ g) n = powHom f n ≫ powHom g n := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [powHom_succ, CommFrobeniusData.comp_hom, ih]
      rw [MonoidalCategory.tensorHom_comp_tensorHom]

/-- Tensor powers commute with the canonical comparison from a single power
of a sum to the tensor product of the two powers. -/
@[reassoc]
theorem powAdd_hom_naturality (f : A ⟶ B) (a c : ℕ) :
    (A.powAdd a c).hom ≫ (powHom f a ⊗ₘ powHom f c) =
      powHom f (a + c) ≫ (B.powAdd a c).hom := by
  induction c with
  | zero =>
      simp only [CommFrobeniusData.powAdd_zero, powHom_zero, Nat.add_zero]
      simp
  | succ c ih =>
      simp only [CommFrobeniusData.powAdd_succ, Iso.trans_hom,
        whiskerRightIso_hom, Nat.add_succ, powHom_succ]
      rw [Category.assoc, ← MonoidalCategory.associator_naturality]
      simp only [← Category.assoc]
      rw [← MonoidalCategory.tensorHom_id,
        MonoidalCategory.tensorHom_comp_tensorHom, ih]
      simp
      monoidal

/-- Inverse form of `powAdd_hom_naturality`. -/
theorem powAdd_inv_naturality (f : A ⟶ B) (a c : ℕ) :
    (A.powAdd a c).inv ≫ powHom f (a + c) =
      (powHom f a ⊗ₘ powHom f c) ≫ (B.powAdd a c).inv := by
  rw [← cancel_epi (A.powAdd a c).hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, powAdd_hom_naturality]
  simp

private theorem interpret_mul_naturality (f : A ⟶ B) :
    A.interpret (.μ) ≫ powHom f 1 =
      powHom f 2 ≫ B.interpret (.μ) := by
  dsimp [CommFrobeniusData.interpret, powHom]
  simp only [Category.assoc, MonoidalCategory.id_tensorHom]
  rw [← MonoidalCategory.leftUnitor_inv_naturality]
  rw [← Category.assoc A.mul f.hom (λ_ B.X).inv, ← f.map_mul]
  simp only [← Category.assoc]
  monoidal

private theorem interpret_unit_naturality (f : A ⟶ B) :
    A.interpret (.η) ≫ powHom f 1 =
      powHom f 0 ≫ B.interpret (.η) := by
  dsimp [CommFrobeniusData.interpret, powHom]
  simp only [Category.assoc, MonoidalCategory.id_tensorHom]
  rw [← MonoidalCategory.leftUnitor_inv_naturality]
  rw [← Category.assoc A.unit f.hom (λ_ B.X).inv, f.map_unit]
  simp

private theorem interpret_counit_naturality (f : A ⟶ B) :
    A.interpret (.ε) ≫ powHom f 0 =
      powHom f 1 ≫ B.interpret (.ε) := by
  dsimp [CommFrobeniusData.interpret, powHom]
  simp only [Category.comp_id, MonoidalCategory.id_tensorHom]
  rw [← f.map_counit]
  simp only [← Category.assoc]
  rw [MonoidalCategory.leftUnitor_naturality]

private theorem interpret_comul_naturality (f : A ⟶ B) :
    A.interpret (.δ) ≫ powHom f 2 =
      powHom f 1 ≫ B.interpret (.δ) := by
  dsimp [CommFrobeniusData.interpret, powHom]
  have hpow :
      ((λ_ A.X).inv ▷ A.X) ≫
          ((𝟙 (𝟙_ C) ⊗ₘ f.hom) ⊗ₘ f.hom) =
        (f.hom ⊗ₘ f.hom) ≫ ((λ_ B.X).inv ▷ B.X) := by
    monoidal
  simp only [Category.assoc]
  rw [hpow]
  rw [← Category.assoc A.comul (f.hom ⊗ₘ f.hom)
    ((λ_ B.X).inv ▷ B.X), f.map_comul]
  monoidal

/-- A morphism of commutative Frobenius data intertwines the interpretations
of every raw presentation word. -/
theorem interpret_naturality (f : A ⟶ B) {a b : ℕ}
    (w : Cob2Mor a b) :
    A.interpret w ≫ powHom f b =
      powHom f a ≫ B.interpret w := by
  induction w with
  | id n => simp
  | μ => exact interpret_mul_naturality f
  | η => exact interpret_unit_naturality f
  | δ => exact interpret_comul_naturality f
  | ε => exact interpret_counit_naturality f
  | comp p q ihp ihq =>
      simp only [CommFrobeniusData.interpret_comp, Category.assoc]
      rw [ihq, ← Category.assoc, ihp, Category.assoc]
  | @tensor a b c d p q ihp ihq =>
      simp only [CommFrobeniusData.interpret_tensor, Category.assoc]
      rw [powAdd_inv_naturality]
      simp only [← Category.assoc]
      apply (cancel_mono (B.powAdd b d).inv).2
      simp only [Category.assoc]
      rw [MonoidalCategory.tensorHom_comp_tensorHom, ihp, ihq,
        ← MonoidalCategory.tensorHom_comp_tensorHom]
      simp only [← Category.assoc]
      rw [powAdd_hom_naturality]
  | swap a b =>
      dsimp [CommFrobeniusData.interpret]
      simp only [Category.assoc]
      rw [powAdd_inv_naturality]
      simp only [← Category.assoc]
      apply (cancel_mono (B.powAdd b a).inv).2
      simp only [Category.assoc]
      rw [← CategoryTheory.BraidedCategory.braiding_naturality]
      simp only [← Category.assoc]
      rw [powAdd_hom_naturality]

/-- The natural transformation between presentation interpretations induced
by a morphism of Frobenius data. -/
noncomputable def natTrans (f : A ⟶ B) :
    A.toCob2SymmetricFunctor ⟶ B.toCob2SymmetricFunctor where
  app X := powHom f X.arity
  naturality X Y q := by
    induction q using Quotient.inductionOn
    exact interpret_naturality f _

@[simp]
theorem natTrans_app (f : A ⟶ B) (X : Cob2SymmetricObj) :
    (natTrans f).app X = powHom f X.arity := rfl

/-- A Frobenius morphism induces a monoidal natural transformation, hence a
morphism between the bundled strong braided interpretation functors. -/
noncomputable def bundledMap (f : A ⟶ B) :
    interpretFrobeniusObj A ⟶ interpretFrobeniusObj B := by
  letI : A.toCob2SymmetricFunctor.Monoidal :=
    A.toCob2SymmetricFunctorMonoidal
  letI : B.toCob2SymmetricFunctor.Monoidal :=
    B.toCob2SymmetricFunctorMonoidal
  let τ := natTrans f
  letI : τ.IsMonoidal :=
    { unit := by
        change 𝟙 (𝟙_ C) ≫ powHom f 0 = 𝟙 (𝟙_ C)
        simp
      tensor := by
        intro X Y
        change (A.powAdd X.arity Y.arity).inv ≫
            powHom f (X.arity + Y.arity) =
          (powHom f X.arity ⊗ₘ powHom f Y.arity) ≫
            (B.powAdd X.arity Y.arity).inv
        exact powAdd_inv_naturality f X.arity Y.arity }
  exact ObjectProperty.homMk (LaxBraidedFunctor.homMk τ)

@[simp]
theorem bundledMap_app (f : A ⟶ B) (X : Cob2SymmetricObj) :
    (bundledMap f).hom.hom.hom.app X = powHom f X.arity := rfl

end InterpretFrobenius

/-- Interpretation is functorial in structure-preserving morphisms of
commutative Frobenius data. -/
noncomputable def interpretFrobenius :
    CommFrobeniusData C ⥤
      StrongBraidedFunctor Cob2SymmetricObj C where
  obj := interpretFrobeniusObj
  map := InterpretFrobenius.bundledMap
  map_id A := by
    apply InducedCategory.hom_ext
    apply LaxBraidedFunctor.hom_ext
    ext X
    exact InterpretFrobenius.powHom_id A X.arity
  map_comp f g := by
    apply InducedCategory.hom_ext
    apply LaxBraidedFunctor.hom_ext
    ext X
    exact InterpretFrobenius.powHom_comp f g X.arity

@[simp]
theorem interpretFrobenius_obj (A : CommFrobeniusData C) :
    interpretFrobenius.obj A = interpretFrobeniusObj A := rfl

@[simp]
theorem interpretFrobenius_map_app
    {A B : CommFrobeniusData C} (f : A ⟶ B)
    (X : Cob2SymmetricObj) :
    (interpretFrobenius.map f).hom.hom.hom.app X =
      InterpretFrobenius.powHom f X.arity := rfl

end UniversalObjects

end Cob2Symmetric
