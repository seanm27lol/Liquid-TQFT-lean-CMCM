import RequestProject.Cob2

open CategoryTheory MonoidalCategory

noncomputable section

/-!
# A lawful monoidal quotient of the `Cob2` presentation

This file strengthens the relation on `Cob2Mor` by tensor identity,
interchange, and structural naturality.  The resulting quotient is a lawful
monoidal category; pentagon and triangle follow from the equality transports
used for its associator and unitors.

Every `CommFrobeniusData` interpretation respects the strengthened relation.
It therefore descends to the quotient, and the recursively defined `powAdd`
isomorphisms supply a machine-checked strong monoidal structure.

No braiding or symmetric-monoidal structure is claimed here, and this remains
an algebraic presentation rather than an identification with geometric
oriented bordisms.
-/

/-- A genuine wrapper around the natural-number arities of the existing presentation. -/
@[ext] structure Cob2MonoidalObj where
  arity : ℕ

namespace Cob2Mor

/-- The raw identity word transported along an equality of arities. -/
def eqToMor {a b : ℕ} (h : a = b) : Cob2Mor a b := by
  subst b
  exact .id a

end Cob2Mor

/-- Raw associator transport. -/
def cob2αm (a b c : ℕ) : Cob2Mor ((a + b) + c) (a + (b + c)) :=
  Cob2Mor.eqToMor (Nat.add_assoc a b c)

/-- Raw left-unitor transport. -/
def cob2Leftm (a : ℕ) : Cob2Mor (0 + a) a :=
  Cob2Mor.eqToMor (Nat.zero_add a)

/-- Raw right-unitor transport. -/
def cob2Rightm (a : ℕ) : Cob2Mor (a + 0) a :=
  Cob2Mor.eqToMor (Nat.add_zero a)

/-- The strengthened congruence imposing functorial tensor and structural naturality.
Pentagon and triangle are deliberately not constructors: they are proved from transports. -/
inductive Cob2MonoidalRel : {a b : ℕ} → Cob2Mor a b → Cob2Mor a b → Prop
  | old {a b} {f g : Cob2Mor a b} : Cob2Rel f g → Cob2MonoidalRel f g
  | comp_congr {a b c} {f f' : Cob2Mor a b} {g g' : Cob2Mor b c} :
      Cob2MonoidalRel f f' → Cob2MonoidalRel g g' →
        Cob2MonoidalRel (.comp f g) (.comp f' g')
  | tensor_congr {a b c d} {f f' : Cob2Mor a b} {g g' : Cob2Mor c d} :
      Cob2MonoidalRel f f' → Cob2MonoidalRel g g' →
        Cob2MonoidalRel (.tensor f g) (.tensor f' g')
  | refl {a b} (f : Cob2Mor a b) : Cob2MonoidalRel f f
  | symm {a b} {f g : Cob2Mor a b} : Cob2MonoidalRel f g → Cob2MonoidalRel g f
  | trans {a b} {f g h : Cob2Mor a b} :
      Cob2MonoidalRel f g → Cob2MonoidalRel g h → Cob2MonoidalRel f h
  | tensor_id (a c : ℕ) :
      Cob2MonoidalRel (.tensor (.id a) (.id c)) (.id (a + c))
  | interchange {a₁ b₁ c₁ a₂ b₂ c₂}
      (f₁ : Cob2Mor a₁ b₁) (f₂ : Cob2Mor a₂ b₂)
      (g₁ : Cob2Mor b₁ c₁) (g₂ : Cob2Mor b₂ c₂) :
      Cob2MonoidalRel (.comp (.tensor f₁ f₂) (.tensor g₁ g₂))
        (.tensor (.comp f₁ g₁) (.comp f₂ g₂))
  | associator_naturality {a₁ b₁ a₂ b₂ a₃ b₃}
      (f₁ : Cob2Mor a₁ b₁) (f₂ : Cob2Mor a₂ b₂) (f₃ : Cob2Mor a₃ b₃) :
      Cob2MonoidalRel
        (.comp (.tensor (.tensor f₁ f₂) f₃) (cob2αm b₁ b₂ b₃))
        (.comp (cob2αm a₁ a₂ a₃) (.tensor f₁ (.tensor f₂ f₃)))
  | leftUnitor_naturality {a b} (f : Cob2Mor a b) :
      Cob2MonoidalRel
        (.comp (.tensor (.id 0) f) (cob2Leftm b))
        (.comp (cob2Leftm a) f)
  | rightUnitor_naturality {a b} (f : Cob2Mor a b) :
      Cob2MonoidalRel
        (.comp (.tensor f (.id 0)) (cob2Rightm b))
        (.comp (cob2Rightm a) f)

/-- The indexed setoid for the strengthened quotient. -/
def Cob2MonoidalSetoid (a b : ℕ) : Setoid (Cob2Mor a b) where
  r := Cob2MonoidalRel
  iseqv := ⟨Cob2MonoidalRel.refl, Cob2MonoidalRel.symm, Cob2MonoidalRel.trans⟩

/-- Morphisms in the strengthened quotient. -/
def Cob2MonoidalHom (X Y : Cob2MonoidalObj) : Type :=
  Quotient (Cob2MonoidalSetoid X.arity Y.arity)

namespace Cob2Monoidal

private def qid (X : Cob2MonoidalObj) : Cob2MonoidalHom X X := ⟦Cob2Mor.id X.arity⟧

private def qcomp {X Y Z : Cob2MonoidalObj}
    (f : Cob2MonoidalHom X Y) (g : Cob2MonoidalHom Y Z) : Cob2MonoidalHom X Z :=
  Quotient.map₂ Cob2Mor.comp (fun _ _ hf _ _ hg => by
    change Cob2MonoidalRel _ _ at hf hg
    exact Cob2MonoidalRel.comp_congr hf hg) f g

instance category : Category Cob2MonoidalObj where
  Hom := Cob2MonoidalHom
  id := qid
  comp := qcomp
  id_comp f := by
    obtain ⟨f⟩ := f
    exact Quotient.sound (.old (.id_comp f))
  comp_id f := by
    obtain ⟨f⟩ := f
    exact Quotient.sound (.old (.comp_id f))
  assoc f g h := by
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    obtain ⟨h⟩ := h
    exact Quotient.sound (.old (.assoc f g h))

/-- Tensor on wrapped arities. -/
def tensorObj (X Y : Cob2MonoidalObj) : Cob2MonoidalObj := ⟨X.arity + Y.arity⟩

/-- Tensor on quotient morphisms. -/
def tensorHom {X₁ Y₁ X₂ Y₂ : Cob2MonoidalObj}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  Quotient.map₂ Cob2Mor.tensor
    (fun _ _ hf _ _ hg => by
      change Cob2MonoidalRel _ _ at hf hg
      exact Cob2MonoidalRel.tensor_congr hf hg) f g

/-- Named multiplication class. -/
def mul : (⟨2⟩ : Cob2MonoidalObj) ⟶ ⟨1⟩ := ⟦Cob2Mor.μ⟧
/-- Named unit class. -/
def unit : (⟨0⟩ : Cob2MonoidalObj) ⟶ ⟨1⟩ := ⟦Cob2Mor.η⟧
/-- Named comultiplication class. -/
def comul : (⟨1⟩ : Cob2MonoidalObj) ⟶ ⟨2⟩ := ⟦Cob2Mor.δ⟧
/-- Named counit class. -/
def counit : (⟨1⟩ : Cob2MonoidalObj) ⟶ ⟨0⟩ := ⟦Cob2Mor.ε⟧
/-- Named swap class only; no braiding is asserted. -/
def swap (a b : ℕ) : (⟨a + b⟩ : Cob2MonoidalObj) ⟶ ⟨b + a⟩ := ⟦Cob2Mor.swap a b⟧

private def assocEq (X Y Z : Cob2MonoidalObj) :
    tensorObj (tensorObj X Y) Z = tensorObj X (tensorObj Y Z) := by
  apply Cob2MonoidalObj.ext
  exact Nat.add_assoc _ _ _

private def leftEq (X : Cob2MonoidalObj) : tensorObj ⟨0⟩ X = X := by
  apply Cob2MonoidalObj.ext
  exact Nat.zero_add _

private def rightEq (X : Cob2MonoidalObj) : tensorObj X ⟨0⟩ = X := by
  apply Cob2MonoidalObj.ext
  exact Nat.add_zero _

instance monoidalStruct : MonoidalCategoryStruct Cob2MonoidalObj where
  tensorObj := tensorObj
  tensorHom := tensorHom
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorUnit := ⟨0⟩
  associator X Y Z := eqToIso (assocEq X Y Z)
  leftUnitor X := eqToIso (leftEq X)
  rightUnitor X := eqToIso (rightEq X)

/-
A raw equality transport represents the categorical `eqToHom` of wrapped arities.
-/
theorem class_eqToMor {a b : ℕ} (h : a = b) :
    (⟦Cob2Mor.eqToMor h⟧ : (⟨a⟩ : Cob2MonoidalObj) ⟶ ⟨b⟩) =
      eqToHom (Cob2MonoidalObj.ext h) := by
        aesop

theorem associator_hom_class (X Y Z : Cob2MonoidalObj) :
    (α_ X Y Z).hom =
      (⟦cob2αm X.arity Y.arity Z.arity⟧ :
        tensorObj (tensorObj X Y) Z ⟶ tensorObj X (tensorObj Y Z)) := by
          convert rfl;
          convert class_eqToMor _

theorem leftUnitor_hom_class (X : Cob2MonoidalObj) :
    (λ_ X).hom =
      (⟦cob2Leftm X.arity⟧ : tensorObj ⟨0⟩ X ⟶ X) := by
        convert rfl;
        convert class_eqToMor _

theorem rightUnitor_hom_class (X : Cob2MonoidalObj) :
    (ρ_ X).hom =
      (⟦cob2Rightm X.arity⟧ : tensorObj X ⟨0⟩ ⟶ X) := by
        convert class_eqToMor _;
        exact Nat.add_zero _

/-
Tensoring two raw equality transports gives transport along addition.
-/
theorem tensor_eqToMor {a b c d : ℕ} (h : a = b) (k : c = d) :
    (⟦Cob2Mor.tensor (Cob2Mor.eqToMor h) (Cob2Mor.eqToMor k)⟧ :
      (⟨a + c⟩ : Cob2MonoidalObj) ⟶ ⟨b + d⟩) =
      eqToHom (Cob2MonoidalObj.ext (congrArg₂ (· + ·) h k)) := by
        have h_tensor_id : Cob2MonoidalRel (Cob2Mor.tensor (Cob2Mor.eqToMor h) (Cob2Mor.eqToMor k)) (Cob2Mor.eqToMor (by
        rw [ h, k ])) := by
          all_goals generalize_proofs at *;
          induction h ; induction k ; simp_all +decide [ Cob2Mor.eqToMor ];
          exact Cob2MonoidalRel.tensor_id a c
        generalize_proofs at *;
        exact Quotient.sound h_tensor_id |> fun h => h.trans ( by aesop )

private theorem tensorHom_eqToHom
    {X X' Y Y' : Cob2MonoidalObj} (h : X = X') (k : Y = Y') :
    tensorHom (eqToHom h) (eqToHom k) =
      eqToHom (congrArg₂ tensorObj h k) := by
        unfold eqToHom tensorHom;
        convert tensor_eqToMor _ _;
        rotate_left;
        exact congr_arg Cob2MonoidalObj.arity h;
        exact congr_arg Cob2MonoidalObj.arity k;
        unfold Quotient.map₂; aesop;

private theorem pentagon_transport (W X Y Z : Cob2MonoidalObj) :
    tensorHom (eqToIso (assocEq W X Y)).hom (𝟙 Z) ≫
        (eqToIso (assocEq W (tensorObj X Y) Z)).hom ≫
          tensorHom (𝟙 W) (eqToIso (assocEq X Y Z)).hom =
      (eqToIso (assocEq (tensorObj W X) Y Z)).hom ≫
        (eqToIso (assocEq W X (tensorObj Y Z))).hom := by
          simp +decide [ eqToIso, CategoryTheory.eqToHom_trans ];
          grind +suggestions

private theorem triangle_transport (X Y : Cob2MonoidalObj) :
    (eqToIso (assocEq X ⟨0⟩ Y)).hom ≫ tensorHom (𝟙 X) (eqToIso (leftEq Y)).hom =
      tensorHom (eqToIso (rightEq X)).hom (𝟙 Y) := by
        convert tensorHom_eqToHom _ _ using 1;
        all_goals norm_num [ eqToIso, eqToHom ];
        · grind +locals;
        · convert tensorHom_eqToHom rfl rfl using 1;
        · exact Cob2MonoidalObj.ext ( Nat.add_zero _ )

/-- The lawful monoidal category on the strengthened quotient. -/
instance cob2MonoidalCategory : MonoidalCategory Cob2MonoidalObj :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by
      intro X Y
      exact Quotient.sound (.tensor_id X.arity Y.arity))
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := by
      intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
      obtain ⟨f₁⟩ := f₁
      obtain ⟨f₂⟩ := f₂
      obtain ⟨g₁⟩ := g₁
      obtain ⟨g₂⟩ := g₂
      exact Quotient.sound (.interchange f₁ f₂ g₁ g₂))
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      obtain ⟨f₁⟩ := f₁
      obtain ⟨f₂⟩ := f₂
      obtain ⟨f₃⟩ := f₃
      rw [associator_hom_class Y₁ Y₂ Y₃, associator_hom_class X₁ X₂ X₃]
      exact Quotient.sound (.associator_naturality f₁ f₂ f₃))
    (leftUnitor_naturality := by
      intro X Y f
      obtain ⟨f⟩ := f
      rw [leftUnitor_hom_class Y, leftUnitor_hom_class X]
      exact Quotient.sound (.leftUnitor_naturality f))
    (rightUnitor_naturality := by
      intro X Y f
      obtain ⟨f⟩ := f
      rw [rightUnitor_hom_class Y, rightUnitor_hom_class X]
      exact Quotient.sound (.rightUnitor_naturality f))
    (pentagon := pentagon_transport)
    (triangle := triangle_transport)

/-- Interchange smoke theorem. -/
theorem cob2Monoidal_interchange
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Cob2MonoidalObj}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂) :=
  MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _

/-- Associator-naturality smoke theorem. -/
theorem cob2Monoidal_associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Cob2MonoidalObj}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom =
      (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) :=
  MonoidalCategory.associator_naturality _ _ _

end Cob2Monoidal

/-- The canonical ordinary functor from the old quotient to the strengthened quotient. -/
def Cob2.toMonoidalQuotient : Cob2Cat ⥤ Cob2MonoidalObj where
  obj n := ⟨n⟩
  map f := Quotient.map (fun w => w) (fun _ _ h => Cob2MonoidalRel.old h) f
  map_id _ := rfl
  map_comp f g := by
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    rfl



namespace CommFrobeniusData

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

/-- Interpreting an arity transport gives the corresponding object transport. -/
theorem interpret_eqToMor (A : CommFrobeniusData C) {a b : ℕ} (h : a = b) :
    A.interpret (Cob2Mor.eqToMor h) = eqToHom (congrArg A.objPow h) := by
  subst b
  rfl

private theorem interpret_tensor_id (A : CommFrobeniusData C) (a c : ℕ) :
    A.interpret (.tensor (.id a) (.id c)) = A.interpret (.id (a + c)) := by
  simp only [interpret_tensor, interpret_id]
  simp

private theorem interpret_interchange (A : CommFrobeniusData C)
    {a₁ b₁ c₁ a₂ b₂ c₂ : ℕ}
    (f₁ : Cob2Mor a₁ b₁) (f₂ : Cob2Mor a₂ b₂)
    (g₁ : Cob2Mor b₁ c₁) (g₂ : Cob2Mor b₂ c₂) :
    A.interpret (.comp (.tensor f₁ f₂) (.tensor g₁ g₂)) =
      A.interpret (.tensor (.comp f₁ g₁) (.comp f₂ g₂)) := by
  simp only [interpret_comp, interpret_tensor]
  simp

private theorem eqToHom_objPow_succ (A : CommFrobeniusData C)
    {a b : ℕ} (h : a = b) :
    eqToHom (congrArg A.objPow (congrArg Nat.succ h)) =
      eqToHom (congrArg A.objPow h) ▷ A.X := by
  subst b
  simp

/-- Associativity coherence for the recursively defined `powAdd` isomorphisms. -/
theorem powAdd_associativity (A : CommFrobeniusData C) (a b c : ℕ) :
    (A.powAdd a b).inv ▷ A.objPow c ≫
          (A.powAdd (a + b) c).inv ≫
            eqToHom (congrArg A.objPow (Nat.add_assoc a b c)) =
      (α_ (A.objPow a) (A.objPow b) (A.objPow c)).hom ≫
          A.objPow a ◁ (A.powAdd b c).inv ≫
            (A.powAdd a (b + c)).inv := by
  induction c with
  | zero =>
      simp
  | succ c ih =>
      have transport_succ :
          eqToHom (congrArg A.objPow (Nat.add_assoc a b (c + 1))) =
            eqToHom (congrArg A.objPow (Nat.add_assoc a b c)) ▷ A.X := by
        convert eqToHom_objPow_succ A (Nat.add_assoc a b c)
      simp only [powAdd_succ, Nat.add_succ]
      simp only [Iso.trans_inv, whiskerRightIso_inv, objPow_succ]
      simp only [Category.assoc]
      rw [transport_succ]
      calc
        _ = (α_ (A.objPow a ⊗ A.objPow b) (A.objPow c) A.X).inv ≫
              (((A.powAdd a b).inv ▷ A.objPow c ≫
                  (A.powAdd (a + b) c).inv ≫
                    eqToHom (congrArg A.objPow (Nat.add_assoc a b c))) ▷ A.X) := by
              monoidal
        _ = (α_ (A.objPow a ⊗ A.objPow b) (A.objPow c) A.X).inv ≫
              (((α_ (A.objPow a) (A.objPow b) (A.objPow c)).hom ≫
                  A.objPow a ◁ (A.powAdd b c).inv ≫
                    (A.powAdd a (b + c)).inv) ▷ A.X) := by
              rw [ih]
        _ = _ := by
              monoidal

private theorem powAdd_associativity_hom (A : CommFrobeniusData C) (a b c : ℕ) :
    eqToHom (congrArg A.objPow (Nat.add_assoc a b c)).symm ≫
        (A.powAdd (a + b) c).hom ≫
          ((A.powAdd a b).hom ▷ A.objPow c) =
      (A.powAdd a (b + c)).hom ≫
            (A.objPow a ◁ (A.powAdd b c).hom) ≫
              (α_ (A.objPow a) (A.objPow b) (A.objPow c)).inv := by
  apply CategoryTheory.eq_of_inv_eq_inv
  simpa only [IsIso.inv_comp, MonoidalCategory.inv_whiskerRight,
    MonoidalCategory.inv_whiskerLeft, CategoryTheory.inv_eqToHom,
    IsIso.Iso.inv_hom, IsIso.Iso.inv_inv, Category.assoc] using
      powAdd_associativity A a b c

private theorem powAdd_associativity_hom' (A : CommFrobeniusData C) (a b c : ℕ) :
    (A.powAdd (a + b) c).hom ≫
          ((A.powAdd a b).hom ▷ A.objPow c) =
      eqToHom (congrArg A.objPow (Nat.add_assoc a b c)) ≫
          (A.powAdd a (b + c)).hom ≫
            (A.objPow a ◁ (A.powAdd b c).hom) ≫
              (α_ (A.objPow a) (A.objPow b) (A.objPow c)).inv := by
  rw [← cancel_epi
    (eqToHom (congrArg A.objPow (Nat.add_assoc a b c)).symm)]
  rw [powAdd_associativity_hom]
  simp

/-- Right-unit coherence for `powAdd`. -/
theorem powAdd_right_unitality (A : CommFrobeniusData C) (a : ℕ) :
    (ρ_ (A.objPow a)).hom =
      (A.powAdd a 0).inv ≫
        eqToHom (congrArg A.objPow (Nat.add_zero a)) := by
  simp

/-- Left-unit coherence for `powAdd`. -/
theorem powAdd_left_unitality (A : CommFrobeniusData C) (a : ℕ) :
    (λ_ (A.objPow a)).hom =
      (A.powAdd 0 a).inv ≫
        eqToHom (congrArg A.objPow (Nat.zero_add a)) := by
  induction a with
  | zero => simpa using (unitors_equal (C := C))
  | succ a ih =>
      have transport_succ :
          eqToHom (congrArg A.objPow (Nat.zero_add (a + 1))) =
            eqToHom (congrArg A.objPow (Nat.zero_add a)) ▷ A.X := by
        convert eqToHom_objPow_succ A (Nat.zero_add a)
      rw [powAdd_succ]
      simp only [Iso.trans_inv, whiskerRightIso_inv]
      simp only [objPow_succ, objPow_zero]
      rw [leftUnitor_tensor_hom]
      rw [Category.assoc]
      rw [cancel_epi]
      rw [ih, comp_whiskerRight, transport_succ]

private theorem interpret_associator_naturality (A : CommFrobeniusData C)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℕ}
    (f₁ : Cob2Mor a₁ b₁) (f₂ : Cob2Mor a₂ b₂) (f₃ : Cob2Mor a₃ b₃) :
    A.interpret
        (.comp (.tensor (.tensor f₁ f₂) f₃) (cob2αm b₁ b₂ b₃)) =
      A.interpret
        (.comp (cob2αm a₁ a₂ a₃) (.tensor f₁ (.tensor f₂ f₃))) := by
  simp only [interpret_comp, interpret_tensor, cob2αm, interpret_eqToMor]
  calc
    _ = (A.powAdd (a₁ + a₂) a₃).hom ≫
          ((A.powAdd a₁ a₂).hom ▷ A.objPow a₃) ≫
          ((A.interpret f₁ ⊗ₘ A.interpret f₂) ⊗ₘ A.interpret f₃) ≫
          ((A.powAdd b₁ b₂).inv ▷ A.objPow b₃) ≫
          (A.powAdd (b₁ + b₂) b₃).inv ≫
          eqToHom (congrArg A.objPow (Nat.add_assoc b₁ b₂ b₃)) := by
            slice_rhs 2 3 =>
              rw [← tensorHom_id,
                MonoidalCategory.tensorHom_comp_tensorHom]
            slice_rhs 2 3 =>
              rw [← tensorHom_id,
                MonoidalCategory.tensorHom_comp_tensorHom]
            simp only [Category.id_comp, Category.comp_id, Category.assoc]
    _ = (eqToHom (congrArg A.objPow (Nat.add_assoc a₁ a₂ a₃)) ≫
          (A.powAdd a₁ (a₂ + a₃)).hom ≫
          (A.objPow a₁ ◁ (A.powAdd a₂ a₃).hom) ≫
          (α_ (A.objPow a₁) (A.objPow a₂) (A.objPow a₃)).inv) ≫
          ((A.interpret f₁ ⊗ₘ A.interpret f₂) ⊗ₘ A.interpret f₃) ≫
          ((α_ (A.objPow b₁) (A.objPow b₂) (A.objPow b₃)).hom ≫
          (A.objPow b₁ ◁ (A.powAdd b₂ b₃).inv) ≫
          (A.powAdd b₁ (b₂ + b₃)).inv) := by
            slice_lhs 1 2 => rw [powAdd_associativity_hom']
            slice_lhs 6 8 => rw [powAdd_associativity]
            simp only [Category.assoc]
    _ = _ := by
          slice_lhs 4 6 =>
            rw [← associator_inv_conjugation]
          slice_lhs 3 4 =>
            rw [whiskerLeft_comp_tensorHom]
          slice_lhs 3 4 =>
            rw [tensorHom_comp_whiskerLeft]
          simp only [Category.assoc]

private theorem interpret_leftUnitor_naturality (A : CommFrobeniusData C)
    {a b : ℕ} (f : Cob2Mor a b) :
    A.interpret
        (.comp (.tensor (.id 0) f) (cob2Leftm b)) =
      A.interpret (.comp (cob2Leftm a) f) := by
  simp only [interpret_comp, interpret_tensor, interpret_id, cob2Leftm,
    interpret_eqToMor]
  simp only [Category.assoc]
  rw [← powAdd_left_unitality A b]
  simp only [objPow_zero]
  rw [MonoidalCategory.id_tensorHom]
  rw [leftUnitor_naturality]
  rw [powAdd_left_unitality A a]
  simp

private theorem interpret_rightUnitor_naturality (A : CommFrobeniusData C)
    {a b : ℕ} (f : Cob2Mor a b) :
    A.interpret
        (.comp (.tensor f (.id 0)) (cob2Rightm b)) =
      A.interpret (.comp (cob2Rightm a) f) := by
  simp only [interpret_comp, interpret_tensor, interpret_id, cob2Rightm,
    interpret_eqToMor]
  simp only [Category.assoc]
  rw [← powAdd_right_unitality A b]
  simp only [objPow_zero]
  rw [MonoidalCategory.tensorHom_id]
  rw [rightUnitor_naturality]
  rw [powAdd_right_unitality A a]
  simp

/-- Every Frobenius interpretation respects the strengthened monoidal relation. -/
theorem interpretMonoidal_sound (A : CommFrobeniusData C)
    {a b : ℕ} {f g : Cob2Mor a b} (h : Cob2MonoidalRel f g) :
    A.interpret f = A.interpret g := by
  induction h with
  | old h => exact A.interpret_sound h
  | comp_congr hf hg ihf ihg =>
      simp only [interpret_comp]
      rw [ihf, ihg]
  | tensor_congr hf hg ihf ihg =>
      simp only [interpret_tensor]
      rw [ihf, ihg]
  | refl f => rfl
  | symm h ih => exact ih.symm
  | trans hf hg ihf ihg => exact ihf.trans ihg
  | tensor_id a c => exact interpret_tensor_id A a c
  | interchange f₁ f₂ g₁ g₂ =>
      exact interpret_interchange A f₁ f₂ g₁ g₂
  | associator_naturality f₁ f₂ f₃ =>
      exact interpret_associator_naturality A f₁ f₂ f₃
  | leftUnitor_naturality f =>
      exact interpret_leftUnitor_naturality A f
  | rightUnitor_naturality f =>
      exact interpret_rightUnitor_naturality A f

/-- The Frobenius interpretation descended to the lawful monoidal quotient. -/
noncomputable def toCob2MonoidalFunctor (A : CommFrobeniusData C) :
    Cob2MonoidalObj ⥤ C where
  obj X := A.objPow X.arity
  map f := Quotient.lift (fun w => A.interpret w)
    (fun _ _ h => by
      change Cob2MonoidalRel _ _ at h
      exact interpretMonoidal_sound A h) f
  map_id X := rfl
  map_comp f g := by
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    rfl

/-- Evaluation of the descended functor on a raw representative. -/
@[simp]
theorem toCob2MonoidalFunctor_map_mk (A : CommFrobeniusData C)
    {a b : ℕ} (w : Cob2Mor a b) :
    (toCob2MonoidalFunctor A).map
        (⟦w⟧ : (⟨a⟩ : Cob2MonoidalObj) ⟶ ⟨b⟩) =
      A.interpret w := rfl

/-- Tensor maps are conjugated by the canonical `powAdd` comparisons. -/
theorem toCob2MonoidalFunctor_map_tensor (A : CommFrobeniusData C)
    {X₁ Y₁ X₂ Y₂ : Cob2MonoidalObj}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (toCob2MonoidalFunctor A).map (f ⊗ₘ g) =
      (A.powAdd X₁.arity X₂.arity).hom ≫
        ((toCob2MonoidalFunctor A).map f ⊗ₘ
          (toCob2MonoidalFunctor A).map g) ≫
            (A.powAdd Y₁.arity Y₂.arity).inv := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  rfl

/-- Coherent tensorator data for the descended interpretation. -/
noncomputable def toCob2MonoidalCore (A : CommFrobeniusData C) :
    (toCob2MonoidalFunctor A).CoreMonoidal where
  εIso := Iso.refl _
  μIso X Y := (A.powAdd X.arity Y.arity).symm
  μIso_hom_natural_left := by
    intro X Y f X'
    obtain ⟨f⟩ := f
    change (A.interpret f ▷ A.objPow X'.arity) ≫
        (A.powAdd Y.arity X'.arity).inv =
      (A.powAdd X.arity X'.arity).inv ≫
        A.interpret (.tensor f (.id X'.arity))
    simp only [interpret_tensor, interpret_id]
    simp
  μIso_hom_natural_right := by
    intro X Y X' f
    obtain ⟨f⟩ := f
    change (A.objPow X'.arity ◁ A.interpret f) ≫
        (A.powAdd X'.arity Y.arity).inv =
      (A.powAdd X'.arity X.arity).inv ≫
        A.interpret (.tensor (.id X'.arity) f)
    simp only [interpret_tensor, interpret_id]
    simp
  associativity := by
    intro X Y Z
    change (A.powAdd X.arity Y.arity).inv ▷ A.objPow Z.arity ≫
          (A.powAdd (X.arity + Y.arity) Z.arity).inv ≫
            (toCob2MonoidalFunctor A).map (α_ X Y Z).hom =
      (α_ (A.objPow X.arity) (A.objPow Y.arity) (A.objPow Z.arity)).hom ≫
          A.objPow X.arity ◁ (A.powAdd Y.arity Z.arity).inv ≫
            (A.powAdd X.arity (Y.arity + Z.arity)).inv
    rw [Cob2Monoidal.associator_hom_class]
    rw [toCob2MonoidalFunctor_map_mk]
    rw [cob2αm, interpret_eqToMor]
    convert powAdd_associativity A X.arity Y.arity Z.arity
  left_unitality := by
    intro X
    change (λ_ (A.objPow X.arity)).hom =
      (𝟙 (𝟙_ C) ▷ A.objPow X.arity) ≫
        (A.powAdd 0 X.arity).inv ≫
          (toCob2MonoidalFunctor A).map (λ_ X).hom
    rw [Cob2Monoidal.leftUnitor_hom_class]
    rw [toCob2MonoidalFunctor_map_mk]
    rw [cob2Leftm, interpret_eqToMor]
    simpa using powAdd_left_unitality A X.arity
  right_unitality := by
    intro X
    change (ρ_ (A.objPow X.arity)).hom =
      (A.objPow X.arity ◁ 𝟙 (𝟙_ C)) ≫
        (A.powAdd X.arity 0).inv ≫
          (toCob2MonoidalFunctor A).map (ρ_ X).hom
    rw [Cob2Monoidal.rightUnitor_hom_class]
    rw [toCob2MonoidalFunctor_map_mk]
    rw [cob2Rightm, interpret_eqToMor]
    simpa only [MonoidalCategory.whiskerLeft_id, Category.id_comp] using
      powAdd_right_unitality A X.arity

/-- The descended interpretation is a strong monoidal functor. -/
noncomputable def toCob2MonoidalFunctorMonoidal
    (A : CommFrobeniusData C) :
    (toCob2MonoidalFunctor A).Monoidal :=
  (toCob2MonoidalCore A).toMonoidal

/-- Precomposition with the old quotient recovers the original interpretation. -/
theorem toCob2MonoidalFunctor_comp_toMonoidalQuotient
    (A : CommFrobeniusData C) :
    Cob2.toMonoidalQuotient ⋙ toCob2MonoidalFunctor A =
      A.toCob2Functor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  induction f using Quotient.inductionOn
  rfl

end CommFrobeniusData
