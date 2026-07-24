import RequestProject.Cob2Symmetric

/-!
# The canonical commutative Frobenius object in the symmetric source

The object of arity one in `Cob2SymmetricObj`, together with the four named
generator classes, carries the commutative Frobenius structure presented by
the quotient.  This is the first internal step toward a generators-and-
relations universal property.

No normal-form theorem or comparison with geometric bordisms is asserted in
this file.
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace Cob2Symmetric

private theorem associator_one_hom :
    (α_ (⟨1⟩ : Cob2SymmetricObj) ⟨1⟩ ⟨1⟩).hom =
      𝟙 (⟨3⟩ : Cob2SymmetricObj) := by
  rfl

private theorem associator_one_inv :
    (α_ (⟨1⟩ : Cob2SymmetricObj) ⟨1⟩ ⟨1⟩).inv =
      𝟙 (⟨3⟩ : Cob2SymmetricObj) := by
  rfl

private theorem leftUnitor_one_hom :
    (λ_ (⟨1⟩ : Cob2SymmetricObj)).hom =
      𝟙 (⟨1⟩ : Cob2SymmetricObj) := by
  rfl

private theorem leftUnitor_one_inv :
    (λ_ (⟨1⟩ : Cob2SymmetricObj)).inv =
      𝟙 (⟨1⟩ : Cob2SymmetricObj) := by
  rfl

private theorem rightUnitor_one_hom :
    (ρ_ (⟨1⟩ : Cob2SymmetricObj)).hom =
      𝟙 (⟨1⟩ : Cob2SymmetricObj) := by
  rfl

private theorem rightUnitor_one_inv :
    (ρ_ (⟨1⟩ : Cob2SymmetricObj)).inv =
      𝟙 (⟨1⟩ : Cob2SymmetricObj) := by
  rfl

private theorem associator_unit_one_one_hom :
    (α_ (𝟙_ Cob2SymmetricObj)
      (⟨1⟩ : Cob2SymmetricObj) ⟨1⟩).hom =
        𝟙 (⟨2⟩ : Cob2SymmetricObj) := by
  rfl

private theorem associator_unit_one_one_inv :
    (α_ (𝟙_ Cob2SymmetricObj)
      (⟨1⟩ : Cob2SymmetricObj) ⟨1⟩).inv =
        𝟙 (⟨2⟩ : Cob2SymmetricObj) := by
  rfl

private theorem leftUnitor_two_hom :
    (λ_ ((⟨1⟩ : Cob2SymmetricObj) ⊗ ⟨1⟩)).hom =
      𝟙 (⟨2⟩ : Cob2SymmetricObj) := by
  rfl

private theorem leftUnitor_two_inv :
    (λ_ ((⟨1⟩ : Cob2SymmetricObj) ⊗ ⟨1⟩)).inv =
      𝟙 (⟨2⟩ : Cob2SymmetricObj) := by
  rfl

/-- The canonical commutative Frobenius datum carried by the arity-one
generator of the symmetric algebraic source. -/
def canonicalFrobenius : CommFrobeniusData Cob2SymmetricObj where
  X := ⟨1⟩
  mul := mul
  unit := unit
  comul := comul
  counit := counit
  mul_assoc' := by
    change _ = (𝟙 _ : (⟨3⟩ : Cob2SymmetricObj) ⟶ ⟨3⟩) ≫ _ ≫ _
    simp only [Category.id_comp]
    exact Quotient.sound (.monoidal (.old Cob2Rel.mul_assoc))
  unit_mul := by
    rw [leftUnitor_hom_class]
    exact Quotient.sound (.monoidal (.old Cob2Rel.unit_left))
  mul_unit := by
    rw [rightUnitor_hom_class]
    exact Quotient.sound (.monoidal (.old Cob2Rel.unit_right))
  comul_coassoc' := by
    change _ = _ ≫ _ ≫ (𝟙 _ : (⟨3⟩ : Cob2SymmetricObj) ⟶ ⟨3⟩)
    simp only [Category.comp_id]
    exact Quotient.sound (.monoidal (.old Cob2Rel.comul_coassoc.symm))
  counit_comul := by
    change _ = 𝟙 (⟨1⟩ : Cob2SymmetricObj)
    exact Quotient.sound (.monoidal (.old Cob2Rel.counit_left))
  comul_counit := by
    change _ = 𝟙 (⟨1⟩ : Cob2SymmetricObj)
    exact Quotient.sound (.monoidal (.old Cob2Rel.counit_right))
  frobenius_left := by
    change _ ≫ (𝟙 _ : (⟨3⟩ : Cob2SymmetricObj) ⟶ ⟨3⟩) ≫ _ = _
    simp only [Category.id_comp]
    exact Quotient.sound (.monoidal (.old Cob2Rel.frobenius))
  frobenius_right := by
    change _ ≫ (𝟙 _ : (⟨3⟩ : Cob2SymmetricObj) ⟶ ⟨3⟩) ≫ _ = _
    simp only [Category.id_comp]
    exact Quotient.sound (.monoidal (.old Cob2Rel.frobenius_right))
  mul_comm' := by
    exact Quotient.sound (.monoidal (.old Cob2Rel.mul_comm))

@[simp]
theorem canonicalFrobenius_X :
    canonicalFrobenius.X = (⟨1⟩ : Cob2SymmetricObj) := rfl

@[simp]
theorem canonicalFrobenius_mul :
    canonicalFrobenius.mul = mul := rfl

@[simp]
theorem canonicalFrobenius_unit :
    canonicalFrobenius.unit = unit := rfl

@[simp]
theorem canonicalFrobenius_comul :
    canonicalFrobenius.comul = comul := rfl

@[simp]
theorem canonicalFrobenius_counit :
    canonicalFrobenius.counit = counit := rfl

/-- The canonical comultiplication is cocommutative. -/
@[simp]
theorem canonical_comul_braiding :
    comul ≫
        (β_ (⟨1⟩ : Cob2SymmetricObj) ⟨1⟩).hom =
      comul := by
  simpa using
    CommFrobeniusData.comul_comm canonicalFrobenius

/-- The recursively associated tensor power of the canonical generator has
the expected arity. -/
@[simp]
theorem canonicalFrobenius_objPow_arity (n : ℕ) :
    (canonicalFrobenius.objPow n).arity = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (canonicalFrobenius.objPow n).arity + 1 = n + 1
      rw [ih]

/-- Canonical comparison from the recursively associated tensor power of the
generator to the object represented directly by its arity. -/
def canonicalPowIso :
    (n : ℕ) →
      canonicalFrobenius.objPow n ≅
        (⟨n⟩ : Cob2SymmetricObj)
  | 0 => Iso.refl _
  | n + 1 =>
      whiskerRightIso (canonicalPowIso n)
        canonicalFrobenius.X

private def canonicalObjPowEq (n : ℕ) :
    canonicalFrobenius.objPow n =
      (⟨n⟩ : Cob2SymmetricObj) :=
  Cob2SymmetricObj.ext
    (canonicalFrobenius_objPow_arity n)

private theorem canonicalPowIso_hom_eqToHom (n : ℕ) :
    (canonicalPowIso n).hom =
      eqToHom (canonicalObjPowEq n) := by
  induction n with
  | zero =>
      change 𝟙 (𝟙_ Cob2SymmetricObj) = eqToHom _
      symm
      apply eqToHom_refl
  | succ n ih =>
      simp only [canonicalPowIso, whiskerRightIso_hom]
      rw [ih]
      change tensorHom
          (eqToHom (canonicalObjPowEq n))
          (𝟙 canonicalFrobenius.X) =
        eqToHom (canonicalObjPowEq (n + 1))
      rw [show 𝟙 canonicalFrobenius.X =
          eqToHom rfl by simp]
      rw [tensorHom_eqToHom]

private def canonicalPowAddEq (a c : ℕ) :
    canonicalFrobenius.objPow (a + c) =
      canonicalFrobenius.objPow a ⊗
        canonicalFrobenius.objPow c :=
  Cob2SymmetricObj.ext (by
    rw [canonicalFrobenius_objPow_arity]
    change a + c =
      (canonicalFrobenius.objPow a).arity +
        (canonicalFrobenius.objPow c).arity
    simp)

private def canonicalAssocEq
    (X Y Z : Cob2SymmetricObj) :
    tensorObj (tensorObj X Y) Z =
      tensorObj X (tensorObj Y Z) :=
  Cob2SymmetricObj.ext (Nat.add_assoc _ _ _)

private theorem canonicalPowAdd_hom_eqToHom (a c : ℕ) :
    (canonicalFrobenius.powAdd a c).hom =
      eqToHom (canonicalPowAddEq a c) := by
  induction c with
  | zero =>
      change (ρ_ (canonicalFrobenius.objPow a)).inv =
        eqToHom (canonicalPowAddEq a 0)
      rw [← cancel_epi
        (ρ_ (canonicalFrobenius.objPow a)).hom]
      rw [Iso.hom_inv_id]
      rw [rightUnitor_hom_class]
      unfold cob2Rightm
      rw [class_eqToMor]
      rw [eqToHom_trans]
      symm
      apply eqToHom_refl
  | succ c ih =>
      simp only [CommFrobeniusData.powAdd_succ,
        Iso.trans_hom, whiskerRightIso_hom]
      rw [ih]
      change
        tensorHom
            (eqToHom (canonicalPowAddEq a c))
            (𝟙 canonicalFrobenius.X) ≫
              eqToHom
                (canonicalAssocEq
                  (canonicalFrobenius.objPow a)
                  (canonicalFrobenius.objPow c)
                  canonicalFrobenius.X) =
          eqToHom (canonicalPowAddEq a (c + 1))
      rw [show 𝟙 canonicalFrobenius.X =
          eqToHom rfl by simp]
      rw [tensorHom_eqToHom]
      rw [eqToHom_trans]

/-- The canonical comparisons respect the recursively defined tensor-power
comparison `powAdd`. -/
theorem canonicalPowIso_tensor (a c : ℕ) :
    (canonicalFrobenius.powAdd a c).hom ≫
        ((canonicalPowIso a).hom ⊗ₘ
          (canonicalPowIso c).hom) =
      (canonicalPowIso (a + c)).hom := by
  rw [canonicalPowAdd_hom_eqToHom,
    canonicalPowIso_hom_eqToHom,
    canonicalPowIso_hom_eqToHom]
  change
    eqToHom (canonicalPowAddEq a c) ≫
        tensorHom
          (eqToHom (canonicalObjPowEq a))
          (eqToHom (canonicalObjPowEq c)) =
      (canonicalPowIso (a + c)).hom
  rw [tensorHom_eqToHom]
  rw [eqToHom_trans]
  rw [canonicalPowIso_hom_eqToHom]

private theorem canonicalPowAdd_inv_comp (a c : ℕ) :
    (canonicalFrobenius.powAdd a c).inv ≫
        (canonicalPowIso (a + c)).hom =
      (canonicalPowIso a).hom ⊗ₘ
        (canonicalPowIso c).hom := by
  rw [← canonicalPowIso_tensor]
  simp

/-- Raw-word naturality for the canonical interpretation: interpreting a
word in the source's canonical Frobenius object recovers its own symmetric
quotient class, up to the canonical tensor-power comparisons. -/
theorem canonical_interpret_naturality
    {a b : ℕ} (w : Cob2Mor a b) :
    canonicalFrobenius.interpret w ≫
        (canonicalPowIso b).hom =
      (canonicalPowIso a).hom ≫
        (⟦w⟧ :
          (⟨a⟩ : Cob2SymmetricObj) ⟶ ⟨b⟩) := by
  induction w with
  | id n =>
      simp only [CommFrobeniusData.interpret_id,
        Category.id_comp]
      change (canonicalPowIso n).hom =
        (canonicalPowIso n).hom ≫
          (⟦Cob2Mor.id n⟧ :
            (⟨n⟩ : Cob2SymmetricObj) ⟶ ⟨n⟩)
      have h :
          (⟦Cob2Mor.id n⟧ :
            (⟨n⟩ : Cob2SymmetricObj) ⟶ ⟨n⟩) =
            𝟙 (⟨n⟩ : Cob2SymmetricObj) := rfl
      rw [h, Category.comp_id]
  | μ =>
      simp [CommFrobeniusData.interpret,
        canonicalPowIso, canonicalFrobenius,
        associator_unit_one_one_hom,
        leftUnitor_two_hom, leftUnitor_one_inv]
      change
        (⟦Cob2Mor.comp (.id 2)
            (.comp (.id 2) .μ)⟧ :
          Cob2SymmetricHom ⟨2⟩ ⟨1⟩) =
            ⟦Cob2Mor.μ⟧
      exact Quotient.sound (.monoidal (.old
        (.trans (.id_comp _) (.id_comp _))))
  | η =>
      simp [CommFrobeniusData.interpret,
        canonicalPowIso, canonicalFrobenius,
        leftUnitor_one_inv]
      rfl
  | δ =>
      simp [CommFrobeniusData.interpret,
        canonicalPowIso, canonicalFrobenius,
        associator_unit_one_one_inv,
        leftUnitor_two_inv, leftUnitor_one_hom]
      change
        (⟦Cob2Mor.comp (.id 1)
            (.comp .δ (.comp (.id 2) (.id 2)))⟧ :
          Cob2SymmetricHom ⟨1⟩ ⟨2⟩) =
            ⟦Cob2Mor.δ⟧
      apply Quotient.sound
      apply Cob2SymmetricRel.monoidal
      apply Cob2MonoidalRel.old
      exact Cob2Rel.trans (.id_comp _)
        (.trans
          (.comp_congr (.refl _) (.comp_id _))
          (.comp_id _))
  | ε =>
      simp [CommFrobeniusData.interpret,
        canonicalPowIso, canonicalFrobenius,
        leftUnitor_one_hom]
      change
        (⟦Cob2Mor.comp (.id 1) .ε⟧ :
          Cob2SymmetricHom ⟨1⟩ ⟨0⟩) =
            ⟦Cob2Mor.ε⟧
      exact Quotient.sound (.monoidal (.old (.id_comp _)))
  | comp f g ihf ihg =>
      simp only [CommFrobeniusData.interpret_comp,
        Category.assoc]
      rw [ihg]
      rw [← Category.assoc]
      rw [ihf]
      rw [Category.assoc]
      rw [cancel_epi]
      rfl
  | tensor f g ihf ihg =>
      simp only [CommFrobeniusData.interpret_tensor,
        Category.assoc]
      rw [canonicalPowAdd_inv_comp]
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
      rw [ihf, ihg]
      rw [← MonoidalCategory.tensorHom_comp_tensorHom]
      rw [← Category.assoc]
      rw [canonicalPowIso_tensor]
      rfl
  | swap a b =>
      simp only [CommFrobeniusData.interpret_swap,
        Category.assoc]
      rw [canonicalPowAdd_inv_comp]
      rw [← BraidedCategory.braiding_naturality]
      rw [← Category.assoc]
      rw [canonicalPowIso_tensor]
      rfl

/-- Interpreting the canonical Frobenius object reconstructs the identity
functor on the symmetric algebraic source. -/
def canonicalInterpretationIso :
    canonicalFrobenius.toCob2SymmetricFunctor ≅
      𝟭 Cob2SymmetricObj := by
  refine NatIso.ofComponents
    (fun X => canonicalPowIso X.arity) ?_
  rintro ⟨a⟩ ⟨b⟩ f
  obtain ⟨w⟩ := f
  change Cob2Mor a b at w
  exact canonical_interpret_naturality w

/-- The canonical interpretation, bundled as a lax braided functor using
its already verified strong monoidal and braided structures. -/
def canonicalInterpretationLaxBraidedFunctor :
    LaxBraidedFunctor
      Cob2SymmetricObj Cob2SymmetricObj := by
  letI :=
    canonicalFrobenius.toCob2SymmetricFunctorMonoidal
  letI :=
    canonicalFrobenius.toCob2SymmetricFunctorBraided
  exact LaxBraidedFunctor.of
    canonicalFrobenius.toCob2SymmetricFunctor

/-- The identity functor on the symmetric algebraic source, bundled as a
lax braided functor. -/
def identityLaxBraidedFunctor :
    LaxBraidedFunctor
      Cob2SymmetricObj Cob2SymmetricObj :=
  LaxBraidedFunctor.of (𝟭 Cob2SymmetricObj)

/-- The canonical interpretation reconstructs the identity also in the
category of bundled lax braided functors. -/
def canonicalInterpretationBraidedIso :
    canonicalInterpretationLaxBraidedFunctor ≅
      identityLaxBraidedFunctor := by
  refine LaxBraidedFunctor.isoOfComponents
    (fun X => canonicalPowIso X.arity) ?_ ?_ ?_
  · intro X Y f
    exact canonicalInterpretationIso.hom.naturality f
  · dsimp [canonicalInterpretationLaxBraidedFunctor,
      identityLaxBraidedFunctor,
      CommFrobeniusData.toCob2SymmetricFunctorMonoidal,
      CommFrobeniusData.toCob2SymmetricCore,
      canonicalPowIso]
    change (𝟙 (𝟙_ Cob2SymmetricObj)) ≫
        𝟙 (𝟙_ Cob2SymmetricObj) =
      𝟙 (𝟙_ Cob2SymmetricObj)
    simp
  · intro X Y
    dsimp [canonicalInterpretationLaxBraidedFunctor,
      identityLaxBraidedFunctor,
      CommFrobeniusData.toCob2SymmetricFunctorMonoidal,
      CommFrobeniusData.toCob2SymmetricCore]
    change
      (canonicalFrobenius.powAdd
          X.arity Y.arity).inv ≫
          (canonicalPowIso
            (X.arity + Y.arity)).hom =
        ((canonicalPowIso X.arity).hom ⊗ₘ
          (canonicalPowIso Y.arity).hom) ≫
            𝟙 (X ⊗ Y)
    rw [Category.comp_id]
    rw [← canonicalPowIso_tensor]
    simp

end Cob2Symmetric
