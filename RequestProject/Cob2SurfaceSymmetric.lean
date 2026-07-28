import RequestProject.Cob2SurfaceWiring

/-!
# Symmetric monoidal structure on surface normal forms

This module packages the already verified graph-gluing category and
disjoint-union bifunctor on `SurfaceNFObj` as a lawful symmetric monoidal
category.  The structural isomorphisms are the canonical transports of
natural-number arities, and the braiding is the block-swap surface code.

This remains a finite combinatorial category.  No comparison with smooth
oriented bordisms is asserted here.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

namespace Cob2NormalForm

namespace SurfaceNFMonoidal

/-- Tensor product of wrapped arities. -/
def tensorObj (X Y : SurfaceNFObj) : SurfaceNFObj :=
  SurfaceNFObj.tensorObj X Y

/-- Tensor product of surface normal-form morphisms. -/
def tensorHom {X₁ Y₁ X₂ Y₂ : SurfaceNFObj}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  SurfaceNF.tensor f g

private def assocEq (X Y Z : SurfaceNFObj) :
    tensorObj (tensorObj X Y) Z = tensorObj X (tensorObj Y Z) := by
  apply SurfaceNFObj.ext
  exact Nat.add_assoc _ _ _

private def leftEq (X : SurfaceNFObj) : tensorObj ⟨0⟩ X = X := by
  apply SurfaceNFObj.ext
  exact Nat.zero_add _

private def rightEq (X : SurfaceNFObj) : tensorObj X ⟨0⟩ = X := by
  apply SurfaceNFObj.ext
  exact Nat.add_zero _

instance monoidalStruct : MonoidalCategoryStruct SurfaceNFObj where
  tensorObj := tensorObj
  tensorHom := tensorHom
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorUnit := ⟨0⟩
  associator X Y Z := eqToIso (assocEq X Y Z)
  leftUnitor X := eqToIso (leftEq X)
  rightUnitor X := eqToIso (rightEq X)

private theorem tensorHom_eqToHom
    {X X' Y Y' : SurfaceNFObj} (h : X = X') (k : Y = Y') :
    tensorHom (eqToHom h) (eqToHom k) =
      eqToHom (congrArg₂ tensorObj h k) := by
  subst X'
  subst Y'
  exact SurfaceNF.tensor_identity X.arity Y.arity

private theorem pentagon_transport (W X Y Z : SurfaceNFObj) :
    tensorHom (eqToIso (assocEq W X Y)).hom (𝟙 Z) ≫
        (eqToIso (assocEq W (tensorObj X Y) Z)).hom ≫
          tensorHom (𝟙 W) (eqToIso (assocEq X Y Z)).hom =
      (eqToIso (assocEq (tensorObj W X) Y Z)).hom ≫
        (eqToIso (assocEq W X (tensorObj Y Z))).hom := by
  change
    tensorHom (eqToHom (assocEq W X Y)) (eqToHom rfl) ≫
        eqToHom (assocEq W (tensorObj X Y) Z) ≫
          tensorHom (eqToHom rfl) (eqToHom (assocEq X Y Z)) =
      eqToHom (assocEq (tensorObj W X) Y Z) ≫
        eqToHom (assocEq W X (tensorObj Y Z))
  rw [tensorHom_eqToHom, tensorHom_eqToHom]
  simp

private theorem triangle_transport (X Y : SurfaceNFObj) :
    (eqToIso (assocEq X ⟨0⟩ Y)).hom ≫
        tensorHom (𝟙 X) (eqToIso (leftEq Y)).hom =
      tensorHom (eqToIso (rightEq X)).hom (𝟙 Y) := by
  change
    eqToHom (assocEq X ⟨0⟩ Y) ≫
        tensorHom (eqToHom rfl) (eqToHom (leftEq Y)) =
      tensorHom (eqToHom (rightEq X)) (eqToHom rfl)
  rw [tensorHom_eqToHom, tensorHom_eqToHom]
  simp

/-- The explicit arity cast on normal forms agrees with categorical
transport at the source and target objects. -/
private theorem cast_eq_transport
    {a b a' b' : ℕ} (ha : a = a') (hb : b = b')
    (s : SurfaceNF a b) :
    (eqToHom (SurfaceNFObj.ext ha).symm ≫ s ≫
        eqToHom (SurfaceNFObj.ext hb) :
      (⟨a'⟩ : SurfaceNFObj) ⟶ ⟨b'⟩) =
      SurfaceNF.cast ha hb s := by
  subst a'
  subst b'
  change
    (𝟙 (⟨a⟩ : SurfaceNFObj) ≫ s ≫
        𝟙 (⟨b⟩ : SurfaceNFObj)) =
      SurfaceNF.cast rfl rfl s
  simp only [Category.comp_id, Category.id_comp]
  induction s using Quotient.inductionOn with
  | _ s => rfl

private theorem identity_zero_eq_empty :
    SurfaceNF.identity 0 = SurfaceNF.empty := by
  apply Quotient.sound
  refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
  · intro i
    exact i.elim0
  · intro j
    exact j.elim0
  · intro k
    exact k.elim0

instance monoidalCategory : MonoidalCategory SurfaceNFObj :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by
      intro X Y
      exact SurfaceNF.tensor_identity X.arity Y.arity)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := by
      intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
      exact SurfaceNF.tensor_comp f₁ g₁ f₂ g₂)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      let ha := Nat.add_assoc X₁.arity X₂.arity X₃.arity
      let hb := Nat.add_assoc Y₁.arity Y₂.arity Y₃.arity
      let s := SurfaceNF.tensor (SurfaceNF.tensor f₁ f₂) f₃
      have hcast :
          SurfaceNF.cast ha hb s =
            SurfaceNF.tensor f₁ (SurfaceNF.tensor f₂ f₃) :=
        SurfaceNF.tensor_assoc f₁ f₂ f₃
      have htransport :=
        cast_eq_transport ha hb s
      change
        s ≫ eqToHom (assocEq Y₁ Y₂ Y₃) =
          eqToHom (assocEq X₁ X₂ X₃) ≫
            SurfaceNF.tensor f₁ (SurfaceNF.tensor f₂ f₃)
      calc
        s ≫ eqToHom (assocEq Y₁ Y₂ Y₃) =
            (eqToHom (assocEq X₁ X₂ X₃) ≫
              eqToHom (assocEq X₁ X₂ X₃).symm) ≫
                s ≫ eqToHom (assocEq Y₁ Y₂ Y₃) := by simp
        _ = eqToHom (assocEq X₁ X₂ X₃) ≫
              (eqToHom (assocEq X₁ X₂ X₃).symm ≫
                s ≫ eqToHom (assocEq Y₁ Y₂ Y₃)) := by simp [Category.assoc]
        _ = eqToHom (assocEq X₁ X₂ X₃) ≫
              SurfaceNF.cast ha hb s := by
                rw [htransport]
        _ = eqToHom (assocEq X₁ X₂ X₃) ≫
              SurfaceNF.tensor f₁ (SurfaceNF.tensor f₂ f₃) := by
                rw [hcast])
    (leftUnitor_naturality := by
      intro X Y f
      let ha := Nat.zero_add X.arity
      let hb := Nat.zero_add Y.arity
      let s := SurfaceNF.tensor SurfaceNF.empty f
      have hcast : SurfaceNF.cast ha hb s = f :=
        SurfaceNF.tensor_empty_left f
      have htransport := cast_eq_transport ha hb s
      change
        SurfaceNF.tensor (SurfaceNF.identity 0) f ≫
            eqToHom (leftEq Y) =
          eqToHom (leftEq X) ≫ f
      rw [identity_zero_eq_empty]
      calc
        s ≫ eqToHom (leftEq Y) =
            (eqToHom (leftEq X) ≫ eqToHom (leftEq X).symm) ≫
              s ≫ eqToHom (leftEq Y) := by simp
        _ = eqToHom (leftEq X) ≫
              (eqToHom (leftEq X).symm ≫ s ≫ eqToHom (leftEq Y)) := by
                simp [Category.assoc]
        _ = eqToHom (leftEq X) ≫ SurfaceNF.cast ha hb s := by
              rw [htransport]
        _ = eqToHom (leftEq X) ≫ f := by rw [hcast])
    (rightUnitor_naturality := by
      intro X Y f
      let ha := Nat.add_zero X.arity
      let hb := Nat.add_zero Y.arity
      let s := SurfaceNF.tensor f SurfaceNF.empty
      have hcast : SurfaceNF.cast ha hb s = f :=
        SurfaceNF.tensor_empty_right f
      have htransport := cast_eq_transport ha hb s
      change
        SurfaceNF.tensor f (SurfaceNF.identity 0) ≫
            eqToHom (rightEq Y) =
          eqToHom (rightEq X) ≫ f
      rw [identity_zero_eq_empty]
      calc
        s ≫ eqToHom (rightEq Y) =
            (eqToHom (rightEq X) ≫ eqToHom (rightEq X).symm) ≫
              s ≫ eqToHom (rightEq Y) := by simp
        _ = eqToHom (rightEq X) ≫
              (eqToHom (rightEq X).symm ≫ s ≫ eqToHom (rightEq Y)) := by
                simp [Category.assoc]
        _ = eqToHom (rightEq X) ≫ SurfaceNF.cast ha hb s := by
              rw [htransport]
        _ = eqToHom (rightEq X) ≫ f := by rw [hcast])
    (pentagon := pentagon_transport)
    (triangle := triangle_transport)

theorem swap_eq_wiring (a b : ℕ) :
    SurfaceNF.swap a b =
      SurfaceNF.wiring
        (finAddFlip.symm : Fin (b + a) ≃ Fin (a + b)) :=
  rfl

/-- The block-swap normal form is an isomorphism. -/
def surfaceBraiding (X Y : SurfaceNFObj) : X ⊗ Y ≅ Y ⊗ X where
  hom := SurfaceNF.swap X.arity Y.arity
  inv := SurfaceNF.swap Y.arity X.arity
  hom_inv_id := by
    rw [swap_eq_wiring, swap_eq_wiring]
    change
      SurfaceNF.comp (SurfaceNF.wiring _) (SurfaceNF.wiring _) =
        SurfaceNF.identity _
    rw [SurfaceNF.comp_wiring]
    let e : Fin (Y.arity + X.arity) ≃ Fin (X.arity + Y.arity) :=
      finAddFlip.symm
    let f : Fin (X.arity + Y.arity) ≃ Fin (Y.arity + X.arity) :=
      finAddFlip.symm
    change SurfaceNF.wiring (f.trans e) =
      SurfaceNF.identity (X ⊗ Y).arity
    rw [show f.trans e = Equiv.refl _ by
      ext i
      simp [e, f, finAddFlip]]
    exact SurfaceNF.wiring_refl _
  inv_hom_id := by
    rw [swap_eq_wiring, swap_eq_wiring]
    change
      SurfaceNF.comp (SurfaceNF.wiring _) (SurfaceNF.wiring _) =
        SurfaceNF.identity _
    rw [SurfaceNF.comp_wiring]
    let e : Fin (X.arity + Y.arity) ≃ Fin (Y.arity + X.arity) :=
      finAddFlip.symm
    let f : Fin (Y.arity + X.arity) ≃ Fin (X.arity + Y.arity) :=
      finAddFlip.symm
    change SurfaceNF.wiring (f.trans e) =
      SurfaceNF.identity (Y ⊗ X).arity
    rw [show f.trans e = Equiv.refl _ by
      ext i
      simp [e, f, finAddFlip]]
    exact SurfaceNF.wiring_refl _

theorem swap_naturality
    {X X' Y Y' : SurfaceNFObj}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ (surfaceBraiding X' Y').hom =
      (surfaceBraiding X Y).hom ≫ (g ⊗ₘ f) := by
  change
    SurfaceNF.comp (SurfaceNF.tensor f g)
        (SurfaceNF.swap X'.arity Y'.arity) =
      SurfaceNF.comp (SurfaceNF.swap X.arity Y.arity)
        (SurfaceNF.tensor g f)
  rw [swap_eq_wiring, swap_eq_wiring]
  change
    SurfaceNF.comp (SurfaceNF.tensor f g) (SurfaceNF.wiring _) =
      SurfaceNF.comp (SurfaceNF.wiring _) (SurfaceNF.tensor g f)
  let eOut : Fin (Y'.arity + X'.arity) ≃
      Fin (X'.arity + Y'.arity) := finAddFlip.symm
  let eIn : Fin (Y.arity + X.arity) ≃
      Fin (X.arity + Y.arity) := finAddFlip.symm
  calc
    SurfaceNF.comp (SurfaceNF.tensor f g) (SurfaceNF.wiring _) =
        SurfaceNF.reindexOut finAddFlip.symm
          (SurfaceNF.tensor f g) := by
            simpa [eOut] using
              SurfaceNF.comp_wiring_right
                (SurfaceNF.tensor f g) eOut
    _ = SurfaceNF.reindexIn finAddFlip
          (SurfaceNF.tensor g f) :=
      SurfaceNF.reindexOut_tensor_flip f g
    _ = SurfaceNF.comp (SurfaceNF.wiring _)
          (SurfaceNF.tensor g f) := by
            simpa [eIn] using
              (SurfaceNF.comp_wiring_left eIn
                (SurfaceNF.tensor g f)).symm

theorem swap_involutive (X Y : SurfaceNFObj) :
    (surfaceBraiding X Y).hom ≫ (surfaceBraiding Y X).hom =
      𝟙 (X ⊗ Y) :=
  (surfaceBraiding X Y).hom_inv_id

private theorem associator_hom_eq_wiring (X Y Z : SurfaceNFObj) :
    (α_ X Y Z).hom =
      SurfaceNF.wiring
        (finCongr (Nat.add_assoc X.arity Y.arity Z.arity)).symm := by
  change eqToHom (assocEq X Y Z) = _
  convert SurfaceNF.eqToHom_eq_wiring
    (Nat.add_assoc X.arity Y.arity Z.arity)

private theorem associator_inv_eq_wiring (X Y Z : SurfaceNFObj) :
    (α_ X Y Z).inv =
      SurfaceNF.wiring
        (finCongr (Nat.add_assoc X.arity Y.arity Z.arity).symm).symm := by
  change eqToHom (assocEq X Y Z).symm = _
  convert SurfaceNF.eqToHom_eq_wiring
    (Nat.add_assoc X.arity Y.arity Z.arity).symm

@[simp]
private theorem finCongr_assoc_symm_first
    {m n p : ℕ} (i : Fin m) :
    (finCongr (Nat.add_assoc m n p)).symm
        (Fin.castAdd (n + p) i) =
      Fin.castAdd p (Fin.castAdd n i) := by
  apply Fin.ext
  rfl

@[simp]
private theorem finCongr_assoc_symm_middle
    {m n p : ℕ} (j : Fin n) :
    (finCongr (Nat.add_assoc m n p)).symm
        (Fin.natAdd m (Fin.castAdd p j)) =
      Fin.castAdd p (Fin.natAdd m j) := by
  apply Fin.ext
  rfl

@[simp]
private theorem finCongr_assoc_symm_last
    {m n p : ℕ} (k : Fin p) :
    (finCongr (Nat.add_assoc m n p)).symm
        (Fin.natAdd m (Fin.natAdd n k)) =
      Fin.natAdd (m + n) k := by
  apply Fin.ext
  simp [Nat.add_assoc]

@[simp]
private theorem finCongr_assoc_inv_symm_first
    {m n p : ℕ} (i : Fin m) :
    (finCongr (Nat.add_assoc m n p).symm).symm
        (Fin.castAdd p (Fin.castAdd n i)) =
      Fin.castAdd (n + p) i := by
  apply Fin.ext
  rfl

@[simp]
private theorem finCongr_assoc_inv_symm_middle
    {m n p : ℕ} (j : Fin n) :
    (finCongr (Nat.add_assoc m n p).symm).symm
        (Fin.castAdd p (Fin.natAdd m j)) =
      Fin.natAdd m (Fin.castAdd p j) := by
  apply Fin.ext
  rfl

@[simp]
private theorem finCongr_assoc_inv_symm_last
    {m n p : ℕ} (k : Fin p) :
    (finCongr (Nat.add_assoc m n p).symm).symm
        (Fin.natAdd (m + n) k) =
      Fin.natAdd m (Fin.natAdd n k) := by
  apply Fin.ext
  simp [Nat.add_assoc]

private theorem hexagonForwardEquiv (x y z : ℕ) :
    (finCongr (Nat.add_assoc y z x)).symm.trans
        (((finAddFlip :
            Fin (x + (y + z)) ≃ Fin ((y + z) + x)).symm).trans
          (finCongr (Nat.add_assoc x y z)).symm) =
      (SurfaceCode.sumRelabel (Equiv.refl (Fin y))
          (finAddFlip :
            Fin (x + z) ≃ Fin (z + x)).symm).trans
        ((finCongr (Nat.add_assoc y x z)).symm.trans
          (SurfaceCode.sumRelabel
            (finAddFlip :
              Fin (x + y) ≃ Fin (y + x)).symm
            (Equiv.refl (Fin z)))) := by
  apply Equiv.ext
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro iy
    simp only [Equiv.trans_apply, finCongr_assoc_symm_first,
      finCongr_assoc_symm_middle, finCongr_assoc_symm_last,
      SurfaceCode.sumRelabel_castAdd, SurfaceCode.sumRelabel_natAdd,
      Equiv.refl_apply, finAddFlip_symm_eq,
      finAddFlip_apply_castAdd, finAddFlip_apply_natAdd]
  · intro izx
    refine Fin.addCases ?_ ?_ izx
    · intro iz
      simp only [Equiv.trans_apply, finCongr_assoc_symm_first,
        finCongr_assoc_symm_middle, finCongr_assoc_symm_last,
        SurfaceCode.sumRelabel_castAdd, SurfaceCode.sumRelabel_natAdd,
        Equiv.refl_apply, finAddFlip_symm_eq,
        finAddFlip_apply_castAdd, finAddFlip_apply_natAdd]
    · intro ix
      simp only [Equiv.trans_apply, finCongr_assoc_symm_first,
        finCongr_assoc_symm_middle, finCongr_assoc_symm_last,
        SurfaceCode.sumRelabel_castAdd, SurfaceCode.sumRelabel_natAdd,
        Equiv.refl_apply, finAddFlip_symm_eq,
        finAddFlip_apply_castAdd, finAddFlip_apply_natAdd]

private theorem hexagonReverseEquiv (x y z : ℕ) :
    (finCongr (Nat.add_assoc z x y).symm).symm.trans
        (((finAddFlip :
            Fin ((x + y) + z) ≃ Fin (z + (x + y))).symm).trans
          (finCongr (Nat.add_assoc x y z).symm).symm) =
      (SurfaceCode.sumRelabel
          (finAddFlip :
            Fin (x + z) ≃ Fin (z + x)).symm
          (Equiv.refl (Fin y))).trans
        ((finCongr (Nat.add_assoc x z y).symm).symm.trans
          (SurfaceCode.sumRelabel (Equiv.refl (Fin x))
            (finAddFlip :
              Fin (y + z) ≃ Fin (z + y)).symm)) := by
  apply Equiv.ext
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro izx
    refine Fin.addCases ?_ ?_ izx
    · intro iz
      simp only [Equiv.trans_apply, finCongr_assoc_inv_symm_first,
        finCongr_assoc_inv_symm_middle, finCongr_assoc_inv_symm_last,
        SurfaceCode.sumRelabel_castAdd, SurfaceCode.sumRelabel_natAdd,
        Equiv.refl_apply, finAddFlip_symm_eq,
        finAddFlip_apply_castAdd, finAddFlip_apply_natAdd]
    · intro ix
      simp only [Equiv.trans_apply, finCongr_assoc_inv_symm_first,
        finCongr_assoc_inv_symm_middle, finCongr_assoc_inv_symm_last,
        SurfaceCode.sumRelabel_castAdd, SurfaceCode.sumRelabel_natAdd,
        Equiv.refl_apply, finAddFlip_symm_eq,
        finAddFlip_apply_castAdd, finAddFlip_apply_natAdd]
  · intro iy
    simp only [Equiv.trans_apply, finCongr_assoc_inv_symm_first,
      finCongr_assoc_inv_symm_middle, finCongr_assoc_inv_symm_last,
      SurfaceCode.sumRelabel_castAdd, SurfaceCode.sumRelabel_natAdd,
      Equiv.refl_apply, finAddFlip_symm_eq,
      finAddFlip_apply_castAdd, finAddFlip_apply_natAdd]

instance braidedCategory : BraidedCategory SurfaceNFObj where
  braiding := surfaceBraiding
  braiding_naturality_left := by
    intro X Y f Z
    exact swap_naturality f (𝟙 Z)
  braiding_naturality_right := by
    intro X Y Z f
    exact swap_naturality (𝟙 X) f
  hexagon_forward := by
    intro X Y Z
    rw [associator_hom_eq_wiring, associator_hom_eq_wiring,
      associator_hom_eq_wiring]
    simp only [← Category.assoc]
    dsimp only [CategoryStruct.comp, CategoryStruct.id,
      MonoidalCategoryStruct.whiskerLeft,
      MonoidalCategoryStruct.whiskerRight, surfaceBraiding, tensorHom]
    rw [swap_eq_wiring, swap_eq_wiring, swap_eq_wiring,
      ← SurfaceNF.wiring_refl Z.arity,
      ← SurfaceNF.wiring_refl Y.arity]
    change
      SurfaceNF.comp
          (SurfaceNF.comp (SurfaceNF.wiring _) (SurfaceNF.wiring _))
          (SurfaceNF.wiring _) =
        SurfaceNF.comp
          (SurfaceNF.comp
            (SurfaceNF.tensor (SurfaceNF.wiring _) (SurfaceNF.wiring _))
            (SurfaceNF.wiring _))
          (SurfaceNF.tensor (SurfaceNF.wiring _) (SurfaceNF.wiring _))
    rw [SurfaceNF.tensor_wiring, SurfaceNF.tensor_wiring,
      SurfaceNF.comp_wiring, SurfaceNF.comp_wiring,
      SurfaceNF.comp_wiring, SurfaceNF.comp_wiring]
    congr 1
    exact hexagonForwardEquiv X.arity Y.arity Z.arity
  hexagon_reverse := by
    intro X Y Z
    rw [associator_inv_eq_wiring, associator_inv_eq_wiring,
      associator_inv_eq_wiring]
    simp only [← Category.assoc]
    dsimp only [CategoryStruct.comp, CategoryStruct.id,
      MonoidalCategoryStruct.whiskerLeft,
      MonoidalCategoryStruct.whiskerRight, surfaceBraiding, tensorHom]
    rw [swap_eq_wiring, swap_eq_wiring, swap_eq_wiring,
      ← SurfaceNF.wiring_refl X.arity,
      ← SurfaceNF.wiring_refl Y.arity]
    change
      SurfaceNF.comp
          (SurfaceNF.comp (SurfaceNF.wiring _) (SurfaceNF.wiring _))
          (SurfaceNF.wiring _) =
        SurfaceNF.comp
          (SurfaceNF.comp
            (SurfaceNF.tensor (SurfaceNF.wiring _) (SurfaceNF.wiring _))
            (SurfaceNF.wiring _))
          (SurfaceNF.tensor (SurfaceNF.wiring _) (SurfaceNF.wiring _))
    rw [SurfaceNF.tensor_wiring, SurfaceNF.tensor_wiring,
      SurfaceNF.comp_wiring, SurfaceNF.comp_wiring,
      SurfaceNF.comp_wiring, SurfaceNF.comp_wiring]
    congr 1
    exact hexagonReverseEquiv X.arity Y.arity Z.arity

@[simp]
theorem braiding_hom_eq_swap (X Y : SurfaceNFObj) :
    (β_ X Y).hom = SurfaceNF.swap X.arity Y.arity :=
  rfl

instance symmetricCategory : SymmetricCategory SurfaceNFObj where
  symmetry := swap_involutive

theorem swap_symmetry (X Y : SurfaceNFObj) :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) :=
  SymmetricCategory.symmetry X Y

end SurfaceNFMonoidal

end Cob2NormalForm
