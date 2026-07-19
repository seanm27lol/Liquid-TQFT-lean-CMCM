import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Balanced and ribbon monoidal categories

## Mathlib rigid/braided API audit

* The zigzag identities are
  `ExactPairing.coevaluation_evaluation` and `ExactPairing.evaluation_coevaluation`, stated with
  explicit whiskering, associators, and unitors.  Their normalized monoidal-composition forms are
  `coevaluation_evaluation''` and `evaluation_coevaluation''`; reassociated simp lemmas are generated
  for the two original identities.
* For right mates, `rightAdjointMate_id` and `comp_rightAdjointMate` give identity and reversed
  composition.  The two naturality/absorption results needed below already exist in whiskered form:
  `coevaluation_comp_rightAdjointMate` and `rightAdjointMate_comp_evaluation` (both `[reassoc]`).
* Braiding naturality is available one variable at a time as
  `BraidedCategory.braiding_naturality_left` and `..._right`, jointly in tensor-morphism form as
  `BraidedCategory.braiding_naturality`, and likewise for inverse braidings as
  `braiding_inv_naturality_left`, `..._right`, and `..._naturality`.  Reassociated forms are
  generated for all of these.
* Mathlib's existing `CategoryTheory.Balanced` is the unrelated property that every morphism which
  is both mono and epi is an isomorphism.  Searches found no declarations named
  `BalancedMonoidalCategory` or `RibbonCategory`; those collision-free names are used below.
* Concrete symmetric right-rigid examples are available: `FGModuleCat K` is right rigid (under its
  field hypotheses), and finite-dimensional representation categories inherit symmetric and rigid
  structures.
* The available coherence support is `monoidal`, `monoidal_coherence`, and the category simplifier
  (`simp`/`cat_disch`).  There is no separate braided-coherence tactic in this Mathlib version;
  braided calculations use the named naturality, hexagon, unit-braiding, and symmetry lemmas.

The twist is represented as an object-indexed family of isomorphisms, rather than a natural
isomorphism `𝟭 C ≅ 𝟭 C`.  This makes the unit and tensor axioms literal equalities of isomorphisms,
while naturality remains an explicit, conveniently reusable field.
-/

open CategoryTheory CategoryTheory.MonoidalCategory

universe v u

noncomputable section

namespace CategoryTheory

/-- A balanced monoidal category is a braided monoidal category with a natural twist.

Our composition convention is left-to-right: the tensor twist is first
`θ_X ⊗ θ_Y`, then `β_{X,Y}`, then `β_{Y,X}`.
-/
class BalancedMonoidalCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] where
  /-- The twist automorphism of an object. -/
  twist : ∀ X : C, X ≅ X
  /-- Naturality of the twist. -/
  twist_naturality : ∀ {X Y : C} (f : X ⟶ Y),
    f ≫ (twist Y).hom = (twist X).hom ≫ f := by cat_disch
  /-- The twist of the tensor unit is the identity. -/
  twist_unit : twist (𝟙_ C) = Iso.refl _
  /-- The balancing axiom, in left-to-right composition order. -/
  twist_tensor : ∀ X Y : C,
    twist (X ⊗ Y) = (twist X ⊗ᵢ twist Y) ≪≫ β_ X Y ≪≫ β_ Y X

namespace BalancedMonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [BalancedMonoidalCategory C]

/-- Notation-free accessor for the twist. -/
abbrev θ (X : C) : X ≅ X := twist X

@[reassoc (attr := simp)]
lemma twist_naturality_hom {X Y : C} (f : X ⟶ Y) :
    f ≫ (twist Y).hom = (twist X).hom ≫ f :=
  twist_naturality f

@[reassoc (attr := simp)]
lemma twist_naturality_inv {X Y : C} (f : X ⟶ Y) :
    f ≫ (twist Y).inv = (twist X).inv ≫ f := by
  exact CommSq.w <| .vert_inv <| .mk <| twist_naturality_hom f

/-
The hom direction of the balancing axiom, unfolded.
-/
lemma twist_tensor_hom (X Y : C) :
    (twist (X ⊗ Y)).hom =
      ((twist X).hom ⊗ₘ (twist Y).hom) ≫ (β_ X Y).hom ≫ (β_ Y X).hom := by
  exact congr_arg Iso.hom (twist_tensor X Y)

/-
The inverse direction of the balancing axiom, unfolded.
-/
lemma twist_tensor_inv (X Y : C) :
    (twist (X ⊗ Y)).inv =
      (β_ Y X).inv ≫ (β_ X Y).inv ≫ ((twist X).inv ⊗ₘ (twist Y).inv) := by
  rw [twist_tensor]
  simp only [Iso.trans_inv, tensorIso_inv, Category.assoc]

end BalancedMonoidalCategory

open BalancedMonoidalCategory ExactPairing HasRightDual

/-- A ribbon category is a balanced monoidal category with chosen right duals such that the twist
commutes with right-dualization.  The compatibility is stated on hom morphisms; equality of the
inverse morphisms then follows automatically.
-/
class RibbonCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    extends BalancedMonoidalCategory C, RightRigidCategory C where
  /-- The twist commutes with the right-adjoint mate construction. -/
  twist_rightDual : ∀ X : C,
    (BalancedMonoidalCategory.twist (Xᘁ)).hom =
      (BalancedMonoidalCategory.twist X).homᘁ

/-- Every symmetric right-rigid monoidal category is ribbon, with identity twist. -/
instance symmetricRibbonCategory (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] [RightRigidCategory C] : RibbonCategory C where
  twist X := Iso.refl X
  twist_naturality f := by simp
  twist_unit := rfl
  twist_tensor X Y := by
    ext
    simp
  twist_rightDual X := by simp

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RibbonCategory C]

/-- The quantum trace of `f : X ⟶ X` is the composite
`𝟙_ C --η--> X ⊗ Xᘁ --((f ≫ θ_X) ⊗ 𝟙)--> X ⊗ Xᘁ
 --β--> Xᘁ ⊗ X --ε--> 𝟙_ C`.
-/
def qTrace {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X Xᘁ ≫
    ((f ≫ (BalancedMonoidalCategory.twist X).hom) ⊗ₘ 𝟙 (Xᘁ)) ≫
    (β_ X Xᘁ).hom ≫ ε_ X Xᘁ

/-- The quantum dimension of an object is the quantum trace of its identity. -/
def qDim (X : C) : 𝟙_ C ⟶ 𝟙_ C := qTrace (𝟙 X)

@[simp]
lemma qDim_def (X : C) : qDim X = qTrace (𝟙 X) := rfl

lemma qTrace_eq {X : C} (f : X ⟶ X) :
    qTrace f = η_ X Xᘁ ≫
      ((f ≫ (BalancedMonoidalCategory.twist X).hom) ⊗ₘ 𝟙 (Xᘁ)) ≫
      (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := rfl

omit [RibbonCategory C] in
/-- Closing any exact pairing whose first object is the tensor unit gives the identity scalar. -/
lemma coevaluation_braiding_evaluation_unit (Y : C) [ExactPairing (𝟙_ C) Y] :
    η_ (𝟙_ C) Y ≫ (β_ (𝟙_ C) Y).hom ≫ ε_ (𝟙_ C) Y = 𝟙 (𝟙_ C) := by
  rw [braiding_tensorUnit_left, ← whiskerRight_iff]
  calc
    (η_ (𝟙_ C) Y ≫ ((λ_ Y).hom ≫ (ρ_ Y).inv) ≫ ε_ (𝟙_ C) Y) ▷ (𝟙_ C) =
      η_ (𝟙_ C) Y ▷ (𝟙_ C) ≫ (α_ (𝟙_ C) Y (𝟙_ C)).hom ≫
        (𝟙_ C) ◁ ε_ (𝟙_ C) Y := by monoidal
    _ = (λ_ (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).inv := by
      rw [ExactPairing.evaluation_coevaluation]
    _ = (𝟙 (𝟙_ C)) ▷ (𝟙_ C) := by monoidal

@[simp]
lemma qTrace_unit : qTrace (𝟙 (𝟙_ C)) = 𝟙 (𝟙_ C) := by
  simp only [qTrace, BalancedMonoidalCategory.twist_unit, Iso.refl_hom,
    Category.comp_id, id_tensorHom]
  let i : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
  simpa only [MonoidalCategory.whiskerLeft_id, Category.comp_id, Category.id_comp] using
    (@coevaluation_braiding_evaluation_unit C _ _ _
      (@rightDual C _ _ (𝟙_ C) i) i.exact)

/-
A morphism can be absorbed into a coevaluation on either leg, with the morphism on the
right leg replaced by its right mate.  This tensor-morphism orientation matches `qTrace`.
-/
lemma coevaluation_absorption {X Y : C} (f : X ⟶ Y) :
    η_ X Xᘁ ≫ (f ⊗ₘ 𝟙 (Xᘁ)) = η_ Y Yᘁ ≫ (𝟙 Y ⊗ₘ fᘁ) := by
  simpa using (coevaluation_comp_rightAdjointMate f).symm

/-
Dual evaluation absorption: a morphism can be moved from the primal leg to the dual leg as
its right mate.
-/
lemma evaluation_absorption {X Y : C} (f : X ⟶ Y) :
    (fᘁ ⊗ₘ 𝟙 X) ≫ ε_ X Xᘁ = (𝟙 (Yᘁ) ⊗ₘ f) ≫ ε_ Y Yᘁ := by
  simpa using rightAdjointMate_comp_evaluation f

/-
The twist slides past every morphism.
-/
lemma twist_slide {X Y : C} (f : X ⟶ Y) :
    f ≫ (BalancedMonoidalCategory.twist Y).hom =
      (BalancedMonoidalCategory.twist X).hom ≫ f :=
  BalancedMonoidalCategory.twist_naturality_hom f

/-
Coevaluation absorption, reassociated with a further tensor map.
-/
lemma coevaluation_absorption_tensor_assoc {X Y Z : C} (f : X ⟶ Y) (h : Y ⟶ Z)
    (k : Z ⊗ Xᘁ ⟶ 𝟙_ C) :
    η_ X Xᘁ ≫ ((f ≫ h) ⊗ₘ 𝟙 (Xᘁ)) ≫ k =
      η_ Y Yᘁ ≫ (𝟙 Y ⊗ₘ fᘁ) ≫ (h ⊗ₘ 𝟙 (Xᘁ)) ≫ k := by
  simp +decide [← Category.assoc]
  grind +suggestions

/-
The middle, braided part of trace rotation.
-/
@[reassoc]
lemma absorption_braiding {X Y : C} (f : X ⟶ Y) (h : Y ⟶ X) :
    (𝟙 Y ⊗ₘ fᘁ) ≫ (h ⊗ₘ 𝟙 (Xᘁ)) ≫ (β_ X Xᘁ).hom =
      (β_ Y Yᘁ).hom ≫ (fᘁ ⊗ₘ h) := by
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.comp_id, Category.id_comp,
    BraidedCategory.braiding_naturality]

/-
Evaluation absorption after both tensor legs have acquired morphisms.
-/
@[reassoc]
lemma tensor_evaluation_absorption {X Y : C} (f : X ⟶ Y) (h : Y ⟶ X) :
    (fᘁ ⊗ₘ h) ≫ ε_ X Xᘁ =
      (𝟙 (Yᘁ) ⊗ₘ (h ≫ f)) ≫ ε_ Y Yᘁ := by
  rw [MonoidalCategory.tensorHom_def']
  grind +suggestions

/-- Sliding a morphism all the way around the closed quantum-trace diagram. -/
lemma qTrace_rotate {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    qTrace (f ≫ g) =
      η_ Y Yᘁ ≫ (β_ Y Yᘁ).hom ≫
        (𝟙 (Yᘁ) ⊗ₘ (g ≫ (BalancedMonoidalCategory.twist X).hom ≫ f)) ≫ ε_ Y Yᘁ := by
  unfold qTrace
  simp only [Category.assoc]
  let h : Y ⟶ X := g ≫ (BalancedMonoidalCategory.twist X).hom
  change η_ X Xᘁ ≫ ((f ≫ h) ⊗ₘ 𝟙 (Xᘁ)) ≫
      (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = _
  rw [coevaluation_absorption_tensor_assoc f h]
  rw [absorption_braiding_assoc f h]
  rw [tensor_evaluation_absorption f h]
  simp only [h, Category.assoc]

/-
Cyclicity of the quantum trace.
-/
lemma qTrace_cyclic {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    qTrace (f ≫ g) = qTrace (g ≫ f) := by
  rw [qTrace_rotate f g]
  unfold qTrace
  simp only [Category.assoc]
  rw [BraidedCategory.braiding_naturality_assoc]
  rw [← twist_slide f]

/-- The S-pairing is the quantum trace of the double braiding on `X ⊗ Y`.
Nondegeneracy of this pairing is the modularity condition; no such condition is imposed here.
-/
def sPairing (X Y : C) : 𝟙_ C ⟶ 𝟙_ C :=
  qTrace ((β_ X Y).hom ≫ (β_ Y X).hom)

omit [BraidedCategory C] [RibbonCategory C] in
/-- The dual-side triangle for the standard nested cup and cap. -/
lemma tensorExactPairing_dual_triangle {X X' Y Y' : C}
    (pX : ExactPairing X X') (pY : ExactPairing Y Y') :
    letI : ExactPairing X X' := pX
    letI : ExactPairing Y Y' := pY
    (Y' ⊗ X') ◁ (η_ X X' ⊗≫ (X ◁ η_ Y Y') ▷ X' ⊗≫ 𝟙 _) ≫
      (α_ (Y' ⊗ X') (X ⊗ Y) (Y' ⊗ X')).inv ≫
      (𝟙 _ ⊗≫ (Y' ◁ ε_ X X') ▷ Y ⊗≫ ε_ Y Y') ▷ (Y' ⊗ X') =
        (ρ_ (Y' ⊗ X')).hom ≫ (λ_ (Y' ⊗ X')).inv := by
  rw [Iso.eq_comp_inv, ← Iso.inv_comp_eq_id]
  calc
    _ = 𝟙 (Y' ⊗ X') ⊗≫ (Y' ⊗ X') ◁ η_ X X' ⊗≫
        (Y' ⊗ X') ◁ ((X ◁ η_ Y Y') ▷ X') ⊗≫
        ((Y' ◁ ε_ X X') ▷ Y) ▷ (Y' ⊗ X') ⊗≫
        ε_ Y Y' ▷ (Y' ⊗ X') ⊗≫ 𝟙 (Y' ⊗ X') := by
      monoidal
    _ = 𝟙 (Y' ⊗ X') ⊗≫ (Y' ⊗ X') ◁ η_ X X' ⊗≫
        (Y' ◁ (((X' ⊗ X) ◁ η_ Y Y') ≫
          ε_ X X' ▷ (Y ⊗ Y'))) ▷ X' ⊗≫
        ε_ Y Y' ▷ (Y' ⊗ X') ⊗≫ 𝟙 (Y' ⊗ X') := by
      monoidal
    _ = 𝟙 (Y' ⊗ X') ⊗≫ (Y' ⊗ X') ◁ η_ X X' ⊗≫
        (Y' ◁ ((ε_ X X' ▷ (𝟙_ C)) ≫
          (𝟙_ C) ◁ η_ Y Y')) ▷ X' ⊗≫
        ε_ Y Y' ▷ (Y' ⊗ X') ⊗≫ 𝟙 (Y' ⊗ X') := by
      rw [whisker_exchange]
    _ = 𝟙 (Y' ⊗ X') ⊗≫
        Y' ◁ (X' ◁ η_ X X' ⊗≫ ε_ X X' ▷ X') ⊗≫
        (Y' ◁ η_ Y Y' ⊗≫ ε_ Y Y' ▷ Y') ▷ X' ⊗≫
        𝟙 (Y' ⊗ X') := by
      monoidal
    _ = _ := by
      rw [ExactPairing.coevaluation_evaluation'',
        ExactPairing.coevaluation_evaluation'']
      monoidal

omit [BraidedCategory C] [RibbonCategory C] in
/-- The primal-side triangle for the standard nested cup and cap. -/
lemma tensorExactPairing_primal_triangle {X X' Y Y' : C}
    (pX : ExactPairing X X') (pY : ExactPairing Y Y') :
    letI : ExactPairing X X' := pX
    letI : ExactPairing Y Y' := pY
    (η_ X X' ⊗≫ (X ◁ η_ Y Y') ▷ X' ⊗≫ 𝟙 _) ▷ (X ⊗ Y) ≫
      (α_ (X ⊗ Y) (Y' ⊗ X') (X ⊗ Y)).hom ≫
      (X ⊗ Y) ◁ (𝟙 _ ⊗≫ (Y' ◁ ε_ X X') ▷ Y ⊗≫ ε_ Y Y') =
        (λ_ (X ⊗ Y)).hom ≫ (ρ_ (X ⊗ Y)).inv := by
  rw [Iso.eq_comp_inv, ← Iso.inv_comp_eq_id]
  calc
    _ = 𝟙 (X ⊗ Y) ⊗≫ η_ X X' ▷ (X ⊗ Y) ⊗≫
        ((X ◁ η_ Y Y') ▷ X') ▷ (X ⊗ Y) ⊗≫
        (X ⊗ Y) ◁ ((Y' ◁ ε_ X X') ▷ Y) ⊗≫
        (X ⊗ Y) ◁ ε_ Y Y' ⊗≫ 𝟙 (X ⊗ Y) := by
      monoidal
    _ = 𝟙 (X ⊗ Y) ⊗≫ η_ X X' ▷ (X ⊗ Y) ⊗≫
        (X ◁ ((η_ Y Y' ▷ (X' ⊗ X)) ≫
          (Y ⊗ Y') ◁ ε_ X X')) ▷ Y ⊗≫
        (X ⊗ Y) ◁ ε_ Y Y' ⊗≫ 𝟙 (X ⊗ Y) := by
      monoidal
    _ = 𝟙 (X ⊗ Y) ⊗≫ η_ X X' ▷ (X ⊗ Y) ⊗≫
        (X ◁ (((𝟙_ C) ◁ ε_ X X') ≫
          η_ Y Y' ▷ (𝟙_ C))) ▷ Y ⊗≫
        (X ⊗ Y) ◁ ε_ Y Y' ⊗≫ 𝟙 (X ⊗ Y) := by
      rw [← whisker_exchange]
    _ = 𝟙 (X ⊗ Y) ⊗≫
        (η_ X X' ▷ X ⊗≫ X ◁ ε_ X X') ▷ Y ⊗≫
        X ◁ (η_ Y Y' ▷ Y ⊗≫ Y ◁ ε_ Y Y') ⊗≫
        𝟙 (X ⊗ Y) := by
      monoidal
    _ = _ := by
      rw [ExactPairing.evaluation_coevaluation'',
        ExactPairing.evaluation_coevaluation'']
      monoidal

/-- The standard nested-cup/nested-cap pairing of a tensor product with the
reverse tensor product of two chosen dual objects. -/
def tensorExactPairing {X X' Y Y' : C}
    (pX : ExactPairing X X') (pY : ExactPairing Y Y') :
    ExactPairing (X ⊗ Y) (Y' ⊗ X') := by
  letI : ExactPairing X X' := pX
  letI : ExactPairing Y Y' := pY
  refine
    { coevaluation' :=
        η_ X X' ⊗≫ (X ◁ η_ Y Y') ▷ X' ⊗≫ 𝟙 _
      evaluation' :=
        𝟙 _ ⊗≫ (Y' ◁ ε_ X X') ▷ Y ⊗≫ ε_ Y Y'
      coevaluation_evaluation' := ?_
      evaluation_coevaluation' := ?_ }
  · exact tensorExactPairing_dual_triangle pX pY
  · exact tensorExactPairing_primal_triangle pX pY

/-- Quantum trace computed using an explicitly supplied exact pairing. -/
def qTraceWithPairing {X D : C} (p : ExactPairing X D) (f : X ⟶ X) :
    𝟙_ C ⟶ 𝟙_ C :=
  letI : ExactPairing X D := p
  η_ X D ≫ ((f ≫ (BalancedMonoidalCategory.twist X).hom) ⊗ₘ 𝟙 D) ≫
    (β_ X D).hom ≫ ε_ X D

omit [BraidedCategory C] [RibbonCategory C] in
/-
The canonical comparison of two right duals transports coevaluation in the expected way.
-/
lemma rightDualIso_coevaluation {X D₁ D₂ : C}
    (p₁ : ExactPairing X D₁) (p₂ : ExactPairing X D₂) :
    let i := rightDualIso p₁ p₂
    @ExactPairing.coevaluation C _ _ X D₁ p₁ ≫ (𝟙 X ⊗ₘ i.hom) =
      @ExactPairing.coevaluation C _ _ X D₂ p₂ := by
  simp +decide [ rightDualIso ];
    have := @coevaluation_comp_rightAdjointMate C _ _ X X { rightDual := D₂, exact := p₂ } { rightDual := D₁, exact := p₁ } ( 𝟙 X ) ; simp_all +decide [ Category.comp_id ] ;

omit [BraidedCategory C] [RibbonCategory C] in
/-
The canonical comparison of two right duals transports evaluation in the expected way.
-/
lemma rightDualIso_evaluation {X D₁ D₂ : C}
    (p₁ : ExactPairing X D₁) (p₂ : ExactPairing X D₂) :
    let i := rightDualIso p₁ p₂
    (i.hom ⊗ₘ 𝟙 X) ≫ @ExactPairing.evaluation C _ _ X D₂ p₂ =
      @ExactPairing.evaluation C _ _ X D₁ p₁ := by
  have := @rightAdjointMate_comp_evaluation C _ _ X X { rightDual := D₂, exact := p₂ } { rightDual := D₁, exact := p₁ } ( 𝟙 X ) ; aesop;

/-
The closed quantum trace is independent of the chosen exact right pairing.
-/
lemma qTraceWithPairing_eq {X D₁ D₂ : C}
    (p₁ : ExactPairing X D₁) (p₂ : ExactPairing X D₂) (f : X ⟶ X) :
    qTraceWithPairing p₁ f = qTraceWithPairing p₂ f := by
  unfold qTraceWithPairing;
  rename_i h;
  revert h;
  intro h
  set i := rightDualIso p₁ p₂
  have h_coevaluation : @ExactPairing.coevaluation C _ _ X D₁ p₁ ≫ (𝟙 X ⊗ₘ i.hom) = @ExactPairing.coevaluation C _ _ X D₂ p₂ := by
    have := @coevaluation_comp_rightAdjointMate C _ _ X X { rightDual := D₂, exact := p₂ } { rightDual := D₁, exact := p₁ } ( 𝟙 X ) ; aesop;
  have h_evaluation : (i.hom ⊗ₘ 𝟙 X) ≫ @ExactPairing.evaluation C _ _ X D₂ p₂ = @ExactPairing.evaluation C _ _ X D₁ p₁ := by
    have := @rightAdjointMate_comp_evaluation C _ _ X X { rightDual := D₂, exact := p₂ } { rightDual := D₁, exact := p₁ } ( 𝟙 X ) ; aesop;
  simp +decide [ ← h_coevaluation, ← h_evaluation ];
  simp +decide [ ← Category.assoc, ← MonoidalCategory.whisker_exchange ];
  simp +decide [ Category.assoc, ← MonoidalCategory.whisker_exchange ]

/-- The original trace is definitionally its explicitly-paired version at the chosen right dual. -/
lemma qTrace_eq_qTraceWithPairing {X : C} (f : X ⟶ X) :
    qTrace f = qTraceWithPairing (inferInstance : ExactPairing X Xᘁ) f := rfl

omit [RibbonCategory C] in
/-- The balancing double braid turns the left evaluation of a tensor product into the two
individual left evaluations. -/
lemma braidedCap_tensor {X X' Y Y' : C}
    (pX : ExactPairing X X') (pY : ExactPairing Y Y') :
    letI : ExactPairing X X' := pX
    letI : ExactPairing Y Y' := pY
    (((β_ X Y).hom ≫ (β_ Y X).hom) ⊗ₘ 𝟙 (Y' ⊗ X')) ≫
        (β_ (X ⊗ Y) (Y' ⊗ X')).hom ≫
        (𝟙 _ ⊗≫ (Y' ◁ ε_ X X') ▷ Y ⊗≫ ε_ Y Y') =
      𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
        (X ◁ ((β_ Y Y').hom ≫ ε_ Y Y')) ▷ X' ⊗≫
        ((β_ X X').hom ≫ ε_ X X') := by
  letI : ExactPairing X X' := pX
  letI : ExactPairing Y Y' := pY
  calc
    _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
        (β_ X Y).hom ▷ (Y' ⊗ X') ⊗≫
        ((β_ Y X).hom ▷ Y' ⊗≫
          X ◁ (β_ Y Y').hom ⊗≫
          (β_ X Y').hom ▷ Y) ▷ X' ⊗≫
        (Y' ⊗ X) ◁ (β_ Y X').hom ⊗≫
        Y' ◁ (β_ X X').hom ▷ Y ⊗≫
        Y' ◁ ε_ X X' ▷ Y ⊗≫ ε_ Y Y' := by
      simp only [BraidedCategory.braiding_tensor_left_hom,
        BraidedCategory.braiding_tensor_right_hom]
      monoidal
    _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
        (β_ X Y).hom ▷ (Y' ⊗ X') ⊗≫
        (𝟙 _ ⊗≫
          (Y ◁ (β_ X Y').hom ⊗≫
            (β_ Y Y').hom ▷ X ⊗≫
            Y' ◁ (β_ Y X).hom) ⊗≫ 𝟙 _) ▷ X' ⊗≫
        (Y' ⊗ X) ◁ (β_ Y X').hom ⊗≫
        Y' ◁ (β_ X X').hom ▷ Y ⊗≫
        Y' ◁ ε_ X X' ▷ Y ⊗≫ ε_ Y Y' := by
      rw [BraidedCategory.yang_baxter']
    _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
        ((β_ X Y).hom ▷ Y' ⊗≫
          Y ◁ (β_ X Y').hom ⊗≫
          (β_ Y Y').hom ▷ X) ▷ X' ⊗≫
        Y' ◁ (β_ Y X).hom ▷ X' ⊗≫
        (Y' ⊗ X) ◁ (β_ Y X').hom ⊗≫
        Y' ◁ (β_ X X').hom ▷ Y ⊗≫
        Y' ◁ ε_ X X' ▷ Y ⊗≫ ε_ Y Y' := by
      monoidal
    _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
        (𝟙 _ ⊗≫
          (X ◁ (β_ Y Y').hom ⊗≫
            (β_ X Y').hom ▷ Y ⊗≫
            Y' ◁ (β_ X Y).hom) ⊗≫ 𝟙 _) ▷ X' ⊗≫
        Y' ◁ (β_ Y X).hom ▷ X' ⊗≫
        (Y' ⊗ X) ◁ (β_ Y X').hom ⊗≫
        Y' ◁ (β_ X X').hom ▷ Y ⊗≫
        Y' ◁ ε_ X X' ▷ Y ⊗≫ ε_ Y Y' := by
      rw [BraidedCategory.yang_baxter']
    _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
        X ◁ (β_ Y Y').hom ▷ X' ⊗≫
        (β_ X Y').hom ▷ (Y ⊗ X') ⊗≫
        Y' ◁ (β_ X Y).hom ▷ X' ⊗≫
        Y' ◁ ((β_ Y X).hom ▷ X' ⊗≫
          X ◁ (β_ Y X').hom ⊗≫
          (β_ X X').hom ▷ Y) ⊗≫
        Y' ◁ ε_ X X' ▷ Y ⊗≫ ε_ Y Y' := by
      monoidal
    _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
        X ◁ (β_ Y Y').hom ▷ X' ⊗≫
        (β_ X Y').hom ▷ (Y ⊗ X') ⊗≫
        Y' ◁ (β_ X Y).hom ▷ X' ⊗≫
        Y' ◁ (𝟙 _ ⊗≫
          (Y ◁ (β_ X X').hom ⊗≫
            (β_ Y X').hom ▷ X ⊗≫
            X' ◁ (β_ Y X).hom) ⊗≫ 𝟙 _) ⊗≫
        Y' ◁ ε_ X X' ▷ Y ⊗≫ ε_ Y Y' := by
      rw [BraidedCategory.yang_baxter']
    _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
        (X ◁ (β_ Y Y').hom) ▷ X' ⊗≫
        (β_ X (Y' ⊗ Y)).hom ▷ X' ⊗≫
        (Y' ⊗ Y) ◁ (β_ X X').hom ⊗≫
        Y' ◁ (β_ Y (X' ⊗ X)).hom ⊗≫
        Y' ◁ (ε_ X X' ▷ Y) ⊗≫
        ε_ Y Y' := by
      simp only [BraidedCategory.braiding_tensor_right_hom]
      monoidal
    _ = _ := by
      calc
        _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
            (X ◁ (β_ Y Y').hom) ▷ X' ⊗≫
            (β_ X (Y' ⊗ Y)).hom ▷ X' ⊗≫
            (Y' ⊗ Y) ◁ (β_ X X').hom ⊗≫
            Y' ◁ ((β_ Y (X' ⊗ X)).hom ≫ ε_ X X' ▷ Y) ⊗≫
            ε_ Y Y' := by
          monoidal
        _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
            (X ◁ (β_ Y Y').hom) ▷ X' ⊗≫
            (β_ X (Y' ⊗ Y)).hom ▷ X' ⊗≫
            (Y' ⊗ Y) ◁ (β_ X X').hom ⊗≫
            Y' ◁ (Y ◁ ε_ X X' ≫ (β_ Y (𝟙_ C)).hom) ⊗≫
            ε_ Y Y' := by
          rw [← BraidedCategory.braiding_naturality_right]
        _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
            (X ◁ (β_ Y Y').hom) ▷ X' ⊗≫
            (β_ X (Y' ⊗ Y)).hom ▷ X' ⊗≫
            ((Y' ⊗ Y) ◁ ((β_ X X').hom ≫ ε_ X X') ≫
              ε_ Y Y' ▷ (𝟙_ C)) ⊗≫ 𝟙 (𝟙_ C) := by
          rw [braiding_tensorUnit_right]
          monoidal
        _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
            (X ◁ (β_ Y Y').hom) ▷ X' ⊗≫
            (β_ X (Y' ⊗ Y)).hom ▷ X' ⊗≫
            (ε_ Y Y' ▷ (X ⊗ X') ≫
              (𝟙_ C) ◁ ((β_ X X').hom ≫ ε_ X X')) ⊗≫ 𝟙 (𝟙_ C) := by
          rw [whisker_exchange]
        _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
            (X ◁ (β_ Y Y').hom) ▷ X' ⊗≫
            ((β_ X (Y' ⊗ Y)).hom ≫ ε_ Y Y' ▷ X) ▷ X' ⊗≫
            (β_ X X').hom ⊗≫ ε_ X X' := by
          monoidal
        _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
            (X ◁ (β_ Y Y').hom) ▷ X' ⊗≫
            (X ◁ ε_ Y Y' ≫ (β_ X (𝟙_ C)).hom) ▷ X' ⊗≫
            (β_ X X').hom ⊗≫ ε_ X X' := by
          rw [← BraidedCategory.braiding_naturality_right]
        _ = _ := by
          rw [braiding_tensorUnit_right]
          monoidal

/-- The quantum evaluation of a tensor product factors through the two quantum evaluations. -/
lemma qCap_tensor {X X' Y Y' : C}
    (pX : ExactPairing X X') (pY : ExactPairing Y Y') :
    letI : ExactPairing X X' := pX
    letI : ExactPairing Y Y' := pY
    (((BalancedMonoidalCategory.twist (X ⊗ Y)).hom ⊗ₘ 𝟙 (Y' ⊗ X')) ≫
        (β_ (X ⊗ Y) (Y' ⊗ X')).hom ≫
        (𝟙 _ ⊗≫ (Y' ◁ ε_ X X') ▷ Y ⊗≫ ε_ Y Y')) =
      𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
        (X ◁ ((((BalancedMonoidalCategory.twist Y).hom ⊗ₘ 𝟙 Y') ≫
          (β_ Y Y').hom ≫ ε_ Y Y'))) ▷ X' ⊗≫
        (((BalancedMonoidalCategory.twist X).hom ⊗ₘ 𝟙 X') ≫
          (β_ X X').hom ≫ ε_ X X') := by
  letI : ExactPairing X X' := pX
  letI : ExactPairing Y Y' := pY
  rw [BalancedMonoidalCategory.twist_tensor_hom]
  have h_tensor :
      ((((BalancedMonoidalCategory.twist X).hom ⊗ₘ
          (BalancedMonoidalCategory.twist Y).hom) ≫
          (β_ X Y).hom ≫ (β_ Y X).hom) ⊗ₘ 𝟙 (Y' ⊗ X')) =
        (((BalancedMonoidalCategory.twist X).hom ⊗ₘ
            (BalancedMonoidalCategory.twist Y).hom) ⊗ₘ 𝟙 (Y' ⊗ X')) ≫
          (((β_ X Y).hom ≫ (β_ Y X).hom) ⊗ₘ 𝟙 (Y' ⊗ X')) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.comp_id]
  calc
    _ = ((((BalancedMonoidalCategory.twist X).hom ⊗ₘ
          (BalancedMonoidalCategory.twist Y).hom) ⊗ₘ 𝟙 (Y' ⊗ X')) ≫
        ((((β_ X Y).hom ≫ (β_ Y X).hom) ⊗ₘ 𝟙 (Y' ⊗ X')) ≫
          (β_ (X ⊗ Y) (Y' ⊗ X')).hom ≫
          (𝟙 _ ⊗≫ (Y' ◁ ε_ X X') ▷ Y ⊗≫ ε_ Y Y'))) := by
      rw [h_tensor]
      simp only [Category.assoc]
    _ = (((BalancedMonoidalCategory.twist X).hom ⊗ₘ
          (BalancedMonoidalCategory.twist Y).hom) ⊗ₘ 𝟙 (Y' ⊗ X')) ≫
        (𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
          (X ◁ ((β_ Y Y').hom ≫ ε_ Y Y')) ▷ X' ⊗≫
          ((β_ X X').hom ≫ ε_ X X')) := by
      rw [braidedCap_tensor pX pY]
    _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
        (((BalancedMonoidalCategory.twist X).hom ▷ (Y ⊗ Y') ≫
          X ◁ ((((BalancedMonoidalCategory.twist Y).hom ⊗ₘ 𝟙 Y') ≫
            (β_ Y Y').hom ≫ ε_ Y Y'))) ▷ X') ⊗≫
        ((β_ X X').hom ≫ ε_ X X') := by
      simp only [MonoidalCategory.tensorHom_def]
      monoidal
    _ = 𝟙 ((X ⊗ Y) ⊗ (Y' ⊗ X')) ⊗≫
        ((X ◁ ((((BalancedMonoidalCategory.twist Y).hom ⊗ₘ 𝟙 Y') ≫
            (β_ Y Y').hom ≫ ε_ Y Y')) ≫
          (BalancedMonoidalCategory.twist X).hom ▷ (𝟙_ C)) ▷ X') ⊗≫
        ((β_ X X').hom ≫ ε_ X X') := by
      rw [whisker_exchange]
    _ = _ := by
      simp only [MonoidalCategory.tensorHom_def]
      monoidal

omit [RibbonCategory C] in
/-- A scalar may be moved from the left side of an object to the right side. -/
lemma scalar_move_right (X : C) (s : 𝟙_ C ⟶ 𝟙_ C) :
    𝟙 ((𝟙_ C) ⊗ X) ⊗≫ s ▷ X ⊗≫ 𝟙 ((𝟙_ C) ⊗ X) =
      𝟙 ((𝟙_ C) ⊗ X) ⊗≫ X ◁ s ⊗≫ 𝟙 ((𝟙_ C) ⊗ X) := by
  calc
    _ = (β_ X (𝟙_ C)).inv ≫ (β_ X (𝟙_ C)).hom ≫ s ▷ X := by
      simp
      monoidal
    _ = (β_ X (𝟙_ C)).inv ≫ X ◁ s ≫ (β_ X (𝟙_ C)).hom := by
      rw [← BraidedCategory.braiding_naturality_right]
    _ = _ := by
      simp only [braiding_tensorUnit_right, braiding_inv_tensorUnit_right]
      monoidal

omit [RibbonCategory C] in
/-- A scalar inserted between two tensor factors can be moved past a map to the tensor unit. -/
lemma middleScalar_comp {X X' : C} (s : 𝟙_ C ⟶ 𝟙_ C)
    (f : X ⊗ X' ⟶ 𝟙_ C) :
    𝟙 (X ⊗ X') ⊗≫ (X ◁ s) ▷ X' ⊗≫ f = f ≫ s := by
  calc
    _ = 𝟙 (X ⊗ X') ⊗≫
        X ◁ (𝟙 ((𝟙_ C) ⊗ X') ⊗≫ s ▷ X' ⊗≫
          𝟙 ((𝟙_ C) ⊗ X')) ⊗≫ f := by
      monoidal
    _ = 𝟙 (X ⊗ X') ⊗≫
        X ◁ (𝟙 ((𝟙_ C) ⊗ X') ⊗≫ X' ◁ s ⊗≫
          𝟙 ((𝟙_ C) ⊗ X')) ⊗≫ f := by
      rw [scalar_move_right]
    _ = 𝟙 (X ⊗ X') ⊗≫
        ((X ⊗ X') ◁ s ≫ f ▷ (𝟙_ C)) ⊗≫ 𝟙 (𝟙_ C) := by
      monoidal
    _ = 𝟙 (X ⊗ X') ⊗≫
        (f ▷ (𝟙_ C) ≫ (𝟙_ C) ◁ s) ⊗≫ 𝟙 (𝟙_ C) := by
      rw [whisker_exchange]
    _ = _ := by
      monoidal

/-- Closing the standard reversed tensor pairing factors into the two individual quantum loops. -/
lemma qTraceWithPairing_tensor_id (X Y : C) :
    qTraceWithPairing
        (tensorExactPairing
          (inferInstance : ExactPairing X Xᘁ)
          (inferInstance : ExactPairing Y Yᘁ))
        (𝟙 (X ⊗ Y)) = qDim X ≫ qDim Y := by
  dsimp [qTraceWithPairing, tensorExactPairing, qDim, qTrace]
  simp only [ExactPairing.coevaluation, ExactPairing.evaluation,
    Category.id_comp, Category.assoc]
  calc
    _ = (η_ X Xᘁ ⊗≫ (X ◁ η_ Y Yᘁ) ▷ Xᘁ ⊗≫
          𝟙 ((X ⊗ Y) ⊗ (Yᘁ ⊗ Xᘁ))) ≫
        (((BalancedMonoidalCategory.twist (X ⊗ Y)).hom ⊗ₘ
            𝟙 (Yᘁ ⊗ Xᘁ)) ≫
          (β_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).hom ≫
          (𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ (X ⊗ Y)) ⊗≫
            (Yᘁ ◁ ε_ X Xᘁ) ▷ Y ⊗≫ ε_ Y Yᘁ)) := by
      rfl
    _ = η_ X Xᘁ ⊗≫ (X ◁ η_ Y Yᘁ) ▷ Xᘁ ⊗≫
        (𝟙 ((X ⊗ Y) ⊗ (Yᘁ ⊗ Xᘁ)) ⊗≫
          (X ◁ ((((BalancedMonoidalCategory.twist Y).hom ⊗ₘ 𝟙 Yᘁ) ≫
            (β_ Y Yᘁ).hom ≫ ε_ Y Yᘁ))) ▷ Xᘁ ⊗≫
          (((BalancedMonoidalCategory.twist X).hom ⊗ₘ 𝟙 Xᘁ) ≫
            (β_ X Xᘁ).hom ≫ ε_ X Xᘁ)) := by
      rw [qCap_tensor
        (inferInstance : ExactPairing X Xᘁ)
        (inferInstance : ExactPairing Y Yᘁ)]
      monoidal
    _ = η_ X Xᘁ ≫
        (𝟙 (X ⊗ Xᘁ) ⊗≫
          (X ◁ (η_ Y Yᘁ ≫
            (((BalancedMonoidalCategory.twist Y).hom ⊗ₘ 𝟙 Yᘁ) ≫
              (β_ Y Yᘁ).hom ≫ ε_ Y Yᘁ))) ▷ Xᘁ ⊗≫
          (((BalancedMonoidalCategory.twist X).hom ⊗ₘ 𝟙 Xᘁ) ≫
            (β_ X Xᘁ).hom ≫ ε_ X Xᘁ)) := by
      monoidal
    _ = _ := by
      rw [middleScalar_comp]
      simp only [Category.assoc]
      rfl

/-
Quantum dimension is multiplicative under tensor product.
-/
lemma qDim_tensor (X Y : C) : qDim (X ⊗ Y) = qDim X ≫ qDim Y := by
  rename_i h;
  have := @qTraceWithPairing_eq C _ _ _ h;
  have := @qTraceWithPairing_tensor_id C _ _ _ h;
  convert this X Y using 1;
  rename_i h';
  convert h' _ _ _ using 1

/-- The S-pairing is symmetric. -/
lemma sPairing_symm (X Y : C) : sPairing X Y = sPairing Y X := by
  unfold sPairing
  exact qTrace_cyclic (β_ X Y).hom (β_ Y X).hom

end CategoryTheory
