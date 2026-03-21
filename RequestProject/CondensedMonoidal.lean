/- SUPERSEDED by MonoidalViaLocalization.lean. Retained for historical reference.
# Monoidal Structure on Condensed Abelian Groups: Investigation and Partial Construction

This file investigates the construction of a `MonoidalCategory` instance on `CondensedAb`
(condensed abelian groups) using existing Mathlib infrastructure (v4.28.0).

## Summary of Findings

### What EXISTS in Mathlib (verified by `inferInstance`):

1. **Presheaf monoidal structure** (`Mathlib.CategoryTheory.Monoidal.FunctorCategory`):
   - `MonoidalCategory (C ⥤ D)` for any monoidal `D` — pointwise tensor product
   - `BraidedCategory (C ⥤ D)` when `D` is braided
   - `SymmetricCategory (C ⥤ D)` when `D` is symmetric
   - All three apply to `CompHausᵒᵖ ⥤ ModuleCat (ULift ℤ)` (presheaves of abelian groups)

2. **Module category monoidal structure** (`Mathlib.Algebra.Category.ModuleCat.Monoidal`):
   - `MonoidalCategory (ModuleCat R)` for any commutative ring `R`
   - This gives the tensor product on `Ab = ModuleCat ℤ`

3. **Sheafification adjunction** (`Mathlib.CategoryTheory.Sites.Sheafification`):
   - `presheafToSheaf J A ⊣ sheafToPresheaf J A` (when `HasWeakSheafify J A`)
   - `HasWeakSheafify (coherentTopology CompHaus) (ModuleCat (ULift ℤ))` ✅
   - `sheafToPresheaf` is full and faithful

4. **Condensed abelian groups** (`Mathlib.Condensed`):
   - `CondensedAb = Condensed (ModuleCat (ULift ℤ))`
   - `Abelian CondensedAb` (from `sheafIsAbelian`)
   - `CondensedMod.IsSolid` (the solid module predicate)

### What is MISSING from Mathlib:

1. **`MonoidalCategory (Sheaf J A)`** — no instance exists
2. **Sheafification as a monoidal functor** — `presheafToSheaf` has no `LaxMonoidal` instance
3. **Day convolution** — not formalized at all
4. **Solid tensor product** — no tensor product on solid modules
5. **The key coherence issue**: defining `tensorObj F G = sheafify(F.val ⊗ G.val)` works,
   but the associator requires relating `sheafify(sheafify(F.val ⊗ G.val).val ⊗ H.val)`
   with `sheafify((F.val ⊗ G.val) ⊗ H.val)`, which needs:
   - The sheafification unit `P ⟶ sheafify(P).val` to be compatible with tensoring
   - Or a proof that `sheafify(P ⊗ Q) ≅ sheafify(sheafify(P).val ⊗ Q)` naturally

### Roadmap to eliminate `condensedAb_monoidal`:

The minimal path requires formalizing ONE of:
  (a) **General sheaf monoidal transfer**: Show that if `A` is monoidal and `J` is a
      Grothendieck topology such that sheafification exists, then `Sheaf J A` inherits
      a monoidal structure. This requires showing `presheafToSheaf J A` is a monoidal
      functor (for colimit-preserving tensor products) or developing the theory of
      monoidal reflective subcategories.
  (b) **Direct construction**: Build the `MonoidalCategory CondensedAb` instance by hand,
      proving the pentagon and triangle identities using the universal property of
      sheafification. The key technical lemma needed is the "double sheafification"
      comparison (Lemma `sheafify_tensor_comparison` below).

## What this file constructs (without axioms):

- `condensedAbTensorObj`: the tensor product of two condensed abelian groups
- `condensedAbTensorHom`: functoriality of the tensor product
- `condensedAbTensorUnit`: the monoidal unit (constant sheaf ℤ)
- `condensedAbWhiskerLeft`, `condensedAbWhiskerRight`: whiskering operations
- `condensedAbLeftUnitor`, `condensedAbRightUnitor`: left/right unitors (with sorry)
- `condensedAbAssociator`: associativity iso (with sorry)
- `condensedAb_monoidalCategoryStruct`: the `MonoidalCategoryStruct` instance (fully defined)
- The full `MonoidalCategory` instance with sorry's identifying exactly what needs proof

Each sorry is annotated with what Mathlib lemma or construction would resolve it.
-/

import Mathlib

open CategoryTheory MonoidalCategory

noncomputable section

set_option synthInstance.maxHeartbeats 800000

/-! ## Part 1: Verification of Existing Mathlib Infrastructure

We verify that the key mathematical ingredients are available in Mathlib.
-/

section MatlibAudit

/-! ### 1a. ModuleCat (ULift ℤ) is a symmetric monoidal category -/

instance : MonoidalCategory (ModuleCat (ULift.{1} ℤ)) := inferInstance
instance : BraidedCategory (ModuleCat (ULift.{1} ℤ)) := inferInstance
instance : SymmetricCategory (ModuleCat (ULift.{1} ℤ)) := inferInstance

/-! ### 1b. Presheaves on CompHaus with values in Ab inherit pointwise monoidal structure

Source: `Mathlib.CategoryTheory.Monoidal.FunctorCategory`
The instances `functorCategoryMonoidal`, `functorCategoryBraided`, `functorCategorySymmetric`
give us the pointwise monoidal structure on any functor category `C ⥤ D` when `D` is monoidal.
-/

/-- Presheaves of abelian groups on CompHaus form a monoidal category via pointwise tensor. -/
instance presheafAb_monoidal : MonoidalCategory (CompHausᵒᵖ ⥤ ModuleCat (ULift.{1} ℤ)) :=
  inferInstance

/-- The pointwise monoidal structure is braided. -/
instance presheafAb_braided : BraidedCategory (CompHausᵒᵖ ⥤ ModuleCat (ULift.{1} ℤ)) :=
  inferInstance

/-- The pointwise monoidal structure is symmetric. -/
instance presheafAb_symmetric : SymmetricCategory (CompHausᵒᵖ ⥤ ModuleCat (ULift.{1} ℤ)) :=
  inferInstance

/-! ### 1c. Sheafification exists for condensed abelian groups

Source: `Mathlib.CategoryTheory.Sites.Sheafification`
The adjunction `presheafToSheaf J A ⊣ sheafToPresheaf J A` gives sheafification.
-/

/-- Sheafification exists for abelian presheaves on CompHaus. -/
instance : HasWeakSheafify (coherentTopology CompHaus.{0}) (ModuleCat.{1} (ULift.{1} ℤ)) :=
  inferInstance

/-- The sheafification adjunction for condensed abelian groups. -/
def condensedAbSheafificationAdj :
    presheafToSheaf (coherentTopology CompHaus.{0}) (ModuleCat (ULift.{1} ℤ)) ⊣
    sheafToPresheaf (coherentTopology CompHaus.{0}) (ModuleCat (ULift.{1} ℤ)) :=
  sheafificationAdjunction _ _

/-! ### 1d. The forgetful functor sheafToPresheaf is fully faithful

This is crucial: it means the counit of the adjunction is an isomorphism,
so `sheafify(S.val) ≅ S` for any sheaf `S` (sheafification is idempotent).
-/

instance : (sheafToPresheaf (coherentTopology CompHaus.{0})
    (ModuleCat (ULift.{1} ℤ))).Full := inferInstance

instance : (sheafToPresheaf (coherentTopology CompHaus.{0})
    (ModuleCat (ULift.{1} ℤ))).Faithful := inferInstance

/-! ### 1e. CondensedAb is abelian -/

instance : Abelian CondensedAb.{0} := inferInstance

/-! ### 1f. No MonoidalCategory instance on CondensedAb exists in Mathlib

The following would fail if uncommented:
```
#check (inferInstance : MonoidalCategory CondensedAb.{0})  -- fails
```
-/

end MatlibAudit

/-! ## Part 2: Construction of the Monoidal Data

We construct the tensor product, unit, and morphism data for `CondensedAb`.
These are the "easy" parts that follow directly from sheafification.
-/

section MonoidalData

/-- Abbreviation for the Grothendieck topology on CompHaus. -/
abbrev J_CompHaus : GrothendieckTopology CompHaus.{0} := coherentTopology CompHaus

/-- Abbreviation for the target abelian category. -/
abbrev Ab_ulift : Type 2 := ModuleCat.{1} (ULift.{1} ℤ)

/-- The sheafification functor for condensed abelian groups. -/
def sheafifyAb : (CompHausᵒᵖ ⥤ Ab_ulift) ⥤ CondensedAb.{0} :=
  presheafToSheaf J_CompHaus Ab_ulift

/-- The forgetful functor from condensed abelian groups to presheaves. -/
def forgetSheafAb : CondensedAb.{0} ⥤ (CompHausᵒᵖ ⥤ Ab_ulift) :=
  sheafToPresheaf J_CompHaus Ab_ulift

/-- **Tensor product of condensed abelian groups.**
Given sheaves `F` and `G`, their tensor product is the sheafification of the
presheaf `S ↦ F(S) ⊗_ℤ G(S)`. -/
def condensedAbTensorObj (F G : CondensedAb.{0}) : CondensedAb.{0} :=
  sheafifyAb.obj (F.val ⊗ G.val)

/-- **Tensor product of morphisms.**
Given morphisms `α : F ⟶ G` and `β : F' ⟶ G'` of condensed abelian groups,
we get `α ⊗ β : F ⊗ F' ⟶ G ⊗ G'` by sheafifying the pointwise tensor. -/
def condensedAbTensorHom {F G F' G' : CondensedAb.{0}}
    (α : F ⟶ G) (β : F' ⟶ G') :
    condensedAbTensorObj F F' ⟶ condensedAbTensorObj G G' :=
  sheafifyAb.map (α.val ⊗ₘ β.val)

/-- **Monoidal unit.**
The monoidal unit is the sheafification of the constant presheaf ℤ. Since the
constant presheaf ℤ is already a sheaf (representable), this is equivalent to
the constant sheaf ℤ. -/
def condensedAbTensorUnit : CondensedAb.{0} :=
  sheafifyAb.obj (𝟙_ (CompHausᵒᵖ ⥤ Ab_ulift))

/-- **Left whiskering**: `F ◁ β` for a condensed abelian group `F` and morphism `β`. -/
def condensedAbWhiskerLeft (F : CondensedAb.{0}) {G H : CondensedAb.{0}} (β : G ⟶ H) :
    condensedAbTensorObj F G ⟶ condensedAbTensorObj F H :=
  sheafifyAb.map (F.val ◁ β.val)

/-- **Right whiskering**: `α ▷ G` for a morphism `α` and condensed abelian group `G`. -/
def condensedAbWhiskerRight {F G : CondensedAb.{0}} (α : F ⟶ G) (H : CondensedAb.{0}) :
    condensedAbTensorObj F H ⟶ condensedAbTensorObj G H :=
  sheafifyAb.map (α.val ▷ H.val)

end MonoidalData

/-! ## Part 3: The Coherence Isomorphisms (The Hard Part)

The associator and unitors require relating sheafifications of different presheaf tensors.
The fundamental difficulty is the "double sheafification" problem:

  `tensorObj (tensorObj F G) H = sheafify(sheafify(F.val ⊗ G.val).val ⊗ H.val)`

but the presheaf associator gives us:

  `(F.val ⊗ G.val) ⊗ H.val ≅ F.val ⊗ (G.val ⊗ H.val)`

To bridge the gap, we need the **sheafification comparison map**:

  `sheafify(sheafify(P).val ⊗ Q) ≅ sheafify(P ⊗ Q)`

This is the key missing piece. Mathematically, this follows because:
1. The unit `η_P : P ⟶ sheafify(P).val` induces `η_P ⊗ id : P ⊗ Q ⟶ sheafify(P).val ⊗ Q`
2. Sheafifying both sides and using idempotency gives the comparison iso.

The proof that this comparison is an isomorphism requires showing that `η_P ⊗ id_Q`
becomes an isomorphism after sheafification. This would follow from:
- The tensor product preserving the class of "local isomorphisms" (morphisms that
  become isos after sheafification), OR
- A general result about monoidal left adjoints / monoidal reflective subcategories.

Neither is currently in Mathlib.
-/

section CoherenceIsos

/-- The sheafification unit gives a natural transformation from a presheaf to its
sheafification's underlying presheaf. -/
def sheafificationUnit :
    𝟭 (CompHausᵒᵖ ⥤ Ab_ulift) ⟶ sheafifyAb ⋙ forgetSheafAb :=
  condensedAbSheafificationAdj.unit

/-- For any sheaf `S`, the counit `sheafify(S.val) ⟶ S` is an isomorphism,
because `sheafToPresheaf` is fully faithful (Lean synthesizes this automatically
from the adjunction + full + faithful instances). -/
instance sheafifyCounitIsIso (S : CondensedAb.{0}) :
    IsIso (condensedAbSheafificationAdj.counit.app S) :=
  inferInstance

/-- `sheafify(S.val) ≅ S` for any sheaf `S` (sheafification is idempotent). -/
def sheafifyIdempotent (S : CondensedAb.{0}) :
    sheafifyAb.obj (forgetSheafAb.obj S) ≅ S :=
  asIso (condensedAbSheafificationAdj.counit.app S)

/-- **The sheafification comparison map (forward direction).**
Given presheaves `P` and `Q`, the unit `η_P : P ⟶ sheafify(P).val` induces:
  `P ⊗ Q ⟶ sheafify(P).val ⊗ Q`
Sheafifying gives:
  `sheafify(P ⊗ Q) ⟶ sheafify(sheafify(P).val ⊗ Q)`

This is a morphism of sheaves, constructed from the functoriality of sheafification. -/
def sheafifyTensorComparisonLeft (P Q : CompHausᵒᵖ ⥤ Ab_ulift) :
    sheafifyAb.obj (P ⊗ Q) ⟶ sheafifyAb.obj ((sheafifyAb.obj P).val ⊗ Q) :=
  sheafifyAb.map (sheafificationUnit.app P ⊗ₘ 𝟙 Q)

/-- The analogous comparison on the right factor. -/
def sheafifyTensorComparisonRight (P Q : CompHausᵒᵖ ⥤ Ab_ulift) :
    sheafifyAb.obj (P ⊗ Q) ⟶ sheafifyAb.obj (P ⊗ (sheafifyAb.obj Q).val) :=
  sheafifyAb.map (𝟙 P ⊗ₘ sheafificationUnit.app Q)

/-- **KEY MISSING LEMMA**: The sheafification comparison is an isomorphism.

This is the critical piece needed for the monoidal structure. It says that
sheafifying a tensor product does not depend on whether the factors are
already sheafified or not.

**Proof strategy** (not yet formalized):
The morphism `η_P ⊗ id_Q : P ⊗ Q → sheafify(P).val ⊗ Q` is a "local isomorphism"
for the coherent topology — meaning it becomes an iso after sheafification.
This follows because:
1. `η_P` is a local isomorphism (by definition of sheafification)
2. Tensoring with a presheaf preserves local isomorphisms for the coherent topology
   on CompHaus (this uses that CompHaus has finite products and the coherent topology
   is subcanonical)

Alternatively, this follows from the general theory of monoidal reflective
subcategories: if the reflector (sheafification) is a monoidal functor,
then the reflective subcategory (sheaves) inherits the monoidal structure.
The reflector being monoidal is equivalent to this comparison being an iso. -/
def sheafifyTensorComparisonLeftIso (P Q : CompHausᵒᵖ ⥤ Ab_ulift) :
    sheafifyAb.obj (P ⊗ Q) ≅ sheafifyAb.obj ((sheafifyAb.obj P).val ⊗ Q) := by
  -- BLOCKED: Requires showing sheafifyTensorComparisonLeft is an iso.
  -- Mathlib gap: No result that tensoring preserves local isomorphisms
  -- for the coherent topology, or that sheafification is monoidal.
  sorry

/-- Right-factor version of the comparison iso. -/
def sheafifyTensorComparisonRightIso (P Q : CompHausᵒᵖ ⥤ Ab_ulift) :
    sheafifyAb.obj (P ⊗ Q) ≅ sheafifyAb.obj (P ⊗ (sheafifyAb.obj Q).val) := by
  sorry

/-- **Associator** for condensed abelian groups.

`(F ⊗ G) ⊗ H ≅ F ⊗ (G ⊗ H)`

Construction:
  `sheafify(sheafify(F.val ⊗ G.val).val ⊗ H.val)`
  `≅ sheafify((F.val ⊗ G.val) ⊗ H.val)`      -- by sheafifyTensorComparisonLeftIso⁻¹
  `≅ sheafify(F.val ⊗ (G.val ⊗ H.val))`       -- by presheaf associator
  `≅ sheafify(F.val ⊗ sheafify(G.val ⊗ H.val).val)`  -- by sheafifyTensorComparisonRightIso -/
def condensedAbAssociator (F G H : CondensedAb.{0}) :
    condensedAbTensorObj (condensedAbTensorObj F G) H ≅
    condensedAbTensorObj F (condensedAbTensorObj G H) :=
  (sheafifyTensorComparisonLeftIso (F.val ⊗ G.val) H.val).symm ≪≫
    sheafifyAb.mapIso (α_ F.val G.val H.val) ≪≫
    sheafifyTensorComparisonRightIso F.val (G.val ⊗ H.val)

/-- **Left unitor**: `𝟙 ⊗ F ≅ F`.

Construction:
  `sheafify(sheafify(𝟙_presheaf).val ⊗ F.val)`
  `≅ sheafify(𝟙_presheaf ⊗ F.val)`  -- by sheafifyTensorComparisonLeftIso⁻¹
  `≅ sheafify(F.val)`                -- by presheaf left unitor
  `≅ F`                              -- by sheafification idempotency -/
def condensedAbLeftUnitor (F : CondensedAb.{0}) :
    condensedAbTensorObj condensedAbTensorUnit F ≅ F :=
  (sheafifyTensorComparisonLeftIso (𝟙_ _) F.val).symm ≪≫
    sheafifyAb.mapIso (λ_ F.val) ≪≫ sheafifyIdempotent F

/-- **Right unitor**: `F ⊗ 𝟙 ≅ F`. -/
def condensedAbRightUnitor (F : CondensedAb.{0}) :
    condensedAbTensorObj F condensedAbTensorUnit ≅ F :=
  (sheafifyTensorComparisonRightIso F.val (𝟙_ _)).symm ≪≫
    sheafifyAb.mapIso (ρ_ F.val) ≪≫ sheafifyIdempotent F

end CoherenceIsos

/-! ## Part 4: The MonoidalCategoryStruct Instance

We assemble the data into a `MonoidalCategoryStruct` instance.
This compiles fully — the sorry's are confined to the coherence isos above.
-/

section MonoidalInstance

/-- The `MonoidalCategoryStruct` on `CondensedAb`, assembling tensor product,
unit, associator, and unitors. All data is defined; sorry's are only in
the coherence isomorphisms (associator and unitors), which depend on
`sheafifyTensorComparisonLeftIso` and `sheafifyTensorComparisonRightIso`. -/
instance condensedAb_monoidalCategoryStruct :
    MonoidalCategoryStruct CondensedAb.{0} where
  tensorObj := condensedAbTensorObj
  tensorHom := condensedAbTensorHom
  whiskerLeft := condensedAbWhiskerLeft
  whiskerRight := condensedAbWhiskerRight
  tensorUnit := condensedAbTensorUnit
  associator := condensedAbAssociator
  leftUnitor := condensedAbLeftUnitor
  rightUnitor := condensedAbRightUnitor

/-
PROBLEM
The full `MonoidalCategory` instance on `CondensedAb`.

**sorry's and what they need:**

1. `tensorHom_def`: `α ⊗ₘ β = (α ▷ _) ≫ (_ ◁ β)` — follows from the same identity
   in the presheaf category + functoriality of sheafification.

2. `id_tensorHom_id`, `tensorHom_comp_tensorHom`, `whiskerLeft_id`, `id_whiskerRight`:
   Basic functoriality — follow from `Functor.map_id` and `Functor.map_comp` applied
   to `sheafifyAb`, combined with the corresponding identities in the presheaf category.

3. `associator_naturality`: naturality of the associator — requires naturality of
   the comparison iso `sheafifyTensorComparisonLeftIso`.

4. `leftUnitor_naturality`, `rightUnitor_naturality`: similar.

5. `pentagon`: the pentagon identity — follows from the presheaf pentagon +
   compatibility of the comparison isos.

6. `triangle`: the triangle identity — similar.

All sorry's here are DOWNSTREAM of the two key sorry's in
`sheafifyTensorComparisonLeftIso` and `sheafifyTensorComparisonRightIso`.
Once those are proved, the remaining sorry's should follow by routine
categorical reasoning (functoriality of sheafification + corresponding
identities in the presheaf category).

PROVIDED SOLUTION
The tensorHom_def follows from tensorHom_def in the presheaf category plus sheafifyAb.map_comp. Specifically: f ⊗ₘ g unfolds to sheafifyAb.map (f.val ⊗ₘ g.val), and f ▷ X₂ ≫ Y₁ ◁ g unfolds to sheafifyAb.map (f.val ▷ X₂.val) ≫ sheafifyAb.map (Y₁.val ◁ g.val) = sheafifyAb.map (f.val ▷ X₂.val ≫ Y₁.val ◁ g.val). Use tensorHom_def in the presheaf category.

id_tensorHom_id: 𝟙 X₁ ⊗ₘ 𝟙 X₂ = sheafifyAb.map (𝟙 ⊗ₘ 𝟙) = sheafifyAb.map 𝟙 = 𝟙. Use id_tensorHom_id in presheaves and Functor.map_id.

tensorHom_comp_tensorHom: use the corresponding identity in presheaves plus Functor.map_comp.

whiskerLeft_id: X ◁ 𝟙 Y = sheafifyAb.map (X.val ◁ 𝟙 Y.val) = sheafifyAb.map (𝟙 (X.val ⊗ Y.val)) = 𝟙. Use MonoidalCategory.whiskerLeft_id and Functor.map_id.

id_whiskerRight: similar.

For associator_naturality, leftUnitor_naturality, rightUnitor_naturality, pentagon, triangle: these all depend on the sorry'd sheafifyTensorComparisonLeftIso and sheafifyTensorComparisonRightIso, so just sorry them.

Key simp lemmas: condensedAbTensorHom, condensedAbWhiskerLeft, condensedAbWhiskerRight, sheafifyAb. The definitions unfold as sheafifyAb.map of presheaf operations. Use simp with Functor.map_comp, Functor.map_id, tensorHom_def, id_tensorHom_id, etc.
-/
instance condensedAb_monoidalCategory : MonoidalCategory CondensedAb.{0} where
  tensorHom_def := by
    -- f ⊗ₘ g = (f ▷ _) ≫ (_ ◁ g): follows from presheaf tensorHom_def + Functor.map_comp
    intro _ _ _ _ f g
    show sheafifyAb.map (f.val ⊗ₘ g.val) =
      sheafifyAb.map (f.val ▷ _) ≫ sheafifyAb.map (_ ◁ g.val)
    rw [← sheafifyAb.map_comp, MonoidalCategory.tensorHom_def]
  id_tensorHom_id := by
    -- 𝟙 ⊗ₘ 𝟙 = 𝟙: follows from presheaf id_tensorHom_id + Functor.map_id
    intro X₁ X₂
    change sheafifyAb.map (𝟙 X₁.val ⊗ₘ 𝟙 X₂.val) = 𝟙 (sheafifyAb.obj (X₁.val ⊗ X₂.val))
    simp
  tensorHom_comp_tensorHom := by
    -- (f₁ ⊗ₘ f₂) ≫ (g₁ ⊗ₘ g₂) = (f₁ ≫ g₁) ⊗ₘ (f₂ ≫ g₂)
    intro _ _ _ _ _ _ f₁ f₂ g₁ g₂
    show sheafifyAb.map (f₁.val ⊗ₘ f₂.val) ≫ sheafifyAb.map (g₁.val ⊗ₘ g₂.val) =
      sheafifyAb.map ((f₁ ≫ g₁).val ⊗ₘ (f₂ ≫ g₂).val)
    rw [← sheafifyAb.map_comp]; congr 1
    simp [MonoidalCategory.tensorHom_comp_tensorHom]
  whiskerLeft_id := by
    -- X ◁ 𝟙 Y = 𝟙 (X ⊗ Y): follows from presheaf whiskerLeft_id + Functor.map_id
    intro X Y
    change sheafifyAb.map (X.val ◁ 𝟙 Y.val) = 𝟙 (sheafifyAb.obj (X.val ⊗ Y.val))
    simp
  id_whiskerRight := by
    -- 𝟙 X ▷ Y = 𝟙 (X ⊗ Y): follows from presheaf id_whiskerRight + Functor.map_id
    intro X Y
    change sheafifyAb.map (𝟙 X.val ▷ Y.val) = 𝟙 (sheafifyAb.obj (X.val ⊗ Y.val))
    simp
  associator_naturality := by
    intros; sorry
    -- Blocked by: sheafifyTensorComparisonLeftIso/RightIso naturality
  leftUnitor_naturality := by
    intros; sorry
    -- Blocked by: sheafifyTensorComparisonLeftIso naturality
  rightUnitor_naturality := by
    intros; sorry
    -- Blocked by: sheafifyTensorComparisonRightIso naturality
  pentagon := by
    intros; sorry
    -- Blocked by: sheafifyTensorComparisonLeftIso/RightIso coherence
  triangle := by
    intros; sorry
    -- Blocked by: sheafifyTensorComparison{Left,Right}Iso coherence

-- Blocked by: sheafifyTensorComparison{Left,Right}Iso coherence

end MonoidalInstance

/-! ## Part 5: What Would Resolve Everything

The entire construction reduces to a single mathematical fact:

**Theorem (not in Mathlib)**: For the coherent topology `J` on `CompHaus` and any
presheaves `P, Q : CompHausᵒᵖ ⥤ Ab`, the sheafification comparison map
  `sheafify(η_P ⊗ id_Q) : sheafify(P ⊗ Q) → sheafify(sheafify(P).val ⊗ Q)`
is an isomorphism, where `η_P : P → sheafify(P).val` is the unit of sheafification.

Equivalently, `presheafToSheaf J Ab` is a **monoidal functor** with respect to the
pointwise tensor product.

### Possible proof approaches (for future Mathlib development):

**Approach A: Monoidal reflective subcategories.**
If `Sheaf J A` is a reflective subcategory of `Cᵒᵖ ⥤ A` (which it is, via the
sheafification adjunction) and the reflector preserves binary products (or tensors),
then the reflective subcategory inherits the monoidal structure. Mathlib has
`Monoidal.reflective` in some form but not for arbitrary sites.

**Approach B: Tensoring preserves local isomorphisms.**
Show that if `f : P ⟶ Q` is a local isomorphism (i.e., `sheafify(f)` is an iso),
then `f ⊗ id_R` is also a local isomorphism. For the coherent topology on CompHaus,
this follows from the fact that the stalks of `P ⊗ Q` at a point `x` are
`P_x ⊗ Q_x` and tensor products of abelian groups preserve isomorphisms.
But "stalks for the coherent topology" is itself nontrivial and may not be in Mathlib.

**Approach C: Direct construction via the universal property.**
Use the universal property of sheafification to directly construct the inverse of
the comparison map. Given a map `sheafify(P).val ⊗ Q → T.val` for a sheaf `T`,
precompose with `η_P ⊗ id_Q` to get `P ⊗ Q → T.val`, then use the universal
property of `sheafify(P ⊗ Q)`. This constructs the inverse but proving it's
actually inverse requires the same "tensoring preserves local isos" fact.
-/

/-! ## Part 6: Day Convolution (Not in Mathlib)

Day convolution would give an alternative monoidal structure on presheaves
when the source category has a monoidal structure (via products for CompHaus).
This is NOT formalized in Mathlib as of v4.28.0.

The Day convolution tensor of presheaves `F, G : Cᵒᵖ ⥤ A` is:
  `(F ⊗_Day G)(X) = ∫^{Y,Z} Hom(X, Y ⊗ Z) ⊗ F(Y) ⊗ G(Z)`

For the pointwise tensor product (which we use above), this simplifies when
the source category has diagonal maps, which CompHaus does.

The Day convolution approach would be more general but requires:
1. Coend formalism (partially in Mathlib)
2. Monoidal structure on CompHaus via products (exists)
3. Day convolution construction (not in Mathlib)
4. Proof that Day convolution agrees with pointwise tensor for cartesian monoidal source
-/

/-! ## Part 7: Solid Tensor Product (Very Far from Mathlib)

`Mathlib.Condensed.Solid` defines `CondensedMod.IsSolid R` as a predicate on
condensed R-modules, but there is NO tensor product on solid modules.

The mathematical theory (Clausen-Scholze) states:
- There exists a unique symmetric monoidal structure on solid abelian groups
  such that the solidification functor is symmetric monoidal.
- The solid tensor product `M ⊗^solid N` is defined as the solidification
  of the "naive" tensor product `M ⊗ N` of the underlying condensed modules.
- The key property: the solid tensor product is EXACT (both left and right exact),
  unlike the classical completed tensor product which is only right exact.

Formalizing this requires:
1. First, the monoidal structure on CondensedAb (this file's goal)
2. The solidification functor (right Kan extension, partially in Mathlib via
   `Condensed.profiniteSolid`)
3. Showing solidification is monoidal
4. Restricting to the full subcategory of solid modules

This is approximately the content of the Liquid Tensor Experiment (LTE),
which was formalized in a separate Lean 4 project but NOT upstreamed to Mathlib.
-/

/-! ## Summary: Dependency Graph for Eliminating `condensedAb_monoidal`

```
condensedAb_monoidal (axiom in LiquidTQFT.lean)
  ├── condensedAb_monoidalCategory (this file, sorry'd)
  │   ├── tensorHom_def ✔ (proved: presheaf tensorHom_def + Functor.map_comp)
  │   ├── id_tensorHom_id ✔ (proved: simp)
  │   ├── tensorHom_comp_tensorHom ✔ (proved: Functor.map_comp + presheaf identity)
  │   ├── whiskerLeft_id / id_whiskerRight ✔ (proved: simp)
  │   ├── associator_naturality — needs comparison iso naturality [MEDIUM]
  │   ├── leftUnitor_naturality / rightUnitor_naturality — [MEDIUM]
  │   ├── pentagon — needs presheaf pentagon + comparison coherence [MEDIUM]
  │   └── triangle — [MEDIUM]
  │       └── ALL blocked by:
  │           sheafifyTensorComparisonLeftIso  (KEY SORRY #1)
  │           sheafifyTensorComparisonRightIso (KEY SORRY #2)
  │               ├── Option A: Monoidal reflective subcategory theory [HARD, GENERAL]
  │               ├── Option B: Tensor preserves local isos for coherent topology [MEDIUM]
  │               └── Option C: Direct universal property argument [MEDIUM]
  ├── condensedAb_monoidalCategoryStruct (this file, FULLY CONSTRUCTED ✅)
  │   ├── condensedAbTensorObj ✅ (sheafify pointwise tensor)
  │   ├── condensedAbTensorHom ✅ (sheafify pointwise tensor of morphisms)
  │   ├── condensedAbTensorUnit ✅ (sheafify constant presheaf ℤ)
  │   ├── condensedAbWhiskerLeft / condensedAbWhiskerRight ✅
  │   ├── condensedAbAssociator ✅ (constructed from comparison isos)
  │   ├── condensedAbLeftUnitor ✅ (constructed from comparison isos)
  │   └── condensedAbRightUnitor ✅ (constructed from comparison isos)
  └── presheafAb_monoidal ✅ (from Mathlib, inferInstance)
      └── functorCategoryMonoidal ✅ (Mathlib.CategoryTheory.Monoidal.FunctorCategory)
```

**Bottom line**: The entire `condensedAb_monoidal` axiom reduces to proving that
`sheafifyTensorComparisonLeftIso` and `sheafifyTensorComparisonRightIso` are
isomorphisms. Everything else is either in Mathlib or constructed in this file.
-/

end
