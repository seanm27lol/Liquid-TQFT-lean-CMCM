/-
# Monoidal Structure on Condensed Abelian Groups via Localization

This file constructs the monoidal category structure on `CondensedAb` (condensed abelian groups)
using existing Mathlib infrastructure from `Mathlib.CategoryTheory.Sites.Monoidal` and
`Mathlib.CategoryTheory.Localization.Monoidal.Basic`.

## Overview

The construction follows the localization approach:

1. **Presheaf category is monoidal**: `CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u+1} (ULift.{u+1} ℤ)` inherits
   a monoidal structure from the pointwise tensor product in `ModuleCat`.

2. **Sheafification is a localization**: `presheafToSheaf J A` is a localization functor for the
   class `J.W` of morphisms inverted by sheafification (`Mathlib.CategoryTheory.Sites.Localization`).

3. **`W` is a monoidal morphism property**: The class `J.W` of local isomorphisms is closed under
   tensoring. This is proved in `Mathlib.CategoryTheory.Sites.Monoidal` using the internal hom
   (monoidal closed structure) and enriched hom technology. The key insight is that for a closed
   braided monoidal category `A`, the morphism property `J.W` is automatically monoidal.

4. **Localized monoidal structure**: `Mathlib.CategoryTheory.Localization.Monoidal.Basic` constructs
   a monoidal category structure on any localization of a monoidal category at a monoidal morphism
   property.

5. **Application to condensed abelian groups**: Combining these gives
   `MonoidalCategory CondensedAb`, `BraidedCategory CondensedAb`, and
   `SymmetricCategory CondensedAb`.

## Key Mathlib Components Used

- `GrothendieckTopology.W`: The class of morphisms of presheaves inverted by sheafification.
- `GrothendieckTopology.W.monoidal`: Instance showing `J.W` is monoidal when `A` is closed braided.
- `Sheaf.monoidalCategory`: The monoidal structure on `Sheaf J A` via localization.
- `Sheaf.braidedCategory` / `Sheaf.symmetricCategory`: Braided/symmetric refinements.
- `MonoidalClosed.enrichedOrdinaryCategorySelf`: Scoped instance making a closed monoidal category
  enriched over itself (needed for the `W.IsMonoidal` proof).

## Universe Setup

`CondensedAb.{u} = Condensed (ModuleCat (ULift.{u+1} ℤ))`
where `Condensed C = Sheaf (coherentTopology CompHaus.{u}) C`.

- `CompHaus.{u}` lives in `Type (u+1)` with `Category.{u}`.
- `ModuleCat.{u+1} (ULift.{u+1} ℤ)` lives in `Type (u+2)` with `Category.{u+1}`.
- The enriched hom construction requires limits indexed by `Under (op X)` for `X : CompHaus.{u}ᵒᵖ`,
  which has objects in `Type (u+1)` and morphisms in `Type u`. This works because
  `ModuleCat.{u+1}` has `HasLimitsOfSize.{u+1, u+1}`.
-/

import Mathlib

universe u

open CategoryTheory MonoidalClosed Enriched.FunctorCategory

noncomputable section

/-! ## Step 1: Verify prerequisites -/

section Prerequisites

/-- The presheaf category has a monoidal structure from pointwise tensor product. -/
example : MonoidalCategory (CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u+1} (ULift.{u+1} ℤ)) :=
  inferInstance

/-- The presheaf category is symmetric monoidal. -/
example : SymmetricCategory (CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u+1} (ULift.{u+1} ℤ)) :=
  inferInstance

/-- `ModuleCat` over a commutative ring is monoidal closed. -/
example : MonoidalClosed (ModuleCat.{u+1} (ULift.{u+1} ℤ)) :=
  inferInstance

/-- `ModuleCat` is a braided (in fact symmetric) monoidal category. -/
example : BraidedCategory (ModuleCat.{u+1} (ULift.{u+1} ℤ)) :=
  inferInstance

/-- `presheafToSheaf` is a localization functor for `J.W`. -/
example : (presheafToSheaf (coherentTopology CompHaus.{u})
    (ModuleCat.{u+1} (ULift.{u+1} ℤ))).IsLocalization
    (coherentTopology CompHaus.{u}).W :=
  inferInstance

/-- `HasWeakSheafify` holds for our setting. -/
example : HasWeakSheafify (coherentTopology CompHaus.{u})
    (ModuleCat.{u+1} (ULift.{u+1} ℤ)) :=
  inferInstance

/-- `ModuleCat` has all limits (needed for enriched hom construction). -/
example : Limits.HasLimitsOfSize.{u+1, u+1}
    (ModuleCat.{u+1} (ULift.{u+1} ℤ)) :=
  inferInstance

/-- The enriched hom between presheaves exists (needs limits for the end construction). -/
example (F₁ F₂ : CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u+1} (ULift.{u+1} ℤ)) :
    HasEnrichedHom (ModuleCat.{u+1} (ULift.{u+1} ℤ)) F₁ F₂ :=
  inferInstance

/-- The functor-level enriched hom also exists. -/
example (F₁ F₂ : CompHaus.{u}ᵒᵖ ⥤ ModuleCat.{u+1} (ULift.{u+1} ℤ)) :
    HasFunctorEnrichedHom (ModuleCat.{u+1} (ULift.{u+1} ℤ)) F₁ F₂ :=
  inferInstance

end Prerequisites

/-! ## Step 2: `W.IsMonoidal` — the key property

The class `J.W` of morphisms inverted by sheafification is monoidal. This is the
crucial property that allows the localization machinery to construct a monoidal
structure on the sheaf category.

The proof in Mathlib (`GrothendieckTopology.W.monoidal`) works as follows:

- **Whiskering on the left** (`W.whiskerLeft`): If `g ∈ W` and `F` is any presheaf, then
  `F ◁ g ∈ W`. This is proved using the internal hom (monoidal closed structure):
  for any sheaf `H`, the map `Hom(F ⊗ G₂, H) → Hom(F ⊗ G₁, H)` induced by `F ◁ g`
  is identified with `Hom(G₂, [F,H]) → Hom(G₁, [F,H])` via currying, and `[F,H]` is
  a sheaf when `H` is (this is `Presheaf.isSheaf_functorEnrichedHom`), so `g ∈ W`
  gives the bijection.

- **Whiskering on the right** (`W.whiskerRight`): If `f ∈ W` and `G` is any presheaf,
  then `f ▷ G ∈ W`. This follows from the left case using the braiding.

- **Multiplicativity**: `W` contains identities and is closed under composition
  (inherited from `ObjectProperty.isLocal`).
-/

/-- The class of local isomorphisms for the coherent topology on `CompHaus` with values
in `ModuleCat (ULift ℤ)` is a monoidal morphism property. This is the key fact enabling
the localized monoidal structure on condensed abelian groups. -/
instance condensedAb_W_isMonoidal :
    ((coherentTopology CompHaus.{u}).W
      (A := ModuleCat.{u+1} (ULift.{u+1} ℤ))).IsMonoidal :=
  GrothendieckTopology.W.monoidal

/-! ## Step 3: The monoidal structure on CondensedAb -/

/-- The monoidal category structure on condensed abelian groups, constructed via
localization of the pointwise tensor product on presheaves. The tensor product of
two condensed abelian groups `F ⊗ G` is the sheafification of their pointwise
tensor product as presheaves. -/
instance condensedAb_monoidalCategory :
    MonoidalCategory CondensedAb.{u} :=
  Sheaf.monoidalCategory _ _

/-- The braided category structure on condensed abelian groups. -/
instance condensedAb_braidedCategory :
    @BraidedCategory CondensedAb.{u} _ condensedAb_monoidalCategory :=
  Sheaf.braidedCategory _ _

/-- The symmetric category structure on condensed abelian groups. -/
instance condensedAb_symmetricCategory :
    @SymmetricCategory CondensedAb.{u} _ condensedAb_monoidalCategory :=
  Sheaf.symmetricCategory _ _

section SheafificationMonoidal

local instance : MonoidalCategory
    (Sheaf (coherentTopology CompHaus.{u}) (ModuleCat.{u+1} (ULift.{u+1} ℤ))) :=
  condensedAb_monoidalCategory

local instance : BraidedCategory
    (Sheaf (coherentTopology CompHaus.{u}) (ModuleCat.{u+1} (ULift.{u+1} ℤ))) :=
  condensedAb_braidedCategory

/-- The sheafification functor is monoidal with respect to the localized monoidal structure. -/
example : (presheafToSheaf (coherentTopology CompHaus.{u})
    (ModuleCat.{u+1} (ULift.{u+1} ℤ))).Monoidal :=
  inferInstance

/-- The sheafification functor is braided. -/
example : (presheafToSheaf (coherentTopology CompHaus.{u})
    (ModuleCat.{u+1} (ULift.{u+1} ℤ))).Braided :=
  inferInstance

end SheafificationMonoidal

/-! ## Step 4: Verification that no sorry is needed

The entire construction is sorry-free. All components are provided by Mathlib:

1. `GrothendieckTopology.W.monoidal` (from `Mathlib.CategoryTheory.Sites.Monoidal`)
2. `Sheaf.monoidalCategory` (from `Mathlib.CategoryTheory.Sites.Monoidal`)
3. `presheafToSheaf ... IsLocalization J.W` (from `Mathlib.CategoryTheory.Sites.Localization`)
4. Localization monoidal machinery (from `Mathlib.CategoryTheory.Localization.Monoidal.Basic`)
5. `MonoidalClosed (ModuleCat R)` (from `Mathlib.Algebra.Category.ModuleCat.Monoidal`)
6. Enriched hom infrastructure (from `Mathlib.CategoryTheory.Enriched.FunctorCategory` and
   `Mathlib.CategoryTheory.Monoidal.Closed.Enrichment`)
-/

/-! ## Answers to the investigation questions

### Question 1: Localization infrastructure
- ✅ `presheafToSheaf J A` is recognized as `Functor.IsLocalization J.W` in
  `Mathlib.CategoryTheory.Sites.Localization`.
- ✅ The `MorphismProperty` is `GrothendieckTopology.W`, defined as
  `ObjectProperty.isLocal (Presheaf.IsSheaf J)`. Equivalently, `J.W f ↔ IsIso ((presheafToSheaf J A).map f)`.
- ✅ `MorphismProperty.IsMonoidal` requires `IsMultiplicative` (id ∈ W, comp-closed) plus
  stability under left/right whiskering.

### Question 2: `W.IsMonoidal` for local isomorphisms
- ✅ Fully proved by `GrothendieckTopology.W.monoidal` in `Mathlib.CategoryTheory.Sites.Monoidal`.
  The proof uses the internal hom (monoidal closed structure of `ModuleCat`) and enriched hom
  technology. No sorry needed.
- The key mathematical argument: if `g : G₁ ⟶ G₂` is in `W` and `F` is any presheaf, then
  for any sheaf `H`, `Hom(F ⊗ G₂, H) ≅ Hom(G₂, [F,H])` by adjunction, and `[F,H]` is a sheaf
  (shown in `Presheaf.isSheaf_functorEnrichedHom`), so `g ∈ W` gives the required bijection.

### Question 3: Connecting to CondensedAb
- ✅ `Sheaf.monoidalCategory` directly gives `MonoidalCategory (Sheaf J A)`, which IS `CondensedAb`.
  No transport or type synonym issues — `Sheaf.monoidalCategory` constructs the instance as
  `inferInstanceAs (MonoidalCategory (LocalizedMonoidal ...))`, and since `LocalizedMonoidal` is
  a type synonym for the target type `D` (which is `Sheaf J A`), the instance applies directly.

### Question 4: Direct attack via stalks
- Not needed! The Mathlib proof avoids stalks entirely. Instead of showing that stalk functors
  commute with tensor products, it uses the internal hom / monoidal closed structure. This is
  more general (works for any closed braided target category, not just abelian categories with
  enough points) and is already fully formalized.
- For the record: CompHaus with the coherent topology does NOT have enough points in the
  classical sense (it's not a spatial topos), so a stalk-based approach would require
  significant additional development.
-/

end
