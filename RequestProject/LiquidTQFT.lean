/-
# Liquid Vector Spaces as a Target Category for TQFTs

This file investigates whether condensed/liquid vector spaces can serve as
a target category for topological quantum field theories (TQFTs), replacing
topological vector spaces.

## Mathematical Context

A (d+1)-dimensional TQFT is a symmetric monoidal functor Z : Cob_{d+1} → C.
When C = Vect (finite-dimensional), this is classical (Atiyah 1988).
For infinite-dimensional state spaces (e.g., Chern-Simons with non-compact
gauge group SL(2,ℂ)), the natural target is topological vector spaces,
but the category TopAb is not abelian.

The proposed fix: use LiqVect (liquid vector spaces) or Cond(Ab)
(condensed abelian groups), which ARE abelian categories with exact
completed tensor products.

## What is formalized here

1. The key obstruction in TopAb: mono + epi need not be iso.
2. Abstract TQFT framework as a braided monoidal functor.
3. Transfer of TQFT structure along braided monoidal functors.
4. Symmetric monoidal structure on CondensedAb (assembled from Mathlib).
5. Gluing exactness from short exact sequences in abelian categories.

## New material (not just Mathlib recall)

- `AbstractTQFT` structure and `AbstractTQFT.transfer` theorem.
- Assembly of monoidal/braided/symmetric instances on CondensedAb.
- `abelian_mono_epi_is_iso` (one-liner, but documents the key obstruction).
- A gluing lemma connecting abelian short exactness to the mono/epi/exact data used in TQFT gluing.
-/

import Mathlib

open CategoryTheory

noncomputable section

set_option synthInstance.maxHeartbeats 800000

/-! ## Part 1: The Abelian Obstruction

In any abelian category (hence in CondensedAb), a morphism that is both
monic and epic is an isomorphism. This is precisely what fails in TopAb:
a continuous bijective homomorphism need not have a continuous inverse.
-/

/-- In any abelian category, mono + epi = iso. This is the key property
that makes CondensedAb suitable as a TQFT target, unlike TopAb. -/
theorem abelian_mono_epi_is_iso {C : Type*} [Category C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f :=
  isIso_of_mono_of_epi f

/-! ## Part 2: Abstract TQFT Framework

We define a TQFT abstractly as a braided monoidal functor from any
braided monoidal category (playing the role of cobordisms) into a
target braided monoidal category.

In a full formalization, the source would be the cobordism category
Cob_{d+1}, but since cobordism categories are not yet in Mathlib,
we work with an arbitrary source category.
-/

/-- An abstract TQFT with source category `S` and target category `C`,
both equipped with braided monoidal structure. A TQFT is a braided
monoidal functor `Z : S ⥤ C`. -/
structure AbstractTQFT
    (S : Type*) [Category S] [MonoidalCategory S] [BraidedCategory S]
    (C : Type*) [Category C] [MonoidalCategory C] [BraidedCategory C] where
  /-- The underlying functor from cobordisms to the target category -/
  Z : S ⥤ C
  /-- The (strong) monoidal structure on Z -/
  monoidal : Z.Monoidal
  /-- Z respects braidings -/
  braided : Z.Braided

/-! ## Part 3: Transfer of TQFT Structure Along Braided Monoidal Functors

**Key theorem**: If `F : C ⥤ D` is a braided monoidal functor and
`Z : S ⥤ C` is a TQFT, then `Z ⋙ F : S ⥤ D` is also a TQFT.

This is the abstract version of: "If Ban → LiqVect is braided monoidal,
then any Banach TQFT automatically becomes a liquid TQFT."
-/

/-- Composition of a TQFT with a braided monoidal functor yields a TQFT. -/
def AbstractTQFT.transfer
    {S : Type*} [Category S] [MonoidalCategory S] [BraidedCategory S]
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type*} [Category D] [MonoidalCategory D] [BraidedCategory D]
    (T : AbstractTQFT S C)
    (F : C ⥤ D) [hF : F.Monoidal] [hFb : F.Braided] :
    AbstractTQFT S D where
  Z := T.Z ⋙ F
  monoidal := by
    letI := T.monoidal
    infer_instance
  braided := by
    letI := T.monoidal
    letI := T.braided
    infer_instance

/-! ## Part 4: The Monoidal Structure on CondensedAb

The construction assembles existing Mathlib infrastructure:
1. Presheaf category inherits pointwise monoidal structure from `ModuleCat`.
2. Sheafification is a localization functor for `J.W` (local isomorphisms).
3. `J.W` is a monoidal morphism property (via internal hom / monoidal closed).
4. General localization machinery gives `MonoidalCategory (Sheaf J A)`.

See `MonoidalViaLocalization.lean` for the detailed construction.
-/

open MonoidalClosed Enriched.FunctorCategory

/-- The class of local isomorphisms for the coherent topology on `CompHaus` with
values in `ModuleCat (ULift ℤ)` is a monoidal morphism property. -/
instance condensedAb_W_isMonoidal :
    ((coherentTopology CompHaus.{0}).W
      (A := ModuleCat.{1} (ULift.{1} ℤ))).IsMonoidal :=
  GrothendieckTopology.W.monoidal

/-- `CondensedAb` admits a monoidal structure via sheafified pointwise tensor. -/
instance condensedAb_monoidal : MonoidalCategory CondensedAb.{0} :=
  Sheaf.monoidalCategory _ _

/-- `CondensedAb` admits a braided monoidal structure. -/
instance condensedAb_braided :
    @BraidedCategory CondensedAb.{0} _ condensedAb_monoidal :=
  Sheaf.braidedCategory _ _

/-- `CondensedAb` admits a symmetric monoidal structure. -/
instance condensedAb_symmetric :
    @SymmetricCategory CondensedAb.{0} _ condensedAb_monoidal :=
  Sheaf.symmetricCategory _ _

/-! ## Part 5: Exactness and the Gluing Problem

When a manifold M is cut along Σ into M₁ and M₂, the TQFT gluing axiom
requires Z(M) = ⟨Z(M₁), Z(M₂)⟩ via contraction over Z(Σ). This depends
on exactness of the tensor product.

In TopVect, the completed tensor product is NOT exact. In CondensedAb
(and its liquid subcategory), exactness holds (Clausen-Scholze, LTE).

We formalize the abstract categorical consequence: short exact sequences
in abelian categories provide the decomposition structure for gluing.
Note: these take exactness as a hypothesis. The claim that the liquid
tensor product IS exact depends on the LTE and is not verified here.
-/


/-- A short exact sequence in an abelian category provides mono, epi,
and exactness at the middle -- the three ingredients for TQFT gluing. -/
theorem short_exact_gives_gluing
    {C : Type*} [Category C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) :
    Mono S.f ∧ Epi S.g ∧ S.Exact :=
  ⟨hS.mono_f, hS.epi_g, hS.exact⟩



end
