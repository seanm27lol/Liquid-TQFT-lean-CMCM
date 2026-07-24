import RequestProject.Cob2Canonical

/-!
# Ordered connected spiders in the symmetric algebraic Cob2 source

This file defines one fixed, ordered family of connected presentation words:
all inputs are merged to one circle, a chosen number of handles is inserted,
and that circle is split into all outputs.  It proves the corresponding
positive-boundary composition law

`spider a b g ≫ spider b c h = spider a c (g + (b - 1) + h)`

when `0 < b`.  The extra `b - 1` handles count the cycles created by gluing
the two connected words along `b` common circles.

This is a planar/ordered spider-calculus milestone.  It does **not** prove
that every connected `Cob2Mor` word is equal to one of these spiders.  In
particular, no connectivity predicate, arbitrary permutation normalization,
multi-component normal form, generators-and-relations completeness theorem,
or comparison with geometric smooth bordisms is constructed here.
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace CommFrobeniusData

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]

/-- The handle operator of any Frobenius datum is a right-comodule map.
This is the local Frobenius slide used by the ordered spider calculation. -/
theorem handleOperator_comul (A : CommFrobeniusData C) :
    A.comul ≫ ((A.comul ≫ A.mul) ▷ A.X) =
      (A.comul ≫ A.mul) ≫ A.comul := by
  have hco :
      A.comul ≫ (A.comul ▷ A.X) =
        A.comul ≫ (A.X ◁ A.comul) ≫ (α_ A.X A.X A.X).inv := by
    rw [← cancel_mono (α_ A.X A.X A.X).hom]
    simpa [Category.assoc] using A.comul_coassoc'.symm
  rw [MonoidalCategory.comp_whiskerRight]
  rw [← Category.assoc, hco]
  simp only [Category.assoc]
  rw [A.frobenius_left]

end CommFrobeniusData

namespace Cob2Spider

/-- The positive-arity, left-associated multiplication comb on `k + 1`
inputs. -/
def mergePositive : (k : ℕ) → Cob2Mor (k + 1) 1
  | 0 => .id 1
  | k + 1 => .comp (.tensor (mergePositive k) (.id 1)) .μ

/-- The nullary unit or the positive-arity multiplication comb. -/
def mergeWord : (a : ℕ) → Cob2Mor a 1
  | 0 => .η
  | a + 1 => mergePositive a

/-- The positive-arity, ordered comultiplication comb with `k + 1`
outputs. -/
def splitPositive : (k : ℕ) → Cob2Mor 1 (k + 1)
  | 0 => .id 1
  | k + 1 => .comp .δ (.tensor (splitPositive k) (.id 1))

/-- The nullary counit or the positive-arity comultiplication comb. -/
def splitWord : (b : ℕ) → Cob2Mor 1 b
  | 0 => .ε
  | b + 1 => splitPositive b

/-- The `g`-fold ordered iteration of the handle word `δ ≫ μ`. -/
def handleWord : (g : ℕ) → Cob2Mor 1 1
  | 0 => .id 1
  | g + 1 => .comp (handleWord g) (.comp .δ .μ)

/-- The canonical ordered genus-`g` word with `a` inputs and `b` outputs. -/
def spiderWord (a b g : ℕ) : Cob2Mor a b :=
  .comp (.comp (mergeWord a) (handleWord g)) (splitWord b)

/-- The ordered merge word in the symmetric quotient. -/
def merge (a : ℕ) :
    (⟨a⟩ : Cob2SymmetricObj) ⟶ (⟨1⟩ : Cob2SymmetricObj) :=
  ⟦mergeWord a⟧

/-- The ordered split word in the symmetric quotient. -/
def split (b : ℕ) :
    (⟨1⟩ : Cob2SymmetricObj) ⟶ (⟨b⟩ : Cob2SymmetricObj) :=
  ⟦splitWord b⟧

/-- The iterated handle word in the symmetric quotient. -/
def handle (g : ℕ) :
    (⟨1⟩ : Cob2SymmetricObj) ⟶ (⟨1⟩ : Cob2SymmetricObj) :=
  ⟦handleWord g⟧

/-- The canonical ordered spider in the symmetric quotient. -/
def spider (a b g : ℕ) :
    (⟨a⟩ : Cob2SymmetricObj) ⟶ (⟨b⟩ : Cob2SymmetricObj) :=
  ⟦spiderWord a b g⟧

@[simp]
theorem merge_zero : merge 0 = Cob2Symmetric.unit := rfl

@[simp]
theorem merge_one : merge 1 = 𝟙 (⟨1⟩ : Cob2SymmetricObj) := rfl

@[simp]
theorem split_zero : split 0 = Cob2Symmetric.counit := rfl

@[simp]
theorem split_one : split 1 = 𝟙 (⟨1⟩ : Cob2SymmetricObj) := rfl

@[simp]
theorem handle_zero : handle 0 = 𝟙 (⟨1⟩ : Cob2SymmetricObj) := rfl

@[simp]
theorem merge_succ_succ (a : ℕ) :
    merge (a + 2) =
      (merge (a + 1) ⊗ₘ 𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
        Cob2Symmetric.mul := rfl

@[simp]
theorem split_succ_succ (b : ℕ) :
    split (b + 2) =
      Cob2Symmetric.comul ≫
        (split (b + 1) ⊗ₘ 𝟙 (⟨1⟩ : Cob2SymmetricObj)) := rfl

@[simp]
theorem handle_succ (g : ℕ) :
    handle (g + 1) =
      handle g ≫ Cob2Symmetric.comul ≫ Cob2Symmetric.mul := rfl

/-- Iterating `g` handles and then `h` handles gives `g + h` handles. -/
theorem handle_add (g h : ℕ) :
    handle (g + h) = handle g ≫ handle h := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [Nat.add_succ, handle_succ, handle_succ, ih]
      simp [Category.assoc]

/-- Handles slide through the chosen output side of comultiplication. -/
theorem comul_handle (g : ℕ) :
    Cob2Symmetric.comul ≫
        (handle g ▷ (⟨1⟩ : Cob2SymmetricObj)) =
      handle g ≫ Cob2Symmetric.comul := by
  induction g with
  | zero =>
      rw [handle_zero, MonoidalCategory.id_whiskerRight]
      exact Quotient.sound (.monoidal (.old
        (.trans (.comp_id Cob2Mor.δ) (.symm (.id_comp Cob2Mor.δ)))))
  | succ g ih =>
      rw [handle_succ, MonoidalCategory.comp_whiskerRight,
        MonoidalCategory.comp_whiskerRight]
      simp only [Category.assoc]
      rw [← Category.assoc Cob2Symmetric.comul
        (handle g ▷ (⟨1⟩ : Cob2SymmetricObj))]
      rw [ih]
      calc
        _ = handle g ≫
              (Cob2Symmetric.comul ≫
                ((Cob2Symmetric.comul ≫ Cob2Symmetric.mul) ▷
                  (⟨1⟩ : Cob2SymmetricObj))) := by
              simp [MonoidalCategory.comp_whiskerRight, Category.assoc]
        _ = handle g ≫
              ((Cob2Symmetric.comul ≫ Cob2Symmetric.mul) ≫
                Cob2Symmetric.comul) := by
              have h := CommFrobeniusData.handleOperator_comul
                Cob2Symmetric.canonicalFrobenius
              change Cob2Symmetric.comul ≫
                  ((Cob2Symmetric.comul ≫ Cob2Symmetric.mul) ▷
                    (⟨1⟩ : Cob2SymmetricObj)) =
                (Cob2Symmetric.comul ≫ Cob2Symmetric.mul) ≫
                  Cob2Symmetric.comul at h
              simpa only [Category.assoc] using
                congrArg (fun q => handle g ≫ q) h
        _ = _ := by simp [Category.assoc]

/-- Splitting into `k + 1` ordered circles and merging them again creates
exactly `k` handles. -/
theorem split_merge_succ (k : ℕ) :
    split (k + 1) ≫ merge (k + 1) = handle k := by
  induction k with
  | zero =>
      change (𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫ 𝟙 (⟨1⟩ : Cob2SymmetricObj) =
        𝟙 (⟨1⟩ : Cob2SymmetricObj)
      exact Category.id_comp _
  | succ k ih =>
      rw [split_succ_succ, merge_succ_succ]
      simp only [Category.assoc]
      slice_lhs 2 3 =>
        rw [Cob2Symmetric.cob2Symmetric_interchange]
      rw [Category.id_comp]
      rw [ih]
      change Cob2Symmetric.comul ≫
          (handle k ▷ (⟨1⟩ : Cob2SymmetricObj)) ≫
            Cob2Symmetric.mul =
        handle (k + 1)
      calc
        _ = (handle k ≫ Cob2Symmetric.comul) ≫
              Cob2Symmetric.mul := by
            simpa only [Category.assoc] using
              congrArg (fun q => q ≫ Cob2Symmetric.mul) (comul_handle k)
        _ = _ := by
            rw [handle_succ]
            simp only [Category.assoc]

@[simp]
theorem spider_eq :
    spider a b g = (merge a ≫ handle g) ≫ split b := rfl

/-- Positive-boundary split followed by merge contributes `b - 1`
handles. -/
theorem split_merge (b : ℕ) (hb : 0 < b) :
    split b ≫ merge b = handle (b - 1) := by
  cases b with
  | zero => omega
  | succ b => simpa using split_merge_succ b

/-- Ordered connected spiders compose along a nonempty common boundary.
The statement concerns this chosen family; it is not an arbitrary-word
normal-form theorem. -/
theorem spider_comp (a b c g h : ℕ) (hb : 0 < b) :
    spider a b g ≫ spider b c h =
      spider a c (g + (b - 1) + h) := by
  rw [spider_eq, spider_eq, spider_eq]
  simp only [Category.assoc]
  slice_lhs 3 4 =>
    rw [split_merge b hb]
  slice_lhs 2 3 =>
    rw [← handle_add]
  slice_lhs 2 3 =>
    rw [← handle_add]

end Cob2Spider
