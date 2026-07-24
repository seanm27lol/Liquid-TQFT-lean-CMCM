import RequestProject.Cob2SpiderPermutations

/-!
# Finite words of boundary-adjacent swaps

This file packages a boundary-adjacent swap at a fixed arity `n`, retaining
the proof that its leading and trailing wire counts add up to `n`.  The swap
is transported to an endomorphism of the object `⟨n⟩` by explicit
`eqToHom` conjugation.  Lists of these swaps are evaluated by categorical
composition.

Every represented finite word is absorbed by the ordered multiplication and
comultiplication combs.  This follows from the all-position adjacent-swap
theorems and introduces no new presentation relation.

This is a word-level boundary invariance theorem.  It does not construct an
action of `Equiv.Perm (Fin n)`, prove that every finite permutation has a
representation by `BoundarySwap n`, or prove an arbitrary-word spider normal
form.  No comparison with geometric bordisms is asserted.
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace Cob2SpiderPermutationWords

open Cob2Spider Cob2BoundaryPermutations Cob2SpiderPermutations

/-- An adjacent boundary transposition whose total arity is `n`. -/
structure BoundarySwap (n : ℕ) where
  /-- Number of fixed leading wires. -/
  leading : ℕ
  /-- Number of fixed trailing wires. -/
  trailing : ℕ
  /-- The adjacent pair and the fixed wires exhaust the boundary. -/
  arity_eq : boundaryArity leading trailing = n

namespace BoundarySwap

/-- The object equality witnessing the arity stored in a boundary swap. -/
def objectEq {n : ℕ} (s : BoundarySwap n) :
    (⟨boundaryArity s.leading s.trailing⟩ : Cob2SymmetricObj) =
      (⟨n⟩ : Cob2SymmetricObj) :=
  Cob2SymmetricObj.ext s.arity_eq

/-- A stored adjacent swap, explicitly conjugated to an endomorphism of
the fixed-arity object `⟨n⟩`. -/
def hom {n : ℕ} (s : BoundarySwap n) :
    (⟨n⟩ : Cob2SymmetricObj) ⟶ (⟨n⟩ : Cob2SymmetricObj) :=
  eqToHom s.objectEq.symm ≫
    adjacentSwap s.leading s.trailing ≫
      eqToHom s.objectEq

/-- A transported adjacent swap is absorbed by the ordered merge comb. -/
@[simp]
theorem hom_merge {n : ℕ} (s : BoundarySwap n) :
    s.hom ≫ merge n = merge n := by
  obtain ⟨i, k, h⟩ := s
  subst n
  change
    (eqToHom _ ≫ adjacentSwap i k ≫ eqToHom _) ≫
        merge (boundaryArity i k) =
      merge (boundaryArity i k)
  simpa [objectEq] using adjacentSwap_merge i k

/-- The ordered split comb absorbs a transported adjacent swap. -/
@[simp]
theorem split_hom {n : ℕ} (s : BoundarySwap n) :
    split n ≫ s.hom = split n := by
  obtain ⟨i, k, h⟩ := s
  subst n
  change
    split (boundaryArity i k) ≫
        (eqToHom _ ≫ adjacentSwap i k ≫ eqToHom _) =
      split (boundaryArity i k)
  simpa [objectEq] using split_adjacentSwap i k

end BoundarySwap

/-- A finite word of adjacent boundary swaps at a fixed arity. -/
abbrev BoundarySwapWord (n : ℕ) := List (BoundarySwap n)

namespace BoundarySwapWord

/-- Evaluate a finite swap word by categorical composition, in list order. -/
def eval {n : ℕ} :
    BoundarySwapWord n →
      ((⟨n⟩ : Cob2SymmetricObj) ⟶ (⟨n⟩ : Cob2SymmetricObj))
  | [] => 𝟙 _
  | s :: w => s.hom ≫ eval w

/-- The empty swap word evaluates to the identity. -/
@[simp]
theorem eval_nil (n : ℕ) :
    eval ([] : BoundarySwapWord n) =
      𝟙 (⟨n⟩ : Cob2SymmetricObj) := rfl

/-- Evaluation sends list cons to categorical composition. -/
@[simp]
theorem eval_cons {n : ℕ} (s : BoundarySwap n)
    (w : BoundarySwapWord n) :
    eval (s :: w) = s.hom ≫ eval w := rfl

/-- Every represented finite adjacent-swap word is absorbed by the merge
comb at its fixed arity. -/
@[simp]
theorem eval_merge {n : ℕ} (w : BoundarySwapWord n) :
    eval w ≫ merge n = merge n := by
  induction w with
  | nil => simp
  | cons s w ih =>
      simp [Category.assoc, ih]

/-- The split comb absorbs every represented finite adjacent-swap word at
its fixed arity. -/
@[simp]
theorem split_eval {n : ℕ} (w : BoundarySwapWord n) :
    split n ≫ eval w = split n := by
  induction w with
  | nil => simp
  | cons s w ih =>
      rw [eval_cons]
      rw [← Category.assoc]
      rw [BoundarySwap.split_hom]
      exact ih

end BoundarySwapWord

end Cob2SpiderPermutationWords
