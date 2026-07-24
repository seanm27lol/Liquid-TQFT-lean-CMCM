import RequestProject.Cob2Permutation

/-!
# Boundary-adjacent transpositions for ordered Cob2 spiders

This file extends the first-boundary transposition from
`RequestProject.Cob2Permutation` to an adjacent transposition after an
arbitrary number of fixed leading wires.  The construction retains the
parenthesization of the algebraic symmetric monoidal source and derives all
equalities from its lawful tensor product and symmetry.

This is still an algebraic boundary-permutation layer.  It does not identify
the presentation with geometric bordisms, prove arbitrary-position
merge/split invariance, construct a full permutation action, or prove a
complete spider normal form.
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace Cob2BoundaryPermutations

open Cob2Permutation Cob2Spider

/-- The total arity for an adjacent pair with `i` leading and `k` trailing
wires.  Its recursive presentation is chosen to match the tensor
parenthesization used below. -/
def boundaryArity : ℕ → ℕ → ℕ
  | 0, k => Nat.succ (Nat.succ k)
  | Nat.succ i, k => 1 + boundaryArity i k

@[simp]
theorem boundaryArity_zero (k : ℕ) :
    boundaryArity 0 k = Nat.succ (Nat.succ k) := rfl

@[simp]
theorem boundaryArity_succ (i k : ℕ) :
    boundaryArity (Nat.succ i) k = 1 + boundaryArity i k := rfl

theorem boundaryArity_eq (i k : ℕ) :
    boundaryArity i k = i + k + 2 := by
  induction i with
  | zero => simp [boundaryArity]
  | succ i ih =>
      rw [boundaryArity_succ, ih]
      omega

/-- Exchange two adjacent wires after `i` fixed leading wires and before `k`
fixed trailing wires. -/
def adjacentSwap : (i k : ℕ) →
    (⟨boundaryArity i k⟩ : Cob2SymmetricObj) ⟶
      (⟨boundaryArity i k⟩ : Cob2SymmetricObj)
  | 0, k => firstAdjacentSwap k
  | Nat.succ i, k =>
      𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ adjacentSwap i k

@[simp]
theorem adjacentSwap_zero (k : ℕ) :
    adjacentSwap 0 k = firstAdjacentSwap k := rfl

@[simp]
theorem adjacentSwap_succ (i k : ℕ) :
    adjacentSwap (Nat.succ i) k =
      𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ adjacentSwap i k := rfl

/-- Every boundary-adjacent transposition is an involution. -/
theorem adjacentSwap_involutive (i k : ℕ) :
    adjacentSwap i k ≫ adjacentSwap i k =
      𝟙 (⟨boundaryArity i k⟩ : Cob2SymmetricObj) := by
  induction i with
  | zero =>
      simpa using firstAdjacentSwap_involutive k
  | succ i ih =>
      change
        (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ adjacentSwap i k) ≫
            (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ adjacentSwap i k) =
          𝟙 ((⟨1⟩ : Cob2SymmetricObj) ⊗
            (⟨boundaryArity i k⟩ : Cob2SymmetricObj))
      rw [Cob2Symmetric.cob2Symmetric_interchange, ih]
      simp

end Cob2BoundaryPermutations
