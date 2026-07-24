import RequestProject.Cob2SurfaceMonoidal

/-!
# Unit coherence for disjoint union of surface normal forms

This file proves the two missing unit laws for disjoint union on the verified
category of component-and-genus normal forms.  The proofs are carried out on
representatives by explicit equivalences of component labels and then
descended to the quotient.
-/

noncomputable section

namespace Cob2NormalForm

open CategoryTheory

namespace SurfaceCode

/-- Removing the empty component block on the left is a component
relabeling. -/
theorem rel_tensor_empty_left {a b : ℕ} (s : SurfaceCode a b) :
    Rel
      (cast (Nat.zero_add a) (Nat.zero_add b) (tensor empty s))
      s := by
  refine ⟨finCongr (Nat.zero_add s.ncomp), ?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    simp [cast, tensor, empty]
    rw [show Fin.cast (Nat.zero_add a).symm i = Fin.natAdd 0 i by
      apply Fin.ext
      simp]
    rw [Fin.addCases_right]
    simp
  · intro j
    apply Fin.ext
    simp [cast, tensor, empty]
    rw [show Fin.cast (Nat.zero_add b).symm j = Fin.natAdd 0 j by
      apply Fin.ext
      simp]
    rw [Fin.addCases_right]
    simp
  · intro k
    refine Fin.addCases (fun i => i.elim0) (fun j => ?_) k
    simp [cast, tensor, empty]
    rw [show Fin.cast (Nat.zero_add s.ncomp).symm j =
        Fin.natAdd 0 j by
      apply Fin.ext
      simp]
    rw [Fin.addCases_right]

/-- Removing the empty component block on the right is a component
relabeling. -/
theorem rel_tensor_empty_right {a b : ℕ} (s : SurfaceCode a b) :
    Rel
      (cast (Nat.add_zero a) (Nat.add_zero b) (tensor s empty))
      s := by
  refine ⟨finCongr (Nat.add_zero s.ncomp), ?_, ?_, ?_⟩
  · intro i
    apply Fin.ext
    simp [cast, tensor, empty]
    rw [show i = Fin.castAdd 0 i by
      apply Fin.ext
      simp]
    rw [Fin.addCases_left]
    rw [show Fin.castAdd 0 i = i by
      apply Fin.ext
      simp]
  · intro j
    apply Fin.ext
    simp [cast, tensor, empty]
    rw [show j = Fin.castAdd 0 j by
      apply Fin.ext
      simp]
    rw [Fin.addCases_left]
    rw [show Fin.castAdd 0 j = j by
      apply Fin.ext
      simp]
  · intro k
    refine Fin.addCases (fun i => ?_) (fun j => j.elim0) k
    simp [cast, tensor, empty]
    rw [show i = Fin.castAdd 0 i by
      apply Fin.ext
      simp]
    rw [Fin.addCases_left]
    rw [show Fin.castAdd 0 i = i by
      apply Fin.ext
      simp]

end SurfaceCode

namespace SurfaceNF

/-- The empty normal form is a left unit for disjoint union, after the
canonical transport of boundary arities. -/
@[simp]
theorem tensor_empty_left {a b : ℕ} (s : SurfaceNF a b) :
    cast (Nat.zero_add a) (Nat.zero_add b) (tensor empty s) = s := by
  induction s using Quotient.inductionOn with
  | _ s =>
      apply Quotient.sound
      exact SurfaceCode.rel_tensor_empty_left s

/-- The empty normal form is a right unit for disjoint union, after the
canonical transport of boundary arities. -/
@[simp]
theorem tensor_empty_right {a b : ℕ} (s : SurfaceNF a b) :
    cast (Nat.add_zero a) (Nat.add_zero b) (tensor s empty) = s := by
  induction s using Quotient.inductionOn with
  | _ s =>
      apply Quotient.sound
      exact SurfaceCode.rel_tensor_empty_right s

end SurfaceNF

end Cob2NormalForm
