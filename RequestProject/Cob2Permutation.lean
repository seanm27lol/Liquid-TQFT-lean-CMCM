import RequestProject.Cob2Spider

/-!
# A first boundary-permutation result for ordered Cob2 spiders

This file isolates the adjacent transposition exchanging the first two
boundary wires while fixing `k` recursively parenthesized trailing wires.  It
proves that this transposition is involutive and that the ordered `k + 2`-ary
split and merge combs are invariant under it.  Binary cocommutativity is
obtained from the generic theorem for commutative Frobenius data, rather than
added as another presentation relation.

The result is deliberately bounded: it does not yet construct transpositions
at arbitrary positions, an action of `Equiv.Perm (Fin n)`, arbitrary
permutation invariance, a spider normal-form theorem, or geometric bordisms.
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace Cob2Permutation

open Cob2Spider

/-- The symmetry exchanging the first two wires and fixing `k` trailing
wires, with the same recursive parenthesization used by `split` and `merge`. -/
def firstAdjacentSwap : (k : ℕ) →
    (⟨Nat.succ (Nat.succ k)⟩ : Cob2SymmetricObj) ⟶
      (⟨Nat.succ (Nat.succ k)⟩ : Cob2SymmetricObj)
  | 0 => (β_ (⟨1⟩ : Cob2SymmetricObj) (⟨1⟩ : Cob2SymmetricObj)).hom
  | Nat.succ k =>
      firstAdjacentSwap k ⊗ₘ 𝟙 (⟨1⟩ : Cob2SymmetricObj)

@[simp]
theorem firstAdjacentSwap_zero :
    firstAdjacentSwap 0 =
      (β_ (⟨1⟩ : Cob2SymmetricObj) (⟨1⟩ : Cob2SymmetricObj)).hom := rfl

@[simp]
theorem firstAdjacentSwap_succ (k : ℕ) :
    firstAdjacentSwap (k + 1) =
      firstAdjacentSwap k ⊗ₘ 𝟙 (⟨1⟩ : Cob2SymmetricObj) := rfl

/-- Binary comultiplication in the canonical source is cocommutative. -/
theorem canonical_comul_cocommutative :
    Cob2Symmetric.comul ≫
        (β_ (⟨1⟩ : Cob2SymmetricObj) (⟨1⟩ : Cob2SymmetricObj)).hom =
      Cob2Symmetric.comul := by
  exact CommFrobeniusData.comul_comm Cob2Symmetric.canonicalFrobenius

/-- Binary multiplication in the canonical source is commutative. -/
theorem canonical_mul_commutative :
    (β_ (⟨1⟩ : Cob2SymmetricObj) (⟨1⟩ : Cob2SymmetricObj)).hom ≫
        Cob2Symmetric.mul =
      Cob2Symmetric.mul := by
  simpa using Cob2Symmetric.canonicalFrobenius.mul_comm'

/-- The chosen adjacent transposition is an involution. -/
theorem firstAdjacentSwap_involutive (k : ℕ) :
    firstAdjacentSwap k ≫ firstAdjacentSwap k =
      𝟙 (⟨k + 2⟩ : Cob2SymmetricObj) := by
  induction k with
  | zero =>
      exact SymmetricCategory.symmetry _ _
  | succ k ih =>
      change
        (firstAdjacentSwap k ⊗ₘ 𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
            (firstAdjacentSwap k ⊗ₘ 𝟙 (⟨1⟩ : Cob2SymmetricObj)) =
          𝟙 ((⟨k + 2⟩ : Cob2SymmetricObj) ⊗
            (⟨1⟩ : Cob2SymmetricObj))
      rw [Cob2Symmetric.cob2Symmetric_interchange]
      rw [ih]
      simp

/-- The ordered recursive split is invariant under exchanging its first two
boundary outputs and fixing all trailing outputs. -/
theorem split_firstAdjacentSwap (k : ℕ) :
    split (k + 2) ≫ firstAdjacentSwap k = split (k + 2) := by
  induction k with
  | zero =>
      rw [split_succ_succ 0]
      change
        (Cob2Symmetric.comul ≫
            (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj))) ≫
              (β_ (⟨1⟩ : Cob2SymmetricObj)
                (⟨1⟩ : Cob2SymmetricObj)).hom =
          Cob2Symmetric.comul ≫
            (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj))
      rw [MonoidalCategory.id_tensorHom_id]
      let h :
          Cob2Symmetric.comul ≫
              𝟙 ((⟨1⟩ : Cob2SymmetricObj) ⊗
                (⟨1⟩ : Cob2SymmetricObj)) =
            Cob2Symmetric.comul :=
        Category.comp_id _
      exact
        (congrArg
          (fun f => f ≫
            (β_ (⟨1⟩ : Cob2SymmetricObj)
              (⟨1⟩ : Cob2SymmetricObj)).hom) h).trans
          (canonical_comul_cocommutative.trans h.symm)
  | succ k ih =>
      change
        (Cob2Symmetric.comul ≫
            (split (k + 2) ⊗ₘ 𝟙 (⟨1⟩ : Cob2SymmetricObj))) ≫
              (firstAdjacentSwap k ⊗ₘ
                𝟙 (⟨1⟩ : Cob2SymmetricObj)) =
          Cob2Symmetric.comul ≫
            (split (k + 2) ⊗ₘ 𝟙 (⟨1⟩ : Cob2SymmetricObj))
      simp only [Category.assoc]
      rw [Cob2Symmetric.cob2Symmetric_interchange]
      rw [ih]
      simp

/-- The ordered recursive merge is invariant under exchanging its first two
boundary inputs and fixing all trailing inputs. -/
theorem firstAdjacentSwap_merge (k : ℕ) :
    firstAdjacentSwap k ≫ merge (k + 2) = merge (k + 2) := by
  induction k with
  | zero =>
      rw [merge_succ_succ 0]
      change
        (β_ (⟨1⟩ : Cob2SymmetricObj)
            (⟨1⟩ : Cob2SymmetricObj)).hom ≫
            ((𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
              𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
                Cob2Symmetric.mul) =
          (𝟙 (⟨1⟩ : Cob2SymmetricObj) ⊗ₘ
            𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
              Cob2Symmetric.mul
      rw [MonoidalCategory.id_tensorHom_id]
      let h :
          𝟙 ((⟨1⟩ : Cob2SymmetricObj) ⊗
              (⟨1⟩ : Cob2SymmetricObj)) ≫
              Cob2Symmetric.mul =
            Cob2Symmetric.mul :=
        Category.id_comp _
      exact
        (congrArg
          (fun f =>
            (β_ (⟨1⟩ : Cob2SymmetricObj)
              (⟨1⟩ : Cob2SymmetricObj)).hom ≫ f) h).trans
          (canonical_mul_commutative.trans h.symm)
  | succ k ih =>
      change
        (firstAdjacentSwap k ⊗ₘ 𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
            ((merge (k + 2) ⊗ₘ 𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
              Cob2Symmetric.mul) =
          (merge (k + 2) ⊗ₘ 𝟙 (⟨1⟩ : Cob2SymmetricObj)) ≫
            Cob2Symmetric.mul
      rw [← Category.assoc]
      rw [Cob2Symmetric.cob2Symmetric_interchange]
      rw [ih]
      simp

end Cob2Permutation
