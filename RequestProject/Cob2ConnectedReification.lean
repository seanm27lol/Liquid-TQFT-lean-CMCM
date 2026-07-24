import RequestProject.Cob2SurfaceSignature

/-!
# Reifying connected surface codes by ordered spiders

This file connects two algebraic tracks already developed in the project:
the component-and-genus signature of raw `Cob2Mor` words and the canonical
ordered connected spiders.  It computes the signature of the merge comb,
each handle, the split comb, and finally the complete spider.

The calculation is uniform in the external arities.  In particular it
includes closed spiders and words with only incoming or only outgoing
boundary circles.  It proves that every canonical one-component surface
code is represented by an explicit algebraic word (and by its class in the
original commutative-Frobenius quotient).

This is a connected-code reification result.  It does not assert that every
connected raw word is equal to a spider, classify arbitrary raw words, or
identify the algebraic presentation with the geometric bordism category.
-/

noncomputable section

namespace Cob2NormalForm

open CategoryTheory

namespace Cob2Mor

/-- The positive multiplication comb has one genus-zero component. -/
@[simp]
theorem signature_mergePositive (k : ℕ) :
    signature (Cob2Spider.mergePositive k) =
      SurfaceNF.connected (k + 1) 1 0 := by
  induction k with
  | zero =>
      exact SurfaceNF.identity_one_eq_connected
  | succ k ih =>
      simp only [Cob2Spider.mergePositive, signature_comp,
        signature_tensor, signature_mul, signature_id]
      rw [ih, SurfaceNF.identity_one_eq_connected]
      simpa [Nat.add_assoc] using
        SurfaceNF.tensor_connected_pair_comp_connected (k + 1) 1 1

/-- The nullary unit and all positive multiplication combs have the
canonical one-component genus-zero signature. -/
@[simp]
theorem signature_mergeWord (a : ℕ) :
    signature (Cob2Spider.mergeWord a) =
      SurfaceNF.connected a 1 0 := by
  cases a with
  | zero => rfl
  | succ a =>
      simp [Cob2Spider.mergeWord]

/-- The positive comultiplication comb has one genus-zero component. -/
@[simp]
theorem signature_splitPositive (k : ℕ) :
    signature (Cob2Spider.splitPositive k) =
      SurfaceNF.connected 1 (k + 1) 0 := by
  induction k with
  | zero =>
      exact SurfaceNF.identity_one_eq_connected
  | succ k ih =>
      simp only [Cob2Spider.splitPositive, signature_comp,
        signature_tensor, signature_comul, signature_id]
      rw [ih, SurfaceNF.identity_one_eq_connected]
      simpa [Nat.add_assoc] using
        SurfaceNF.connected_comp_tensor_connected_pair 1 (k + 1) 1

/-- The nullary counit and all positive comultiplication combs have the
canonical one-component genus-zero signature. -/
@[simp]
theorem signature_splitWord (b : ℕ) :
    signature (Cob2Spider.splitWord b) =
      SurfaceNF.connected 1 b 0 := by
  cases b with
  | zero => rfl
  | succ b =>
      simp [Cob2Spider.splitWord]

/-- One comultiplication followed by multiplication contributes one graph
cycle and hence one unit of genus. -/
@[simp]
theorem signature_handleStep :
    signature (.comp _root_.Cob2Mor.δ _root_.Cob2Mor.μ) =
      SurfaceNF.connected 1 1 1 := by
  simp only [signature_comp, signature_comul, signature_mul]
  simpa using SurfaceNF.comp_connected 1 2 1 0 0 (by omega)

/-- Iterating the handle word records exactly the iteration count as genus. -/
@[simp]
theorem signature_handleWord (g : ℕ) :
    signature (Cob2Spider.handleWord g) =
      SurfaceNF.connected 1 1 g := by
  induction g with
  | zero =>
      exact SurfaceNF.identity_one_eq_connected
  | succ g ih =>
      change
        SurfaceNF.comp
            (signature (Cob2Spider.handleWord g))
            (signature (.comp _root_.Cob2Mor.δ _root_.Cob2Mor.μ)) =
          SurfaceNF.connected 1 1 (g + 1)
      rw [ih, signature_handleStep]
      simpa [Nat.add_assoc] using
        SurfaceNF.comp_connected 1 1 1 g 1 (by omega)

/-- The raw ordered spider has precisely the canonical connected
component-and-genus signature.  The statement includes all zero-arity edge
cases. -/
@[simp]
theorem signature_spiderWord (a b g : ℕ) :
    signature (Cob2Spider.spiderWord a b g) =
      SurfaceNF.connected a b g := by
  simp only [Cob2Spider.spiderWord, signature_comp, signature_mergeWord,
    signature_handleWord, signature_splitWord]
  calc
    SurfaceNF.comp
          (SurfaceNF.comp (SurfaceNF.connected a 1 0)
            (SurfaceNF.connected 1 1 g))
          (SurfaceNF.connected 1 b 0) =
        SurfaceNF.comp (SurfaceNF.connected a 1 g)
          (SurfaceNF.connected 1 b 0) := by
            congr 1
            simpa using
              SurfaceNF.comp_connected a 1 1 0 g (by omega)
    _ = SurfaceNF.connected a b g := by
      simpa using SurfaceNF.comp_connected a 1 b g 0 (by omega)

end Cob2Mor

namespace Cob2Hom

/-- The class of the ordered spider in the original Frobenius quotient has
the same connected surface signature as its raw representative. -/
@[simp]
theorem signature_spiderClass (a b g : ℕ) :
    signature
        (⟦Cob2Spider.spiderWord a b g⟧ : _root_.Cob2Hom a b) =
      SurfaceNF.connected a b g := by
  exact Cob2Mor.signature_spiderWord a b g

/-- Every canonical connected surface code is reified by the explicitly
given ordered spider class. -/
theorem connected_reified (a b g : ℕ) :
    ∃ f : _root_.Cob2Hom a b,
      signature f = SurfaceNF.connected a b g :=
  ⟨⟦Cob2Spider.spiderWord a b g⟧, signature_spiderClass a b g⟩

end Cob2Hom

namespace SurfaceNF

/-- At fixed boundary arities, the genus parameter of a connected code is
injective. -/
theorem connected_genus_injective {a b g h : ℕ}
    (e : connected a b g = connected a b h) :
    g = h := by
  simpa using congrArg totalGenus e

end SurfaceNF

end Cob2NormalForm
