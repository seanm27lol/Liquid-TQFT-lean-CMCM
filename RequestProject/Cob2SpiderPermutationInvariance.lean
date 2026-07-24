import RequestProject.Cob2SpiderPermutationWords

/-!
# Boundary-permutation invariance of ordered connected spiders

Finite words of represented boundary-adjacent swaps are absorbed at both
ends of every ordered connected spider.  Incoming words disappear against
the merge comb, while outgoing words disappear against the split comb.
The two facts combine to give simultaneous invariance at both boundaries.

The proofs use only the existing spider factorization, the word-level
merge/split absorption theorems, and categorical associativity.  No raw word
is unfolded and no presentation relation is added.

This covers words represented by `BoundarySwapWord`.  It does not yet prove
that every `Equiv.Perm (Fin n)` has such a representation, prove an
arbitrary-word spider normal form, or identify the algebraic source with a
geometric bordism category.
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace Cob2SpiderPermutationInvariance

open Cob2Spider
open Cob2SpiderPermutationWords
open Cob2SpiderPermutationWords.BoundarySwapWord

/-- A represented incoming boundary-permutation word is absorbed by every
ordered connected spider. -/
@[simp]
theorem eval_spider (a b g : ℕ) (p : BoundarySwapWord a) :
    p.eval ≫ spider a b g = spider a b g := by
  rw [spider_eq]
  simp only [Category.assoc]
  slice_lhs 1 2 =>
    rw [eval_merge]
  simp only [Category.assoc]

/-- Every ordered connected spider absorbs a represented outgoing
boundary-permutation word. -/
@[simp]
theorem spider_eval (a b g : ℕ) (q : BoundarySwapWord b) :
    spider a b g ≫ q.eval = spider a b g := by
  rw [spider_eq]
  slice_lhs 3 4 =>
    rw [split_eval]
  simp only [Category.assoc]

/-- Ordered connected spiders are simultaneously invariant under represented
incoming and outgoing boundary-permutation words. -/
@[simp]
theorem eval_spider_eval (a b g : ℕ)
    (p : BoundarySwapWord a) (q : BoundarySwapWord b) :
    p.eval ≫ spider a b g ≫ q.eval = spider a b g := by
  rw [spider_eval, eval_spider]

end Cob2SpiderPermutationInvariance
