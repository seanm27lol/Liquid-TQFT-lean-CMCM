import RequestProject.Cob2SpiderPermutationInvariance
import Mathlib.GroupTheory.Perm.Sign

/-!
# Adjacent-swap words representing arbitrary finite boundary permutations

The earlier boundary-invariance layer absorbs every explicitly represented
word of adjacent swaps.  This file closes the remaining finite-generation
gap.  It gives each stored adjacent boundary swap a precise permutation of
`Fin n`, obtained by transporting its two adjacent source indices across its
stored arity equality.  Word semantics is multiplication in
`Equiv.Perm (Fin n)`.

Mathlib's theorem that adjacent transpositions generate every finite
symmetric group then shows that every permutation has at least one
`BoundarySwapWord` representative.  A noncomputably chosen representative
therefore supplies incoming, outgoing, and two-sided spider absorption for
every finite boundary permutation.

No uniqueness statement is made: this file does not prove that two words
representing the same permutation evaluate to the same Cob2 morphism, and
the chosen representatives are not asserted to form a categorical group
action.  The result remains internal to the algebraic
generators-and-relations source and makes no geometric-bordism claim.
-/

open CategoryTheory MonoidalCategory

noncomputable section

namespace Cob2SpiderPermutationWords

open Cob2BoundaryPermutations
open Cob2Spider
open Cob2SpiderPermutationWords
open Cob2SpiderPermutationInvariance

namespace BoundarySwap

/-- The first index of a stored adjacent swap, before transport to `Fin n`. -/
def sourceLeft {n : ℕ} (s : BoundarySwap n) :
    Fin (boundaryArity s.leading s.trailing) :=
  ⟨s.leading, by
    rw [boundaryArity_eq]
    omega⟩

/-- The second index of a stored adjacent swap, before transport to `Fin n`. -/
def sourceRight {n : ℕ} (s : BoundarySwap n) :
    Fin (boundaryArity s.leading s.trailing) :=
  ⟨s.leading + 1, by
    rw [boundaryArity_eq]
    omega⟩

/-- The first adjacent index transported across the stored arity equality. -/
def targetLeft {n : ℕ} (s : BoundarySwap n) : Fin n :=
  finCongr s.arity_eq s.sourceLeft

/-- The second adjacent index transported across the stored arity equality. -/
def targetRight {n : ℕ} (s : BoundarySwap n) : Fin n :=
  finCongr s.arity_eq s.sourceRight

/-- Permutation semantics of a stored boundary swap.

The adjacent transposition at `s.leading` is transported from
`Fin (boundaryArity s.leading s.trailing)` to `Fin n` using `s.arity_eq`. -/
def permutation {n : ℕ} (s : BoundarySwap n) : Equiv.Perm (Fin n) :=
  Equiv.swap s.targetLeft s.targetRight

/-- The canonical stored swap corresponding to Mathlib's adjacent generator
`swap i.castSucc i.succ` of `Perm (Fin (k + 1))`. -/
def canonicalAdjacent {k : ℕ} (i : Fin k) : BoundarySwap (k + 1) where
  leading := i
  trailing := k - (i + 1)
  arity_eq := by
    rw [boundaryArity_eq]
    omega

@[simp]
theorem canonicalAdjacent_targetLeft {k : ℕ} (i : Fin k) :
    (canonicalAdjacent i).targetLeft = i.castSucc := by
  apply Fin.ext
  rfl

@[simp]
theorem canonicalAdjacent_targetRight {k : ℕ} (i : Fin k) :
    (canonicalAdjacent i).targetRight = i.succ := by
  apply Fin.ext
  rfl

/-- The canonical stored swap has exactly Mathlib's adjacent-transposition
semantics. -/
@[simp]
theorem canonicalAdjacent_permutation {k : ℕ} (i : Fin k) :
    (canonicalAdjacent i).permutation =
      Equiv.swap i.castSucc i.succ := by
  simp [permutation]

end BoundarySwap

namespace BoundarySwapWord

/-- Permutation semantics of a boundary-swap word, using the recursive group
product convention displayed in `permutation_cons`. -/
def permutation {n : ℕ} : BoundarySwapWord n → Equiv.Perm (Fin n)
  | [] => 1
  | s :: w => s.permutation * permutation w

@[simp]
theorem permutation_nil (n : ℕ) :
    permutation ([] : BoundarySwapWord n) = 1 := rfl

@[simp]
theorem permutation_cons {n : ℕ} (s : BoundarySwap n)
    (w : BoundarySwapWord n) :
    permutation (s :: w) = s.permutation * permutation w := rfl

/-- Word concatenation agrees with multiplication of permutation semantics. -/
@[simp]
theorem permutation_append {n : ℕ}
    (w v : BoundarySwapWord n) :
    permutation (w ++ v) = permutation w * permutation v := by
  induction w with
  | nil => simp
  | cons s w ih =>
      simp [ih, mul_assoc]

end BoundarySwapWord

end Cob2SpiderPermutationWords

namespace Cob2FinitePermutationWords

open Cob2Spider
open Cob2SpiderPermutationWords
open Cob2SpiderPermutationWords.BoundarySwapWord
open Cob2SpiderPermutationInvariance

/-- Every permutation of `Fin n` is represented by a finite word of the
stored adjacent boundary swaps. -/
theorem exists_boundarySwapWord (n : ℕ) (p : Equiv.Perm (Fin n)) :
    ∃ w : BoundarySwapWord n, w.permutation = p := by
  cases n with
  | zero =>
      refine ⟨[], ?_⟩
      exact Subsingleton.elim _ _
  | succ k =>
      have hp :
          p ∈ Submonoid.closure
            (Set.range fun i : Fin k =>
              Equiv.swap i.castSucc i.succ) := by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ k]
        exact Submonoid.mem_top p
      induction hp using Submonoid.closure_induction with
      | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact ⟨[BoundarySwap.canonicalAdjacent i], by simp⟩
      | one =>
          exact ⟨[], rfl⟩
      | mul x y hx hy ihx ihy =>
          obtain ⟨wx, hwx⟩ := ihx
          obtain ⟨wy, hwy⟩ := ihy
          exact ⟨wx ++ wy, by simp [hwx, hwy]⟩

/-- A chosen adjacent-swap-word representative of a finite permutation.

No coherence between choices for products is asserted. -/
def representativeWord {n : ℕ} (p : Equiv.Perm (Fin n)) :
    BoundarySwapWord n :=
  Classical.choose (exists_boundarySwapWord n p)

/-- The chosen word represents the requested finite permutation. -/
@[simp]
theorem representativeWord_permutation {n : ℕ}
    (p : Equiv.Perm (Fin n)) :
    (representativeWord p).permutation = p :=
  Classical.choose_spec (exists_boundarySwapWord n p)

/-- The Cob2 endomorphism obtained by evaluating the chosen adjacent-swap
word for a finite permutation.  It is not asserted to be independent of the
chosen word. -/
def representativeHom {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (⟨n⟩ : Cob2SymmetricObj) ⟶ (⟨n⟩ : Cob2SymmetricObj) :=
  (representativeWord p).eval

/-- Every finite incoming boundary permutation has a chosen word whose Cob2
evaluation is absorbed by a connected spider. -/
@[simp]
theorem representativeHom_spider (a b g : ℕ)
    (p : Equiv.Perm (Fin a)) :
    representativeHom p ≫ spider a b g = spider a b g :=
  eval_spider a b g (representativeWord p)

/-- Every finite outgoing boundary permutation has a chosen word whose Cob2
evaluation is absorbed by a connected spider. -/
@[simp]
theorem spider_representativeHom (a b g : ℕ)
    (q : Equiv.Perm (Fin b)) :
    spider a b g ≫ representativeHom q = spider a b g :=
  spider_eval a b g (representativeWord q)

/-- Connected spiders absorb chosen adjacent-swap-word representatives of
arbitrary finite permutations at both boundaries. -/
@[simp]
theorem representativeHom_spider_representativeHom (a b g : ℕ)
    (p : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)) :
    representativeHom p ≫ spider a b g ≫ representativeHom q =
      spider a b g :=
  eval_spider_eval a b g (representativeWord p) (representativeWord q)

end Cob2FinitePermutationWords
