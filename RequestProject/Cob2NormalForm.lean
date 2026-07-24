import RequestProject.Cob2Spider

/-!
# Component-and-genus codes for algebraic Cob2 normal forms

This file introduces the finite combinatorial data expected to classify
morphisms in the symmetric Frobenius presentation.  A label records one
connected component, the two boundary maps record which component contains
each incoming and outgoing circle, and each component carries a genus.
Labels missed by both boundary maps represent closed components.

Codes are quotiented by component relabeling.  This file establishes the
basic quotient and its elementary representatives; it does not yet define
composition, prove that raw words have these normal forms, or identify the
codes with smooth surfaces.
-/

open CategoryTheory
open scoped BigOperators

noncomputable section

namespace Cob2NormalForm

/-- A finite component-and-genus code with `a` incoming and `b` outgoing
boundary circles. -/
structure SurfaceCode (a b : ℕ) where
  ncomp : ℕ
  inComp : Fin a → Fin ncomp
  outComp : Fin b → Fin ncomp
  genus : Fin ncomp → ℕ

namespace SurfaceCode

/-- Two codes are related when a bijection of component labels preserves
both boundary assignments and every genus. -/
def Rel {a b : ℕ} (s t : SurfaceCode a b) : Prop :=
  ∃ e : Fin s.ncomp ≃ Fin t.ncomp,
    (∀ i, e (s.inComp i) = t.inComp i) ∧
    (∀ j, e (s.outComp j) = t.outComp j) ∧
    (∀ k, t.genus (e k) = s.genus k)

theorem rel_refl {a b : ℕ} (s : SurfaceCode a b) : Rel s s := by
  exact ⟨Equiv.refl _, by simp, by simp, by simp⟩

theorem rel_symm {a b : ℕ} {s t : SurfaceCode a b} (h : Rel s t) :
    Rel t s := by
  rcases h with ⟨e, hin, hout, hgenus⟩
  refine ⟨e.symm, ?_, ?_, ?_⟩
  · intro i
    simpa using congrArg e.symm (hin i).symm
  · intro j
    simpa using congrArg e.symm (hout j).symm
  · intro k
    simpa using (hgenus (e.symm k)).symm

theorem rel_trans {a b : ℕ} {s t u : SurfaceCode a b}
    (hst : Rel s t) (htu : Rel t u) : Rel s u := by
  rcases hst with ⟨e, ein, eout, egenus⟩
  rcases htu with ⟨f, fin, fout, fgenus⟩
  refine ⟨e.trans f, ?_, ?_, ?_⟩
  · intro i
    simp only [Equiv.trans_apply]
    rw [ein, fin]
  · intro j
    simp only [Equiv.trans_apply]
    rw [eout, fout]
  · intro k
    simp only [Equiv.trans_apply]
    rw [fgenus, egenus]

/-- Component relabeling is an equivalence relation on surface codes. -/
def setoid (a b : ℕ) : Setoid (SurfaceCode a b) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

/-- The empty code, representing no components and no boundary. -/
def empty : SurfaceCode 0 0 where
  ncomp := 0
  inComp := Fin.elim0
  outComp := Fin.elim0
  genus := Fin.elim0

/-- A one-component code with arbitrary boundary arities and genus. -/
def connected (a b g : ℕ) : SurfaceCode a b where
  ncomp := 1
  inComp := fun _ => 0
  outComp := fun _ => 0
  genus := fun _ => g

/-- The code for `n` disjoint identity cylinders. -/
def identity (n : ℕ) : SurfaceCode n n where
  ncomp := n
  inComp := id
  outComp := id
  genus := fun _ => 0

/-- The component code of the block symmetry. -/
def swap (a b : ℕ) : SurfaceCode (a + b) (b + a) where
  ncomp := a + b
  inComp := id
  outComp := finAddFlip.symm
  genus := fun _ => 0

/-- Disjoint union of component codes. -/
def tensor {a b c d : ℕ} (s : SurfaceCode a b) (t : SurfaceCode c d) :
    SurfaceCode (a + c) (b + d) where
  ncomp := s.ncomp + t.ncomp
  inComp := Fin.addCases
    (fun i => Fin.castAdd t.ncomp (s.inComp i))
    (fun j => Fin.natAdd s.ncomp (t.inComp j))
  outComp := Fin.addCases
    (fun i => Fin.castAdd t.ncomp (s.outComp i))
    (fun j => Fin.natAdd s.ncomp (t.outComp j))
  genus := Fin.addCases s.genus t.genus

/-- Block sum of two component relabelings. -/
def sumRelabel {m m' n n' : ℕ} (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n') :
    Fin (m + n) ≃ Fin (m' + n') :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e f).trans finSumFinEquiv)

@[simp]
theorem sumRelabel_castAdd {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n') (i : Fin m) :
    sumRelabel e f (Fin.castAdd n i) = Fin.castAdd n' (e i) := by
  simp [sumRelabel]

@[simp]
theorem sumRelabel_natAdd {m m' n n' : ℕ}
    (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n') (j : Fin n) :
    sumRelabel e f (Fin.natAdd m j) = Fin.natAdd m' (f j) := by
  simp [sumRelabel]

/-- Disjoint union respects component relabeling. -/
theorem rel_tensor {a b c d : ℕ}
    {s s' : SurfaceCode a b} {t t' : SurfaceCode c d}
    (hs : Rel s s') (ht : Rel t t') :
    Rel (tensor s t) (tensor s' t') := by
  rcases hs with ⟨e, ein, eout, egenus⟩
  rcases ht with ⟨f, fin, fout, fgenus⟩
  refine ⟨sumRelabel e f, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro k
      simp [tensor, ein]
    · intro k
      simp [tensor, fin]
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp [tensor, eout]
    · intro k
      simp [tensor, fout]
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simp [tensor, egenus]
    · intro j
      simp [tensor, fgenus]

end SurfaceCode

/-- Component-and-genus normal-form candidates, modulo component
relabeling. -/
def SurfaceNF (a b : ℕ) :=
  Quotient (SurfaceCode.setoid a b)

namespace SurfaceNF

/-- The number of connected components is invariant under relabeling. -/
def componentCount {a b : ℕ} : SurfaceNF a b → ℕ :=
  Quotient.lift SurfaceCode.ncomp (fun s t h => by
    rcases h with ⟨e, _, _, _⟩
    simpa using Fintype.card_congr e)

/-- Total genus is invariant under component relabeling.  It will separate
the genus parameter in the connected normal-form corollary. -/
def totalGenus {a b : ℕ} : SurfaceNF a b → ℕ :=
  Quotient.lift (fun s => ∑ k, s.genus k) (fun s t h => by
    rcases h with ⟨e, _, _, hgenus⟩
    calc
      (∑ k, s.genus k) = ∑ k, t.genus (e k) := by
        apply Finset.sum_congr rfl
        intro k _
        exact (hgenus k).symm
      _ = ∑ k, t.genus k := e.sum_comp t.genus)

@[simp]
theorem componentCount_mk {a b : ℕ} (s : SurfaceCode a b) :
    componentCount (Quotient.mk (SurfaceCode.setoid a b) s) = s.ncomp := rfl

@[simp]
theorem totalGenus_mk {a b : ℕ} (s : SurfaceCode a b) :
    totalGenus (Quotient.mk (SurfaceCode.setoid a b) s) =
      ∑ k, s.genus k := rfl

/-- The class of the empty component code. -/
def empty : SurfaceNF 0 0 :=
  Quotient.mk (SurfaceCode.setoid 0 0) SurfaceCode.empty

/-- The class of the canonical one-component genus code. -/
def connected (a b g : ℕ) : SurfaceNF a b :=
  Quotient.mk (SurfaceCode.setoid a b) (SurfaceCode.connected a b g)

/-- The class of the identity-cylinder code. -/
def identity (n : ℕ) : SurfaceNF n n :=
  Quotient.mk (SurfaceCode.setoid n n) (SurfaceCode.identity n)

/-- The multiplication-generator code. -/
def mul : SurfaceNF 2 1 :=
  connected 2 1 0

/-- The unit-generator code. -/
def unit : SurfaceNF 0 1 :=
  connected 0 1 0

/-- The comultiplication-generator code. -/
def comul : SurfaceNF 1 2 :=
  connected 1 2 0

/-- The counit-generator code. -/
def counit : SurfaceNF 1 0 :=
  connected 1 0 0

/-- The block-symmetry code. -/
def swap (a b : ℕ) : SurfaceNF (a + b) (b + a) :=
  Quotient.mk (SurfaceCode.setoid (a + b) (b + a))
    (SurfaceCode.swap a b)

/-- Disjoint union descends to normal-form candidates. -/
def tensor {a b c d : ℕ} (s : SurfaceNF a b) (t : SurfaceNF c d) :
    SurfaceNF (a + c) (b + d) :=
  Quotient.map₂ SurfaceCode.tensor
    (fun _ _ hs _ _ ht => SurfaceCode.rel_tensor hs ht) s t

@[simp]
theorem componentCount_tensor {a b c d : ℕ}
    (s : SurfaceNF a b) (t : SurfaceNF c d) :
    componentCount (tensor s t) = componentCount s + componentCount t := by
  induction s using Quotient.inductionOn with
  | _ s =>
      induction t using Quotient.inductionOn with
      | _ t => rfl

@[simp]
theorem componentCount_empty : componentCount empty = 0 := rfl

@[simp]
theorem componentCount_connected (a b g : ℕ) :
    componentCount (connected a b g) = 1 := rfl

@[simp]
theorem totalGenus_connected (a b g : ℕ) :
    totalGenus (connected a b g) = g := by
  simp [totalGenus, connected, SurfaceCode.connected]

@[simp]
theorem componentCount_identity (n : ℕ) :
    componentCount (identity n) = n := rfl

end SurfaceNF

end Cob2NormalForm
