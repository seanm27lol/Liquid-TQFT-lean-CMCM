import RequestProject.Cob2SurfaceCategory

/-!
# Disjoint union and composition of surface normal forms

This file proves that the disjoint-union operation on component-and-genus
normal forms is compatible with the graph-gluing composition constructed in
`Cob2SurfaceCategory`.

The proof first splits the gluing graph of two block sums into the disjoint
sum of the two original gluing graphs.  Parallel middle circles and genus
labels are retained componentwise.  This file declares the resulting
uncurried bifunctor, but not a `MonoidalCategory` instance; the construction
remains a category of algebraic normal-form codes, not a geometric bordism
category.
-/

noncomputable section

namespace Cob2NormalForm

open CategoryTheory

namespace SurfaceCode

section TensorComposition

variable {a b c a' b' c' : ℕ}
  (s : SurfaceCode a b) (t : SurfaceCode b c)
  (r : SurfaceCode a' b') (u : SurfaceCode b' c')

/-- Embed a vertex of the first gluing graph into the first block of the
block-sum gluing graph. -/
def tensorLeftGlueVertex :
    GlueVertex s t → GlueVertex (tensor s r) (tensor t u)
  | Sum.inl i => Sum.inl (Fin.castAdd r.ncomp i)
  | Sum.inr j => Sum.inr (Fin.castAdd u.ncomp j)

/-- Embed a vertex of the second gluing graph into the second block of the
block-sum gluing graph. -/
def tensorRightGlueVertex :
    GlueVertex r u → GlueVertex (tensor s r) (tensor t u)
  | Sum.inl i => Sum.inl (Fin.natAdd s.ncomp i)
  | Sum.inr j => Sum.inr (Fin.natAdd t.ncomp j)

/-- The old vertices of a block-sum gluing are canonically the disjoint sum
of the old vertices of the two original gluing graphs. -/
def tensorGlueVertexEquiv :
    GlueVertex (tensor s r) (tensor t u) ≃
      GlueVertex s t ⊕ GlueVertex r u where
  toFun
    | Sum.inl k =>
        Fin.addCases
          (fun i => Sum.inl (Sum.inl i))
          (fun j => Sum.inr (Sum.inl j)) k
    | Sum.inr k =>
        Fin.addCases
          (fun i => Sum.inl (Sum.inr i))
          (fun j => Sum.inr (Sum.inr j)) k
  invFun
    | Sum.inl (Sum.inl i) =>
        Sum.inl (Fin.castAdd r.ncomp i)
    | Sum.inl (Sum.inr j) =>
        Sum.inr (Fin.castAdd u.ncomp j)
    | Sum.inr (Sum.inl i) =>
        Sum.inl (Fin.natAdd s.ncomp i)
    | Sum.inr (Sum.inr j) =>
        Sum.inr (Fin.natAdd t.ncomp j)
  left_inv := by
    intro x
    rcases x with k | l
    · refine Fin.addCases ?_ ?_ k <;> intro i <;> simp
    · refine Fin.addCases ?_ ?_ l <;> intro j <;> simp
  right_inv := by
    intro x
    rcases x with (i | j) | (i | j) <;> simp

@[simp]
theorem tensorGlueVertexEquiv_left (x : GlueVertex s t) :
    tensorGlueVertexEquiv s t r u
        (tensorLeftGlueVertex s t r u x) = Sum.inl x := by
  rcases x with i | j <;>
    simp [tensorGlueVertexEquiv, tensorLeftGlueVertex]

@[simp]
theorem tensorGlueVertexEquiv_right (x : GlueVertex r u) :
    tensorGlueVertexEquiv s t r u
        (tensorRightGlueVertex s t r u x) = Sum.inr x := by
  rcases x with i | j <;>
    simp [tensorGlueVertexEquiv, tensorRightGlueVertex]

private theorem tensorLeft_connected
    {x y : GlueVertex s t}
    (h : (glueSetoid s t) x y) :
    (glueSetoid (tensor s r) (tensor t u))
      (tensorLeftGlueVertex s t r u x)
      (tensorLeftGlueVertex s t r u y) := by
  change Relation.EqvGen (GlueStep s t) x y at h
  change Relation.EqvGen
    (GlueStep (tensor s r) (tensor t u)) _ _
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨i, hxy⟩
      apply Relation.EqvGen.rel
      refine ⟨Fin.castAdd b' i, ?_⟩
      have hx : x = Sum.inl (s.outComp i) :=
        congrArg Prod.fst hxy
      have hy : y = Sum.inr (t.inComp i) :=
        congrArg Prod.snd hxy
      subst x
      subst y
      simp [edgeEnds, tensor, tensorLeftGlueVertex]
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ihxy ihyz =>
      exact Relation.EqvGen.trans _ _ _ ihxy ihyz

private theorem tensorRight_connected
    {x y : GlueVertex r u}
    (h : (glueSetoid r u) x y) :
    (glueSetoid (tensor s r) (tensor t u))
      (tensorRightGlueVertex s t r u x)
      (tensorRightGlueVertex s t r u y) := by
  change Relation.EqvGen (GlueStep r u) x y at h
  change Relation.EqvGen
    (GlueStep (tensor s r) (tensor t u)) _ _
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨j, hxy⟩
      apply Relation.EqvGen.rel
      refine ⟨Fin.natAdd b j, ?_⟩
      have hx : x = Sum.inl (r.outComp j) :=
        congrArg Prod.fst hxy
      have hy : y = Sum.inr (u.inComp j) :=
        congrArg Prod.snd hxy
      subst x
      subst y
      simp [edgeEnds, tensor, tensorRightGlueVertex]
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ihxy ihyz =>
      exact Relation.EqvGen.trans _ _ _ ihxy ihyz

/-- Embed a component of the first gluing graph into the block-sum gluing
graph. -/
def tensorLeftGlueComponent :
    GlueComponent s t →
      GlueComponent (tensor s r) (tensor t u) :=
  Quotient.map' (tensorLeftGlueVertex s t r u)
    (fun _ _ h => tensorLeft_connected s t r u h)

/-- Embed a component of the second gluing graph into the block-sum gluing
graph. -/
def tensorRightGlueComponent :
    GlueComponent r u →
      GlueComponent (tensor s r) (tensor t u) :=
  Quotient.map' (tensorRightGlueVertex s t r u)
    (fun _ _ h => tensorRight_connected s t r u h)

@[simp]
theorem tensorLeftGlueComponent_vertex (x : GlueVertex s t) :
    tensorLeftGlueComponent s t r u (vertexComponent s t x) =
      vertexComponent (tensor s r) (tensor t u)
        (tensorLeftGlueVertex s t r u x) :=
  rfl

@[simp]
theorem tensorRightGlueComponent_vertex (x : GlueVertex r u) :
    tensorRightGlueComponent s t r u (vertexComponent r u x) =
      vertexComponent (tensor s r) (tensor t u)
        (tensorRightGlueVertex s t r u x) :=
  rfl

/-- Send an old vertex in the block-sum gluing graph to the corresponding
component of one of the two original graphs. -/
def tensorGlueVertexTarget :
    GlueVertex (tensor s r) (tensor t u) →
      GlueComponent s t ⊕ GlueComponent r u
  | Sum.inl k =>
      Fin.addCases
        (fun i => Sum.inl (vertexComponent s t (Sum.inl i)))
        (fun j => Sum.inr (vertexComponent r u (Sum.inl j))) k
  | Sum.inr k =>
      Fin.addCases
        (fun i => Sum.inl (vertexComponent s t (Sum.inr i)))
        (fun j => Sum.inr (vertexComponent r u (Sum.inr j))) k

@[simp]
theorem tensorGlueVertexTarget_left (x : GlueVertex s t) :
    tensorGlueVertexTarget s t r u
        (tensorLeftGlueVertex s t r u x) =
      Sum.inl (vertexComponent s t x) := by
  rcases x with i | j <;>
    simp [tensorGlueVertexTarget, tensorLeftGlueVertex]

@[simp]
theorem tensorGlueVertexTarget_right (x : GlueVertex r u) :
    tensorGlueVertexTarget s t r u
        (tensorRightGlueVertex s t r u x) =
      Sum.inr (vertexComponent r u x) := by
  rcases x with i | j <;>
    simp [tensorGlueVertexTarget, tensorRightGlueVertex]

private theorem tensorGlueVertexTarget_eq_of_connected
    {x y : GlueVertex (tensor s r) (tensor t u)}
    (h : (glueSetoid (tensor s r) (tensor t u)) x y) :
    tensorGlueVertexTarget s t r u x =
      tensorGlueVertexTarget s t r u y := by
  change Relation.EqvGen
    (GlueStep (tensor s r) (tensor t u)) x y at h
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨k, hxy⟩
      have hx : x = Sum.inl ((tensor s r).outComp k) :=
        congrArg Prod.fst hxy
      have hy : y = Sum.inr ((tensor t u).inComp k) :=
        congrArg Prod.snd hxy
      subst x
      subst y
      refine Fin.addCases ?_ ?_ k
      · intro i
        simpa [tensor, tensorGlueVertexTarget] using
          congrArg
            (Sum.inl :
              GlueComponent s t →
                GlueComponent s t ⊕ GlueComponent r u)
            (edgeEnds_same_component s t i)
      · intro j
        simpa [tensor, tensorGlueVertexTarget] using
          congrArg
            (Sum.inr :
              GlueComponent r u →
                GlueComponent s t ⊕ GlueComponent r u)
            (edgeEnds_same_component r u j)
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- Split a block-sum gluing component into the corresponding component of
one of the two original gluing graphs. -/
def tensorGlueComponentTarget :
    GlueComponent (tensor s r) (tensor t u) →
      GlueComponent s t ⊕ GlueComponent r u :=
  Quotient.lift (tensorGlueVertexTarget s t r u)
    (fun _ _ h => tensorGlueVertexTarget_eq_of_connected s t r u h)

@[simp]
theorem tensorGlueComponentTarget_vertex
    (x : GlueVertex (tensor s r) (tensor t u)) :
    tensorGlueComponentTarget s t r u
        (vertexComponent (tensor s r) (tensor t u) x) =
      tensorGlueVertexTarget s t r u x :=
  rfl

/-- The block-sum gluing graph is the disjoint sum of its two input gluing
graphs, at the level of connected components. -/
def tensorGlueComponentEquiv :
    GlueComponent (tensor s r) (tensor t u) ≃
      GlueComponent s t ⊕ GlueComponent r u where
  toFun := tensorGlueComponentTarget s t r u
  invFun := Sum.elim
    (tensorLeftGlueComponent s t r u)
    (tensorRightGlueComponent s t r u)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
        rcases x with k | l
        · refine Fin.addCases ?_ ?_ k
          · intro i
            simp [tensorGlueComponentTarget, tensorGlueVertexTarget,
              tensorLeftGlueComponent, Quotient.map', Quot.map,
              tensorLeftGlueVertex, vertexComponent] <;> rfl
          · intro j
            simp [tensorGlueComponentTarget, tensorGlueVertexTarget,
              tensorRightGlueComponent, Quotient.map', Quot.map,
              tensorRightGlueVertex, vertexComponent] <;> rfl
        · refine Fin.addCases ?_ ?_ l
          · intro i
            simp [tensorGlueComponentTarget, tensorGlueVertexTarget,
              tensorLeftGlueComponent, Quotient.map', Quot.map,
              tensorLeftGlueVertex, vertexComponent] <;> rfl
          · intro j
            simp [tensorGlueComponentTarget, tensorGlueVertexTarget,
              tensorRightGlueComponent, Quotient.map', Quot.map,
              tensorRightGlueVertex, vertexComponent] <;> rfl
  right_inv := by
    intro q
    rcases q with p | p
    · induction p using Quotient.inductionOn with
      | _ x =>
          change tensorGlueVertexTarget s t r u
              (tensorLeftGlueVertex s t r u x) =
            Sum.inl (vertexComponent s t x)
          exact tensorGlueVertexTarget_left s t r u x
    · induction p using Quotient.inductionOn with
      | _ x =>
          change tensorGlueVertexTarget s t r u
              (tensorRightGlueVertex s t r u x) =
            Sum.inr (vertexComponent r u x)
          exact tensorGlueVertexTarget_right s t r u x

@[simp]
theorem tensorGlueComponentEquiv_left
    (p : GlueComponent s t) :
    tensorGlueComponentEquiv s t r u
        (tensorLeftGlueComponent s t r u p) = Sum.inl p :=
  (tensorGlueComponentEquiv s t r u).apply_symm_apply (Sum.inl p)

@[simp]
theorem tensorGlueComponentEquiv_right
    (p : GlueComponent r u) :
    tensorGlueComponentEquiv s t r u
        (tensorRightGlueComponent s t r u p) = Sum.inr p :=
  (tensorGlueComponentEquiv s t r u).apply_symm_apply (Sum.inr p)

@[simp]
theorem tensorGlueComponentEquiv_vertex
    (x : GlueVertex (tensor s r) (tensor t u)) :
    tensorGlueComponentEquiv s t r u
        (vertexComponent (tensor s r) (tensor t u) x) =
      Sum.map (vertexComponent s t) (vertexComponent r u)
        (tensorGlueVertexEquiv s t r u x) := by
  change tensorGlueVertexTarget s t r u x =
    Sum.map (vertexComponent s t) (vertexComponent r u)
      (tensorGlueVertexEquiv s t r u x)
  rcases x with k | l
  · refine Fin.addCases ?_ ?_ k
    · intro i
      simp [tensorGlueVertexTarget, tensorGlueVertexEquiv]
    · intro j
      simp [tensorGlueVertexTarget, tensorGlueVertexEquiv]
  · refine Fin.addCases ?_ ?_ l
    · intro i
      simp [tensorGlueVertexTarget, tensorGlueVertexEquiv]
    · intro j
      simp [tensorGlueVertexTarget, tensorGlueVertexEquiv]

theorem tensorLeft_vertex_mem_iff
    (p : GlueComponent s t) (x : GlueVertex s t) :
    vertexComponent (tensor s r) (tensor t u)
        (tensorLeftGlueVertex s t r u x) =
        tensorLeftGlueComponent s t r u p ↔
      vertexComponent s t x = p := by
  constructor
  · intro h
    have h' := congrArg (tensorGlueComponentEquiv s t r u) h
    simpa using h'
  · intro h
    apply (tensorGlueComponentEquiv s t r u).injective
    simpa using congrArg
      (Sum.inl :
        GlueComponent s t → GlueComponent s t ⊕ GlueComponent r u) h

theorem tensorRight_vertex_mem_iff
    (p : GlueComponent r u) (x : GlueVertex r u) :
    vertexComponent (tensor s r) (tensor t u)
        (tensorRightGlueVertex s t r u x) =
        tensorRightGlueComponent s t r u p ↔
      vertexComponent r u x = p := by
  constructor
  · intro h
    have h' := congrArg (tensorGlueComponentEquiv s t r u) h
    simpa using h'
  · intro h
    apply (tensorGlueComponentEquiv s t r u).injective
    simpa using congrArg
      (Sum.inr :
        GlueComponent r u → GlueComponent s t ⊕ GlueComponent r u) h

theorem tensorRight_vertex_ne_left
    (p : GlueComponent s t) (x : GlueVertex r u) :
    vertexComponent (tensor s r) (tensor t u)
        (tensorRightGlueVertex s t r u x) ≠
      tensorLeftGlueComponent s t r u p := by
  intro h
  have h' := congrArg (tensorGlueComponentEquiv s t r u) h
  simpa using h'

theorem tensorLeft_vertex_ne_right
    (p : GlueComponent r u) (x : GlueVertex s t) :
    vertexComponent (tensor s r) (tensor t u)
        (tensorLeftGlueVertex s t r u x) ≠
      tensorRightGlueComponent s t r u p := by
  intro h
  have h' := congrArg (tensorGlueComponentEquiv s t r u) h
  simpa using h'

@[simp]
theorem tensorLeft_inl_castAdd_mem_iff
    (p : GlueComponent s t) (i : Fin s.ncomp) :
    vertexComponent (tensor s r) (tensor t u)
        (Sum.inl (Fin.castAdd r.ncomp i)) =
        tensorLeftGlueComponent s t r u p ↔
      vertexComponent s t (Sum.inl i) = p := by
  simpa [tensorLeftGlueVertex] using
    tensorLeft_vertex_mem_iff s t r u p (Sum.inl i)

@[simp]
theorem tensorLeft_inr_castAdd_mem_iff
    (p : GlueComponent s t) (j : Fin t.ncomp) :
    vertexComponent (tensor s r) (tensor t u)
        (Sum.inr (Fin.castAdd u.ncomp j)) =
        tensorLeftGlueComponent s t r u p ↔
      vertexComponent s t (Sum.inr j) = p := by
  simpa [tensorLeftGlueVertex] using
    tensorLeft_vertex_mem_iff s t r u p (Sum.inr j)

@[simp]
theorem tensorRight_inl_natAdd_ne_left
    (p : GlueComponent s t) (i : Fin r.ncomp) :
    vertexComponent (tensor s r) (tensor t u)
        (Sum.inl (Fin.natAdd s.ncomp i)) ≠
      tensorLeftGlueComponent s t r u p := by
  simpa [tensorRightGlueVertex] using
    tensorRight_vertex_ne_left s t r u p (Sum.inl i)

@[simp]
theorem tensorRight_inr_natAdd_ne_left
    (p : GlueComponent s t) (j : Fin u.ncomp) :
    vertexComponent (tensor s r) (tensor t u)
        (Sum.inr (Fin.natAdd t.ncomp j)) ≠
      tensorLeftGlueComponent s t r u p := by
  simpa [tensorRightGlueVertex] using
    tensorRight_vertex_ne_left s t r u p (Sum.inr j)

@[simp]
theorem tensorLeft_inl_castAdd_ne_right
    (p : GlueComponent r u) (i : Fin s.ncomp) :
    vertexComponent (tensor s r) (tensor t u)
        (Sum.inl (Fin.castAdd r.ncomp i)) ≠
      tensorRightGlueComponent s t r u p := by
  simpa [tensorLeftGlueVertex] using
    tensorLeft_vertex_ne_right s t r u p (Sum.inl i)

@[simp]
theorem tensorLeft_inr_castAdd_ne_right
    (p : GlueComponent r u) (j : Fin t.ncomp) :
    vertexComponent (tensor s r) (tensor t u)
        (Sum.inr (Fin.castAdd u.ncomp j)) ≠
      tensorRightGlueComponent s t r u p := by
  simpa [tensorLeftGlueVertex] using
    tensorLeft_vertex_ne_right s t r u p (Sum.inr j)

@[simp]
theorem tensorRight_inl_natAdd_mem_iff
    (p : GlueComponent r u) (i : Fin r.ncomp) :
    vertexComponent (tensor s r) (tensor t u)
        (Sum.inl (Fin.natAdd s.ncomp i)) =
        tensorRightGlueComponent s t r u p ↔
      vertexComponent r u (Sum.inl i) = p := by
  simpa [tensorRightGlueVertex] using
    tensorRight_vertex_mem_iff s t r u p (Sum.inl i)

@[simp]
theorem tensorRight_inr_natAdd_mem_iff
    (p : GlueComponent r u) (j : Fin u.ncomp) :
    vertexComponent (tensor s r) (tensor t u)
        (Sum.inr (Fin.natAdd t.ncomp j)) =
        tensorRightGlueComponent s t r u p ↔
      vertexComponent r u (Sum.inr j) = p := by
  simpa [tensorRightGlueVertex] using
    tensorRight_vertex_mem_iff s t r u p (Sum.inr j)

private def sumInlFiberEquiv
    {α β γ δ : Type} (f : α → γ) (g : β → δ) (p : γ) :
    {z : α ⊕ β // Sum.map f g z = Sum.inl p} ≃
      {x : α // f x = p} where
  toFun z := by
    rcases z with ⟨x | y, h⟩
    · exact ⟨x, Sum.inl.inj h⟩
    · exact (Sum.inr_ne_inl h).elim
  invFun x := ⟨Sum.inl x.1, congrArg
    (Sum.inl : γ → γ ⊕ δ) x.2⟩
  left_inv z := by
    rcases z with ⟨x | y, h⟩
    · rfl
    · exact (Sum.inr_ne_inl h).elim
  right_inv _ := rfl

private def sumInrFiberEquiv
    {α β γ δ : Type} (f : α → γ) (g : β → δ) (p : δ) :
    {z : α ⊕ β // Sum.map f g z = Sum.inr p} ≃
      {y : β // g y = p} where
  toFun z := by
    rcases z with ⟨x | y, h⟩
    · exact (Sum.inl_ne_inr h).elim
    · exact ⟨y, Sum.inr.inj h⟩
  invFun y := ⟨Sum.inr y.1, congrArg
    (Sum.inr : δ → γ ⊕ δ) y.2⟩
  left_inv z := by
    rcases z with ⟨x | y, h⟩
    · exact (Sum.inl_ne_inr h).elim
    · rfl
  right_inv _ := rfl

private def tensorLeftVertexFiberEquiv
    (p : GlueComponent s t) :
    GlueVertexFiber (tensor s r) (tensor t u)
        (tensorLeftGlueComponent s t r u p) ≃
      GlueVertexFiber s t p :=
  (Equiv.subtypeEquiv (tensorGlueVertexEquiv s t r u) (fun x => by
    constructor
    · intro h
      have h' := congrArg (tensorGlueComponentEquiv s t r u) h
      simpa using h'
    · intro h
      apply (tensorGlueComponentEquiv s t r u).injective
      simpa using h)).trans
    (sumInlFiberEquiv
      (vertexComponent s t) (vertexComponent r u) p)

private def tensorRightVertexFiberEquiv
    (p : GlueComponent r u) :
    GlueVertexFiber (tensor s r) (tensor t u)
        (tensorRightGlueComponent s t r u p) ≃
      GlueVertexFiber r u p :=
  (Equiv.subtypeEquiv (tensorGlueVertexEquiv s t r u) (fun x => by
    constructor
    · intro h
      have h' := congrArg (tensorGlueComponentEquiv s t r u) h
      simpa using h'
    · intro h
      apply (tensorGlueComponentEquiv s t r u).injective
      simpa using h)).trans
    (sumInrFiberEquiv
      (vertexComponent s t) (vertexComponent r u) p)

theorem tensorLeft_vertexCount (p : GlueComponent s t) :
    vertexCount (tensor s r) (tensor t u)
        (tensorLeftGlueComponent s t r u p) =
      vertexCount s t p :=
  Nat.card_congr (tensorLeftVertexFiberEquiv s t r u p)

theorem tensorRight_vertexCount (p : GlueComponent r u) :
    vertexCount (tensor s r) (tensor t u)
        (tensorRightGlueComponent s t r u p) =
      vertexCount r u p :=
  Nat.card_congr (tensorRightVertexFiberEquiv s t r u p)

@[simp]
theorem tensorGlueVertexEquiv_edge (k : Fin (b + b')) :
    tensorGlueVertexEquiv s t r u
        (Sum.inl ((tensor s r).outComp k)) =
      Sum.map
        (fun i : Fin b => Sum.inl (s.outComp i))
        (fun j : Fin b' => Sum.inl (r.outComp j))
        (finSumFinEquiv.symm k) := by
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp [tensor, tensorGlueVertexEquiv]
  · intro j
    simp [tensor, tensorGlueVertexEquiv]

@[simp]
theorem tensorGlueComponentEquiv_edge (k : Fin (b + b')) :
    tensorGlueComponentEquiv s t r u
        (vertexComponent (tensor s r) (tensor t u)
          (Sum.inl ((tensor s r).outComp k))) =
      Sum.map
        (fun i : Fin b =>
          vertexComponent s t (Sum.inl (s.outComp i)))
        (fun j : Fin b' =>
          vertexComponent r u (Sum.inl (r.outComp j)))
        (finSumFinEquiv.symm k) := by
  rw [tensorGlueComponentEquiv_vertex,
    tensorGlueVertexEquiv_edge]
  rcases finSumFinEquiv.symm k with i | j <;> rfl

private def tensorLeftEdgeFiberEquiv
    (p : GlueComponent s t) :
    GlueEdgeFiber (tensor s r) (tensor t u)
        (tensorLeftGlueComponent s t r u p) ≃
      GlueEdgeFiber s t p :=
  (Equiv.subtypeEquiv finSumFinEquiv.symm (fun k => by
    constructor
    · intro h
      have h' := congrArg (tensorGlueComponentEquiv s t r u) h
      rw [tensorGlueComponentEquiv_edge,
        tensorGlueComponentEquiv_left] at h'
      exact h'
    · intro h
      apply (tensorGlueComponentEquiv s t r u).injective
      rw [tensorGlueComponentEquiv_edge,
        tensorGlueComponentEquiv_left]
      exact h)).trans
    (sumInlFiberEquiv
      (fun i : Fin b =>
        vertexComponent s t (Sum.inl (s.outComp i)))
      (fun j : Fin b' =>
        vertexComponent r u (Sum.inl (r.outComp j)))
      p)

private def tensorRightEdgeFiberEquiv
    (p : GlueComponent r u) :
    GlueEdgeFiber (tensor s r) (tensor t u)
        (tensorRightGlueComponent s t r u p) ≃
      GlueEdgeFiber r u p :=
  (Equiv.subtypeEquiv finSumFinEquiv.symm (fun k => by
    constructor
    · intro h
      have h' := congrArg (tensorGlueComponentEquiv s t r u) h
      rw [tensorGlueComponentEquiv_edge,
        tensorGlueComponentEquiv_right] at h'
      exact h'
    · intro h
      apply (tensorGlueComponentEquiv s t r u).injective
      rw [tensorGlueComponentEquiv_edge,
        tensorGlueComponentEquiv_right]
      exact h)).trans
    (sumInrFiberEquiv
      (fun i : Fin b =>
        vertexComponent s t (Sum.inl (s.outComp i)))
      (fun j : Fin b' =>
        vertexComponent r u (Sum.inl (r.outComp j)))
      p)

theorem tensorLeft_edgeCount (p : GlueComponent s t) :
    edgeCount (tensor s r) (tensor t u)
        (tensorLeftGlueComponent s t r u p) =
      edgeCount s t p :=
  Nat.card_congr (tensorLeftEdgeFiberEquiv s t r u p)

theorem tensorRight_edgeCount (p : GlueComponent r u) :
    edgeCount (tensor s r) (tensor t u)
        (tensorRightGlueComponent s t r u p) =
      edgeCount r u p :=
  Nat.card_congr (tensorRightEdgeFiberEquiv s t r u p)

@[simp]
theorem tensor_genus_castAdd (i : Fin s.ncomp) :
    (tensor s r).genus (Fin.castAdd r.ncomp i) = s.genus i := by
  simp [tensor]

@[simp]
theorem tensor_genus_natAdd (j : Fin r.ncomp) :
    (tensor s r).genus (Fin.natAdd s.ncomp j) = r.genus j := by
  simp [tensor]

theorem tensorLeft_oldGenus (p : GlueComponent s t) :
    oldGenus (tensor s r) (tensor t u)
        (tensorLeftGlueComponent s t r u p) =
      oldGenus s t p := by
  classical
  unfold oldGenus
  change
    ((∑ i : Fin (s.ncomp + r.ncomp),
        if vertexComponent (tensor s r) (tensor t u) (Sum.inl i) =
            tensorLeftGlueComponent s t r u p
        then (tensor s r).genus i else 0) +
      ∑ j : Fin (t.ncomp + u.ncomp),
        if vertexComponent (tensor s r) (tensor t u) (Sum.inr j) =
            tensorLeftGlueComponent s t r u p
        then (tensor t u).genus j else 0) = _
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp [tensorLeft_vertex_mem_iff,
    tensorRight_vertex_ne_left]

theorem tensorRight_oldGenus (p : GlueComponent r u) :
    oldGenus (tensor s r) (tensor t u)
        (tensorRightGlueComponent s t r u p) =
      oldGenus r u p := by
  classical
  unfold oldGenus
  change
    ((∑ i : Fin (s.ncomp + r.ncomp),
        if vertexComponent (tensor s r) (tensor t u) (Sum.inl i) =
            tensorRightGlueComponent s t r u p
        then (tensor s r).genus i else 0) +
      ∑ j : Fin (t.ncomp + u.ncomp),
        if vertexComponent (tensor s r) (tensor t u) (Sum.inr j) =
            tensorRightGlueComponent s t r u p
        then (tensor t u).genus j else 0) = _
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp [tensorRight_vertex_mem_iff,
    tensorLeft_vertex_ne_right]

theorem tensorLeft_gluedGenus (p : GlueComponent s t) :
    gluedGenus (tensor s r) (tensor t u)
        (tensorLeftGlueComponent s t r u p) =
      gluedGenus s t p := by
  unfold gluedGenus
  rw [tensorLeft_oldGenus, tensorLeft_edgeCount,
    tensorLeft_vertexCount]

theorem tensorRight_gluedGenus (p : GlueComponent r u) :
    gluedGenus (tensor s r) (tensor t u)
        (tensorRightGlueComponent s t r u p) =
      gluedGenus r u p := by
  unfold gluedGenus
  rw [tensorRight_oldGenus, tensorRight_edgeCount,
    tensorRight_vertexCount]

@[simp]
theorem tensorGlueComponentEquiv_input (i : Fin (a + a')) :
    tensorGlueComponentEquiv s t r u
        (vertexComponent (tensor s r) (tensor t u)
          (Sum.inl ((tensor s r).inComp i))) =
      Sum.map
        (fun k : Fin a =>
          vertexComponent s t (Sum.inl (s.inComp k)))
        (fun k : Fin a' =>
          vertexComponent r u (Sum.inl (r.inComp k)))
        (finSumFinEquiv.symm i) := by
  rw [tensorGlueComponentEquiv_vertex]
  refine Fin.addCases ?_ ?_ i
  · intro k
    simp [tensor, tensorGlueVertexEquiv]
  · intro k
    simp [tensor, tensorGlueVertexEquiv]

@[simp]
theorem tensorGlueComponentEquiv_output (j : Fin (c + c')) :
    tensorGlueComponentEquiv s t r u
        (vertexComponent (tensor s r) (tensor t u)
          (Sum.inr ((tensor t u).outComp j))) =
      Sum.map
        (fun k : Fin c =>
          vertexComponent s t (Sum.inr (t.outComp k)))
        (fun k : Fin c' =>
          vertexComponent r u (Sum.inr (u.outComp k)))
        (finSumFinEquiv.symm j) := by
  rw [tensorGlueComponentEquiv_vertex]
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp [tensor, tensorGlueVertexEquiv]
  · intro k
    simp [tensor, tensorGlueVertexEquiv]

/-- Relabel the components of a blockwise composite by first splitting the
gluing graph and then using the labels chosen by the two smaller
composites. -/
def tensorCompLabelEquiv :
    Fin (comp (tensor s r) (tensor t u)).ncomp ≃
      Fin (tensor (comp s t) (comp r u)).ncomp :=
  (compLabelEquiv (tensor s r) (tensor t u)).trans
    ((tensorGlueComponentEquiv s t r u).trans
      ((Equiv.sumCongr
        (compLabelEquiv s t).symm
        (compLabelEquiv r u).symm).trans
        finSumFinEquiv))

/-- Representative-level interchange: gluing two disjoint unions is
component-relabel equivalent to the disjoint union of the two gluings. -/
theorem rel_comp_tensor :
    Rel (comp (tensor s r) (tensor t u))
      (tensor (comp s t) (comp r u)) := by
  refine ⟨tensorCompLabelEquiv s t r u, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro k
      simp only [tensorCompLabelEquiv, Equiv.trans_apply]
      rw [compLabelEquiv_inComp,
        tensorGlueComponentEquiv_input]
      simp [tensor]
      apply (compLabelEquiv s t).injective
      simp
    · intro k
      simp only [tensorCompLabelEquiv, Equiv.trans_apply]
      rw [compLabelEquiv_inComp,
        tensorGlueComponentEquiv_input]
      simp [tensor]
      apply (compLabelEquiv r u).injective
      simp
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [tensorCompLabelEquiv, Equiv.trans_apply]
      rw [compLabelEquiv_outComp,
        tensorGlueComponentEquiv_output]
      simp [tensor]
      apply (compLabelEquiv s t).injective
      simp
    · intro k
      simp only [tensorCompLabelEquiv, Equiv.trans_apply]
      rw [compLabelEquiv_outComp,
        tensorGlueComponentEquiv_output]
      simp [tensor]
      apply (compLabelEquiv r u).injective
      simp
  · intro k
    generalize hq :
      tensorGlueComponentEquiv s t r u
        (compLabelEquiv (tensor s r) (tensor t u) k) = z
    rcases z with p | p
    · have hp :
          compLabelEquiv (tensor s r) (tensor t u) k =
            tensorLeftGlueComponent s t r u p := by
        apply (tensorGlueComponentEquiv s t r u).injective
        simpa [hq]
      have he :
          tensorCompLabelEquiv s t r u k =
            Fin.castAdd (comp r u).ncomp
              ((compLabelEquiv s t).symm p) := by
        change finSumFinEquiv
            (Sum.map
              (compLabelEquiv s t).symm
              (compLabelEquiv r u).symm
              (tensorGlueComponentEquiv s t r u
                (compLabelEquiv (tensor s r) (tensor t u) k))) =
          _
        rw [hq]
        rfl
      rw [he, tensor_genus_castAdd,
        comp_genus_eq_gluedGenus, comp_genus_eq_gluedGenus]
      simp only [Equiv.apply_symm_apply]
      rw [hp, tensorLeft_gluedGenus]
    · have hp :
          compLabelEquiv (tensor s r) (tensor t u) k =
            tensorRightGlueComponent s t r u p := by
        apply (tensorGlueComponentEquiv s t r u).injective
        simpa [hq]
      have he :
          tensorCompLabelEquiv s t r u k =
            Fin.natAdd (comp s t).ncomp
              ((compLabelEquiv r u).symm p) := by
        change finSumFinEquiv
            (Sum.map
              (compLabelEquiv s t).symm
              (compLabelEquiv r u).symm
              (tensorGlueComponentEquiv s t r u
                (compLabelEquiv (tensor s r) (tensor t u) k))) =
          _
        rw [hq]
        rfl
      rw [he, tensor_genus_natAdd,
        comp_genus_eq_gluedGenus, comp_genus_eq_gluedGenus]
      simp only [Equiv.apply_symm_apply]
      rw [hp, tensorRight_gluedGenus]

/-- Disjoint union of identity representatives is a relabeling of the
identity on the summed arity. -/
theorem rel_tensor_identity (a a' : ℕ) :
    Rel (tensor (identity a) (identity a')) (identity (a + a')) := by
  refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i <;> intro k <;>
      simp [tensor, identity]
  · intro j
    refine Fin.addCases ?_ ?_ j <;> intro k <;>
      simp [tensor, identity]
  · intro k
    refine Fin.addCases ?_ ?_ k <;> intro i <;>
      simp [tensor, identity]

end TensorComposition

/-- Reindex only the incoming and outgoing arities of a surface code.  The
component labels and genera are unchanged. -/
def cast {a b a' b' : ℕ} (ha : a = a') (hb : b = b')
    (s : SurfaceCode a b) : SurfaceCode a' b' where
  ncomp := s.ncomp
  inComp i := s.inComp (Fin.cast ha.symm i)
  outComp j := s.outComp (Fin.cast hb.symm j)
  genus := s.genus

theorem rel_cast {a b a' b' : ℕ} (ha : a = a') (hb : b = b')
    {s t : SurfaceCode a b} (h : Rel s t) :
    Rel (cast ha hb s) (cast ha hb t) := by
  rcases h with ⟨e, hin, hout, hgenus⟩
  exact ⟨e,
    fun i => hin (Fin.cast ha.symm i),
    fun j => hout (Fin.cast hb.symm j),
    hgenus⟩

section TensorCoherence

variable {a b c d e f : ℕ}
  (s : SurfaceCode a b) (t : SurfaceCode c d)
  (u : SurfaceCode e f)

/-- Canonical reassociation of the three blocks of component labels. -/
def tensorAssocLabelEquiv :
    Fin (tensor (tensor s t) u).ncomp ≃
      Fin (tensor s (tensor t u)).ncomp :=
  finSumFinEquiv.symm |>.trans
    ((Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)).trans
      ((Equiv.sumAssoc _ _ _).trans
        ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
          finSumFinEquiv)))

@[simp]
theorem tensorAssocLabelEquiv_first (i : Fin s.ncomp) :
    tensorAssocLabelEquiv s t u
        (Fin.castAdd u.ncomp (Fin.castAdd t.ncomp i)) =
      Fin.castAdd (t.ncomp + u.ncomp) i := by
  simp only [tensorAssocLabelEquiv, Equiv.trans_apply, tensor]
  rw [finSumFinEquiv_symm_apply_castAdd]
  simp

@[simp]
theorem tensorAssocLabelEquiv_middle (j : Fin t.ncomp) :
    tensorAssocLabelEquiv s t u
        (Fin.castAdd u.ncomp (Fin.natAdd s.ncomp j)) =
      Fin.natAdd s.ncomp (Fin.castAdd u.ncomp j) := by
  simp only [tensorAssocLabelEquiv, Equiv.trans_apply, tensor]
  rw [finSumFinEquiv_symm_apply_castAdd]
  simp

@[simp]
theorem tensorAssocLabelEquiv_last (k : Fin u.ncomp) :
    tensorAssocLabelEquiv s t u
        (Fin.natAdd (s.ncomp + t.ncomp) k) =
      Fin.natAdd s.ncomp (Fin.natAdd t.ncomp k) := by
  simp only [tensorAssocLabelEquiv, Equiv.trans_apply, tensor]
  rw [finSumFinEquiv_symm_apply_natAdd]
  simp

private theorem cast_add_assoc_first
    {m n p : ℕ} (i : Fin m) :
    Fin.cast (Nat.add_assoc m n p).symm
        (Fin.castAdd (n + p) i) =
      Fin.castAdd p (Fin.castAdd n i) := by
  apply Fin.ext
  rfl

private theorem cast_add_assoc_middle
    {m n p : ℕ} (j : Fin n) :
    Fin.cast (Nat.add_assoc m n p).symm
        (Fin.natAdd m (Fin.castAdd p j)) =
      Fin.castAdd p (Fin.natAdd m j) := by
  apply Fin.ext
  rfl

private theorem cast_add_assoc_last
    {m n p : ℕ} (k : Fin p) :
    Fin.cast (Nat.add_assoc m n p).symm
        (Fin.natAdd m (Fin.natAdd n k)) =
      Fin.natAdd (m + n) k := by
  apply Fin.ext
  simp [Nat.add_assoc]

/-- Representative-level associativity of disjoint union, with the
boundary arities transported along associativity of natural-number
addition. -/
theorem rel_tensor_assoc :
    Rel
      (cast (Nat.add_assoc a c e) (Nat.add_assoc b d f)
        (tensor (tensor s t) u))
      (tensor s (tensor t u)) := by
  refine ⟨tensorAssocLabelEquiv s t u, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro ia
      change tensorAssocLabelEquiv s t u
          ((tensor (tensor s t) u).inComp
            (Fin.cast (Nat.add_assoc a c e).symm
              (Fin.castAdd (c + e) ia))) =
        (tensor s (tensor t u)).inComp
          (Fin.castAdd (c + e) ia)
      rw [cast_add_assoc_first]
      simpa only [tensor, Fin.addCases_left] using
        tensorAssocLabelEquiv_first s t u (s.inComp ia)
    · intro ice
      refine Fin.addCases ?_ ?_ ice
      · intro ic
        change tensorAssocLabelEquiv s t u
            ((tensor (tensor s t) u).inComp
              (Fin.cast (Nat.add_assoc a c e).symm
                (Fin.natAdd a (Fin.castAdd e ic)))) =
          (tensor s (tensor t u)).inComp
            (Fin.natAdd a (Fin.castAdd e ic))
        rw [cast_add_assoc_middle]
        simpa only [tensor, Fin.addCases_left, Fin.addCases_right] using
          tensorAssocLabelEquiv_middle s t u (t.inComp ic)
      · intro ie
        change tensorAssocLabelEquiv s t u
            ((tensor (tensor s t) u).inComp
              (Fin.cast (Nat.add_assoc a c e).symm
                (Fin.natAdd a (Fin.natAdd c ie)))) =
          (tensor s (tensor t u)).inComp
            (Fin.natAdd a (Fin.natAdd c ie))
        rw [cast_add_assoc_last]
        simpa only [tensor, Fin.addCases_right] using
          tensorAssocLabelEquiv_last s t u (u.inComp ie)
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro ib
      change tensorAssocLabelEquiv s t u
          ((tensor (tensor s t) u).outComp
            (Fin.cast (Nat.add_assoc b d f).symm
              (Fin.castAdd (d + f) ib))) =
        (tensor s (tensor t u)).outComp
          (Fin.castAdd (d + f) ib)
      rw [cast_add_assoc_first]
      simpa only [tensor, Fin.addCases_left] using
        tensorAssocLabelEquiv_first s t u (s.outComp ib)
    · intro idf
      refine Fin.addCases ?_ ?_ idf
      · intro id
        change tensorAssocLabelEquiv s t u
            ((tensor (tensor s t) u).outComp
              (Fin.cast (Nat.add_assoc b d f).symm
                (Fin.natAdd b (Fin.castAdd f id)))) =
          (tensor s (tensor t u)).outComp
            (Fin.natAdd b (Fin.castAdd f id))
        rw [cast_add_assoc_middle]
        simpa only [tensor, Fin.addCases_left, Fin.addCases_right] using
          tensorAssocLabelEquiv_middle s t u (t.outComp id)
      · intro iff
        change tensorAssocLabelEquiv s t u
            ((tensor (tensor s t) u).outComp
              (Fin.cast (Nat.add_assoc b d f).symm
                (Fin.natAdd b (Fin.natAdd d iff)))) =
          (tensor s (tensor t u)).outComp
            (Fin.natAdd b (Fin.natAdd d iff))
        rw [cast_add_assoc_last]
        simpa only [tensor, Fin.addCases_right] using
          tensorAssocLabelEquiv_last s t u (u.outComp iff)
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro ist
      refine Fin.addCases ?_ ?_ ist
      · intro is
        simp [cast, tensor, tensorAssocLabelEquiv]
      · intro it
        simp [cast, tensor, tensorAssocLabelEquiv]
    · intro iu
      simp [cast, tensor, tensorAssocLabelEquiv]

end TensorCoherence

end SurfaceCode

namespace SurfaceNF

/-- Transport a surface normal form along equalities of its input and
output arities. -/
def cast {a b a' b' : ℕ} (ha : a = a') (hb : b = b') :
    SurfaceNF a b → SurfaceNF a' b' :=
  Quotient.map (SurfaceCode.cast ha hb)
    (fun _ _ h => SurfaceCode.rel_cast ha hb h)

/-- Quotient-level associativity of disjoint union, with the boundary
arities transported along associativity of natural-number addition. -/
theorem tensor_assoc
    {a b c d e f : ℕ}
    (s : SurfaceNF a b) (t : SurfaceNF c d) (u : SurfaceNF e f) :
    cast (Nat.add_assoc a c e) (Nat.add_assoc b d f)
        (tensor (tensor s t) u) =
      tensor s (tensor t u) := by
  induction s using Quotient.inductionOn with
  | _ s =>
      induction t using Quotient.inductionOn with
      | _ t =>
          induction u using Quotient.inductionOn with
          | _ u =>
              apply Quotient.sound
              exact SurfaceCode.rel_tensor_assoc s t u

/-- Quotient-level interchange for graph gluing and disjoint union. -/
theorem tensor_comp
    {a b c a' b' c' : ℕ}
    (s : SurfaceNF a b) (t : SurfaceNF b c)
    (r : SurfaceNF a' b') (u : SurfaceNF b' c') :
    comp (tensor s r) (tensor t u) =
      tensor (comp s t) (comp r u) := by
  induction s using Quotient.inductionOn with
  | _ s =>
      induction t using Quotient.inductionOn with
      | _ t =>
          induction r using Quotient.inductionOn with
          | _ r =>
              induction u using Quotient.inductionOn with
              | _ u =>
                  apply Quotient.sound
                  exact SurfaceCode.rel_comp_tensor s t r u

/-- The tensor of identity normal forms is the identity normal form on the
sum of arities. -/
@[simp]
theorem tensor_identity (a a' : ℕ) :
    tensor (identity a) (identity a') = identity (a + a') := by
  apply Quotient.sound
  exact SurfaceCode.rel_tensor_identity a a'

end SurfaceNF

/-- Object-level disjoint union for the wrapped surface-normal-form
category. -/
def SurfaceNFObj.tensorObj (X Y : SurfaceNFObj) : SurfaceNFObj :=
  ⟨X.arity + Y.arity⟩

/-- Disjoint union is an actual bifunctor on the verified category of
surface normal forms. -/
def surfaceTensorFunctor :
    SurfaceNFObj × SurfaceNFObj ⥤ SurfaceNFObj where
  obj X := SurfaceNFObj.tensorObj X.1 X.2
  map f := SurfaceNF.tensor f.1 f.2
  map_id X := SurfaceNF.tensor_identity X.1.arity X.2.arity
  map_comp f g := (SurfaceNF.tensor_comp f.1 g.1 f.2 g.2).symm

end Cob2NormalForm
