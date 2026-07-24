import RequestProject.Cob2SurfaceGraphBound

/-!
# Unit and associativity laws for surface-code composition

This file studies the combinatorial gluing operation on component-and-genus
normal forms.  It first identifies the connected-component quotient obtained
by gluing an identity code, including the vertex, edge, and genus counts
needed for the two unit laws.

The eventual target is a category of surface normal forms.  A `Category`
instance is declared here only if associativity of the graph-quotient
composition is proved below; none of the statements in this file identifies
these combinatorial codes with smooth cobordisms.
-/

noncomputable section

namespace Cob2NormalForm

open CategoryTheory

namespace SurfaceCode

section LeftUnit

variable {a b : ℕ} (s : SurfaceCode a b)

/-- Collapse every cylinder component on the left to the component of `s`
containing its outgoing gluing circle. -/
def leftUnitVertexTarget :
    GlueVertex (identity a) s → Fin s.ncomp
  | Sum.inl i => s.inComp i
  | Sum.inr k => k

private theorem leftUnitVertexTarget_eq_of_glueConnected
    {x y : GlueVertex (identity a) s}
    (h : (glueSetoid (identity a) s) x y) :
    leftUnitVertexTarget s x = leftUnitVertexTarget s y := by
  change Relation.EqvGen (GlueStep (identity a) s) x y at h
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨i, hxy⟩
      have hx : x = Sum.inl ((identity a).outComp i) :=
        congrArg Prod.fst hxy
      have hy : y = Sum.inr (s.inComp i) :=
        congrArg Prod.snd hxy
      subst x
      subst y
      rfl
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- Gluing an identity code on the left has exactly the components of the
right-hand code. -/
def leftUnitComponentEquiv :
    GlueComponent (identity a) s ≃ Fin s.ncomp where
  toFun :=
    Quotient.lift (leftUnitVertexTarget s)
      (fun _ _ h => leftUnitVertexTarget_eq_of_glueConnected s h)
  invFun := fun k =>
    vertexComponent (identity a) s (Sum.inr k)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
        rcases x with i | k
        · simpa [leftUnitVertexTarget, identity] using
            (edgeEnds_same_component (identity a) s i).symm
        · rfl
  right_inv := fun _ => rfl

@[simp]
theorem leftUnitComponentEquiv_vertex_inl (i : Fin a) :
    leftUnitComponentEquiv s
        (vertexComponent (identity a) s (Sum.inl i)) =
      s.inComp i :=
  rfl

@[simp]
theorem leftUnitComponentEquiv_vertex_inr (k : Fin s.ncomp) :
    leftUnitComponentEquiv s
        (vertexComponent (identity a) s (Sum.inr k)) =
      k :=
  rfl

private def leftUnitVertexFiberEquiv
    (q : GlueComponent (identity a) s) :
    GlueVertexFiber (identity a) s q ≃
      GlueEdgeFiber (identity a) s q ⊕
        {k : Fin s.ncomp // k = leftUnitComponentEquiv s q} where
  toFun x := by
    rcases x with ⟨i | k, hx⟩
    · change Fin a at i
      exact Sum.inl ⟨i, by simpa [identity] using hx⟩
    · exact Sum.inr ⟨k, by
        simpa using congrArg (leftUnitComponentEquiv s) hx⟩
  invFun x := by
    rcases x with i | k
    · exact ⟨Sum.inl i.1, by simpa [identity] using i.2⟩
    · exact ⟨Sum.inr k.1, by
        apply (leftUnitComponentEquiv s).injective
        simpa using k.2⟩
  left_inv x := by
    rcases x with ⟨i | k, hi⟩ <;> rfl
  right_inv x := by
    rcases x with i | k <;> rfl

/-- A left identity gluing has one component vertex more than it has middle
edges, component by component. -/
theorem leftUnit_vertexCount
    (q : GlueComponent (identity a) s) :
    vertexCount (identity a) s q =
      edgeCount (identity a) s q + 1 := by
  rw [show vertexCount (identity a) s q =
      Nat.card
        (GlueEdgeFiber (identity a) s q ⊕
          {k : Fin s.ncomp // k = leftUnitComponentEquiv s q}) from
    Nat.card_congr (leftUnitVertexFiberEquiv s q)]
  simp [edgeCount]

/-- Identity cylinders carry no genus, and the unique right-hand vertex of
each gluing component carries precisely its old genus label. -/
theorem leftUnit_oldGenus
    (q : GlueComponent (identity a) s) :
    oldGenus (identity a) s q =
      s.genus (leftUnitComponentEquiv s q) := by
  classical
  have heq (k : Fin s.ncomp) :
      (vertexComponent (identity a) s (Sum.inr k) = q) =
        (k = leftUnitComponentEquiv s q) := by
    apply propext
    constructor
    · intro h
      simpa using congrArg (leftUnitComponentEquiv s) h
    · intro h
      apply (leftUnitComponentEquiv s).injective
      simpa using h
  unfold oldGenus
  change
    (∑ i : Fin a,
        if vertexComponent (identity a) s (Sum.inl i) = q
        then 0 else 0) +
      (∑ k : Fin s.ncomp,
        if vertexComponent (identity a) s (Sum.inr k) = q
        then s.genus k else 0) =
      s.genus (leftUnitComponentEquiv s q)
  simp_rw [heq]
  simp

/-- Gluing an identity on the left preserves each component genus. -/
theorem leftUnit_gluedGenus
    (q : GlueComponent (identity a) s) :
    gluedGenus (identity a) s q =
      s.genus (leftUnitComponentEquiv s q) := by
  rw [gluedGenus, leftUnit_oldGenus s q, leftUnit_vertexCount s q]
  omega

/-- The canonical numeric labels chosen by representative composition,
identified with the original component labels after a left identity
gluing. -/
def leftUnitLabelEquiv :
    Fin (comp (identity a) s).ncomp ≃ Fin s.ncomp := by
  let Q := GlueComponent (identity a) s
  letI : Fintype Q :=
    (glueFiniteCode (identity a) s).fintypeComponent
  change Fin (Fintype.card Q) ≃ Fin s.ncomp
  exact (Fintype.equivFin Q).symm.trans (leftUnitComponentEquiv s)

/-- Representative-level left identity law for surface-code gluing. -/
theorem rel_comp_identity_left :
    Rel (comp (identity a) s) s := by
  refine ⟨leftUnitLabelEquiv s, ?_, ?_, ?_⟩
  · intro i
    simp [leftUnitLabelEquiv, comp, glueFiniteCode,
      FiniteCode.toSurfaceCode]
    change s.inComp i = s.inComp i
    rfl
  · intro j
    simp [leftUnitLabelEquiv, comp, glueFiniteCode,
      FiniteCode.toSurfaceCode]
  · intro k
    unfold leftUnitLabelEquiv comp FiniteCode.toSurfaceCode
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    exact (leftUnit_gluedGenus s _).symm

end LeftUnit

section RightUnit

variable {a b : ℕ} (s : SurfaceCode a b)

/-- Collapse every cylinder component on the right to the component of `s`
containing its incoming gluing circle. -/
def rightUnitVertexTarget :
    GlueVertex s (identity b) → Fin s.ncomp
  | Sum.inl k => k
  | Sum.inr j => s.outComp j

private theorem rightUnitVertexTarget_eq_of_glueConnected
    {x y : GlueVertex s (identity b)}
    (h : (glueSetoid s (identity b)) x y) :
    rightUnitVertexTarget s x = rightUnitVertexTarget s y := by
  change Relation.EqvGen (GlueStep s (identity b)) x y at h
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨i, hxy⟩
      have hx : x = Sum.inl (s.outComp i) :=
        congrArg Prod.fst hxy
      have hy : y = Sum.inr ((identity b).inComp i) :=
        congrArg Prod.snd hxy
      subst x
      subst y
      rfl
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- Gluing an identity code on the right has exactly the components of the
left-hand code. -/
def rightUnitComponentEquiv :
    GlueComponent s (identity b) ≃ Fin s.ncomp where
  toFun :=
    Quotient.lift (rightUnitVertexTarget s)
      (fun _ _ h => rightUnitVertexTarget_eq_of_glueConnected s h)
  invFun := fun k =>
    vertexComponent s (identity b) (Sum.inl k)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
        rcases x with k | j
        · rfl
        · simpa [rightUnitVertexTarget, identity] using
            edgeEnds_same_component s (identity b) j
  right_inv := fun _ => rfl

@[simp]
theorem rightUnitComponentEquiv_vertex_inl (k : Fin s.ncomp) :
    rightUnitComponentEquiv s
        (vertexComponent s (identity b) (Sum.inl k)) =
      k :=
  rfl

@[simp]
theorem rightUnitComponentEquiv_vertex_inr (j : Fin b) :
    rightUnitComponentEquiv s
        (vertexComponent s (identity b) (Sum.inr j)) =
      s.outComp j :=
  rfl

private def rightUnitVertexFiberEquiv
    (q : GlueComponent s (identity b)) :
    GlueVertexFiber s (identity b) q ≃
      {k : Fin s.ncomp // k = rightUnitComponentEquiv s q} ⊕
        GlueEdgeFiber s (identity b) q where
  toFun x := by
    rcases x with ⟨k | j, hx⟩
    · exact Sum.inl ⟨k, by
        simpa using congrArg (rightUnitComponentEquiv s) hx⟩
    · change Fin b at j
      exact Sum.inr ⟨j, by
        simpa [identity] using
          (edgeEnds_same_component s (identity b) j).trans hx⟩
  invFun x := by
    rcases x with k | j
    · exact ⟨Sum.inl k.1, by
        apply (rightUnitComponentEquiv s).injective
        simpa using k.2⟩
    · exact ⟨Sum.inr j.1, by
        simpa [identity] using
          (edgeEnds_same_component s (identity b) j.1).symm.trans j.2⟩
  left_inv x := by
    rcases x with ⟨k | j, hk⟩ <;> rfl
  right_inv x := by
    rcases x with k | j <;> rfl

/-- A right identity gluing has one component vertex more than it has middle
edges, component by component. -/
theorem rightUnit_vertexCount
    (q : GlueComponent s (identity b)) :
    vertexCount s (identity b) q =
      edgeCount s (identity b) q + 1 := by
  rw [show vertexCount s (identity b) q =
      Nat.card
        ({k : Fin s.ncomp // k = rightUnitComponentEquiv s q} ⊕
          GlueEdgeFiber s (identity b) q) from
    Nat.card_congr (rightUnitVertexFiberEquiv s q)]
  simp [edgeCount, Nat.add_comm]

/-- Identity cylinders carry no genus, and the unique left-hand vertex of
each gluing component carries precisely its old genus label. -/
theorem rightUnit_oldGenus
    (q : GlueComponent s (identity b)) :
    oldGenus s (identity b) q =
      s.genus (rightUnitComponentEquiv s q) := by
  classical
  have heq (k : Fin s.ncomp) :
      (vertexComponent s (identity b) (Sum.inl k) = q) =
        (k = rightUnitComponentEquiv s q) := by
    apply propext
    constructor
    · intro h
      simpa using congrArg (rightUnitComponentEquiv s) h
    · intro h
      apply (rightUnitComponentEquiv s).injective
      simpa using h
  unfold oldGenus
  change
    (∑ k : Fin s.ncomp,
        if vertexComponent s (identity b) (Sum.inl k) = q
        then s.genus k else 0) +
      (∑ j : Fin b,
        if vertexComponent s (identity b) (Sum.inr j) = q
        then 0 else 0) =
      s.genus (rightUnitComponentEquiv s q)
  simp_rw [heq]
  simp

/-- Gluing an identity on the right preserves each component genus. -/
theorem rightUnit_gluedGenus
    (q : GlueComponent s (identity b)) :
    gluedGenus s (identity b) q =
      s.genus (rightUnitComponentEquiv s q) := by
  rw [gluedGenus, rightUnit_oldGenus s q, rightUnit_vertexCount s q]
  omega

/-- The canonical numeric labels chosen by representative composition,
identified with the original component labels after a right identity
gluing. -/
def rightUnitLabelEquiv :
    Fin (comp s (identity b)).ncomp ≃ Fin s.ncomp := by
  let Q := GlueComponent s (identity b)
  letI : Fintype Q :=
    (glueFiniteCode s (identity b)).fintypeComponent
  change Fin (Fintype.card Q) ≃ Fin s.ncomp
  exact (Fintype.equivFin Q).symm.trans (rightUnitComponentEquiv s)

/-- Representative-level right identity law for surface-code gluing. -/
theorem rel_comp_identity_right :
    Rel (comp s (identity b)) s := by
  refine ⟨rightUnitLabelEquiv s, ?_, ?_, ?_⟩
  · intro i
    simp [rightUnitLabelEquiv, comp, glueFiniteCode,
      FiniteCode.toSurfaceCode]
  · intro j
    simp [rightUnitLabelEquiv, comp, glueFiniteCode,
      FiniteCode.toSurfaceCode]
    change s.outComp j = s.outComp j
    rfl
  · intro k
    unfold rightUnitLabelEquiv comp FiniteCode.toSurfaceCode
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    exact (rightUnit_gluedGenus s _).symm

end RightUnit

section TripleGluing

variable {a b c d : ℕ}
  (s : SurfaceCode a b) (t : SurfaceCode b c) (u : SurfaceCode c d)

/-- The three layers of old components before either parenthesization of a
triple gluing. -/
abbrev TripleVertex :=
  (Fin s.ncomp ⊕ Fin t.ncomp) ⊕ Fin u.ncomp

/-- Endpoints of an indexed circle in the first gluing interface. -/
def tripleFirstEdgeEnds (i : Fin b) :
    TripleVertex s t u × TripleVertex s t u :=
  (Sum.inl (Sum.inl (s.outComp i)),
    Sum.inl (Sum.inr (t.inComp i)))

/-- Endpoints of an indexed circle in the second gluing interface. -/
def tripleSecondEdgeEnds (j : Fin c) :
    TripleVertex s t u × TripleVertex s t u :=
  (Sum.inl (Sum.inr (t.outComp j)),
    Sum.inr (u.inComp j))

/-- Generating edges of the flattened three-layer gluing multigraph. -/
def TripleStep (x y : TripleVertex s t u) : Prop :=
  (∃ i : Fin b, (x, y) = tripleFirstEdgeEnds s t u i) ∨
    ∃ j : Fin c, (x, y) = tripleSecondEdgeEnds s t u j

/-- Connectedness in the flattened three-layer gluing graph. -/
def tripleSetoid : Setoid (TripleVertex s t u) :=
  Relation.EqvGen.setoid (TripleStep s t u)

/-- Components of the flattened three-layer gluing graph. -/
abbrev TripleComponent :=
  Quotient (tripleSetoid s t u)

local instance tripleComponentDecidableEq :
    DecidableEq (TripleComponent s t u) :=
  Classical.decEq _

/-- The flattened component containing an old component vertex. -/
def tripleVertexComponent (x : TripleVertex s t u) :
    TripleComponent s t u :=
  Quotient.mk (tripleSetoid s t u) x

/-- Numeric labels selected by `SurfaceCode.comp` are equivalent to the
underlying graph-component quotient from which they were selected. -/
def compLabelEquiv {a b c : ℕ}
    (s : SurfaceCode a b) (t : SurfaceCode b c) :
    Fin (comp s t).ncomp ≃ GlueComponent s t := by
  let Q := GlueComponent s t
  letI : Fintype Q := (glueFiniteCode s t).fintypeComponent
  change Fin (Fintype.card Q) ≃ Q
  exact (Fintype.equivFin Q).symm

@[simp]
theorem compLabelEquiv_inComp {a b c : ℕ}
    (s : SurfaceCode a b) (t : SurfaceCode b c) (i : Fin a) :
    compLabelEquiv s t ((comp s t).inComp i) =
      vertexComponent s t (Sum.inl (s.inComp i)) := by
  simp [compLabelEquiv, comp, glueFiniteCode, FiniteCode.toSurfaceCode]

@[simp]
theorem compLabelEquiv_outComp {a b c : ℕ}
    (s : SurfaceCode a b) (t : SurfaceCode b c) (j : Fin c) :
    compLabelEquiv s t ((comp s t).outComp j) =
      vertexComponent s t (Sum.inr (t.outComp j)) := by
  simp [compLabelEquiv, comp, glueFiniteCode, FiniteCode.toSurfaceCode]

@[simp]
theorem comp_genus_eq_gluedGenus {a b c : ℕ}
    (s : SurfaceCode a b) (t : SurfaceCode b c)
    (k : Fin (comp s t).ncomp) :
    (comp s t).genus k =
      gluedGenus s t (compLabelEquiv s t k) := by
  simp [compLabelEquiv, comp, glueFiniteCode, FiniteCode.toSurfaceCode]

private theorem firstPairConnected_to_triple
    {x y : GlueVertex s t}
    (h : (glueSetoid s t) x y) :
    (tripleSetoid s t u) (Sum.inl x) (Sum.inl y) := by
  change Relation.EqvGen (GlueStep s t) x y at h
  change Relation.EqvGen (TripleStep s t u) (Sum.inl x) (Sum.inl y)
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨i, hxy⟩
      apply Relation.EqvGen.rel
      left
      exact ⟨i, congrArg (fun p => (Sum.inl p.1, Sum.inl p.2)) hxy⟩
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ihxy ihyz =>
      exact Relation.EqvGen.trans _ _ _ ihxy ihyz

/-- A component of the first two layers determines a flattened triple
component. -/
def firstPairComponentToTriple :
    GlueComponent s t → TripleComponent s t u :=
  Quotient.map' Sum.inl
    (fun _ _ h => firstPairConnected_to_triple s t u h)

@[simp]
theorem firstPairComponentToTriple_vertex (x : GlueVertex s t) :
    firstPairComponentToTriple s t u (vertexComponent s t x) =
      tripleVertexComponent s t u (Sum.inl x) :=
  rfl

private theorem secondPairConnected_to_triple
    {x y : GlueVertex t u}
    (h : (glueSetoid t u) x y) :
    (tripleSetoid s t u)
      (Sum.elim (fun k => Sum.inl (Sum.inr k)) Sum.inr x)
      (Sum.elim (fun k => Sum.inl (Sum.inr k)) Sum.inr y) := by
  change Relation.EqvGen (GlueStep t u) x y at h
  change Relation.EqvGen (TripleStep s t u) _ _
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨j, hxy⟩
      apply Relation.EqvGen.rel
      right
      exact ⟨j, congrArg
        (fun p =>
          (Sum.elim (fun k => Sum.inl (Sum.inr k)) Sum.inr p.1,
            Sum.elim (fun k => Sum.inl (Sum.inr k)) Sum.inr p.2))
        hxy⟩
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ihxy ihyz =>
      exact Relation.EqvGen.trans _ _ _ ihxy ihyz

/-- A component of the last two layers determines a flattened triple
component. -/
def secondPairComponentToTriple :
    GlueComponent t u → TripleComponent s t u :=
  Quotient.map'
    (Sum.elim (fun k => Sum.inl (Sum.inr k)) Sum.inr)
    (fun _ _ h => secondPairConnected_to_triple s t u h)

@[simp]
theorem secondPairComponentToTriple_vertex_inl (k : Fin t.ncomp) :
    secondPairComponentToTriple s t u
        (vertexComponent t u (Sum.inl k)) =
      tripleVertexComponent s t u (Sum.inl (Sum.inr k)) :=
  rfl

@[simp]
theorem secondPairComponentToTriple_vertex_inr (k : Fin u.ncomp) :
    secondPairComponentToTriple s t u
        (vertexComponent t u (Sum.inr k)) =
      tripleVertexComponent s t u (Sum.inr k) :=
  rfl

/-- Map a vertex of the left-parenthesized outer gluing to the flattened
component quotient. -/
def leftNestedVertexToTriple :
    GlueVertex (comp s t) u → TripleComponent s t u
  | Sum.inl k =>
      firstPairComponentToTriple s t u (compLabelEquiv s t k)
  | Sum.inr l =>
      tripleVertexComponent s t u (Sum.inr l)

private theorem leftNestedVertexToTriple_eq_of_connected
    {x y : GlueVertex (comp s t) u}
    (h : (glueSetoid (comp s t) u) x y) :
    leftNestedVertexToTriple s t u x =
      leftNestedVertexToTriple s t u y := by
  change Relation.EqvGen (GlueStep (comp s t) u) x y at h
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨j, hxy⟩
      have hx : x = Sum.inl ((comp s t).outComp j) :=
        congrArg Prod.fst hxy
      have hy : y = Sum.inr (u.inComp j) :=
        congrArg Prod.snd hxy
      subst x
      subst y
      change firstPairComponentToTriple s t u
            (compLabelEquiv s t ((comp s t).outComp j)) =
          tripleVertexComponent s t u (Sum.inr (u.inComp j))
      rw [compLabelEquiv_outComp, firstPairComponentToTriple_vertex]
      apply Quotient.sound
      apply Relation.EqvGen.rel
      right
      exact ⟨j, rfl⟩
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- A component of the left-parenthesized nested gluing determines a
flattened triple component. -/
def leftNestedComponentToTriple :
    GlueComponent (comp s t) u → TripleComponent s t u :=
  Quotient.lift (leftNestedVertexToTriple s t u)
    (fun _ _ h => leftNestedVertexToTriple_eq_of_connected s t u h)

/-- Map a flattened old vertex to its component in the left-parenthesized
gluing. -/
def tripleVertexToLeftNested :
    TripleVertex s t u → GlueComponent (comp s t) u
  | Sum.inl v =>
      vertexComponent (comp s t) u
        (Sum.inl ((compLabelEquiv s t).symm (vertexComponent s t v)))
  | Sum.inr l =>
      vertexComponent (comp s t) u (Sum.inr l)

private theorem tripleVertexToLeftNested_eq_of_connected
    {x y : TripleVertex s t u}
    (h : (tripleSetoid s t u) x y) :
    tripleVertexToLeftNested s t u x =
      tripleVertexToLeftNested s t u y := by
  change Relation.EqvGen (TripleStep s t u) x y at h
  induction h with
  | rel x y hxy =>
      rcases hxy with hxy | hxy
      · rcases hxy with ⟨i, hxy⟩
        have hx : x = Sum.inl (Sum.inl (s.outComp i)) :=
          congrArg Prod.fst hxy
        have hy : y = Sum.inl (Sum.inr (t.inComp i)) :=
          congrArg Prod.snd hxy
        subst x
        subst y
        change vertexComponent (comp s t) u
              (Sum.inl ((compLabelEquiv s t).symm
                (vertexComponent s t (Sum.inl (s.outComp i))))) =
            vertexComponent (comp s t) u
              (Sum.inl ((compLabelEquiv s t).symm
                (vertexComponent s t (Sum.inr (t.inComp i)))))
        rw [edgeEnds_same_component s t i]
      · rcases hxy with ⟨j, hxy⟩
        have hx : x = Sum.inl (Sum.inr (t.outComp j)) :=
          congrArg Prod.fst hxy
        have hy : y = Sum.inr (u.inComp j) :=
          congrArg Prod.snd hxy
        subst x
        subst y
        simpa using edgeEnds_same_component (comp s t) u j
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- A flattened triple component determines a component of the
left-parenthesized nested gluing. -/
def tripleComponentToLeftNested :
    TripleComponent s t u → GlueComponent (comp s t) u :=
  Quotient.lift (tripleVertexToLeftNested s t u)
    (fun _ _ h => tripleVertexToLeftNested_eq_of_connected s t u h)

/-- Connected components of the left-parenthesized gluing are canonically
the connected components of the flattened three-layer graph. -/
def leftNestedComponentEquiv :
    GlueComponent (comp s t) u ≃ TripleComponent s t u where
  toFun := leftNestedComponentToTriple s t u
  invFun := tripleComponentToLeftNested s t u
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
        rcases x with k | l
        · change tripleComponentToLeftNested s t u
              (firstPairComponentToTriple s t u
                (compLabelEquiv s t k)) =
            vertexComponent (comp s t) u (Sum.inl k)
          generalize hp : compLabelEquiv s t k = p
          induction p using Quotient.inductionOn with
          | _ v =>
              change vertexComponent (comp s t) u
                    (Sum.inl ((compLabelEquiv s t).symm
                      (vertexComponent s t v))) =
                  vertexComponent (comp s t) u (Sum.inl k)
              congr 2
              apply (compLabelEquiv s t).injective
              simpa using hp.symm
        · rfl

  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
        rcases x with v | l
        · change leftNestedComponentToTriple s t u
              (vertexComponent (comp s t) u
                (Sum.inl ((compLabelEquiv s t).symm
                  (vertexComponent s t v)))) =
            tripleVertexComponent s t u (Sum.inl v)
          change firstPairComponentToTriple s t u
              (compLabelEquiv s t
                ((compLabelEquiv s t).symm (vertexComponent s t v))) =
            tripleVertexComponent s t u (Sum.inl v)
          simp
        · rfl

@[simp]
theorem leftNestedComponentEquiv_vertex_inl
    (k : Fin (comp s t).ncomp) :
    leftNestedComponentEquiv s t u
        (vertexComponent (comp s t) u (Sum.inl k)) =
      firstPairComponentToTriple s t u (compLabelEquiv s t k) :=
  rfl

@[simp]
theorem leftNestedComponentEquiv_vertex_inr (l : Fin u.ncomp) :
    leftNestedComponentEquiv s t u
        (vertexComponent (comp s t) u (Sum.inr l)) =
      tripleVertexComponent s t u (Sum.inr l) :=
  rfl

/-- Map a vertex of the right-parenthesized outer gluing to the flattened
component quotient. -/
def rightNestedVertexToTriple :
    GlueVertex s (comp t u) → TripleComponent s t u
  | Sum.inl k =>
      tripleVertexComponent s t u (Sum.inl (Sum.inl k))
  | Sum.inr l =>
      secondPairComponentToTriple s t u (compLabelEquiv t u l)

private theorem rightNestedVertexToTriple_eq_of_connected
    {x y : GlueVertex s (comp t u)}
    (h : (glueSetoid s (comp t u)) x y) :
    rightNestedVertexToTriple s t u x =
      rightNestedVertexToTriple s t u y := by
  change Relation.EqvGen (GlueStep s (comp t u)) x y at h
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨i, hxy⟩
      have hx : x = Sum.inl (s.outComp i) :=
        congrArg Prod.fst hxy
      have hy : y = Sum.inr ((comp t u).inComp i) :=
        congrArg Prod.snd hxy
      subst x
      subst y
      change tripleVertexComponent s t u
            (Sum.inl (Sum.inl (s.outComp i))) =
          secondPairComponentToTriple s t u
            (compLabelEquiv t u ((comp t u).inComp i))
      rw [compLabelEquiv_inComp,
        secondPairComponentToTriple_vertex_inl]
      apply Quotient.sound
      apply Relation.EqvGen.rel
      left
      exact ⟨i, rfl⟩
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- A component of the right-parenthesized nested gluing determines a
flattened triple component. -/
def rightNestedComponentToTriple :
    GlueComponent s (comp t u) → TripleComponent s t u :=
  Quotient.lift (rightNestedVertexToTriple s t u)
    (fun _ _ h => rightNestedVertexToTriple_eq_of_connected s t u h)

/-- Map a flattened old vertex to its component in the right-parenthesized
gluing. -/
def tripleVertexToRightNested :
    TripleVertex s t u → GlueComponent s (comp t u)
  | Sum.inl (Sum.inl k) =>
      vertexComponent s (comp t u) (Sum.inl k)
  | Sum.inl (Sum.inr l) =>
      vertexComponent s (comp t u)
        (Sum.inr ((compLabelEquiv t u).symm
          (vertexComponent t u (Sum.inl l))))
  | Sum.inr m =>
      vertexComponent s (comp t u)
        (Sum.inr ((compLabelEquiv t u).symm
          (vertexComponent t u (Sum.inr m))))

private theorem tripleVertexToRightNested_eq_of_connected
    {x y : TripleVertex s t u}
    (h : (tripleSetoid s t u) x y) :
    tripleVertexToRightNested s t u x =
      tripleVertexToRightNested s t u y := by
  change Relation.EqvGen (TripleStep s t u) x y at h
  induction h with
  | rel x y hxy =>
      rcases hxy with hxy | hxy
      · rcases hxy with ⟨i, hxy⟩
        have hx : x = Sum.inl (Sum.inl (s.outComp i)) :=
          congrArg Prod.fst hxy
        have hy : y = Sum.inl (Sum.inr (t.inComp i)) :=
          congrArg Prod.snd hxy
        subst x
        subst y
        simpa using edgeEnds_same_component s (comp t u) i
      · rcases hxy with ⟨j, hxy⟩
        have hx : x = Sum.inl (Sum.inr (t.outComp j)) :=
          congrArg Prod.fst hxy
        have hy : y = Sum.inr (u.inComp j) :=
          congrArg Prod.snd hxy
        subst x
        subst y
        change vertexComponent s (comp t u)
              (Sum.inr ((compLabelEquiv t u).symm
                (vertexComponent t u (Sum.inl (t.outComp j))))) =
            vertexComponent s (comp t u)
              (Sum.inr ((compLabelEquiv t u).symm
                (vertexComponent t u (Sum.inr (u.inComp j)))))
        rw [edgeEnds_same_component t u j]
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- A flattened triple component determines a component of the
right-parenthesized nested gluing. -/
def tripleComponentToRightNested :
    TripleComponent s t u → GlueComponent s (comp t u) :=
  Quotient.lift (tripleVertexToRightNested s t u)
    (fun _ _ h => tripleVertexToRightNested_eq_of_connected s t u h)

/-- Connected components of the right-parenthesized gluing are canonically
the connected components of the flattened three-layer graph. -/
def rightNestedComponentEquiv :
    GlueComponent s (comp t u) ≃ TripleComponent s t u where
  toFun := rightNestedComponentToTriple s t u
  invFun := tripleComponentToRightNested s t u
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
        rcases x with k | l
        · rfl
        · change tripleComponentToRightNested s t u
              (secondPairComponentToTriple s t u
                (compLabelEquiv t u l)) =
            vertexComponent s (comp t u) (Sum.inr l)
          generalize hp : compLabelEquiv t u l = p
          induction p using Quotient.inductionOn with
          | _ v =>
              rcases v with k | m
              · change vertexComponent s (comp t u)
                    (Sum.inr ((compLabelEquiv t u).symm
                      (vertexComponent t u (Sum.inl k)))) =
                  vertexComponent s (comp t u) (Sum.inr l)
                congr 2
                apply (compLabelEquiv t u).injective
                simpa using hp.symm
              · change vertexComponent s (comp t u)
                    (Sum.inr ((compLabelEquiv t u).symm
                      (vertexComponent t u (Sum.inr m)))) =
                  vertexComponent s (comp t u) (Sum.inr l)
                congr 2
                apply (compLabelEquiv t u).injective
                simpa using hp.symm
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
        rcases x with v | m
        · rcases v with k | l
          · rfl
          · change rightNestedComponentToTriple s t u
                (vertexComponent s (comp t u)
                  (Sum.inr ((compLabelEquiv t u).symm
                    (vertexComponent t u (Sum.inl l))))) =
              tripleVertexComponent s t u (Sum.inl (Sum.inr l))
            change secondPairComponentToTriple s t u
                (compLabelEquiv t u
                  ((compLabelEquiv t u).symm
                    (vertexComponent t u (Sum.inl l)))) =
              tripleVertexComponent s t u (Sum.inl (Sum.inr l))
            simp
        · change rightNestedComponentToTriple s t u
              (vertexComponent s (comp t u)
                (Sum.inr ((compLabelEquiv t u).symm
                  (vertexComponent t u (Sum.inr m))))) =
            tripleVertexComponent s t u (Sum.inr m)
          change secondPairComponentToTriple s t u
              (compLabelEquiv t u
                ((compLabelEquiv t u).symm
                  (vertexComponent t u (Sum.inr m)))) =
            tripleVertexComponent s t u (Sum.inr m)
          simp

@[simp]
theorem rightNestedComponentEquiv_vertex_inl (k : Fin s.ncomp) :
    rightNestedComponentEquiv s t u
        (vertexComponent s (comp t u) (Sum.inl k)) =
      tripleVertexComponent s t u (Sum.inl (Sum.inl k)) :=
  rfl

@[simp]
theorem rightNestedComponentEquiv_vertex_inr
    (l : Fin (comp t u).ncomp) :
    rightNestedComponentEquiv s t u
        (vertexComponent s (comp t u) (Sum.inr l)) =
      secondPairComponentToTriple s t u (compLabelEquiv t u l) :=
  rfl

/-- The explicit connected-component equivalence underlying associativity:
both nested graph quotients are the same flattened triple quotient. -/
def nestedComponentEquiv :
    GlueComponent (comp s t) u ≃ GlueComponent s (comp t u) :=
  (leftNestedComponentEquiv s t u).trans
    (rightNestedComponentEquiv s t u).symm

/-! ## Euler data on the flattened quotient -/

/-- Old genera from the first layer that lie in a flattened component. -/
def tripleFirstOldGenus (q : TripleComponent s t u) : ℕ :=
  ∑ i : Fin s.ncomp,
    if tripleVertexComponent s t u (Sum.inl (Sum.inl i)) = q
    then s.genus i else 0

/-- Old genera from the middle layer that lie in a flattened component. -/
def tripleMiddleOldGenus (q : TripleComponent s t u) : ℕ :=
  ∑ j : Fin t.ncomp,
    if tripleVertexComponent s t u (Sum.inl (Sum.inr j)) = q
    then t.genus j else 0

/-- Old genera from the last layer that lie in a flattened component. -/
def tripleLastOldGenus (q : TripleComponent s t u) : ℕ :=
  ∑ k : Fin u.ncomp,
    if tripleVertexComponent s t u (Sum.inr k) = q
    then u.genus k else 0

/-- Number of first-layer old vertices in a flattened component. -/
def tripleFirstVertexCount (q : TripleComponent s t u) : ℕ :=
  Nat.card {i : Fin s.ncomp //
    tripleVertexComponent s t u (Sum.inl (Sum.inl i)) = q}

/-- Number of middle-layer old vertices in a flattened component. -/
def tripleMiddleVertexCount (q : TripleComponent s t u) : ℕ :=
  Nat.card {j : Fin t.ncomp //
    tripleVertexComponent s t u (Sum.inl (Sum.inr j)) = q}

/-- Number of last-layer old vertices in a flattened component. -/
def tripleLastVertexCount (q : TripleComponent s t u) : ℕ :=
  Nat.card {k : Fin u.ncomp //
    tripleVertexComponent s t u (Sum.inr k) = q}

/-- Number of indexed edges from the first gluing interface in a flattened
component. -/
def tripleFirstEdgeCount (q : TripleComponent s t u) : ℕ :=
  Nat.card {i : Fin b //
    tripleVertexComponent s t u
      (Sum.inl (Sum.inl (s.outComp i))) = q}

/-- Number of indexed edges from the second gluing interface in a flattened
component. -/
def tripleSecondEdgeCount (q : TripleComponent s t u) : ℕ :=
  Nat.card {j : Fin c //
    tripleVertexComponent s t u
      (Sum.inl (Sum.inr (t.outComp j))) = q}

/-- Number of first-pair components retained inside a flattened component.
These are precisely the intermediate vertices contracted by the
left-parenthesized outer gluing. -/
def tripleFirstPairComponentCount (q : TripleComponent s t u) : ℕ :=
  Nat.card {p : GlueComponent s t //
    firstPairComponentToTriple s t u p = q}

/-- Number of second-pair components retained inside a flattened component.
These are precisely the intermediate vertices contracted by the
right-parenthesized outer gluing. -/
def tripleSecondPairComponentCount (q : TripleComponent s t u) : ℕ :=
  Nat.card {p : GlueComponent t u //
    secondPairComponentToTriple s t u p = q}

/-- The common integer genus expression for either parenthesization.  It is
kept in `ℤ` while associativity is proved so that cancellation of contracted
intermediate component vertices is literal rather than a statement about
truncated natural subtraction. -/
def tripleGenusInt (q : TripleComponent s t u) : ℤ :=
  tripleFirstOldGenus s t u q +
    tripleMiddleOldGenus s t u q +
    tripleLastOldGenus s t u q +
    tripleFirstEdgeCount s t u q +
    tripleSecondEdgeCount s t u q + 1 -
    tripleFirstVertexCount s t u q -
    tripleMiddleVertexCount s t u q -
    tripleLastVertexCount s t u q

private theorem natCard_subtype_eq_sum_indicator
    {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {x : α // p x} =
      ∑ x : α, if p x then 1 else 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter]

private theorem ite_add_zero (p : Prop) [Decidable p] (x y : ℕ) :
    (if p then x + y else 0) =
      (if p then x else 0) + (if p then y else 0) := by
  by_cases h : p <;> simp [h]

private theorem ite_fintype_sum_zero
    {α : Type} [Fintype α] (p : Prop) [Decidable p] (f : α → ℕ) :
    (if p then ∑ x, f x else 0) =
      ∑ x, if p then f x else 0 := by
  by_cases h : p <;> simp [h]

private theorem sum_if_eq_right
    {α : Type} (inst : Fintype α) [DecidableEq α]
    (i : α) (p : α → Prop) [DecidablePred p] (v : ℕ) :
    (∑ j ∈ @Finset.univ α inst,
      if p j then (if i = j then v else 0) else 0) =
      if p i then v else 0 := by
  letI : Fintype α := inst
  calc
    (∑ j : α, if p j then (if i = j then v else 0) else 0) =
        ∑ j : α, if i = j then (if p j then v else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j <;> by_cases hp : p j <;> simp [hij, hp]
    _ = if p i then v else 0 := Fintype.sum_ite_eq i _

/-- Summing the old-genus contributions of first-pair components inside one
flattened component recovers the first two layers' old genera. -/
theorem sum_firstPair_oldGenus (q : TripleComponent s t u) :
    (∑ p : GlueComponent s t,
      if firstPairComponentToTriple s t u p = q
      then oldGenus s t p else 0) =
      tripleFirstOldGenus s t u q +
        tripleMiddleOldGenus s t u q := by
  classical
  unfold oldGenus tripleFirstOldGenus tripleMiddleOldGenus
  simp_rw [ite_add_zero]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp_rw [ite_fintype_sum_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simpa [firstPairComponentToTriple_vertex] using
      (sum_if_eq_right
        FinCategory.fintypeObj
        (vertexComponent s t (Sum.inl i))
        (fun p : GlueComponent s t =>
          firstPairComponentToTriple s t u p = q)
        (s.genus i))
  · simp_rw [ite_fintype_sum_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simpa [firstPairComponentToTriple_vertex] using
      (sum_if_eq_right
        FinCategory.fintypeObj
        (vertexComponent s t (Sum.inr j))
        (fun p : GlueComponent s t =>
          firstPairComponentToTriple s t u p = q)
        (t.genus j))

/-- First-interface indexed edges partition over the first-pair component
quotient. -/
theorem sum_firstPair_edgeCount (q : TripleComponent s t u) :
    (∑ p : GlueComponent s t,
      if firstPairComponentToTriple s t u p = q
      then edgeCount s t p else 0) =
      tripleFirstEdgeCount s t u q := by
  classical
  unfold edgeCount tripleFirstEdgeCount
  simp_rw [natCard_subtype_eq_sum_indicator]
  simp_rw [ite_fintype_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simpa [firstPairComponentToTriple_vertex] using
    (sum_if_eq_right
      FinCategory.fintypeObj
      (vertexComponent s t (Sum.inl (s.outComp i)))
      (fun p : GlueComponent s t =>
        firstPairComponentToTriple s t u p = q)
      1)

/-- First- and middle-layer vertices partition over the first-pair
component quotient. -/
theorem sum_firstPair_vertexCount (q : TripleComponent s t u) :
    (∑ p : GlueComponent s t,
      if firstPairComponentToTriple s t u p = q
      then vertexCount s t p else 0) =
      tripleFirstVertexCount s t u q +
        tripleMiddleVertexCount s t u q := by
  classical
  unfold vertexCount tripleFirstVertexCount tripleMiddleVertexCount
  simp_rw [natCard_subtype_eq_sum_indicator]
  simp_rw [ite_fintype_sum_zero]
  rw [Finset.sum_comm, Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simpa [firstPairComponentToTriple_vertex] using
      (sum_if_eq_right
        FinCategory.fintypeObj
        (vertexComponent s t (Sum.inl i))
        (fun p : GlueComponent s t =>
          firstPairComponentToTriple s t u p = q)
        1)
  · apply Finset.sum_congr rfl
    intro j _
    simpa [firstPairComponentToTriple_vertex] using
      (sum_if_eq_right
        FinCategory.fintypeObj
        (vertexComponent s t (Sum.inr j))
        (fun p : GlueComponent s t =>
          firstPairComponentToTriple s t u p = q)
        1)

/-- Summing the old-genus contributions of second-pair components inside
one flattened component recovers the last two layers' old genera. -/
theorem sum_secondPair_oldGenus (q : TripleComponent s t u) :
    (∑ p : GlueComponent t u,
      if secondPairComponentToTriple s t u p = q
      then oldGenus t u p else 0) =
      tripleMiddleOldGenus s t u q +
        tripleLastOldGenus s t u q := by
  classical
  unfold oldGenus tripleMiddleOldGenus tripleLastOldGenus
  simp_rw [ite_add_zero]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp_rw [ite_fintype_sum_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simpa [secondPairComponentToTriple_vertex_inl] using
      (sum_if_eq_right
        FinCategory.fintypeObj
        (vertexComponent t u (Sum.inl j))
        (fun p : GlueComponent t u =>
          secondPairComponentToTriple s t u p = q)
        (t.genus j))
  · simp_rw [ite_fintype_sum_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simpa [secondPairComponentToTriple_vertex_inr] using
      (sum_if_eq_right
        FinCategory.fintypeObj
        (vertexComponent t u (Sum.inr k))
        (fun p : GlueComponent t u =>
          secondPairComponentToTriple s t u p = q)
        (u.genus k))

/-- Second-interface indexed edges partition over the second-pair component
quotient. -/
theorem sum_secondPair_edgeCount (q : TripleComponent s t u) :
    (∑ p : GlueComponent t u,
      if secondPairComponentToTriple s t u p = q
      then edgeCount t u p else 0) =
      tripleSecondEdgeCount s t u q := by
  classical
  unfold edgeCount tripleSecondEdgeCount
  simp_rw [natCard_subtype_eq_sum_indicator]
  simp_rw [ite_fintype_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simpa [secondPairComponentToTriple_vertex_inl] using
    (sum_if_eq_right
      FinCategory.fintypeObj
      (vertexComponent t u (Sum.inl (t.outComp j)))
      (fun p : GlueComponent t u =>
        secondPairComponentToTriple s t u p = q)
      1)

/-- Middle- and last-layer vertices partition over the second-pair
component quotient. -/
theorem sum_secondPair_vertexCount (q : TripleComponent s t u) :
    (∑ p : GlueComponent t u,
      if secondPairComponentToTriple s t u p = q
      then vertexCount t u p else 0) =
      tripleMiddleVertexCount s t u q +
        tripleLastVertexCount s t u q := by
  classical
  unfold vertexCount tripleMiddleVertexCount tripleLastVertexCount
  simp_rw [natCard_subtype_eq_sum_indicator]
  simp_rw [ite_fintype_sum_zero]
  rw [Finset.sum_comm, Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    simpa [secondPairComponentToTriple_vertex_inl] using
      (sum_if_eq_right
        FinCategory.fintypeObj
        (vertexComponent t u (Sum.inl j))
        (fun p : GlueComponent t u =>
          secondPairComponentToTriple s t u p = q)
        1)
  · apply Finset.sum_congr rfl
    intro k _
    simpa [secondPairComponentToTriple_vertex_inr] using
      (sum_if_eq_right
        FinCategory.fintypeObj
        (vertexComponent t u (Sum.inr k))
        (fun p : GlueComponent t u =>
          secondPairComponentToTriple s t u p = q)
        1)

private theorem leftNested_inl_mem_iff
    (q : TripleComponent s t u) (k : Fin (comp s t).ncomp) :
    vertexComponent (comp s t) u (Sum.inl k) =
        (leftNestedComponentEquiv s t u).symm q ↔
      firstPairComponentToTriple s t u (compLabelEquiv s t k) = q := by
  rw [← (leftNestedComponentEquiv s t u).apply_eq_iff_eq]
  simp

private theorem leftNested_inr_mem_iff
    (q : TripleComponent s t u) (k : Fin u.ncomp) :
    vertexComponent (comp s t) u (Sum.inr k) =
        (leftNestedComponentEquiv s t u).symm q ↔
      tripleVertexComponent s t u (Sum.inr k) = q := by
  rw [← (leftNestedComponentEquiv s t u).apply_eq_iff_eq]
  simp

/-- The old-genus field of the left-parenthesized outer gluing is the sum
of the retained first-pair genera and the last-layer genera. -/
theorem leftNested_oldGenus
    (q : TripleComponent s t u) :
    oldGenus (comp s t) u
        ((leftNestedComponentEquiv s t u).symm q) =
      (∑ p : GlueComponent s t,
        if firstPairComponentToTriple s t u p = q
        then gluedGenus s t p else 0) +
      tripleLastOldGenus s t u q := by
  classical
  letI : Fintype (GlueComponent s t) :=
    FinCategory.fintypeObj
  unfold oldGenus tripleLastOldGenus
  apply congrArg₂ (fun x y : ℕ => x + y)
  · calc
      (∑ k,
          if vertexComponent (comp s t) u (Sum.inl k) =
              (leftNestedComponentEquiv s t u).symm q
          then (comp s t).genus k else 0) =
          ∑ k,
            if firstPairComponentToTriple s t u
                (compLabelEquiv s t k) = q
            then gluedGenus s t (compLabelEquiv s t k) else 0 := by
              apply Finset.sum_congr rfl
              intro k _
              rw [comp_genus_eq_gluedGenus]
              exact if_congr (leftNested_inl_mem_iff s t u q k) rfl rfl
      _ = ∑ p : GlueComponent s t,
            if firstPairComponentToTriple s t u p = q
            then gluedGenus s t p else 0 := by
        simpa using
          (compLabelEquiv s t).sum_comp
            (fun p : GlueComponent s t =>
              if firstPairComponentToTriple s t u p = q
              then gluedGenus s t p else 0)
  · apply Finset.sum_congr rfl
    intro k _
    exact if_congr (leftNested_inr_mem_iff s t u q k) rfl rfl

/-- The outer left-parenthesized edge count is exactly the flattened
second-interface edge count. -/
theorem leftNested_edgeCount
    (q : TripleComponent s t u) :
    edgeCount (comp s t) u
        ((leftNestedComponentEquiv s t u).symm q) =
      tripleSecondEdgeCount s t u q := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro j
  change
    vertexComponent (comp s t) u
        (Sum.inl ((comp s t).outComp j)) =
          (leftNestedComponentEquiv s t u).symm q ↔
      tripleVertexComponent s t u
        (Sum.inl (Sum.inr (t.outComp j))) = q
  rw [leftNested_inl_mem_iff, compLabelEquiv_outComp,
    firstPairComponentToTriple_vertex]

private def leftNestedVertexFiberEquiv
    (q : TripleComponent s t u) :
    GlueVertexFiber (comp s t) u
        ((leftNestedComponentEquiv s t u).symm q) ≃
      {p : GlueComponent s t //
        firstPairComponentToTriple s t u p = q} ⊕
      {k : Fin u.ncomp //
        tripleVertexComponent s t u (Sum.inr k) = q} where
  toFun x := by
    rcases x with ⟨k | l, hx⟩
    · exact Sum.inl ⟨compLabelEquiv s t k,
        (leftNested_inl_mem_iff s t u q k).mp hx⟩
    · exact Sum.inr ⟨l,
        (leftNested_inr_mem_iff s t u q l).mp hx⟩
  invFun x := by
    rcases x with p | l
    · exact ⟨Sum.inl ((compLabelEquiv s t).symm p.1),
        (leftNested_inl_mem_iff s t u q _).mpr (by simpa using p.2)⟩
    · exact ⟨Sum.inr l.1,
        (leftNested_inr_mem_iff s t u q _).mpr l.2⟩
  left_inv x := by
    rcases x with ⟨k | l, hx⟩ <;> apply Subtype.ext <;> simp
  right_inv x := by
    rcases x with p | l
    · exact congrArg Sum.inl (Subtype.ext (by simp))
    · exact congrArg Sum.inr (Subtype.ext (by simp))

/-- The outer left-parenthesized vertices are its retained first-pair
components together with last-layer vertices. -/
theorem leftNested_vertexCount
    (q : TripleComponent s t u) :
    vertexCount (comp s t) u
        ((leftNestedComponentEquiv s t u).symm q) =
      tripleFirstPairComponentCount s t u q +
        tripleLastVertexCount s t u q := by
  rw [show vertexCount (comp s t) u
        ((leftNestedComponentEquiv s t u).symm q) =
      Nat.card
        ({p : GlueComponent s t //
            firstPairComponentToTriple s t u p = q} ⊕
          {k : Fin u.ncomp //
            tripleVertexComponent s t u (Sum.inr k) = q}) from
    Nat.card_congr (leftNestedVertexFiberEquiv s t u q)]
  simp [tripleFirstPairComponentCount, tripleLastVertexCount]

private theorem rightNested_inl_mem_iff
    (q : TripleComponent s t u) (k : Fin s.ncomp) :
    vertexComponent s (comp t u) (Sum.inl k) =
        (rightNestedComponentEquiv s t u).symm q ↔
      tripleVertexComponent s t u (Sum.inl (Sum.inl k)) = q := by
  rw [← (rightNestedComponentEquiv s t u).apply_eq_iff_eq]
  simp

private theorem rightNested_inr_mem_iff
    (q : TripleComponent s t u) (k : Fin (comp t u).ncomp) :
    vertexComponent s (comp t u) (Sum.inr k) =
        (rightNestedComponentEquiv s t u).symm q ↔
      secondPairComponentToTriple s t u (compLabelEquiv t u k) = q := by
  rw [← (rightNestedComponentEquiv s t u).apply_eq_iff_eq]
  simp

/-- The old-genus field of the right-parenthesized outer gluing is the sum
of the first-layer genera and the retained second-pair genera. -/
theorem rightNested_oldGenus
    (q : TripleComponent s t u) :
    oldGenus s (comp t u)
        ((rightNestedComponentEquiv s t u).symm q) =
      tripleFirstOldGenus s t u q +
      ∑ p : GlueComponent t u,
        if secondPairComponentToTriple s t u p = q
        then gluedGenus t u p else 0 := by
  classical
  letI : Fintype (GlueComponent t u) :=
    FinCategory.fintypeObj
  unfold oldGenus tripleFirstOldGenus
  apply congrArg₂ (fun x y : ℕ => x + y)
  · apply Finset.sum_congr rfl
    intro k _
    exact if_congr (rightNested_inl_mem_iff s t u q k) rfl rfl
  · calc
      (∑ k,
          if vertexComponent s (comp t u) (Sum.inr k) =
              (rightNestedComponentEquiv s t u).symm q
          then (comp t u).genus k else 0) =
          ∑ k,
            if secondPairComponentToTriple s t u
                (compLabelEquiv t u k) = q
            then gluedGenus t u (compLabelEquiv t u k) else 0 := by
              apply Finset.sum_congr rfl
              intro k _
              rw [comp_genus_eq_gluedGenus]
              exact if_congr (rightNested_inr_mem_iff s t u q k) rfl rfl
      _ = ∑ p : GlueComponent t u,
            if secondPairComponentToTriple s t u p = q
            then gluedGenus t u p else 0 := by
        simpa using
          (compLabelEquiv t u).sum_comp
            (fun p : GlueComponent t u =>
              if secondPairComponentToTriple s t u p = q
              then gluedGenus t u p else 0)

/-- The outer right-parenthesized edge count is exactly the flattened
first-interface edge count. -/
theorem rightNested_edgeCount
    (q : TripleComponent s t u) :
    edgeCount s (comp t u)
        ((rightNestedComponentEquiv s t u).symm q) =
      tripleFirstEdgeCount s t u q := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  change
    vertexComponent s (comp t u) (Sum.inl (s.outComp i)) =
          (rightNestedComponentEquiv s t u).symm q ↔
      tripleVertexComponent s t u
        (Sum.inl (Sum.inl (s.outComp i))) = q
  exact rightNested_inl_mem_iff s t u q _

private def rightNestedVertexFiberEquiv
    (q : TripleComponent s t u) :
    GlueVertexFiber s (comp t u)
        ((rightNestedComponentEquiv s t u).symm q) ≃
      {k : Fin s.ncomp //
        tripleVertexComponent s t u (Sum.inl (Sum.inl k)) = q} ⊕
      {p : GlueComponent t u //
        secondPairComponentToTriple s t u p = q} where
  toFun x := by
    rcases x with ⟨k | l, hx⟩
    · exact Sum.inl ⟨k,
        (rightNested_inl_mem_iff s t u q k).mp hx⟩
    · exact Sum.inr ⟨compLabelEquiv t u l,
        (rightNested_inr_mem_iff s t u q l).mp hx⟩
  invFun x := by
    rcases x with k | p
    · exact ⟨Sum.inl k.1,
        (rightNested_inl_mem_iff s t u q _).mpr k.2⟩
    · exact ⟨Sum.inr ((compLabelEquiv t u).symm p.1),
        (rightNested_inr_mem_iff s t u q _).mpr (by simpa using p.2)⟩
  left_inv x := by
    rcases x with ⟨k | l, hx⟩ <;> apply Subtype.ext <;> simp
  right_inv x := by
    rcases x with k | p
    · exact congrArg Sum.inl (Subtype.ext (by simp))
    · exact congrArg Sum.inr (Subtype.ext (by simp))

/-- The outer right-parenthesized vertices are first-layer vertices
together with its retained second-pair components. -/
theorem rightNested_vertexCount
    (q : TripleComponent s t u) :
    vertexCount s (comp t u)
        ((rightNestedComponentEquiv s t u).symm q) =
      tripleFirstVertexCount s t u q +
        tripleSecondPairComponentCount s t u q := by
  rw [show vertexCount s (comp t u)
        ((rightNestedComponentEquiv s t u).symm q) =
      Nat.card
        ({k : Fin s.ncomp //
            tripleVertexComponent s t u (Sum.inl (Sum.inl k)) = q} ⊕
          {p : GlueComponent t u //
            secondPairComponentToTriple s t u p = q}) from
    Nat.card_congr (rightNestedVertexFiberEquiv s t u q)]
  simp [tripleFirstVertexCount, tripleSecondPairComponentCount]

/-- The natural-number gluing genus has the expected untruncated integer
Euler expression. -/
theorem gluedGenus_cast
    {a b c : ℕ} (s : SurfaceCode a b) (t : SurfaceCode b c)
    (q : GlueComponent s t) :
    (gluedGenus s t q : ℤ) =
      oldGenus s t q + edgeCount s t q + 1 - vertexCount s t q := by
  rw [gluedGenus_eq_oldGenus_add_cycleRank]
  rw [Nat.cast_add]
  rw [Nat.cast_sub (vertexCount_le_edgeCount_add_one s t q)]
  push_cast
  ring

private theorem ite_euler_zero (p : Prop) [Decidable p]
    (x y z : ℤ) :
    (if p then x + y + 1 - z else 0) =
      (if p then x else 0) +
        (if p then y else 0) +
        (if p then 1 else 0) -
        (if p then z else 0) := by
  by_cases h : p <;> simp [h]

/-- The total genus carried by retained first-pair components, expressed
using flattened Euler data. -/
theorem sum_firstPair_gluedGenus_cast
    (q : TripleComponent s t u) :
    ((∑ p : GlueComponent s t,
        if firstPairComponentToTriple s t u p = q
        then gluedGenus s t p else 0 : ℕ) : ℤ) =
      tripleFirstOldGenus s t u q +
        tripleMiddleOldGenus s t u q +
        tripleFirstEdgeCount s t u q +
        tripleFirstPairComponentCount s t u q -
        tripleFirstVertexCount s t u q -
        tripleMiddleVertexCount s t u q := by
  classical
  letI : Fintype (GlueComponent s t) :=
    FinCategory.fintypeObj
  have hold := congrArg (fun n : ℕ => (n : ℤ))
    (sum_firstPair_oldGenus s t u q)
  have hedge := congrArg (fun n : ℕ => (n : ℤ))
    (sum_firstPair_edgeCount s t u q)
  have hvertex := congrArg (fun n : ℕ => (n : ℤ))
    (sum_firstPair_vertexCount s t u q)
  push_cast at hold hedge hvertex ⊢
  simp_rw [gluedGenus_cast]
  simp_rw [ite_euler_zero]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hold, hedge, hvertex]
  unfold tripleFirstPairComponentCount
  rw [natCard_subtype_eq_sum_indicator, Nat.cast_sum]
  push_cast
  abel_nf

/-- The total genus carried by retained second-pair components, expressed
using flattened Euler data. -/
theorem sum_secondPair_gluedGenus_cast
    (q : TripleComponent s t u) :
    ((∑ p : GlueComponent t u,
        if secondPairComponentToTriple s t u p = q
        then gluedGenus t u p else 0 : ℕ) : ℤ) =
      tripleMiddleOldGenus s t u q +
        tripleLastOldGenus s t u q +
        tripleSecondEdgeCount s t u q +
        tripleSecondPairComponentCount s t u q -
        tripleMiddleVertexCount s t u q -
        tripleLastVertexCount s t u q := by
  classical
  letI : Fintype (GlueComponent t u) :=
    FinCategory.fintypeObj
  have hold := congrArg (fun n : ℕ => (n : ℤ))
    (sum_secondPair_oldGenus s t u q)
  have hedge := congrArg (fun n : ℕ => (n : ℤ))
    (sum_secondPair_edgeCount s t u q)
  have hvertex := congrArg (fun n : ℕ => (n : ℤ))
    (sum_secondPair_vertexCount s t u q)
  push_cast at hold hedge hvertex ⊢
  simp_rw [gluedGenus_cast]
  simp_rw [ite_euler_zero]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hold, hedge, hvertex]
  unfold tripleSecondPairComponentCount
  rw [natCard_subtype_eq_sum_indicator, Nat.cast_sum]
  push_cast
  abel_nf

/-- The left-parenthesized nested genus is the flattened Euler expression. -/
theorem leftNested_gluedGenus_cast
    (q : TripleComponent s t u) :
    (gluedGenus (comp s t) u
        ((leftNestedComponentEquiv s t u).symm q) : ℤ) =
      tripleGenusInt s t u q := by
  have hsum := sum_firstPair_gluedGenus_cast s t u q
  rw [gluedGenus_cast, leftNested_oldGenus, leftNested_edgeCount,
    leftNested_vertexCount]
  push_cast at hsum ⊢
  rw [hsum]
  unfold tripleGenusInt
  ring

/-- The right-parenthesized nested genus is the same flattened Euler
expression. -/
theorem rightNested_gluedGenus_cast
    (q : TripleComponent s t u) :
    (gluedGenus s (comp t u)
        ((rightNestedComponentEquiv s t u).symm q) : ℤ) =
      tripleGenusInt s t u q := by
  have hsum := sum_secondPair_gluedGenus_cast s t u q
  rw [gluedGenus_cast, rightNested_oldGenus, rightNested_edgeCount,
    rightNested_vertexCount]
  push_cast at hsum ⊢
  rw [hsum]
  unfold tripleGenusInt
  ring

/-- The explicit nested-component equivalence preserves genus. -/
theorem gluedGenus_nestedComponentEquiv
    (q : GlueComponent (comp s t) u) :
    gluedGenus (comp s t) u q =
      gluedGenus s (comp t u) (nestedComponentEquiv s t u q) := by
  apply Int.ofNat_injective
  let r := leftNestedComponentEquiv s t u q
  calc
    (gluedGenus (comp s t) u q : ℤ) =
        tripleGenusInt s t u r := by
      simpa [r] using leftNested_gluedGenus_cast s t u r
    _ = (gluedGenus s (comp t u)
          ((rightNestedComponentEquiv s t u).symm r) : ℤ) :=
      (rightNested_gluedGenus_cast s t u r).symm
    _ = (gluedGenus s (comp t u)
          (nestedComponentEquiv s t u q) : ℤ) := by
      rfl

@[simp]
theorem nestedComponentEquiv_input (i : Fin a) :
    nestedComponentEquiv s t u
        (vertexComponent (comp s t) u
          (Sum.inl ((comp s t).inComp i))) =
      vertexComponent s (comp t u) (Sum.inl (s.inComp i)) := by
  apply (rightNestedComponentEquiv s t u).injective
  simp [nestedComponentEquiv, compLabelEquiv_inComp,
    firstPairComponentToTriple_vertex]

@[simp]
theorem nestedComponentEquiv_output (j : Fin d) :
    nestedComponentEquiv s t u
        (vertexComponent (comp s t) u (Sum.inr (u.outComp j))) =
      vertexComponent s (comp t u)
        (Sum.inr ((comp t u).outComp j)) := by
  apply (rightNestedComponentEquiv s t u).injective
  simp [nestedComponentEquiv, compLabelEquiv_outComp,
    secondPairComponentToTriple_vertex_inr]

/-- The final numeric component labels on the two parenthesizations are
identified through the flattened connected-component quotient. -/
def associatorLabelEquiv :
    Fin (comp (comp s t) u).ncomp ≃
      Fin (comp s (comp t u)).ncomp :=
  (compLabelEquiv (comp s t) u).trans
    ((nestedComponentEquiv s t u).trans
      (compLabelEquiv s (comp t u)).symm)

/-- Representative-level associativity of component-and-genus gluing. -/
theorem rel_comp_assoc :
    Rel (comp (comp s t) u) (comp s (comp t u)) := by
  refine ⟨associatorLabelEquiv s t u, ?_, ?_, ?_⟩
  · intro i
    apply (compLabelEquiv s (comp t u)).injective
    simp [associatorLabelEquiv, compLabelEquiv_inComp,
      nestedComponentEquiv_input]
  · intro j
    apply (compLabelEquiv s (comp t u)).injective
    simp [associatorLabelEquiv, compLabelEquiv_outComp,
      nestedComponentEquiv_output]
  · intro k
    rw [comp_genus_eq_gluedGenus, comp_genus_eq_gluedGenus]
    simp only [associatorLabelEquiv, Equiv.trans_apply,
      Equiv.apply_symm_apply]
    exact (gluedGenus_nestedComponentEquiv s t u _).symm

end TripleGluing

end SurfaceCode

namespace SurfaceNF

/-- Quotient-level left identity law. -/
@[simp]
theorem identity_comp {a b : ℕ} (s : SurfaceNF a b) :
    comp (identity a) s = s := by
  induction s using Quotient.inductionOn with
  | _ s =>
      apply Quotient.sound
      exact SurfaceCode.rel_comp_identity_left s

/-- Quotient-level right identity law. -/
@[simp]
theorem comp_identity {a b : ℕ} (s : SurfaceNF a b) :
    comp s (identity b) = s := by
  induction s using Quotient.inductionOn with
  | _ s =>
      apply Quotient.sound
      exact SurfaceCode.rel_comp_identity_right s

/-- Quotient-level associativity of graph gluing. -/
theorem comp_assoc {a b c d : ℕ}
    (s : SurfaceNF a b) (t : SurfaceNF b c) (u : SurfaceNF c d) :
    comp (comp s t) u = comp s (comp t u) := by
  induction s using Quotient.inductionOn with
  | _ s =>
      induction t using Quotient.inductionOn with
      | _ t =>
          induction u using Quotient.inductionOn with
          | _ u =>
              apply Quotient.sound
              exact SurfaceCode.rel_comp_assoc s t u

end SurfaceNF

/-- Arity objects for the category of component-and-genus normal forms.
The wrapper avoids placing a global category structure on `Nat`. -/
@[ext]
structure SurfaceNFObj where
  arity : ℕ

instance : Quiver SurfaceNFObj where
  Hom X Y := SurfaceNF X.arity Y.arity

/-- Component-and-genus normal forms form a category under graph gluing. -/
instance : Category SurfaceNFObj where
  id X := SurfaceNF.identity X.arity
  comp := SurfaceNF.comp
  id_comp := SurfaceNF.identity_comp
  comp_id := SurfaceNF.comp_identity
  assoc := SurfaceNF.comp_assoc

end Cob2NormalForm
