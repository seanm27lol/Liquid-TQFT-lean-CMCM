import RequestProject.Cob2SurfaceMonoidalCoherence

/-!
# Boundary wirings for surface normal forms

This module isolates the genus-zero cylinder wirings induced by finite
boundary equivalences.  It proves that gluing such a wiring on either side
reindexes the corresponding external boundary and leaves all component and
genus data unchanged.
-/

noncomputable section

namespace Cob2NormalForm

open CategoryTheory

/-- The inverse block rotation is the block rotation with the two block
sizes exchanged. -/
theorem finAddFlip_symm_eq (m n : ℕ) :
    (finAddFlip : Fin (m + n) ≃ Fin (n + m)).symm =
      (finAddFlip : Fin (n + m) ≃ Fin (m + n)) := by
  apply Equiv.ext
  intro i
  apply (finAddFlip : Fin (m + n) ≃ Fin (n + m)).injective
  simp only [Equiv.apply_symm_apply]
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp
  · intro j
    simp

namespace SurfaceCode

/-- A disjoint family of genus-zero cylinders whose outgoing boundary is
identified with the incoming boundary by `e`. -/
def wiring {a b : ℕ} (e : Fin b ≃ Fin a) : SurfaceCode a b where
  ncomp := a
  inComp := id
  outComp := e
  genus := fun _ => 0

/-- Reindex the incoming boundary circles of a surface code. -/
def reindexIn {a a' b : ℕ} (e : Fin a' ≃ Fin a)
    (s : SurfaceCode a b) : SurfaceCode a' b where
  ncomp := s.ncomp
  inComp := s.inComp ∘ e
  outComp := s.outComp
  genus := s.genus

/-- Reindex the outgoing boundary circles of a surface code. -/
def reindexOut {a b b' : ℕ} (e : Fin b' ≃ Fin b)
    (s : SurfaceCode a b) : SurfaceCode a b' where
  ncomp := s.ncomp
  inComp := s.inComp
  outComp := s.outComp ∘ e
  genus := s.genus

theorem rel_reindexIn {a a' b : ℕ} (e : Fin a' ≃ Fin a)
    {s t : SurfaceCode a b} (h : Rel s t) :
    Rel (reindexIn e s) (reindexIn e t) := by
  rcases h with ⟨r, hin, hout, hgenus⟩
  exact ⟨r, fun i => hin (e i), hout, hgenus⟩

theorem rel_reindexOut {a b b' : ℕ} (e : Fin b' ≃ Fin b)
    {s t : SurfaceCode a b} (h : Rel s t) :
    Rel (reindexOut e s) (reindexOut e t) := by
  rcases h with ⟨r, hin, hout, hgenus⟩
  exact ⟨r, hin, fun j => hout (e j), hgenus⟩

theorem rel_tensor_flip
    {a b c d : ℕ} (s : SurfaceCode a b) (t : SurfaceCode c d) :
    Rel
      (reindexOut finAddFlip.symm (tensor s t))
      (reindexIn finAddFlip (tensor t s)) := by
  refine ⟨finAddFlip, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro k
      simp [reindexIn, reindexOut, tensor, finAddFlip]
    · intro k
      simp [reindexIn, reindexOut, tensor, finAddFlip]
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp [reindexIn, reindexOut, tensor, finAddFlip]
    · intro k
      simp [reindexIn, reindexOut, tensor, finAddFlip]
  · intro k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simp [reindexIn, reindexOut, tensor, finAddFlip]
    · intro j
      simp [reindexIn, reindexOut, tensor, finAddFlip]

theorem rel_tensor_wiring
    {a b c d : ℕ} (e : Fin b ≃ Fin a) (f : Fin d ≃ Fin c) :
    Rel
      (tensor (wiring e) (wiring f))
      (wiring (sumRelabel e f)) := by
  refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i <;> intro k <;>
      simp [tensor, wiring]
  · intro j
    refine Fin.addCases ?_ ?_ j <;> intro k <;>
      simp [tensor, wiring, sumRelabel]
  · intro k
    refine Fin.addCases ?_ ?_ k <;> intro i <;>
      simp [tensor, wiring]

theorem rel_reindexOut_wiring
    {a b c : ℕ} (e : Fin b ≃ Fin a) (f : Fin c ≃ Fin b) :
    Rel (reindexOut f (wiring e)) (wiring (f.trans e)) := by
  refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro j
    rfl
  · intro k
    rfl

section RightWiring

variable {a b c : ℕ} (s : SurfaceCode a b) (e : Fin c ≃ Fin b)

def rightWiringVertexTarget :
    GlueVertex s (wiring e) → Fin s.ncomp
  | Sum.inl k => k
  | Sum.inr j => s.outComp j

private theorem rightWiringVertexTarget_eq_of_glueConnected
    {x y : GlueVertex s (wiring e)}
    (h : (glueSetoid s (wiring e)) x y) :
    rightWiringVertexTarget s e x =
      rightWiringVertexTarget s e y := by
  change Relation.EqvGen (GlueStep s (wiring e)) x y at h
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨i, hxy⟩
      have hx : x = Sum.inl (s.outComp i) :=
        congrArg Prod.fst hxy
      have hy : y = Sum.inr ((wiring e).inComp i) :=
        congrArg Prod.snd hxy
      subst x
      subst y
      rfl
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

def rightWiringComponentEquiv :
    GlueComponent s (wiring e) ≃ Fin s.ncomp where
  toFun :=
    Quotient.lift (rightWiringVertexTarget s e)
      (fun _ _ h =>
        rightWiringVertexTarget_eq_of_glueConnected s e h)
  invFun := fun k =>
    vertexComponent s (wiring e) (Sum.inl k)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
        rcases x with k | j
        · rfl
        · simpa [rightWiringVertexTarget, wiring] using
            edgeEnds_same_component s (wiring e) j
  right_inv := fun _ => rfl

@[simp]
theorem rightWiringComponentEquiv_vertex_inl (k : Fin s.ncomp) :
    rightWiringComponentEquiv s e
        (vertexComponent s (wiring e) (Sum.inl k)) =
      k :=
  rfl

@[simp]
theorem rightWiringComponentEquiv_vertex_inr (j : Fin b) :
    rightWiringComponentEquiv s e
        (vertexComponent s (wiring e) (Sum.inr j)) =
      s.outComp j :=
  rfl

private def rightWiringVertexFiberEquiv
    (q : GlueComponent s (wiring e)) :
    GlueVertexFiber s (wiring e) q ≃
      {k : Fin s.ncomp // k = rightWiringComponentEquiv s e q} ⊕
        GlueEdgeFiber s (wiring e) q where
  toFun x := by
    rcases x with ⟨k | j, hx⟩
    · exact Sum.inl ⟨k, by
        simpa using congrArg (rightWiringComponentEquiv s e) hx⟩
    · change Fin b at j
      exact Sum.inr ⟨j, by
        simpa [wiring] using
          (edgeEnds_same_component s (wiring e) j).trans hx⟩
  invFun x := by
    rcases x with k | j
    · exact ⟨Sum.inl k.1, by
        apply (rightWiringComponentEquiv s e).injective
        simpa using k.2⟩
    · exact ⟨Sum.inr j.1, by
        simpa [wiring] using
          (edgeEnds_same_component s (wiring e) j.1).symm.trans j.2⟩
  left_inv x := by
    rcases x with ⟨k | j, hk⟩ <;> rfl
  right_inv x := by
    rcases x with k | j <;> rfl

theorem rightWiring_vertexCount
    (q : GlueComponent s (wiring e)) :
    vertexCount s (wiring e) q =
      edgeCount s (wiring e) q + 1 := by
  rw [show vertexCount s (wiring e) q =
      Nat.card
        ({k : Fin s.ncomp //
            k = rightWiringComponentEquiv s e q} ⊕
          GlueEdgeFiber s (wiring e) q) from
    Nat.card_congr (rightWiringVertexFiberEquiv s e q)]
  simp [edgeCount, Nat.add_comm]

theorem rightWiring_oldGenus
    (q : GlueComponent s (wiring e)) :
    oldGenus s (wiring e) q =
      s.genus (rightWiringComponentEquiv s e q) := by
  classical
  have heq (k : Fin s.ncomp) :
      (vertexComponent s (wiring e) (Sum.inl k) = q) =
        (k = rightWiringComponentEquiv s e q) := by
    apply propext
    constructor
    · intro h
      simpa using congrArg (rightWiringComponentEquiv s e) h
    · intro h
      apply (rightWiringComponentEquiv s e).injective
      simpa using h
  unfold oldGenus
  change
    (∑ k : Fin s.ncomp,
        if vertexComponent s (wiring e) (Sum.inl k) = q
        then s.genus k else 0) +
      (∑ j : Fin b,
        if vertexComponent s (wiring e) (Sum.inr j) = q
        then 0 else 0) =
      s.genus (rightWiringComponentEquiv s e q)
  simp_rw [heq]
  simp

theorem rightWiring_gluedGenus
    (q : GlueComponent s (wiring e)) :
    gluedGenus s (wiring e) q =
      s.genus (rightWiringComponentEquiv s e q) := by
  rw [gluedGenus, rightWiring_oldGenus s e q,
    rightWiring_vertexCount s e q]
  omega

def rightWiringLabelEquiv :
    Fin (comp s (wiring e)).ncomp ≃ Fin s.ncomp := by
  let Q := GlueComponent s (wiring e)
  letI : Fintype Q :=
    (glueFiniteCode s (wiring e)).fintypeComponent
  change Fin (Fintype.card Q) ≃ Fin s.ncomp
  exact (Fintype.equivFin Q).symm.trans
    (rightWiringComponentEquiv s e)

theorem rel_comp_wiring_right :
    Rel (comp s (wiring e)) (reindexOut e s) := by
  refine ⟨rightWiringLabelEquiv s e, ?_, ?_, ?_⟩
  · intro i
    simp [rightWiringLabelEquiv, comp, glueFiniteCode,
      FiniteCode.toSurfaceCode, reindexOut]
  · intro j
    simp [rightWiringLabelEquiv, comp, glueFiniteCode,
      FiniteCode.toSurfaceCode, reindexOut, wiring]
    exact rightWiringComponentEquiv_vertex_inr s e (e j)
  · intro k
    unfold rightWiringLabelEquiv comp FiniteCode.toSurfaceCode
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    exact (rightWiring_gluedGenus s e _).symm

end RightWiring

section LeftWiring

variable {a b c : ℕ} (e : Fin b ≃ Fin a) (s : SurfaceCode b c)

def leftWiringVertexTarget :
    GlueVertex (wiring e) s → Fin s.ncomp
  | Sum.inl i => s.inComp (e.symm i)
  | Sum.inr k => k

private theorem leftWiringVertexTarget_eq_of_glueConnected
    {x y : GlueVertex (wiring e) s}
    (h : (glueSetoid (wiring e) s) x y) :
    leftWiringVertexTarget e s x =
      leftWiringVertexTarget e s y := by
  change Relation.EqvGen (GlueStep (wiring e) s) x y at h
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨i, hxy⟩
      have hx : x = Sum.inl ((wiring e).outComp i) :=
        congrArg Prod.fst hxy
      have hy : y = Sum.inr (s.inComp i) :=
        congrArg Prod.snd hxy
      subst x
      subst y
      simp [leftWiringVertexTarget, wiring]
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

def leftWiringComponentEquiv :
    GlueComponent (wiring e) s ≃ Fin s.ncomp where
  toFun :=
    Quotient.lift (leftWiringVertexTarget e s)
      (fun _ _ h =>
        leftWiringVertexTarget_eq_of_glueConnected e s h)
  invFun := fun k =>
    vertexComponent (wiring e) s (Sum.inr k)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
        rcases x with i | k
        · have h :=
            (edgeEnds_same_component (wiring e) s (e.symm i)).symm
          simpa [leftWiringVertexTarget, wiring] using h
        · rfl
  right_inv := fun _ => rfl

@[simp]
theorem leftWiringComponentEquiv_vertex_inl (i : Fin a) :
    leftWiringComponentEquiv e s
        (vertexComponent (wiring e) s (Sum.inl i)) =
      s.inComp (e.symm i) :=
  rfl

@[simp]
theorem leftWiringComponentEquiv_vertex_inr (k : Fin s.ncomp) :
    leftWiringComponentEquiv e s
        (vertexComponent (wiring e) s (Sum.inr k)) =
      k :=
  rfl

private def leftWiringVertexFiberEquiv
    (q : GlueComponent (wiring e) s) :
    GlueVertexFiber (wiring e) s q ≃
      GlueEdgeFiber (wiring e) s q ⊕
        {k : Fin s.ncomp //
          k = leftWiringComponentEquiv e s q} where
  toFun x := by
    rcases x with ⟨i | k, hx⟩
    · change Fin a at i
      exact Sum.inl ⟨e.symm i, by
        simpa [wiring] using hx⟩
    · exact Sum.inr ⟨k, by
        simpa using congrArg (leftWiringComponentEquiv e s) hx⟩
  invFun x := by
    rcases x with i | k
    · exact ⟨Sum.inl (e i.1), by
        simpa [wiring] using i.2⟩
    · exact ⟨Sum.inr k.1, by
        apply (leftWiringComponentEquiv e s).injective
        simpa using k.2⟩
  left_inv x := by
    rcases x with ⟨i | k, hi⟩
    · simp
    · rfl
  right_inv x := by
    rcases x with i | k
    · simp
    · rfl

theorem leftWiring_vertexCount
    (q : GlueComponent (wiring e) s) :
    vertexCount (wiring e) s q =
      edgeCount (wiring e) s q + 1 := by
  rw [show vertexCount (wiring e) s q =
      Nat.card
        (GlueEdgeFiber (wiring e) s q ⊕
          {k : Fin s.ncomp //
            k = leftWiringComponentEquiv e s q}) from
    Nat.card_congr (leftWiringVertexFiberEquiv e s q)]
  simp [edgeCount]

theorem leftWiring_oldGenus
    (q : GlueComponent (wiring e) s) :
    oldGenus (wiring e) s q =
      s.genus (leftWiringComponentEquiv e s q) := by
  classical
  have heq (k : Fin s.ncomp) :
      (vertexComponent (wiring e) s (Sum.inr k) = q) =
        (k = leftWiringComponentEquiv e s q) := by
    apply propext
    constructor
    · intro h
      simpa using congrArg (leftWiringComponentEquiv e s) h
    · intro h
      apply (leftWiringComponentEquiv e s).injective
      simpa using h
  unfold oldGenus
  change
    (∑ i : Fin a,
        if vertexComponent (wiring e) s (Sum.inl i) = q
        then 0 else 0) +
      (∑ k : Fin s.ncomp,
        if vertexComponent (wiring e) s (Sum.inr k) = q
        then s.genus k else 0) =
      s.genus (leftWiringComponentEquiv e s q)
  simp_rw [heq]
  simp

theorem leftWiring_gluedGenus
    (q : GlueComponent (wiring e) s) :
    gluedGenus (wiring e) s q =
      s.genus (leftWiringComponentEquiv e s q) := by
  rw [gluedGenus, leftWiring_oldGenus e s q,
    leftWiring_vertexCount e s q]
  omega

def leftWiringLabelEquiv :
    Fin (comp (wiring e) s).ncomp ≃ Fin s.ncomp := by
  let Q := GlueComponent (wiring e) s
  letI : Fintype Q :=
    (glueFiniteCode (wiring e) s).fintypeComponent
  change Fin (Fintype.card Q) ≃ Fin s.ncomp
  exact (Fintype.equivFin Q).symm.trans
    (leftWiringComponentEquiv e s)

theorem rel_comp_wiring_left :
    Rel (comp (wiring e) s) (reindexIn e.symm s) := by
  refine ⟨leftWiringLabelEquiv e s, ?_, ?_, ?_⟩
  · intro i
    simp [leftWiringLabelEquiv, comp, glueFiniteCode,
      FiniteCode.toSurfaceCode, reindexIn, wiring]
    exact leftWiringComponentEquiv_vertex_inl e s i
  · intro j
    simp [leftWiringLabelEquiv, comp, glueFiniteCode,
      FiniteCode.toSurfaceCode, reindexIn]
  · intro k
    unfold leftWiringLabelEquiv comp FiniteCode.toSurfaceCode
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    exact (leftWiring_gluedGenus e s _).symm

end LeftWiring

end SurfaceCode

namespace SurfaceNF

/-- The surface normal form represented by a family of boundary-wiring
cylinders. -/
def wiring {a b : ℕ} (e : Fin b ≃ Fin a) : SurfaceNF a b :=
  Quotient.mk (SurfaceCode.setoid a b) (SurfaceCode.wiring e)

/-- Reindex incoming boundary circles of a surface normal form. -/
def reindexIn {a a' b : ℕ} (e : Fin a' ≃ Fin a) :
    SurfaceNF a b → SurfaceNF a' b :=
  Quotient.map (SurfaceCode.reindexIn e)
    (fun _ _ h => SurfaceCode.rel_reindexIn e h)

/-- Reindex outgoing boundary circles of a surface normal form. -/
def reindexOut {a b b' : ℕ} (e : Fin b' ≃ Fin b) :
    SurfaceNF a b → SurfaceNF a b' :=
  Quotient.map (SurfaceCode.reindexOut e)
    (fun _ _ h => SurfaceCode.rel_reindexOut e h)

/-- Gluing a boundary wiring on the right reindexes the outgoing boundary. -/
theorem comp_wiring_right {a b c : ℕ} (s : SurfaceNF a b)
    (e : Fin c ≃ Fin b) :
    comp s (Quotient.mk (SurfaceCode.setoid b c) (SurfaceCode.wiring e)) =
      reindexOut e s := by
  induction s using Quotient.inductionOn with
  | _ s =>
      apply Quotient.sound
      exact SurfaceCode.rel_comp_wiring_right s e

/-- Gluing a boundary wiring on the left reindexes the incoming boundary. -/
theorem comp_wiring_left {a b c : ℕ} (e : Fin b ≃ Fin a)
    (s : SurfaceNF b c) :
    comp (Quotient.mk (SurfaceCode.setoid a b) (SurfaceCode.wiring e)) s =
      reindexIn e.symm s := by
  induction s using Quotient.inductionOn with
  | _ s =>
      apply Quotient.sound
      exact SurfaceCode.rel_comp_wiring_left e s

theorem reindexOut_tensor_flip
    {a b c d : ℕ} (s : SurfaceNF a b) (t : SurfaceNF c d) :
    reindexOut finAddFlip.symm (tensor s t) =
      reindexIn finAddFlip (tensor t s) := by
  induction s using Quotient.inductionOn with
  | _ s =>
      induction t using Quotient.inductionOn with
      | _ t =>
          apply Quotient.sound
          exact SurfaceCode.rel_tensor_flip s t

theorem tensor_wiring
    {a b c d : ℕ} (e : Fin b ≃ Fin a) (f : Fin d ≃ Fin c) :
    tensor (wiring e) (wiring f) =
      wiring (SurfaceCode.sumRelabel e f) := by
  apply Quotient.sound
  exact SurfaceCode.rel_tensor_wiring e f

theorem reindexOut_wiring
    {a b c : ℕ} (e : Fin b ≃ Fin a) (f : Fin c ≃ Fin b) :
    reindexOut f (wiring e) = wiring (f.trans e) := by
  apply Quotient.sound
  exact SurfaceCode.rel_reindexOut_wiring e f

theorem comp_wiring
    {a b c : ℕ} (e : Fin b ≃ Fin a) (f : Fin c ≃ Fin b) :
    comp (wiring e) (wiring f) = wiring (f.trans e) := by
  calc
    comp (wiring e) (wiring f) =
        reindexOut f (wiring e) := by
          exact comp_wiring_right (wiring e) f
    _ = wiring (f.trans e) := reindexOut_wiring e f

@[simp]
theorem wiring_refl (n : ℕ) :
    wiring (Equiv.refl (Fin n)) = identity n := by
  rfl

theorem eqToHom_eq_wiring {a b : ℕ} (h : a = b) :
    (eqToHom (SurfaceNFObj.ext h) :
      (⟨a⟩ : SurfaceNFObj) ⟶ ⟨b⟩) =
      wiring (finCongr h).symm := by
  subst b
  rfl

end SurfaceNF

end Cob2NormalForm
