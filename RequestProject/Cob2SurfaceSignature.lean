import RequestProject.Cob2SurfaceCategory

/-!
# Surface signatures of raw Cob2 words

This file evaluates the raw generators-and-relations syntax `Cob2Mor` in the
category of component-and-genus normal-form candidates.  The evaluation is
defined for every raw word and records composition by graph gluing and tensor
by disjoint union.

The graph calculation below proves all nine commutative-Frobenius generator
equations, so the signature descends through the original `Cob2Rel` quotient
and defines an ordinary functor.  Descent through the strengthened monoidal
and symmetric quotients additionally requires the corresponding disjoint-
union functoriality and coherence results; no comparison with geometric
bordisms is asserted here.
-/

noncomputable section

namespace Cob2NormalForm

open CategoryTheory
open SurfaceNF

namespace SurfaceCode

section ConnectedZeroGluing

variable {a b c : ℕ} (s : SurfaceCode a b) (t : SurfaceCode b c)

private def fullFiberEquiv
    {α β : Type} [Subsingleton β] (f : α → β) (q : β) :
    {x : α // f x = q} ≃ α where
  toFun := Subtype.val
  invFun := fun x => ⟨x, Subsingleton.elim _ _⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- If every old vertex lies in one graph component, the component quotient
is a subsingleton. -/
theorem glueComponent_subsingleton_of_vertex
    (x₀ : GlueVertex s t)
    (hvertex : ∀ x, vertexComponent s t x = vertexComponent s t x₀) :
    Subsingleton (GlueComponent s t) := by
  constructor
  intro q r
  induction q using Quotient.inductionOn with
  | _ x =>
      induction r using Quotient.inductionOn with
      | _ y => exact (hvertex x).trans (hvertex y).symm

/-- A connected gluing graph whose old genera vanish and whose number of
edges is one less than its number of vertices produces genus zero. -/
theorem gluedGenus_eq_zero_of_tree
    [Subsingleton (GlueComponent s t)]
    (hs : ∀ i, s.genus i = 0)
    (ht : ∀ j, t.genus j = 0)
    (htree : b + 1 = s.ncomp + t.ncomp)
    (q : GlueComponent s t) :
    gluedGenus s t q = 0 := by
  have hvertex :
      vertexCount s t q = s.ncomp + t.ncomp := by
    let e := fullFiberEquiv
      (fun x : GlueVertex s t => vertexComponent s t x) q
    simpa [vertexCount, GlueVertex] using Nat.card_congr e
  have hedge : edgeCount s t q = b := by
    let e := fullFiberEquiv
      (fun i : Fin b =>
        vertexComponent s t (Sum.inl (s.outComp i))) q
    simpa [edgeCount] using Nat.card_congr e
  have hold : oldGenus s t q = 0 := by
    unfold oldGenus
    simp [hs, ht]
  simp only [gluedGenus, hold, hedge, hvertex]
  omega

/-- A nonempty connected tree gluing of genus-zero component codes is
relabel-equivalent to the canonical connected genus-zero code. -/
theorem rel_comp_connected_zero_of_tree
    (x₀ : GlueVertex s t)
    (hvertex : ∀ x, vertexComponent s t x = vertexComponent s t x₀)
    (hs : ∀ i, s.genus i = 0)
    (ht : ∀ j, t.genus j = 0)
    (htree : b + 1 = s.ncomp + t.ncomp) :
    Rel (comp s t) (connected a c 0) := by
  letI : Subsingleton (GlueComponent s t) :=
    glueComponent_subsingleton_of_vertex s t x₀ hvertex
  let Q := GlueComponent s t
  letI : Fintype Q := (glueFiniteCode s t).fintypeComponent
  have hcard : Fintype.card Q = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨vertexComponent s t x₀, ?_⟩
    intro q
    exact Subsingleton.elim _ _
  let e : Fin (Fintype.card Q) ≃ Fin 1 := finCongr hcard
  change Rel (glueFiniteCode s t).toSurfaceCode (connected a c 0)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro i
    change e _ = (0 : Fin 1)
    exact Subsingleton.elim _ _
  · intro j
    change e _ = (0 : Fin 1)
    exact Subsingleton.elim _ _
  · intro k
    change 0 =
      gluedGenus s t ((Fintype.equivFin Q).symm k)
    exact (gluedGenus_eq_zero_of_tree s t hs ht htree _).symm

end ConnectedZeroGluing

end SurfaceCode

namespace SurfaceNF

/-- The one-cylinder representative is the canonical connected genus-zero
code. -/
theorem identity_one_eq_connected :
    identity 1 = connected 1 1 0 := by
  apply Quotient.sound
  refine ⟨Equiv.refl (Fin 1), ?_, ?_, ?_⟩
  · intro i
    change Fin 1 at i
    fin_cases i
    rfl
  · intro j
    change Fin 1 at j
    fin_cases j
    rfl
  · intro k
    rfl

/-- Joining two genus-zero connected components, each along one outgoing
circle, to a connected pair-of-pants target produces one genus-zero
component. -/
theorem tensor_connected_pair_comp_connected
    (a a' c : ℕ) :
    comp
        (tensor (connected a 1 0) (connected a' 1 0))
        (connected 2 c 0) =
      connected (a + a') c 0 := by
  apply Quotient.sound
  let s : SurfaceCode (a + a') 2 :=
    SurfaceCode.tensor
      (SurfaceCode.connected a 1 0)
      (SurfaceCode.connected a' 1 0)
  let t : SurfaceCode 2 c := SurfaceCode.connected 2 c 0
  change SurfaceCode.Rel (SurfaceCode.comp s t)
    (SurfaceCode.connected (a + a') c 0)
  apply SurfaceCode.rel_comp_connected_zero_of_tree s t
    (Sum.inr (0 : Fin 1))
  · intro x
    rcases x with i | j
    · change Fin 2 at i
      fin_cases i
      · simpa [s, t, SurfaceCode.tensor, SurfaceCode.connected] using
          SurfaceCode.edgeEnds_same_component s t (0 : Fin 2)
      · simpa [s, t, SurfaceCode.tensor, SurfaceCode.connected] using
          SurfaceCode.edgeEnds_same_component s t (1 : Fin 2)
    · change Fin 1 at j
      fin_cases j
      rfl
  · intro i
    change (SurfaceCode.tensor
      (SurfaceCode.connected a 1 0)
      (SurfaceCode.connected a' 1 0)).genus i = 0
    refine Fin.addCases ?_ ?_ i
    · intro k
      change
        Fin.addCases (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
            (Fin.castAdd 1 k) = 0
      rw [Fin.addCases_left]
    · intro k
      change
        Fin.addCases (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
            (Fin.natAdd 1 k) = 0
      rw [Fin.addCases_right]
  · intro j
    change (SurfaceCode.connected 2 c 0).genus j = 0
    simp [SurfaceCode.connected]
  · rfl

/-- The dual tree gluing: splitting one connected component across two
one-input connected targets again produces a single genus-zero component. -/
theorem connected_comp_tensor_connected_pair
    (a c c' : ℕ) :
    comp
        (connected a 2 0)
        (tensor (connected 1 c 0) (connected 1 c' 0)) =
      connected a (c + c') 0 := by
  apply Quotient.sound
  let s : SurfaceCode a 2 := SurfaceCode.connected a 2 0
  let t : SurfaceCode 2 (c + c') :=
    SurfaceCode.tensor
      (SurfaceCode.connected 1 c 0)
      (SurfaceCode.connected 1 c' 0)
  change SurfaceCode.Rel (SurfaceCode.comp s t)
    (SurfaceCode.connected a (c + c') 0)
  apply SurfaceCode.rel_comp_connected_zero_of_tree s t
    (Sum.inl (0 : Fin 1))
  · intro x
    rcases x with i | j
    · change Fin 1 at i
      fin_cases i
      rfl
    · change Fin 2 at j
      fin_cases j
      · simpa [s, t, SurfaceCode.tensor, SurfaceCode.connected] using
          (SurfaceCode.edgeEnds_same_component s t (0 : Fin 2)).symm
      · simpa [s, t, SurfaceCode.tensor, SurfaceCode.connected] using
          (SurfaceCode.edgeEnds_same_component s t (1 : Fin 2)).symm
  · intro i
    change (SurfaceCode.connected a 2 0).genus i = 0
    simp [SurfaceCode.connected]
  · intro j
    change (SurfaceCode.tensor
      (SurfaceCode.connected 1 c 0)
      (SurfaceCode.connected 1 c' 0)).genus j = 0
    refine Fin.addCases ?_ ?_ j
    · intro k
      change
        Fin.addCases (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
            (Fin.castAdd 1 k) = 0
      rw [Fin.addCases_left]
    · intro k
      change
        Fin.addCases (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
            (Fin.natAdd 1 k) = 0
      rw [Fin.addCases_right]
  · rfl

/-- The left unit Frobenius generator equation holds for graph-gluing
surface signatures. -/
theorem unit_left :
    comp (tensor unit (identity 1)) mul = identity 1 := by
  rw [identity_one_eq_connected]
  exact tensor_connected_pair_comp_connected 0 1 1

/-- The right unit Frobenius generator equation holds for graph-gluing
surface signatures. -/
theorem unit_right :
    comp (tensor (identity 1) unit) mul = identity 1 := by
  rw [identity_one_eq_connected]
  exact tensor_connected_pair_comp_connected 1 0 1

/-- Associativity of the multiplication generator follows because both
parenthesizations glue the same three-boundary genus-zero component. -/
theorem mul_assoc :
    comp (tensor mul (identity 1)) mul =
      comp (tensor (identity 1) mul) mul := by
  rw [identity_one_eq_connected]
  exact
    (tensor_connected_pair_comp_connected 2 1 1).trans
      (tensor_connected_pair_comp_connected 1 2 1).symm

/-- The left counit Frobenius generator equation holds for graph-gluing
surface signatures. -/
theorem counit_left :
    comp comul (tensor counit (identity 1)) = identity 1 := by
  rw [identity_one_eq_connected]
  exact connected_comp_tensor_connected_pair 1 0 1

/-- The right counit Frobenius generator equation holds for graph-gluing
surface signatures. -/
theorem counit_right :
    comp comul (tensor (identity 1) counit) = identity 1 := by
  rw [identity_one_eq_connected]
  exact connected_comp_tensor_connected_pair 1 1 0

/-- Coassociativity of the comultiplication generator follows because both
parenthesizations give the same three-output genus-zero component. -/
theorem comul_coassoc :
    comp comul (tensor comul (identity 1)) =
      comp comul (tensor (identity 1) comul) := by
  rw [identity_one_eq_connected]
  exact
    (connected_comp_tensor_connected_pair 1 2 1).trans
      (connected_comp_tensor_connected_pair 1 1 2).symm

/-- Swapping the two inputs before multiplication does not change the
connected genus-zero surface signature. -/
theorem mul_comm :
    comp (swap 1 1) mul = mul := by
  apply Quotient.sound
  let s : SurfaceCode 2 2 := SurfaceCode.swap 1 1
  let t : SurfaceCode 2 1 := SurfaceCode.connected 2 1 0
  change SurfaceCode.Rel (SurfaceCode.comp s t)
    (SurfaceCode.connected 2 1 0)
  apply SurfaceCode.rel_comp_connected_zero_of_tree s t
    (Sum.inr (0 : Fin 1))
  · intro x
    rcases x with i | j
    · change Fin 2 at i
      fin_cases i
      · simpa [s, t, SurfaceCode.swap, SurfaceCode.connected,
          finAddFlip] using
          SurfaceCode.edgeEnds_same_component s t (1 : Fin 2)
      · simpa [s, t, SurfaceCode.swap, SurfaceCode.connected,
          finAddFlip] using
          SurfaceCode.edgeEnds_same_component s t (0 : Fin 2)
    · change Fin 1 at j
      fin_cases j
      rfl
  · intro i
    change (SurfaceCode.swap 1 1).genus i = 0
    rfl
  · intro j
    change (SurfaceCode.connected 2 1 0).genus j = 0
    rfl
  · rfl

/-- The first Frobenius gluing pattern is a four-vertex tree and therefore
has the connected genus-zero signature. -/
theorem frobenius_tree :
    comp
        (tensor (a := 1) (b := 1) (c := 1) (d := 2)
          (connected 1 1 0) comul)
        (tensor (a := 2) (b := 1) (c := 1) (d := 1)
          mul (connected 1 1 0)) =
      connected 2 2 0 := by
  apply Quotient.sound
  let s : SurfaceCode 2 3 :=
    SurfaceCode.tensor
      (SurfaceCode.connected 1 1 0)
      (SurfaceCode.connected 1 2 0)
  let t : SurfaceCode 3 2 :=
    SurfaceCode.tensor
      (SurfaceCode.connected 2 1 0)
      (SurfaceCode.connected 1 1 0)
  change SurfaceCode.Rel (SurfaceCode.comp s t)
    (SurfaceCode.connected 2 2 0)
  have e0 :
      SurfaceCode.vertexComponent s t (Sum.inl (0 : Fin 2)) =
        SurfaceCode.vertexComponent s t (Sum.inr (0 : Fin 2)) := by
    simpa [s, t, SurfaceCode.tensor, SurfaceCode.connected] using
      SurfaceCode.edgeEnds_same_component s t (0 : Fin 3)
  have e1 :
      SurfaceCode.vertexComponent s t (Sum.inl (1 : Fin 2)) =
        SurfaceCode.vertexComponent s t (Sum.inr (0 : Fin 2)) := by
    simpa [s, t, SurfaceCode.tensor, SurfaceCode.connected] using
      SurfaceCode.edgeEnds_same_component s t (1 : Fin 3)
  have e2 :
      SurfaceCode.vertexComponent s t (Sum.inl (1 : Fin 2)) =
        SurfaceCode.vertexComponent s t (Sum.inr (1 : Fin 2)) := by
    simpa [s, t, SurfaceCode.tensor, SurfaceCode.connected] using
      SurfaceCode.edgeEnds_same_component s t (2 : Fin 3)
  apply SurfaceCode.rel_comp_connected_zero_of_tree s t
    (Sum.inl (0 : Fin 2))
  · intro x
    rcases x with i | j
    · change Fin 2 at i
      fin_cases i
      · rfl
      · exact e1.trans e0.symm
    · change Fin 2 at j
      fin_cases j
      · exact e0.symm
      · exact e2.symm.trans (e1.trans e0.symm)
  · intro i
    change (SurfaceCode.tensor
      (SurfaceCode.connected 1 1 0)
      (SurfaceCode.connected 1 2 0)).genus i = 0
    refine Fin.addCases ?_ ?_ i
    · intro k
      change
        Fin.addCases (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
            (Fin.castAdd 1 k) = 0
      rw [Fin.addCases_left]
    · intro k
      change
        Fin.addCases (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
            (Fin.natAdd 1 k) = 0
      rw [Fin.addCases_right]
  · intro j
    change (SurfaceCode.tensor
      (SurfaceCode.connected 2 1 0)
      (SurfaceCode.connected 1 1 0)).genus j = 0
    refine Fin.addCases ?_ ?_ j
    · intro k
      change
        Fin.addCases (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
            (Fin.castAdd 1 k) = 0
      rw [Fin.addCases_left]
    · intro k
      change
        Fin.addCases (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
            (Fin.natAdd 1 k) = 0
      rw [Fin.addCases_right]
  · rfl

/-- The opposite Frobenius gluing pattern is the mirror four-vertex tree and
has the same connected genus-zero signature. -/
theorem frobenius_right_tree :
    comp
        (tensor (a := 1) (b := 2) (c := 1) (d := 1)
          comul (connected 1 1 0))
        (tensor (a := 1) (b := 1) (c := 2) (d := 1)
          (connected 1 1 0) mul) =
      connected 2 2 0 := by
  apply Quotient.sound
  let s : SurfaceCode 2 3 :=
    SurfaceCode.tensor
      (SurfaceCode.connected 1 2 0)
      (SurfaceCode.connected 1 1 0)
  let t : SurfaceCode 3 2 :=
    SurfaceCode.tensor
      (SurfaceCode.connected 1 1 0)
      (SurfaceCode.connected 2 1 0)
  change SurfaceCode.Rel (SurfaceCode.comp s t)
    (SurfaceCode.connected 2 2 0)
  have e0 :
      SurfaceCode.vertexComponent s t (Sum.inl (0 : Fin 2)) =
        SurfaceCode.vertexComponent s t (Sum.inr (0 : Fin 2)) := by
    simpa [s, t, SurfaceCode.tensor, SurfaceCode.connected] using
      SurfaceCode.edgeEnds_same_component s t (0 : Fin 3)
  have e1 :
      SurfaceCode.vertexComponent s t (Sum.inl (0 : Fin 2)) =
        SurfaceCode.vertexComponent s t (Sum.inr (1 : Fin 2)) := by
    simpa [s, t, SurfaceCode.tensor, SurfaceCode.connected] using
      SurfaceCode.edgeEnds_same_component s t (1 : Fin 3)
  have e2 :
      SurfaceCode.vertexComponent s t (Sum.inl (1 : Fin 2)) =
        SurfaceCode.vertexComponent s t (Sum.inr (1 : Fin 2)) := by
    simpa [s, t, SurfaceCode.tensor, SurfaceCode.connected] using
      SurfaceCode.edgeEnds_same_component s t (2 : Fin 3)
  apply SurfaceCode.rel_comp_connected_zero_of_tree s t
    (Sum.inl (0 : Fin 2))
  · intro x
    rcases x with i | j
    · change Fin 2 at i
      fin_cases i
      · rfl
      · exact e2.trans e1.symm
    · change Fin 2 at j
      fin_cases j
      · exact e0.symm
      · exact e1.symm
  · intro i
    change (SurfaceCode.tensor
      (SurfaceCode.connected 1 2 0)
      (SurfaceCode.connected 1 1 0)).genus i = 0
    refine Fin.addCases ?_ ?_ i
    · intro k
      change
        Fin.addCases (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
            (Fin.castAdd 1 k) = 0
      rw [Fin.addCases_left]
    · intro k
      change
        Fin.addCases (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
            (Fin.natAdd 1 k) = 0
      rw [Fin.addCases_right]
  · intro j
    change (SurfaceCode.tensor
      (SurfaceCode.connected 1 1 0)
      (SurfaceCode.connected 2 1 0)).genus j = 0
    refine Fin.addCases ?_ ?_ j
    · intro k
      change
        Fin.addCases (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
            (Fin.castAdd 1 k) = 0
      rw [Fin.addCases_left]
    · intro k
      change
        Fin.addCases (fun _ : Fin 1 => 0) (fun _ : Fin 1 => 0)
            (Fin.natAdd 1 k) = 0
      rw [Fin.addCases_right]
  · rfl

/-- The first Frobenius generator equation holds for surface signatures. -/
theorem frobenius :
    comp
        (tensor (a := 1) (b := 1) (c := 1) (d := 2)
          (identity 1) comul)
        (tensor (a := 2) (b := 1) (c := 1) (d := 1)
          mul (identity 1)) =
      comp mul comul := by
  rw [identity_one_eq_connected]
  have hcenter : comp mul comul = connected 2 2 0 := by
    simpa using comp_connected 2 1 2 0 0 (by omega)
  exact frobenius_tree.trans hcenter.symm

/-- The opposite Frobenius generator equation holds for surface
signatures. -/
theorem frobenius_right :
    comp
        (tensor (a := 1) (b := 2) (c := 1) (d := 1)
          comul (identity 1))
        (tensor (a := 1) (b := 1) (c := 2) (d := 1)
          (identity 1) mul) =
      comp mul comul := by
  rw [identity_one_eq_connected]
  have hcenter : comp mul comul = connected 2 2 0 := by
    simpa using comp_connected 2 1 2 0 0 (by omega)
  exact frobenius_right_tree.trans hcenter.symm

end SurfaceNF

namespace Cob2Mor

/-- The component-and-genus signature of a raw Frobenius word. -/
def signature : {a b : ℕ} → _root_.Cob2Mor a b → SurfaceNF a b
  | _, _, .id n => identity n
  | _, _, .μ => mul
  | _, _, .η => unit
  | _, _, .δ => comul
  | _, _, .ε => counit
  | _, _, .comp f g => comp (signature f) (signature g)
  | _, _, .tensor f g => tensor (signature f) (signature g)
  | _, _, .swap a b => swap a b

@[simp]
theorem signature_id (n : ℕ) :
    signature (_root_.Cob2Mor.id n) = identity n :=
  rfl

@[simp]
theorem signature_mul :
    signature _root_.Cob2Mor.μ = mul :=
  rfl

@[simp]
theorem signature_unit :
    signature _root_.Cob2Mor.η = unit :=
  rfl

@[simp]
theorem signature_comul :
    signature _root_.Cob2Mor.δ = comul :=
  rfl

@[simp]
theorem signature_counit :
    signature _root_.Cob2Mor.ε = counit :=
  rfl

@[simp]
theorem signature_comp {a b c : ℕ}
    (f : _root_.Cob2Mor a b) (g : _root_.Cob2Mor b c) :
    signature (.comp f g) = comp (signature f) (signature g) :=
  rfl

@[simp]
theorem signature_tensor {a b c d : ℕ}
    (f : _root_.Cob2Mor a b) (g : _root_.Cob2Mor c d) :
    signature (.tensor f g) = tensor (signature f) (signature g) :=
  rfl

@[simp]
theorem signature_swap (a b : ℕ) :
    signature (_root_.Cob2Mor.swap a b) = swap a b :=
  rfl

/-- Equality transports in the raw syntax evaluate to the corresponding
categorical transport between wrapped arities. -/
theorem signature_eqToMor {a b : ℕ} (h : a = b) :
    (signature (_root_.Cob2Mor.eqToMor h) :
      (⟨a⟩ : SurfaceNFObj) ⟶ (⟨b⟩ : SurfaceNFObj)) =
      eqToHom (SurfaceNFObj.ext h) := by
  subst b
  rfl

/-- The signature validates the left identity relation of the raw category
syntax. -/
theorem signature_id_comp {a b : ℕ} (f : _root_.Cob2Mor a b) :
    signature (.comp (.id a) f) = signature f := by
  exact SurfaceNF.identity_comp (signature f)

/-- The signature validates the right identity relation of the raw category
syntax. -/
theorem signature_comp_id {a b : ℕ} (f : _root_.Cob2Mor a b) :
    signature (.comp f (.id b)) = signature f := by
  exact SurfaceNF.comp_identity (signature f)

/-- The signature validates associativity of raw composition. -/
theorem signature_assoc {a b c d : ℕ}
    (f : _root_.Cob2Mor a b) (g : _root_.Cob2Mor b c)
    (h : _root_.Cob2Mor c d) :
    signature (.comp (.comp f g) h) =
      signature (.comp f (.comp g h)) := by
  exact SurfaceNF.comp_assoc (signature f) (signature g) (signature h)

/-- Equality of two first factors is preserved by signature composition. -/
theorem signature_comp_congr_left {a b c : ℕ}
    {f f' : _root_.Cob2Mor a b} (h : signature f = signature f')
    (g : _root_.Cob2Mor b c) :
    signature (.comp f g) = signature (.comp f' g) := by
  exact congrArg (fun s => SurfaceNF.comp s (signature g)) h

/-- Equality of two second factors is preserved by signature composition. -/
theorem signature_comp_congr_right {a b c : ℕ}
    (f : _root_.Cob2Mor a b) {g g' : _root_.Cob2Mor b c}
    (h : signature g = signature g') :
    signature (.comp f g) = signature (.comp f g') := by
  exact congrArg (SurfaceNF.comp (signature f)) h

/-- Signature equality is a congruence for raw composition. -/
theorem signature_comp_congr {a b c : ℕ}
    {f f' : _root_.Cob2Mor a b} {g g' : _root_.Cob2Mor b c}
    (hf : signature f = signature f')
    (hg : signature g = signature g') :
    signature (.comp f g) = signature (.comp f' g') := by
  exact congrArg₂ SurfaceNF.comp hf hg

/-- Signature equality is a congruence for raw tensor words. -/
theorem signature_tensor_congr {a b c d : ℕ}
    {f f' : _root_.Cob2Mor a b} {g g' : _root_.Cob2Mor c d}
    (hf : signature f = signature f')
    (hg : signature g = signature g') :
    signature (.tensor f g) = signature (.tensor f' g') := by
  exact congrArg₂ SurfaceNF.tensor hf hg

/-- Once the nine Frobenius-generator equations have been established for
graph gluing and disjoint union, the raw signature respects every constructor
of the original relation `Cob2Rel`.  Keeping these hypotheses explicit
pinpoints the remaining mathematical work rather than treating quotient
descent as already available. -/
theorem signature_cob2Rel_sound_of_generator_equations
    (h_mul_assoc :
      SurfaceNF.comp
          (SurfaceNF.tensor (a := 2) (b := 1) (c := 1) (d := 1)
            SurfaceNF.mul (SurfaceNF.identity 1))
          SurfaceNF.mul =
        SurfaceNF.comp
          (SurfaceNF.tensor (a := 1) (b := 1) (c := 2) (d := 1)
            (SurfaceNF.identity 1) SurfaceNF.mul)
          SurfaceNF.mul)
    (h_unit_left :
      SurfaceNF.comp
          (SurfaceNF.tensor (a := 0) (b := 1) (c := 1) (d := 1)
            SurfaceNF.unit (SurfaceNF.identity 1))
          SurfaceNF.mul =
        SurfaceNF.identity 1)
    (h_unit_right :
      SurfaceNF.comp
          (SurfaceNF.tensor (a := 1) (b := 1) (c := 0) (d := 1)
            (SurfaceNF.identity 1) SurfaceNF.unit)
          SurfaceNF.mul =
        SurfaceNF.identity 1)
    (h_comul_coassoc :
      SurfaceNF.comp SurfaceNF.comul
          (SurfaceNF.tensor (a := 1) (b := 2) (c := 1) (d := 1)
            SurfaceNF.comul (SurfaceNF.identity 1)) =
        SurfaceNF.comp SurfaceNF.comul
          (SurfaceNF.tensor (a := 1) (b := 1) (c := 1) (d := 2)
            (SurfaceNF.identity 1) SurfaceNF.comul))
    (h_counit_left :
      SurfaceNF.comp SurfaceNF.comul
          (SurfaceNF.tensor (a := 1) (b := 0) (c := 1) (d := 1)
            SurfaceNF.counit (SurfaceNF.identity 1)) =
        SurfaceNF.identity 1)
    (h_counit_right :
      SurfaceNF.comp SurfaceNF.comul
          (SurfaceNF.tensor (a := 1) (b := 1) (c := 1) (d := 0)
            (SurfaceNF.identity 1) SurfaceNF.counit) =
        SurfaceNF.identity 1)
    (h_frobenius :
      SurfaceNF.comp
          (SurfaceNF.tensor (a := 1) (b := 1) (c := 1) (d := 2)
            (SurfaceNF.identity 1) SurfaceNF.comul)
          (SurfaceNF.tensor (a := 2) (b := 1) (c := 1) (d := 1)
            SurfaceNF.mul (SurfaceNF.identity 1)) =
        SurfaceNF.comp SurfaceNF.mul SurfaceNF.comul)
    (h_frobenius_right :
      SurfaceNF.comp
          (SurfaceNF.tensor (a := 1) (b := 2) (c := 1) (d := 1)
            SurfaceNF.comul (SurfaceNF.identity 1))
          (SurfaceNF.tensor (a := 1) (b := 1) (c := 2) (d := 1)
            (SurfaceNF.identity 1) SurfaceNF.mul) =
        SurfaceNF.comp SurfaceNF.mul SurfaceNF.comul)
    (h_mul_comm :
      SurfaceNF.comp (SurfaceNF.swap 1 1) SurfaceNF.mul =
        SurfaceNF.mul)
    {a b : ℕ} {f g : _root_.Cob2Mor a b}
    (h : _root_.Cob2Rel f g) :
    signature f = signature g := by
  induction h with
  | id_comp f => exact signature_id_comp f
  | comp_id f => exact signature_comp_id f
  | assoc f g h => exact signature_assoc f g h
  | mul_assoc => exact h_mul_assoc
  | unit_left => exact h_unit_left
  | unit_right => exact h_unit_right
  | comul_coassoc => exact h_comul_coassoc
  | counit_left => exact h_counit_left
  | counit_right => exact h_counit_right
  | frobenius => exact h_frobenius
  | frobenius_right => exact h_frobenius_right
  | mul_comm => exact h_mul_comm
  | comp_congr _ _ ihf ihg => exact signature_comp_congr ihf ihg
  | tensor_congr _ _ ihf ihg => exact signature_tensor_congr ihf ihg
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ihfg ihgh => exact ihfg.trans ihgh

/-- Every relation in the original commutative-Frobenius quotient preserves
the component-and-genus signature. -/
theorem signature_cob2Rel_sound
    {a b : ℕ} {f g : _root_.Cob2Mor a b}
    (h : _root_.Cob2Rel f g) :
    signature f = signature g := by
  exact signature_cob2Rel_sound_of_generator_equations
    SurfaceNF.mul_assoc
    SurfaceNF.unit_left
    SurfaceNF.unit_right
    SurfaceNF.comul_coassoc
    SurfaceNF.counit_left
    SurfaceNF.counit_right
    SurfaceNF.frobenius
    SurfaceNF.frobenius_right
    SurfaceNF.mul_comm
    h

end Cob2Mor

namespace Cob2Hom

/-- The surface signature descends through the original `Cob2Rel`
quotient.  This is an ordinary-category construction; descent through the
stronger monoidal and symmetric relations is a separate next step. -/
def signature {a b : ℕ} :
    _root_.Cob2Hom a b → SurfaceNF a b :=
  Quotient.lift Cob2Mor.signature
    (fun _ _ h => Cob2Mor.signature_cob2Rel_sound h)

@[simp]
theorem signature_mk {a b : ℕ} (f : _root_.Cob2Mor a b) :
    signature (⟦f⟧ : _root_.Cob2Hom a b) = Cob2Mor.signature f :=
  rfl

end Cob2Hom

/-- The component-and-genus signature is an ordinary functor from the
original Frobenius presentation category. -/
def surfaceSignatureFunctor : _root_.Cob2Cat ⥤ SurfaceNFObj where
  obj n := ⟨n⟩
  map f := Cob2Hom.signature f
  map_id _ := rfl
  map_comp f g := by
    induction f using Quotient.inductionOn with
    | _ f =>
        induction g using Quotient.inductionOn with
        | _ g => rfl

end Cob2NormalForm
