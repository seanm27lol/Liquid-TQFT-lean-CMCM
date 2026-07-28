import RequestProject.Cob2UniversalConverse
import RequestProject.DijkgraafWitten

/-!
# Finite labelled diagonal Frobenius data

For a commutative ring `R` and a finite label type `ι`, this module constructs
the function algebra `ι → R` with pointwise multiplication and diagonal
comultiplication

`e i ↦ e i ⊗ e i`.

This is the labelled version of the `Fin n → ℤ` example in
`DijkgraafWitten.lean`.  It is useful as a finite, computable shadow of a
categorified theory: a permutation of labels induces an honest isomorphism of
commutative Frobenius data.  Nothing here identifies the label set with a
finite group state-sum or upgrades the algebraic cobordism presentation to a
geometric bordism category.
-/

open CategoryTheory MonoidalCategory
open ModuleCat.MonoidalCategory

noncomputable section

universe u

namespace FiniteDiagonalFrobenius

variable (R : Type u) [CommRing R]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]

/-- The finite function module carrying the diagonal Frobenius datum. -/
abbrev FunObj : ModuleCat R := ModuleCat.of R (ι → R)

/-- The delta-function basis of the finite function module. -/
def basis : Module.Basis ι R (ι → R) :=
  Pi.basisFun R ι

/-- Pointwise multiplication. -/
def mul : FunObj R ι ⊗ FunObj R ι ⟶ FunObj R ι :=
  ModuleCat.ofHom (LinearMap.mul' R (ι → R))

/-- The unit sends a scalar to the corresponding constant function. -/
def unit : 𝟙_ (ModuleCat R) ⟶ FunObj R ι :=
  ModuleCat.ofHom (Algebra.linearMap R (ι → R))

/-- Diagonal comultiplication on the delta-function basis. -/
def comul : FunObj R ι ⟶ FunObj R ι ⊗ FunObj R ι :=
  ModuleCat.ofHom <| ((basis R ι).constr R) fun i ↦
    (basis R ι i) ⊗ₜ[R] (basis R ι i)

/-- The counit is the sum of all coordinates. -/
def counit : FunObj R ι ⟶ 𝟙_ (ModuleCat R) :=
  ModuleCat.ofHom
    { toFun := fun x ↦ ∑ i, x i
      map_add' := by
        intro x y
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        simp [Finset.mul_sum] }

@[simp]
theorem mul_tmul (x y : ι → R) :
    mul R ι (x ⊗ₜ[R] y) = x * y := rfl

@[simp]
theorem unit_apply (r : R) :
    unit R ι r = r • (1 : ι → R) :=
  Algebra.algebraMap_eq_smul_one (A := ι → R) r

@[simp]
theorem comul_basis (i : ι) :
    comul R ι (basis R ι i) =
      (basis R ι i) ⊗ₜ[R] (basis R ι i) := by
  exact (basis R ι).constr_basis R
    (fun j ↦ (basis R ι j) ⊗ₜ[R] (basis R ι j)) i

@[simp]
theorem counit_apply (x : ι → R) :
    counit R ι x = ∑ i, x i := rfl

theorem basis_expansion (x : ι → R) :
    x = ∑ i, x i • basis R ι i := by
  classical
  apply funext
  simp [basis, Finset.sum_apply, Pi.single_apply]

theorem mul_basis_right (x : ι → R) (i : ι) :
    x * basis R ι i = x i • basis R ι i := by
  classical
  ext j
  by_cases h : j = i <;> simp [basis, h]

theorem basis_mul_left (i : ι) (y : ι → R) :
    basis R ι i * y = y i • basis R ι i := by
  rw [mul_comm, mul_basis_right]

theorem basis_mul_basis (i j : ι) :
    basis R ι i * basis R ι j =
      if i = j then basis R ι i else 0 := by
  classical
  by_cases h : i = j
  · subst j
    ext k
    by_cases hk : k = i <;> simp [basis, hk]
  · ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [basis, h, hki, hkj] at *

theorem mul_assoc' :
    mul R ι ▷ FunObj R ι ≫ mul R ι =
      (α_ (FunObj R ι) (FunObj R ι) (FunObj R ι)).hom ≫
        FunObj R ι ◁ mul R ι ≫ mul R ι := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          exact congrFun (mul_assoc a b y) ‹_›
      | add x y hx hy => simp_all [TensorProduct.add_tmul]
  | add x y hx hy => simp_all

theorem unit_mul :
    unit R ι ▷ FunObj R ι ≫ mul R ι =
      (λ_ (FunObj R ι)).hom := by
  exact tensor_ext fun m ↦ congrFun rfl

theorem mul_unit :
    FunObj R ι ◁ unit R ι ≫ mul R ι =
      (ρ_ (FunObj R ι)).hom := by
  convert tensor_ext (fun m r ↦ ?_)
  simp [mul, unit]
  exact mul_comm _ _

theorem comul_coassoc :
    comul R ι ≫ FunObj R ι ◁ comul R ι =
      comul R ι ≫ comul R ι ▷ FunObj R ι ≫
        (α_ (FunObj R ι) (FunObj R ι) (FunObj R ι)).hom := by
  apply ModuleCat.hom_ext
  apply (basis R ι).ext
  intro i
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.comp_apply,
    comul_basis]
  change
    (basis R ι i) ⊗ₜ[R] comul R ι (basis R ι i) =
      (α_ (FunObj R ι) (FunObj R ι) (FunObj R ι)).hom
        (comul R ι (basis R ι i) ⊗ₜ[R] basis R ι i)
  rw [comul_basis]
  rfl

theorem counit_comul :
    comul R ι ≫ counit R ι ▷ FunObj R ι =
      (λ_ (FunObj R ι)).inv := by
  classical
  apply ModuleCat.hom_ext
  apply (basis R ι).ext
  intro i
  rw [ModuleCat.comp_apply, comul_basis]
  rw [ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply]
  rw [counit_apply]
  simp [basis, Pi.single_apply]

theorem comul_counit :
    comul R ι ≫ FunObj R ι ◁ counit R ι =
      (ρ_ (FunObj R ι)).inv := by
  classical
  apply ModuleCat.hom_ext
  apply (basis R ι).ext
  intro i
  rw [ModuleCat.comp_apply, comul_basis]
  rw [ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply]
  rw [counit_apply]
  simp [basis, Pi.single_apply]

theorem comul_apply (x : ι → R) :
    comul R ι x =
      ∑ i, x i • ((basis R ι i) ⊗ₜ[R] (basis R ι i)) := by
  classical
  unfold comul basis
  erw [(Module.Basis.ofEquivFun
    (LinearEquiv.refl R (ι → R))).constr_apply]
  simp [Finsupp.sum_fintype]

theorem comul_mul :
    comul R ι ≫ mul R ι = 𝟙 (FunObj R ι) := by
  apply ModuleCat.hom_ext
  apply (basis R ι).ext
  intro i
  change mul R ι (comul R ι (basis R ι i)) = basis R ι i
  rw [comul_basis, mul_tmul, basis_mul_basis]
  simp

theorem frobenius_left :
    (FunObj R ι ◁ comul R ι) ≫
        (α_ (FunObj R ι) (FunObj R ι) (FunObj R ι)).inv ≫
        (mul R ι ▷ FunObj R ι) =
      mul R ι ≫ comul R ι := by
  classical
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      have key : ∀ (i j : ι),
          (mul R ι ▷ FunObj R ι)
              ((α_ (FunObj R ι) (FunObj R ι) (FunObj R ι)).inv
                (basis R ι i ⊗ₜ[R] comul R ι (basis R ι j))) =
            comul R ι
              (mul R ι (basis R ι i ⊗ₜ[R] basis R ι j)) := by
        intro i j
        rw [comul_basis,
          ModuleCat.MonoidalCategory.associator_inv_apply,
          ModuleCat.MonoidalCategory.whiskerRight_apply, mul_tmul]
        simp [basis_mul_basis]
        split_ifs with h
        · subst j
          rw [comul_basis]
        · simp
      have hx := basis_expansion R ι x
      have hy := basis_expansion R ι y
      rw [hx, hy]
      simp only [TensorProduct.tmul_sum, TensorProduct.sum_tmul,
        TensorProduct.tmul_smul, ModuleCat.comp_apply, map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.smul_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have h := key j i
      rw [ModuleCat.MonoidalCategory.whiskerLeft_apply]
      rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul']
      simp only [map_smul, h]
  | add x y hx hy => simp_all

theorem frobenius_right :
    (comul R ι ▷ FunObj R ι) ≫
        (α_ (FunObj R ι) (FunObj R ι) (FunObj R ι)).hom ≫
        (FunObj R ι ◁ mul R ι) =
      mul R ι ≫ comul R ι := by
  classical
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      have key : ∀ (i j : ι),
          (FunObj R ι ◁ mul R ι)
              ((α_ (FunObj R ι) (FunObj R ι) (FunObj R ι)).hom
                (comul R ι (basis R ι i) ⊗ₜ[R] basis R ι j)) =
            comul R ι
              (mul R ι (basis R ι i ⊗ₜ[R] basis R ι j)) := by
        intro i j
        rw [comul_basis,
          ModuleCat.MonoidalCategory.associator_hom_apply,
          ModuleCat.MonoidalCategory.whiskerLeft_apply, mul_tmul]
        simp [basis_mul_basis]
        split_ifs with h
        · subst j
          rw [comul_basis]
        · simp
      have hx := basis_expansion R ι x
      have hy := basis_expansion R ι y
      rw [hx, hy]
      simp only [TensorProduct.tmul_sum, TensorProduct.sum_tmul,
        TensorProduct.tmul_smul, ModuleCat.comp_apply, map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.smul_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have h := key j i
      rw [ModuleCat.MonoidalCategory.whiskerRight_apply]
      simp only [map_smul]
      rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul']
      simp only [map_smul, h]
  | add x y hx hy => simp_all

theorem mul_comm' :
    (β_ (FunObj R ι) (FunObj R ι)).hom ≫ mul R ι =
      mul R ι := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [ModuleCat.comp_apply,
        ModuleCat.MonoidalCategory.braiding_hom_apply, mul_tmul, mul_tmul]
      exact _root_.mul_comm _ _
  | add x y hx hy => simp_all

/-- The diagonal commutative Frobenius datum on a finite label type. -/
def diagonal : CommFrobeniusData (ModuleCat R) where
  X := FunObj R ι
  mul := mul R ι
  unit := unit R ι
  comul := comul R ι
  counit := counit R ι
  mul_assoc' := mul_assoc' R ι
  unit_mul := unit_mul R ι
  mul_unit := mul_unit R ι
  comul_coassoc' := comul_coassoc R ι
  counit_comul := counit_comul R ι
  comul_counit := comul_counit R ι
  frobenius_left := frobenius_left R ι
  frobenius_right := frobenius_right R ι
  mul_comm' := mul_comm' R ι

/-- The labelled diagonal datum is special: its handle operator is the
identity. -/
theorem diagonal_isSpecial :
    (diagonal R ι).comul ≫ (diagonal R ι).mul =
      𝟙 (diagonal R ι).X :=
  comul_mul R ι

/-- The handle operator of the finite labelled datum is the identity. -/
theorem diagonal_handleOperator :
    DijkgraafWitten.handleOperator (diagonal R ι) =
      𝟙 (diagonal R ι).X :=
  comul_mul R ι

/-- Every power of the handle operator of the finite labelled datum is the
identity. -/
theorem diagonal_handlePower (g : ℕ) :
    DijkgraafWitten.handlePower (diagonal R ι) g =
      𝟙 (diagonal R ι).X := by
  unfold DijkgraafWitten.handlePower
  rw [diagonal_handleOperator]
  exact DijkgraafWitten.endomorphismPower_id _ _

/-- Every connected closed genus word evaluates to the cardinality of the
finite label type. -/
theorem Z_genus (g : ℕ) :
    (((diagonal R ι).toCob2Functor.map
      (⟦DijkgraafWitten.genusWord g⟧ : Cob2Hom 0 0)).hom
        ((1 : R) : 𝟙_ (ModuleCat R))) =
      (Fintype.card ι : R) := by
  change
    (diagonal R ι).interpret (DijkgraafWitten.genusWord g) (1 : R) =
      (Fintype.card ι : R)
  rw [DijkgraafWitten.interpret_genusWord_generic, diagonal_handlePower]
  change counit R ι (unit R ι 1) = (Fintype.card ι : R)
  rw [unit_apply, counit_apply]
  simp

/-- The genus-word endomorphism of the monoidal unit is scalar multiplication
by the number of finite labels. -/
theorem Z_genus_eq_smul_id (g : ℕ) :
    (diagonal R ι).toCob2Functor.map
        (⟦DijkgraafWitten.genusWord g⟧ : Cob2Hom 0 0) =
      (Fintype.card ι : R) • 𝟙 (𝟙_ (ModuleCat R)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  refine (Z_genus R ι g).trans ?_
  change (Fintype.card ι : R) =
    (Fintype.card ι : R) * 1
  simp

/-! ## Relabeling symmetry -/

/-- Pull functions back along the inverse of a permutation.  With this
convention, the delta function at `i` is sent to the delta function at
`e i`. -/
def relabelLinearEquiv (e : Equiv.Perm ι) :
    (ι → R) ≃ₗ[R] (ι → R) where
  toFun x j := x (e.symm j)
  invFun x i := x (e i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp
  map_add' x y := rfl
  map_smul' r x := rfl

/-- The module morphism underlying a permutation of finite labels. -/
def relabelHom (e : Equiv.Perm ι) :
    FunObj R ι ⟶ FunObj R ι :=
  ModuleCat.ofHom (relabelLinearEquiv R ι e).toLinearMap

@[simp]
theorem relabelHom_apply (e : Equiv.Perm ι) (x : ι → R) (j : ι) :
    relabelHom R ι e x j = x (e.symm j) := rfl

@[simp]
theorem relabelHom_basis (e : Equiv.Perm ι) (i : ι) :
    relabelHom R ι e (basis R ι i) = basis R ι (e i) := by
  ext j
  unfold relabelHom
  rw [ModuleCat.ofHom_apply]
  change (basis R ι i) (e.symm j) = basis R ι (e i) j
  simp only [basis, Pi.basisFun_apply]
  by_cases h : j = e i
  · subst j
    rw [e.symm_apply_apply]
    simp
  · have h' : e.symm j ≠ i := by
      intro hsymm
      apply h
      simpa using congrArg e hsymm
    simp [h, h']

/-- Every permutation of the finite labels preserves all four Frobenius
structure maps. -/
def relabel (e : Equiv.Perm ι) :
    diagonal R ι ⟶ diagonal R ι where
  hom := relabelHom R ι e
  map_mul := by
    change
      (relabelHom R ι e ⊗ₘ relabelHom R ι e) ≫ mul R ι =
        mul R ι ≫ relabelHom R ι e
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        rw [ModuleCat.comp_apply,
          ModuleCat.MonoidalCategory.tensorHom_tmul,
          ModuleCat.comp_apply, mul_tmul, mul_tmul]
        rfl
    | add x y hx hy => simp_all
  map_unit := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    rfl
  map_comul := by
    change
      comul R ι ≫ (relabelHom R ι e ⊗ₘ relabelHom R ι e) =
        relabelHom R ι e ≫ comul R ι
    apply ModuleCat.hom_ext
    apply (basis R ι).ext
    intro i
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, comul_basis,
      ModuleCat.MonoidalCategory.tensorHom_tmul]
    change
      relabelHom R ι e (basis R ι i) ⊗ₜ[R]
          relabelHom R ι e (basis R ι i) =
        comul R ι (relabelHom R ι e (basis R ι i))
    rw [relabelHom_basis, comul_basis]
  map_counit := by
    change relabelHom R ι e ≫ counit R ι = counit R ι
    apply ModuleCat.hom_ext
    apply (basis R ι).ext
    intro i
    rw [ModuleCat.comp_apply, relabelHom_basis, counit_apply, counit_apply]
    simp [basis, Pi.single_apply]

@[simp]
theorem relabel_id :
    relabel R ι (Equiv.refl ι) = 𝟙 (diagonal R ι) := by
  apply CommFrobeniusData.Hom.ext
  apply ModuleCat.hom_ext
  ext x
  rfl

@[simp]
theorem relabel_comp (e f : Equiv.Perm ι) :
    relabel R ι (e.trans f) =
      relabel R ι e ≫ relabel R ι f := by
  apply CommFrobeniusData.Hom.ext
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- A label permutation as an automorphism of the diagonal Frobenius datum. -/
def relabelIso (e : Equiv.Perm ι) :
    diagonal R ι ≅ diagonal R ι where
  hom := relabel R ι e
  inv := relabel R ι e.symm
  hom_inv_id := by
    rw [← relabel_comp]
    simp
  inv_hom_id := by
    rw [← relabel_comp]
    simp

/-- Interpreting a label permutation gives a monoidal natural automorphism of
the associated algebraic symmetric TQFT. -/
noncomputable def interpretedRelabelIso (e : Equiv.Perm ι) :
    Cob2Symmetric.interpretFrobenius.obj (diagonal R ι) ≅
      Cob2Symmetric.interpretFrobenius.obj (diagonal R ι) :=
  Cob2Symmetric.interpretFrobenius.mapIso (relabelIso R ι e)

end FiniteDiagonalFrobenius
