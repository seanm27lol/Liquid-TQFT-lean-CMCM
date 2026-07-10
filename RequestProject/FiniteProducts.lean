import RequestProject.BanachEmbedding

open CategoryTheory CategoryTheory.Limits ContinuousMap

noncomputable section

attribute [-instance] semiNormedGrpToCondensedAb_preservesFiniteProducts

/-- The underlying type-valued functor obtained by evaluating the condensed realization at `S`. -/
def continuousMapTypeFunctor (S : CompHaus.{0}ᵒᵖ) :
    SemiNormedGrp.{1} ⥤ Type 1 where
  obj V := C(S.unop, V)
  map φ g :=
    ⟨(ConcreteCategory.hom φ) ∘ g,
      (ConcreteCategory.hom φ).continuous.comp g.continuous⟩
  map_id := by
    intro V
    ext g x
    rfl
  map_comp := by
    intro X Y Z φ ψ
    ext g x
    rfl

/-- Evaluating the sheaf-level realization and forgetting the module structure is
naturally isomorphic to the explicit continuous-map functor. -/
def evaluatedForgetIso (S : CompHaus.{0}ᵒᵖ) :
    (((semiNormedGrpToCondensedAb ⋙
      sheafToPresheaf (coherentTopology CompHaus.{0})
        (ModuleCat.{1} (ULift.{1} ℤ))) ⋙
      (evaluation CompHaus.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} ℤ))).obj S) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))) ≅
      continuousMapTypeFunctor S :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    rfl)

/-- The mapped explicit product cone is limiting after evaluating at `S` and
forgetting to types. -/
def continuousMapTypePiIsLimit (S : CompHaus.{0}ᵒᵖ) {n : ℕ}
    (V : Fin n → SemiNormedGrp.{1}) :
    IsLimit ((continuousMapTypeFunctor S).mapCone (SemiNormedGrp.piFan V)) where
  lift s x := ContinuousMap.pi (fun i => (s.π.app (Discrete.mk i)) x)
  fac s j := by
    rcases j with ⟨i⟩
    rfl
  uniq s m hm := by
    funext x
    apply ContinuousMap.ext
    intro y
    funext i
    have h := congrFun (hm (Discrete.mk i)) x
    exact congrArg (fun f : C(S.unop, V i) => f y) h

/-- Continuous maps into a finite product preserve that product at the level of types. -/
theorem continuousMapTypeFunctor_preservesFiniteProducts (S : CompHaus.{0}ᵒᵖ) :
    PreservesFiniteProducts (continuousMapTypeFunctor S) := by
  constructor
  intro n
  constructor
  intro K
  let V : Fin n → SemiNormedGrp.{1} := fun i => K.obj (Discrete.mk i)
  haveI : PreservesLimit (Discrete.functor V) (continuousMapTypeFunctor S) :=
    preservesLimit_of_preserves_limit_cone
      (SemiNormedGrp.piFanIsLimit V)
      (continuousMapTypePiIsLimit S V)
  exact preservesLimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := K)).symm

/-- The evaluated presheaf-valued realization preserves finite products. -/
theorem evaluatedRealization_preservesFiniteProducts (S : CompHaus.{0}ᵒᵖ) :
    PreservesFiniteProducts
      ((semiNormedGrpToCondensedAb ⋙
        sheafToPresheaf (coherentTopology CompHaus.{0})
          (ModuleCat.{1} (ULift.{1} ℤ))) ⋙
        (evaluation CompHaus.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} ℤ))).obj S) := by
  let F :=
    (semiNormedGrpToCondensedAb ⋙
      sheafToPresheaf (coherentTopology CompHaus.{0})
        (ModuleCat.{1} (ULift.{1} ℤ))) ⋙
      (evaluation CompHaus.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} ℤ))).obj S
  haveI : PreservesFiniteProducts (continuousMapTypeFunctor S) :=
    continuousMapTypeFunctor_preservesFiniteProducts S
  haveI : PreservesFiniteProducts (F ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) := by
    constructor
    intro n
    exact preservesLimitsOfShape_of_natIso (evaluatedForgetIso S).symm
  exact preservesFiniteProducts_of_reflects_of_preserves
    F (forget (ModuleCat.{1} (ULift.{1} ℤ))

/-- The presheaf underlying the condensed realization preserves finite products. -/
theorem realizationPresheaf_preservesFiniteProducts :
    PreservesFiniteProducts
      (semiNormedGrpToCondensedAb ⋙
        sheafToPresheaf (coherentTopology CompHaus.{0})
          (ModuleCat.{1} (ULift.{1} ℤ))) := by
  constructor
  intro n
  apply preservesLimitsOfShape_of_evaluation
  intro S
  haveI := evaluatedRealization_preservesFiniteProducts S
  infer_instance

/-- The sheaf-level realization preserves finite products, proved without the
placeholder instance in `BanachEmbedding.lean`. -/
theorem semiNormedGrpToCondensedAb_preservesFiniteProducts_proved :
    PreservesFiniteProducts semiNormedGrpToCondensedAb := by
  haveI := realizationPresheaf_preservesFiniteProducts
  exact preservesFiniteProducts_of_reflects_of_preserves
    semiNormedGrpToCondensedAb
    (sheafToPresheaf (coherentTopology CompHaus.{0})
      (ModuleCat.{1} (ULift.{1} ℤ)))

end
