import RequestProject.BanachEmbedding

open CategoryTheory CategoryTheory.Limits ContinuousMap

noncomputable section

attribute [-instance] semiNormedGrpToCondensedAb_preservesEqualizers

/-- Continuous maps into the explicit seminormed-group equalizer form a limiting fork. -/
def continuousMapTypeForkIsLimit (S : CompHaus.{0}ᵒᵖ)
    {V W : SemiNormedGrp.{1}} (f g : V ⟶ W) :
    IsLimit ((continuousMapTypeFunctor S).mapCone (SemiNormedGrp.fork f g)) :=
  Fork.IsLimit.mk _
    (fun s x =>
      { toFun := fun y =>
          ⟨(Fork.ι s x) y, by
            rw [NormedAddGroupHom.mem_ker]
            change f ((Fork.ι s x) y) - g ((Fork.ι s x) y) = 0
            have h := congrFun (Fork.condition s) x
            have hy := congrArg (fun q : C(S.unop, W) => q y) h
            exact sub_eq_zero.mpr hy⟩
        continuous_toFun := Continuous.subtype_mk (Fork.ι s x).continuous _ })
    (fun s => by
      funext x
      apply ContinuousMap.ext
      intro y
      rfl)
    (fun s m h => by
      funext x
      apply ContinuousMap.ext
      intro y
      apply Subtype.ext
      have hx := congrFun h x
      exact congrArg (fun q : C(S.unop, V) => q y) hx)

/-- Pointwise continuous-map realization preserves equalizers. -/
theorem continuousMapTypeFunctor_preservesEqualizers (S : CompHaus.{0}ᵒᵖ) :
    PreservesLimitsOfShape WalkingParallelPair (continuousMapTypeFunctor S) := by
  constructor
  intro K
  let f := K.map WalkingParallelPairHom.left
  let g := K.map WalkingParallelPairHom.right
  haveI : PreservesLimit (parallelPair f g) (continuousMapTypeFunctor S) :=
    preservesLimit_of_preserves_limit_cone
      (SemiNormedGrp.fork f g |>.isLimit)
      (continuousMapTypeForkIsLimit S f g)
  exact preservesLimit_of_iso_diagram
    (continuousMapTypeFunctor S)
    (diagramIsoParallelPair K).symm

/-- Evaluation of the presheaf realization preserves equalizers. -/
theorem evaluatedRealization_preservesEqualizers (S : CompHaus.{0}ᵒᵖ) :
    PreservesLimitsOfShape WalkingParallelPair
      ((semiNormedGrpToCondensedAb ⋙
        sheafToPresheaf (coherentTopology CompHaus.{0})
          (ModuleCat.{1} (ULift.{1} ℤ))) ⋙
        (evaluation CompHaus.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} ℤ))).obj S) := by
  let F :=
    (semiNormedGrpToCondensedAb ⋙
      sheafToPresheaf (coherentTopology CompHaus.{0})
        (ModuleCat.{1} (ULift.{1} ℤ))) ⋙
      (evaluation CompHaus.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} ℤ))).obj S
  haveI : PreservesLimitsOfShape WalkingParallelPair (continuousMapTypeFunctor S) :=
    continuousMapTypeFunctor_preservesEqualizers S
  haveI : PreservesLimitsOfShape WalkingParallelPair
      (F ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) :=
    preservesLimitsOfShape_of_natIso (evaluatedForgetIso S).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves
    F (forget (ModuleCat.{1} (ULift.{1} ℤ)))

/-- The presheaf underlying the condensed realization preserves equalizers. -/
theorem realizationPresheaf_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      (semiNormedGrpToCondensedAb ⋙
        sheafToPresheaf (coherentTopology CompHaus.{0})
          (ModuleCat.{1} (ULift.{1} ℤ))) := by
  apply preservesLimitsOfShape_of_evaluation
  intro S
  exact evaluatedRealization_preservesEqualizers S

/-- The sheaf-level realization preserves equalizers. -/
theorem semiNormedGrpToCondensedAb_preservesEqualizers_proved :
    PreservesLimitsOfShape WalkingParallelPair semiNormedGrpToCondensedAb := by
  haveI := realizationPresheaf_preservesEqualizers
  let G := sheafToPresheaf (coherentTopology CompHaus.{0})
    (ModuleCat.{1} (ULift.{1} ℤ))
  haveI : CreatesLimitsOfShape WalkingParallelPair G :=
    CategoryTheory.Sheaf.createsLimitsOfShape
  haveI : ReflectsLimitsOfShape WalkingParallelPair G :=
    reflectsLimitsOfShapeOfCreatesLimitsOfShape G
  exact preservesLimitsOfShape_of_reflects_of_preserves
    semiNormedGrpToCondensedAb G

end
