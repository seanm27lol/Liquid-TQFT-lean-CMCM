import RequestProject.BanachEmbedding

open CategoryTheory CategoryTheory.Limits ContinuousMap

noncomputable section

attribute [-instance] semiNormedGrpToCondensedAb_preservesEqualizers

/-- A named proof that Mathlib's explicit kernel fork is limiting in `SemiNormedGrp`. -/
def semiNormedGrpForkIsLimit {V W : SemiNormedGrp.{1}} (f g : V ⟶ W) :
    IsLimit (SemiNormedGrp.fork f g) :=
  have hzero := fun (c : Fork f g) =>
    show NormedAddGroupHom.compHom (f - g).hom c.ι.hom = 0 by
      rw [SemiNormedGrp.hom_sub, map_sub, AddMonoidHom.sub_apply, sub_eq_zero]
      exact congr_arg SemiNormedGrp.Hom.hom c.condition
  Fork.IsLimit.mk _
    (fun c => SemiNormedGrp.ofHom <|
      NormedAddGroupHom.ker.lift (Fork.ι c).hom _ (hzero c))
    (fun _ => SemiNormedGrp.hom_ext <|
      NormedAddGroupHom.ker.incl_comp_lift _ _ (hzero _))
    (fun c k h => by
      ext x
      dsimp
      simp_rw [← h]
      rfl)

/-- The continuous map into the kernel induced by an equalizing family. -/
def continuousMapKernelLift (S : CompHaus.{0}ᵒᵖ)
    {V W : SemiNormedGrp.{1}} (f g : V ⟶ W)
    (s : Fork ((continuousMapTypeFunctor S).map f)
      ((continuousMapTypeFunctor S).map g)) (x : s.pt) :
    C(S.unop, (f - g).hom.ker) where
  toFun y :=
    let h0 : C(S.unop, V) := s.ι x
    ⟨h0 y, by
      rw [NormedAddGroupHom.mem_ker]
      change f (h0 y) - g (h0 y) = 0
      have hc := congrFun (Fork.condition s) x
      change (continuousMapTypeFunctor S).map f h0 =
        (continuousMapTypeFunctor S).map g h0 at hc
      have hy := congrArg (fun q : C(S.unop, W) => q y) hc
      exact sub_eq_zero.mpr hy⟩
  continuous_toFun := by
    let h0 : C(S.unop, V) := s.ι x
    exact Continuous.subtype_mk h0.continuous _

/-- The fork formed by mapping the explicit equalizer inclusion is limiting. -/
def continuousMapMappedForkIsLimit (S : CompHaus.{0}ᵒᵖ)
    {V W : SemiNormedGrp.{1}} (f g : V ⟶ W) :
    IsLimit
      (Fork.ofι
        ((continuousMapTypeFunctor S).map (SemiNormedGrp.fork f g).ι)
        (by
          simp only [← (continuousMapTypeFunctor S).map_comp]
          rw [(SemiNormedGrp.fork f g).condition]) :
        Fork ((continuousMapTypeFunctor S).map f)
          ((continuousMapTypeFunctor S).map g)) :=
  Fork.IsLimit.mk _
    (fun s x => continuousMapKernelLift S f g s x)
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

/-- Continuous maps into the explicit seminormed-group equalizer form a limiting cone. -/
def continuousMapTypeForkIsLimit (S : CompHaus.{0}ᵒᵖ)
    {V W : SemiNormedGrp.{1}} (f g : V ⟶ W) :
    IsLimit ((continuousMapTypeFunctor S).mapCone (SemiNormedGrp.fork f g)) := by
  let w := (SemiNormedGrp.fork f g).condition
  exact (isLimitMapConeForkEquiv (continuousMapTypeFunctor S) w).symm
    (continuousMapMappedForkIsLimit S f g)

/-- Pointwise continuous-map realization preserves equalizers. -/
theorem continuousMapTypeFunctor_preservesEqualizers (S : CompHaus.{0}ᵒᵖ) :
    PreservesLimitsOfShape WalkingParallelPair (continuousMapTypeFunctor S) := by
  constructor
  intro K
  let f := K.map WalkingParallelPairHom.left
  let g := K.map WalkingParallelPairHom.right
  haveI : PreservesLimit (parallelPair f g) (continuousMapTypeFunctor S) :=
    preservesLimit_of_preserves_limit_cone
      (semiNormedGrpForkIsLimit f g)
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
