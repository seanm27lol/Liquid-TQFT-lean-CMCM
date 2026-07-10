import RequestProject.BanachEmbedding
import RequestProject.FullnessCounterexample

open CategoryTheory

noncomputable section

namespace SheafNotFull

open ForgetfulNotFull

/-! ## Sheaf-level non-fullness

`FullnessCounterexample.lean` proves non-fullness for the underlying
`AddCommGrpCat`-valued presheaf functor. The sheaf condition needed to package
those presheaves as objects of `CondensedAb` was already proved in
`BanachEmbedding.lean`, so the same summation map gives a counterexample for the
actual sheaf-level functor.
-/

/-- Summation as a morphism of the `ModuleCat`-valued presheaves used by
`banachCondensed`. -/
def sumBanachPresheafMap :
    banachPresheaf (ℕ →₀ ℤ) ⟶ banachPresheaf ℤ where
  app S := ModuleCat.ofHom {
    toFun := fun g => (ContinuousMap.mk sumHom sumHom_continuous).comp g
    map_add' := by
      intro a b
      ext x
      simp [sumHom.map_add]
    map_smul' := by
      intro n a
      ext x
      simp [ContinuousMap.smul_apply]
  }
  naturality := by
    intro S T f
    ext g x
    rfl

/-- Summation packaged as a genuine morphism in `CondensedAb`. -/
def sumCondensedMap :
    banachCondensed (ℕ →₀ ℤ) ⟶ banachCondensed ℤ :=
  ⟨sumBanachPresheafMap⟩

/-- The sheaf-level functor `semiNormedGrpToCondensedAb` is not full.

The continuous unbounded summation map on finitely supported integer sequences
already defines a morphism between the associated condensed abelian groups. If
the functor were full, that morphism would be induced by a bounded group
homomorphism, contradicting `ForgetfulNotFull.no_normedAddGroupHom`. -/
theorem semiNormedGrpToCondensedAb_not_full :
    ¬ semiNormedGrpToCondensedAb.Full := by
  intro hfull
  obtain ⟨f, hf⟩ :=
    (semiNormedGrpToCondensedAb.map_surjective
      (X := SemiNormedGrp.of (ℕ →₀ ℤ))
      (Y := SemiNormedGrp.of ℤ)) sumCondensedMap
  change (⟨banachPresheafMap f⟩ :
      banachCondensed (ℕ →₀ ℤ) ⟶ banachCondensed ℤ) =
    ⟨sumBanachPresheafMap⟩ at hf
  injection hf with hnat
  have hval : ∀ a, f.hom a = sumHom a := by
    intro a
    have happ := NatTrans.congr_app hnat (Opposite.op (CompHaus.of PUnit))
    have hconst := congrArg
      (fun m => m (ContinuousMap.const _ a)) happ
    have hpoint := congrArg
      (fun g => g PUnit.unit) hconst
    simpa [banachPresheafMap, sumBanachPresheafMap] using hpoint
  exact no_normedAddGroupHom ⟨f.hom, hval⟩

end SheafNotFull
