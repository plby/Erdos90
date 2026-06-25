import Towers.ClassField.Shifting.ShapiroNaturality
import Towers.ClassField.CohomologyOps.RestrictionCompatibility

open Lean Meta Elab Tactic

elab "apply_private_shapiro_coind_naturality" : tactic => do
  let env ← getEnv
  let some (n, _) := env.constants.toList.find? fun (n, _) =>
      n.toString.endsWith "coindIso_naturality"
    | throwError "private coindIso_naturality not found"
  let goal ← getMainGoal
  let goals ← goal.apply (← mkConstWithFreshMVarLevels n)
  replaceMainGoal goals

namespace Towers.CField.COps

open CategoryTheory Rep

noncomputable section

variable {G : Type} [Group G]

theorem coind_naturality_bridge
    {H : Subgroup G} {A B : Rep ℤ H} (f : A ⟶ B) (n : ℕ) :
    (groupCohomology.coindIso A n).hom ≫
        groupCohomology.map (MonoidHom.id H) f n =
      groupCohomology.map (MonoidHom.id G)
          ((coindFunctor ℤ H.subtype).map f) n ≫
        (groupCohomology.coindIso B n).hom := by
  apply_private_shapiro_coind_naturality

theorem coind_iso_counit
    (H : Subgroup G) (A : Rep ℤ H) (n : ℕ) :
    (groupCohomology.coindIso A n).hom =
      restriction (coind H.subtype A) H n ≫
        groupCohomology.map (MonoidHom.id H)
          ((resCoindAdjunction ℤ H.subtype).counit.app A) n := by
  rw [restriction_shapiro]
  dsimp only [shapiroRestriction]
  rw [Category.assoc]
  have hnat := coind_naturality_bridge
    ((resCoindAdjunction ℤ H.subtype).counit.app A) n
  have hnat' :
      (groupCohomology.coindIso
          (Rep.res H.subtype (coind H.subtype A)) n).hom ≫
          groupCohomology.map (MonoidHom.id H)
            ((resCoindAdjunction ℤ H.subtype).counit.app A) n =
        groupCohomology.map (MonoidHom.id G)
            ((coindFunctor ℤ H.subtype).map
              ((resCoindAdjunction ℤ H.subtype).counit.app A)) n ≫
          (groupCohomology.coindIso A n).hom := by
    simpa using hnat
  slice_rhs 2 3 => exact hnat'
  let F := groupCohomology.functor ℤ G n
  let f := F.map
    ((resCoindAdjunction ℤ H.subtype).unit.app (coind H.subtype A))
  let g := F.map ((coindFunctor ℤ H.subtype).map
    ((resCoindAdjunction ℤ H.subtype).counit.app A))
  let h := (groupCohomology.coindIso A n).hom
  have htri := (resCoindAdjunction ℤ H.subtype).right_triangle_components A
  have hfg : f ≫ g = 𝟙 _ := by
    let η := (resCoindAdjunction ℤ H.subtype).unit.app (coind H.subtype A)
    let ε := (coindFunctor ℤ H.subtype).map
      ((resCoindAdjunction ℤ H.subtype).counit.app A)
    have htri' : η ≫ ε = 𝟙 (coind H.subtype A) := by exact htri
    calc
      f ≫ g = F.map (η ≫ ε) := (F.map_comp η ε).symm
      _ = F.map (𝟙 (coind H.subtype A)) := congrArg (fun q => F.map q) htri'
      _ = 𝟙 _ := F.map_id _
  change h = f ≫ g ≫ h
  symm
  calc
    f ≫ g ≫ h = (f ≫ g) ≫ h := (Category.assoc f g h).symm
    _ = 𝟙 _ ≫ h := congrArg (fun q => q ≫ h) hfg
    _ = h := Category.id_comp h

end
end Towers.CField.COps
