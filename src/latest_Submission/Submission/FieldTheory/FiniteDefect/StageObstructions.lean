import Submission.FieldTheory.FiniteDefect.StageFamilies


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PCShadow
open PRFact
open PRQuotie
open RCFact
open RSFact
open ONCompar
open FSCorr

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
One actual finite relator quotient descends continuously, surjectively, and
uniquely through the actual initial Koch quotient exactly when the actual Koch
kernel lies in its kernel.
-/
lemma fin_relator_kernel
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :
    DescendsContinuouslyThrough
        D.fiveRelatorFamily D.fiveRelatorPresented S ↔
      initialKochQuotient.ker ≤ S.map.ker := by
  change SCThroug initialKochQuotient
      S.map ↔ initialKochQuotient.ker ≤ S.map.ker
  exact surjectively_continuously_uniquely
    initialKochQuotient
    S.map
    initial_koch
    S.toRShadow.toShadow.map_continuous
    S.map_surjective

/--
At one actual finite relator quotient's canonical target depth, the honest
finite kernel-image stage lies in that quotient kernel exactly when the actual
initial Koch kernel does.
-/
lemma initial_koch_kernel
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :
    (initialKochImage
      (D.RelatorTargetDepth S)).ker ≤
        S.map.ker ↔
      initialKochQuotient.ker ≤ S.map.ker := by
  constructor
  · intro hstage
    exact (initial_koch_image
      (D.RelatorTargetDepth S)).trans hstage
  · intro hkernel
    apply initial_koch_layer
    · exact D.relator_target_depth
        S.map
        S.toRShadow.toShadow.map_continuous
        S.toRShadow.toShadow.target_p_group
        S.toRShadow.relator_killed
    · exact hkernel

/--
At one actual finite relator quotient's canonical target depth, the corrected
finite defect stage lies in that quotient kernel exactly when the actual
initial Koch kernel does.
-/
lemma defect_ambient_kernel
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :
    (D.canonicalDefectAmbient
      (D.RelatorTargetDepth S)).ker ≤
        S.map.ker ↔
      initialKochQuotient.ker ≤ S.map.ker := by
  rw [D.defect_ambient_image]
  exact D.initial_koch_kernel
    S

/--
The honest finite kernel-image stage at one actual finite relator quotient's
target depth is an exact continuous-surjective-unique descent test for that
quotient through the actual initial Koch quotient.
-/
lemma initial_fin_quotient
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :
    SCThroug
        (initialKochImage
          (D.RelatorTargetDepth S))
        S.map ↔
      DescendsContinuouslyThrough
        D.fiveRelatorFamily D.fiveRelatorPresented S := by
  calc
    SCThroug
        (initialKochImage
          (D.RelatorTargetDepth S))
        S.map ↔
        (initialKochImage
          (D.RelatorTargetDepth S)).ker ≤ S.map.ker :=
      surjectively_continuously_uniquely
        (initialKochImage
          (D.RelatorTargetDepth S))
        S.map
        (koch_image_quotient
          (D.RelatorTargetDepth S))
        S.toRShadow.toShadow.map_continuous
        S.map_surjective
    _ ↔ initialKochQuotient.ker ≤ S.map.ker :=
      D.initial_koch_kernel
        S
    _ ↔ DescendsContinuouslyThrough
        D.fiveRelatorFamily D.fiveRelatorPresented S :=
      (D.fin_relator_kernel
        S).symm

/--
The corrected finite defect stage at one actual finite relator quotient's
target depth is an exact continuous-surjective-unique descent test for that
quotient through the actual initial Koch quotient.
-/
lemma defect_ambient_initial
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :
    SCThroug
        (D.canonicalDefectAmbient
          (D.RelatorTargetDepth S))
        S.map ↔
      DescendsContinuouslyThrough
        D.fiveRelatorFamily D.fiveRelatorPresented S := by
  calc
    SCThroug
        (D.canonicalDefectAmbient
          (D.RelatorTargetDepth S))
        S.map ↔
        (D.canonicalDefectAmbient
          (D.RelatorTargetDepth S)).ker ≤ S.map.ker :=
      surjectively_continuously_uniquely
        (D.canonicalDefectAmbient
          (D.RelatorTargetDepth S))
        S.map
        (D.koch_defect_ambient
          (D.RelatorTargetDepth S))
        S.toRShadow.toShadow.map_continuous
        S.map_surjective
    _ ↔ initialKochQuotient.ker ≤ S.map.ker :=
      D.defect_ambient_kernel
        S
    _ ↔ DescendsContinuouslyThrough
        D.fiveRelatorFamily D.fiveRelatorPresented S :=
      (D.fin_relator_kernel
        S).symm

/--
Failure of descent for one actual finite relator quotient is witnessed by one
actual initial Koch kernel element surviving in that quotient.
-/
lemma not_witness_survives
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :
    ¬ DescendsContinuouslyThrough
        D.fiveRelatorFamily D.fiveRelatorPresented S ↔
      ∃ x : initialKochFree.Carrier,
        x ∈ initialKochQuotient.ker ∧ S.map x ≠ 1 := by
  rw [D.fin_relator_kernel]
  constructor
  · intro hnot
    rcases SetLike.not_le_iff_exists.mp hnot with ⟨x, hx, hxnot⟩
    exact ⟨x, hx, fun hxone => hxnot (MonoidHom.mem_ker.mpr hxone)⟩
  · rintro ⟨x, hx, hxsurvives⟩ hkernel
    exact hxsurvives (MonoidHom.mem_ker.mp (hkernel hx))

/--
Failure of the corrected finite defect target-depth stage to dominate one
actual finite relator quotient is witnessed by one actual initial Koch kernel
element surviving in that quotient.
-/
lemma defect_witness_survives
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :
    ¬ SCThroug
        (D.canonicalDefectAmbient
          (D.RelatorTargetDepth S))
        S.map ↔
      ∃ x : initialKochFree.Carrier,
        x ∈ initialKochQuotient.ker ∧ S.map x ≠ 1 := by
  rw [D.defect_ambient_initial]
  exact D.not_witness_survives
    S

/--
At one canonical relator layer, vanishing finite defect is exactly the
existence of a unique factor from the corrected finite defect stage back to
the original canonical relator quotient layer.
-/
lemma koch_defect_relator
    (D : KRData)
    (n : ℕ) :
    D.CanonicalDefectSubgroup n = ⊥ ↔
      FactorsUniquelyThrough
        (D.canonicalDefectAmbient n)
        (D.ZassenhausRelatorQuotient n).map := by
  constructor
  · intro hdefect
    let E :=
      Group.cSQuotie.finiteDefectBot
        D.ZassenhausRelatorSystem
        D.inverseLimitDescent
        D.limit_projection_surjective
        n
        hdefect
    have hE :
        E.toMonoidHom =
          D.canonicalKochDefect n :=
      Group.cSQuotie.defect_bot_monoid
        D.ZassenhausRelatorSystem
        D.inverseLimitDescent
        D.limit_projection_surjective
        n
        hdefect
    have hfactor :
        FactorsThrough
          (D.canonicalDefectAmbient n)
          (D.ZassenhausRelatorQuotient n).map := by
      refine ⟨E.symm.toMonoidHom, ?_⟩
      apply MonoidHom.ext
      intro x
      have hambient := DFunLike.congr_fun
        (D.koch_fin_ambient
          n)
        x
      change E.symm (D.canonicalDefectAmbient n x) =
        (D.ZassenhausRelatorQuotient n).map x
      calc
        E.symm (D.canonicalDefectAmbient n x) =
            E.symm (D.canonicalKochDefect n
              ((D.ZassenhausRelatorQuotient n).map x)) := by
          simpa only [MonoidHom.comp_apply] using congrArg E.symm hambient
        _ = E.symm (E ((D.ZassenhausRelatorQuotient n).map x)) := by
          simpa only using congrArg E.symm
            (DFunLike.congr_fun hE.symm
              ((D.ZassenhausRelatorQuotient n).map x))
        _ = (D.ZassenhausRelatorQuotient n).map x :=
          E.symm_apply_apply _
    apply factors_uniquely_ker
      (D.canonicalDefectAmbient n)
      (D.ZassenhausRelatorQuotient n).map
      (D.defect_ambient_surjective n)
    exact ker_factors_through
      (D.canonicalDefectAmbient n)
      (D.ZassenhausRelatorQuotient n).map
      hfactor
  · rintro ⟨β, hβ, _hunique⟩
    have hleft :
        β.comp (D.canonicalKochDefect n) =
          MonoidHom.id (D.ZassenhausRelatorSystem.obj n) := by
      apply MonoidHom.ext
      intro y
      rcases (D.ZassenhausRelatorQuotient n).map_surjective y with ⟨x, rfl⟩
      have hβx := DFunLike.congr_fun hβ x
      have hambient := DFunLike.congr_fun
        (D.koch_fin_ambient
          n)
        x
      change β (D.canonicalDefectAmbient n x) =
        (D.ZassenhausRelatorQuotient n).map x at hβx
      change β (D.canonicalKochDefect n
        ((D.ZassenhausRelatorQuotient n).map x)) =
        (D.ZassenhausRelatorQuotient n).map x
      calc
        β (D.canonicalKochDefect n
            ((D.ZassenhausRelatorQuotient n).map x)) =
            β (D.canonicalDefectAmbient n x) := by
          simpa only [MonoidHom.comp_apply] using congrArg β hambient.symm
        _ = (D.ZassenhausRelatorQuotient n).map x := hβx
    have hinjective : Function.Injective (D.canonicalKochDefect n) := by
      intro y z hyz
      have hy := DFunLike.congr_fun hleft y
      have hz := DFunLike.congr_fun hleft z
      change β (D.canonicalKochDefect n y) = y at hy
      change β (D.canonicalKochDefect n z) = z at hz
      exact hy.symm.trans ((congrArg β hyz).trans hz)
    exact (D.ZassenhausRelatorSystem.fin_defect_bot
      D.inverseLimitDescent
      D.limit_projection_surjective
      n).mp hinjective

/--
The desired finite quotient Koch theorem is exactly factorization back from
every corrected finite defect stage to its original canonical relator quotient
layer.
-/
lemma fin_forall_relator
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ n : ℕ,
        FactorsUniquelyThrough
          (D.canonicalDefectAmbient n)
          (D.ZassenhausRelatorQuotient n).map := by
  rw [D.forall_defect_bot]
  exact forall_congr' fun n =>
    D.koch_defect_relator
      n

/--
Failure of the desired finite quotient Koch theorem is detected by one
corrected finite defect stage that cannot factor back to its original
canonical relator quotient layer.
-/
lemma not_ambient_relator
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ n : ℕ,
        ¬ FactorsUniquelyThrough
          (D.canonicalDefectAmbient n)
          (D.ZassenhausRelatorQuotient n).map := by
  rw [D.fin_forall_relator]
  simp only [not_forall]

/--
A canonical finite defect stage obstruction at depth `n` is an actual initial
Koch kernel element that still survives in the `n`th canonical relator
quotient layer.
-/
structure DSObstru
    (D : KRData)
    (n : ℕ) where
  witness : initialKochFree.Carrier
  witness_initial_koch : witness ∈ initialKochQuotient.ker
  witnessSurvivesFin :
    (D.ZassenhausRelatorQuotient n).map witness ≠ 1

namespace DSObstru

variable
    (D : KRData)
    {n : ℕ}
    (W : D.DSObstru n)

/--
The corrected finite defect stage kills every finite defect stage obstruction
witness because it already descends through the actual initial Koch quotient.
-/
lemma defect_ambient_witness :
    D.canonicalDefectAmbient n W.witness = 1 := by
  change D.canonicalDefectFactor n
      (initialKochQuotient W.witness) = 1
  rw [MonoidHom.mem_ker.mp W.witness_initial_koch]
  exact map_one _

/--
The surviving relator-layer image of a finite defect stage obstruction lies in
the kernel of the canonical finite defect quotient map.
-/
lemma finRelatorDefect :
    (D.ZassenhausRelatorQuotient n).map W.witness ∈
      (D.canonicalKochDefect n).ker := by
  apply MonoidHom.mem_ker.mpr
  have hambient := DFunLike.congr_fun
    (D.koch_fin_ambient
      n)
    W.witness
  change D.canonicalDefectAmbient n W.witness =
    D.canonicalKochDefect n
      ((D.ZassenhausRelatorQuotient n).map W.witness) at hambient
  calc
    D.canonicalKochDefect n
        ((D.ZassenhausRelatorQuotient n).map W.witness) =
        D.canonicalDefectAmbient n W.witness :=
      hambient.symm
    _ = 1 := W.defect_ambient_witness

include W
/--
Every finite defect stage obstruction proves that the canonical finite defect
quotient genuinely collapses its original relator layer.
-/
lemma canonical_defect_injective :
    ¬ Function.Injective (D.canonicalKochDefect n) := by
  intro hinjective
  apply DSObstru.witnessSurvivesFin
    W
  apply hinjective
  exact (MonoidHom.mem_ker.mp
    W.finRelatorDefect).trans
      (map_one _).symm

end DSObstru

/--
Canonical finite defect stage obstructions at depth `n` are exactly nontrivial
finite defect images at depth `n`.
-/
lemma nonempty_defect_bot
    (D : KRData)
    (n : ℕ) :
    Nonempty (D.DSObstru n) ↔
      D.CanonicalDefectSubgroup n ≠ ⊥ := by
  constructor
  · rintro ⟨W⟩ hbot
    apply W.witnessSurvivesFin
    have hwitness :
        (D.ZassenhausRelatorQuotient n).map W.witness ∈
          D.CanonicalDefectSubgroup n := by
      rw [D.koch_defect_quotient]
      exact ⟨W.witness, W.witness_initial_koch, rfl⟩
    rw [hbot] at hwitness
    exact Subgroup.mem_bot.mp hwitness
  · intro hnontrivial
    have hnotle : ¬ (D.CanonicalDefectSubgroup n ≤ ⊥) := by
      intro hle
      exact hnontrivial (le_antisymm hle bot_le)
    rcases SetLike.not_le_iff_exists.mp hnotle with ⟨y, hy, hynotbot⟩
    rw [D.koch_defect_quotient] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨{
      witness := x
      witness_initial_koch := hx
      witnessSurvivesFin := by
        intro hxone
        apply hynotbot
        rw [Subgroup.mem_bot]
        exact hxone
    }⟩

/--
Failure of the desired finite quotient Koch theorem is exactly existence of one
canonical finite defect stage obstruction.
-/
lemma defect_stage_obstruction
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ n : ℕ, Nonempty (D.DSObstru n) := by
  rw [D.not_defect_bot]
  exact exists_congr fun n =>
    (D.nonempty_defect_bot
      n).symm

/--
For a failed theorem, the first finite defect depth carries a canonical finite
defect stage obstruction.
-/
def defectStageObstruction
    (D : KRData)
    (hnot : ¬ D.KochFactorizationTheorem) :
    D.DSObstru
      (D.canonicalDefectDepth hnot) :=
  Classical.choice
    ((D.nonempty_defect_bot
      (D.canonicalDefectDepth hnot)).mpr
      (D.ne_bot_depth hnot))

end KRData

end TBluepr
end Submission
