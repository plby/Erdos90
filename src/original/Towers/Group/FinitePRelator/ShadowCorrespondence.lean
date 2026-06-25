import Towers.Group.FinitePRelator.ResidualQuotient


open scoped Topology

noncomputable section

namespace Towers
namespace RSCorr

open PCShadow
open PRFact
open PRQuotie
open RPQuotie
open RCFact
open RRQuot

universe u

variable
    {p : ℕ}
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    [T1Space G]
    {ι : Type*}
    {relator : ι → F}
    (Q : PQuot (G := G) relator)

lemma relator_shadow_universal
    (hUniversal : Q.FinitePUniversal p)
    (S : RShadow p F relator) :
    Q.quotientMap.ker ≤ S.map.ker := by
  exact ((factorization_property_quotient
    (p := p) (relator := relator) (q := Q.quotientMap)).mpr hUniversal) S

namespace Shadow

/-- Pull a finite `p`-shadow of a presented quotient target back to a relator shadow of `F`. -/
def pullbackAlongPresented
    (S : Shadow p G) :
    RShadow p F relator :=
  RRQuot.PQuot.Shadow.pullbackAlongPresented
    relator Q S

lemma along_presented_quotient
    (S : Shadow p G) :
    (pullbackAlongPresented (relator := relator) Q S).map =
      S.map.comp Q.quotientMap := rfl

lemma pullback_along_presented
    (S : Shadow p G)
    (x : F) :
    x ∈ (pullbackAlongPresented (relator := relator) Q S).map.ker ↔
      Q.quotientMap x ∈ S.map.ker := by
  exact S.pullback_kernel Q.quotientMap Q.quotientMap_continuous x

end Shadow

namespace RShadow

/--
Descend a finite relator-killing `p`-shadow through a finite-`p` universal
topological quotient candidate.
-/
def descendAlongPresented
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p)
    (S : RShadow p F relator) :
    Shadow p G where
  Target := S.Target
  map := continuousFactorQuotient
    Q.quotientMap
    S.map
    hquot
    (relator_shadow_universal Q hUniversal S)
  map_continuous := continuous_factor_quotient
    Q.quotientMap
    S.map
    hquot
    S.toShadow.map_continuous
    (relator_shadow_universal Q hUniversal S)
  target_p_group := S.toShadow.target_p_group

lemma descendAlongComp
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p)
    (S : RShadow p F relator) :
    (descendAlongPresented Q hquot hUniversal S).map.comp Q.quotientMap =
      S.map := by
  exact continuous_quotient_comp
    Q.quotientMap
    S.map
    hquot
    (relator_shadow_universal Q hUniversal S)

lemma descend_along_unique
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p)
    (S : RShadow p F relator)
    (β : G →* S.Target)
    (hβ : β.comp Q.quotientMap = S.map) :
    β = (descendAlongPresented Q hquot hUniversal S).map := by
  apply MonoidHom.ext
  intro y
  rcases Q.quotientMap_surjective y with ⟨x, rfl⟩
  have hβx := congrArg (fun φ : F →* S.Target => φ x) hβ
  have hdescx := congrArg
    (fun φ : F →* S.Target => φ x)
    (descendAlongComp Q hquot hUniversal S)
  change β (Q.quotientMap x) = S.map x at hβx
  change (descendAlongPresented Q hquot hUniversal S).map (Q.quotientMap x) =
    S.map x at hdescx
  exact hβx.trans hdescx.symm

lemma pullback_descend_along
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p)
    (S : RShadow p F relator) :
    (Shadow.pullbackAlongPresented (relator := relator) Q
      (descendAlongPresented Q hquot hUniversal S)).map =
      S.map := by
  rw [Shadow.along_presented_quotient]
  exact descendAlongComp Q hquot hUniversal S

end RShadow

namespace Shadow

lemma descend_along_presented
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p)
    (S : Shadow p G) :
    (RShadow.descendAlongPresented Q hquot hUniversal
      (pullbackAlongPresented (relator := relator) Q S)).map =
      S.map := by
  apply MonoidHom.ext
  intro y
  rcases Q.quotientMap_surjective y with ⟨x, rfl⟩
  have hcomp :=
    RShadow.descendAlongComp
      Q hquot hUniversal (pullbackAlongPresented (relator := relator) Q S)
  have happ := congrArg (fun φ : F →* S.Target => φ x) hcomp
  change (RShadow.descendAlongPresented Q hquot hUniversal
      (pullbackAlongPresented (relator := relator) Q S)).map (Q.quotientMap x) =
    (pullbackAlongPresented (relator := relator) Q S).map x at happ
  simpa [along_presented_quotient] using happ

end Shadow

namespace QShadow

/-- Pull an actual finite `p` quotient of `G` back to an actual relator quotient of `F`. -/
def pullbackAlongPresented
    (S : QShadow p G) :
    RQShadow p F relator where
  toRShadow := Shadow.pullbackAlongPresented (relator := relator) Q S.toShadow
  map_surjective := by
    intro y
    rcases S.map_surjective y with ⟨g, hg⟩
    rcases Q.quotientMap_surjective g with ⟨x, rfl⟩
    exact ⟨x, hg⟩

lemma along_presented_quotient
    (S : QShadow p G) :
    (pullbackAlongPresented (relator := relator) Q S).map =
      S.map.comp Q.quotientMap := rfl

end QShadow

namespace RQShadow

/-- Descend an actual finite relator quotient of `F` to an actual finite quotient of `G`. -/
def descendAlongPresented
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p)
    (S : RQShadow p F relator) :
    QShadow p G where
  toShadow := RShadow.descendAlongPresented
    Q hquot hUniversal S.toRShadow
  map_surjective := by
    intro y
    rcases S.map_surjective y with ⟨x, hx⟩
    exact ⟨Q.quotientMap x, by
      have hcomp := congrArg
        (fun φ : F →* S.Target => φ x)
        (RShadow.descendAlongComp
          Q hquot hUniversal S.toRShadow)
      change (RShadow.descendAlongPresented
        Q hquot hUniversal S.toRShadow).map (Q.quotientMap x) = S.map x at hcomp
      exact hcomp.trans hx⟩

lemma descendAlongComp
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p)
    (S : RQShadow p F relator) :
    (descendAlongPresented Q hquot hUniversal S).map.comp Q.quotientMap =
      S.map := by
  exact RShadow.descendAlongComp
    Q hquot hUniversal S.toRShadow

lemma descend_along_unique
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p)
    (S : RQShadow p F relator)
    (β : G →* S.Target)
    (hβ : β.comp Q.quotientMap = S.map) :
    β = (descendAlongPresented Q hquot hUniversal S).map := by
  exact RShadow.descend_along_unique
    Q hquot hUniversal S.toRShadow β hβ

lemma pullback_descend_along
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p)
    (S : RQShadow p F relator) :
    (QShadow.pullbackAlongPresented (relator := relator) Q
      (descendAlongPresented Q hquot hUniversal S)).map =
      S.map := by
  rw [QShadow.along_presented_quotient]
  exact descendAlongComp Q hquot hUniversal S

end RQShadow

namespace QShadow

lemma descend_along_presented
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p)
    (S : QShadow p G) :
    (RQShadow.descendAlongPresented Q hquot hUniversal
      (pullbackAlongPresented (relator := relator) Q S)).map =
      S.map := by
  apply MonoidHom.ext
  intro y
  rcases Q.quotientMap_surjective y with ⟨x, rfl⟩
  have hcomp :=
    RQShadow.descendAlongComp
      Q hquot hUniversal (pullbackAlongPresented (relator := relator) Q S)
  have happ := congrArg (fun φ : F →* S.Target => φ x) hcomp
  change (RQShadow.descendAlongPresented Q hquot hUniversal
      (pullbackAlongPresented (relator := relator) Q S)).map (Q.quotientMap x) =
    (pullbackAlongPresented (relator := relator) Q S).map x at happ
  simpa [along_presented_quotient] using happ

end QShadow

/--
An actual finite relator quotient of `F` descends continuously and
surjectively through a quotient candidate to the same finite target.
-/
def RelatorContinuouslyThrough
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    {ι : Type*}
    {relator : ι → F}
    (q : F →* G)
    (S : RQShadow p F relator) :
    Prop :=
  ∃ β : G →* S.Target,
    Continuous β ∧ Function.Surjective β ∧ β.comp q = S.map

/--
An actual finite relator quotient of `F` descends continuously, surjectively,
and uniquely through a quotient candidate to the same finite target.
-/
def DescendsUniquelyThrough
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    {ι : Type*}
    {relator : ι → F}
    (q : F →* G)
    (S : RQShadow p F relator) :
    Prop :=
  ∃! β : G →* S.Target,
    Continuous β ∧ Function.Surjective β ∧ β.comp q = S.map

lemma descends_continuously_through
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p)
    (S : RQShadow p F relator) :
    RelatorContinuouslyThrough Q.quotientMap S := by
  let T := RQShadow.descendAlongPresented Q hquot hUniversal S
  exact ⟨T.map, T.toShadow.map_continuous, T.map_surjective,
    RQShadow.descendAlongComp
      Q hquot hUniversal S⟩

lemma descends_continuously_uniquely
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p)
    (S : RQShadow p F relator) :
    DescendsUniquelyThrough Q.quotientMap S := by
  let T := RQShadow.descendAlongPresented Q hquot hUniversal S
  refine ⟨T.map, ?_, ?_⟩
  · exact ⟨T.toShadow.map_continuous, T.map_surjective,
      RQShadow.descendAlongComp
        Q hquot hUniversal S⟩
  · intro β hβ
    exact RQShadow.descend_along_unique
      Q hquot hUniversal S β hβ.2.2

lemma all_descend_continuously
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q) :
    Q.FinitePUniversal p ↔
      ∀ S : RQShadow p F relator,
        RelatorContinuouslyThrough Q.quotientMap S := by
  constructor
  · intro hUniversal S
    exact descends_continuously_through
      Q hquot hUniversal S
  · intro hdescend
    change QuotientFactorizationProperty p relator Q.quotientMap
    intro S
    rcases hdescend S with ⟨β, _hβcontinuous, _hβsurjective, hβ⟩
    exact ker_factors_through Q.quotientMap S.map ⟨β, hβ⟩

lemma descend_continuously_uniquely
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q) :
    Q.FinitePUniversal p ↔
      ∀ S : RQShadow p F relator,
        DescendsUniquelyThrough Q.quotientMap S := by
  constructor
  · intro hUniversal S
    exact descends_continuously_uniquely
      Q hquot hUniversal S
  · intro hdescend
    apply (all_descend_continuously Q hquot).mpr
    intro S
    exact (hdescend S).exists

/--
Every element invisible to finite relator shadows maps to an element invisible
to finite `p` shadows of the candidate quotient.
-/
lemma relator_comap_target :
    relatorKernel p relator ≤
      (residualKernel p G).comap Q.quotientMap := by
  intro x hx
  rw [Subgroup.mem_comap, residual_kernel_iff]
  intro S
  have hxPullback :
      x ∈ (Shadow.pullbackAlongPresented (relator := relator) Q S).map.ker := by
    exact relator_kernel
      (Shadow.pullbackAlongPresented (relator := relator) Q S) hx
  exact (Shadow.pullback_along_presented
    (relator := relator) Q S x).mp hxPullback

/--
For a finite-`p` universal topological quotient, the finite relator residual
kernel is exactly the pullback of the target finite-`p` residual kernel.
-/
lemma comap_target_universal
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p) :
    relatorKernel p relator =
      (residualKernel p G).comap Q.quotientMap := by
  apply le_antisymm
  · exact relator_comap_target Q
  · intro x hx
    rw [mem_relator_iff]
    intro S
    rw [Subgroup.mem_comap] at hx
    have hxDescend :
        Q.quotientMap x ∈
          (RShadow.descendAlongPresented Q hquot hUniversal S).map.ker :=
      residual_le_kernel
        (RShadow.descendAlongPresented Q hquot hUniversal S)
        hx
    have hcomp := congrArg
      (fun φ : F →* S.Target => φ x)
      (RShadow.descendAlongComp
        Q hquot hUniversal S)
    change (RShadow.descendAlongPresented Q hquot hUniversal S).map
      (Q.quotientMap x) = S.map x at hcomp
    change S.map x = 1
    rw [← hcomp]
    exact MonoidHom.mem_ker.mp hxDescend

lemma comap_residual_target
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q) :
    Q.FinitePUniversal p ↔
      relatorKernel p relator =
        (residualKernel p G).comap Q.quotientMap := by
  constructor
  · exact comap_target_universal Q hquot
  · intro hkernel
    apply (factorization_property_relator).mpr
    intro x hx
    rw [hkernel, Subgroup.mem_comap]
    rw [MonoidHom.mem_ker.mp hx]
    exact (residualKernel p G).one_mem

lemma projection_p_universal
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p) :
    (RRQuot.PQuot.residualProjection
      relator Q hUniversal).ker =
      residualKernel p G := by
  ext y
  rcases Q.quotientMap_surjective y with ⟨x, rfl⟩
  have hprojection := congrArg
    (fun φ : F →* relatorResidualQuotient (p := p) relator => φ x)
    (RRQuot.PQuot.projection_comp_quotient
      relator Q hUniversal)
  change RRQuot.PQuot.residualProjection
      relator Q hUniversal (Q.quotientMap x) = 1 ↔
    Q.quotientMap x ∈ residualKernel p G
  change RRQuot.PQuot.residualProjection
      relator Q hUniversal (Q.quotientMap x) =
    residualQuotientMap (p := p) relator x at hprojection
  rw [hprojection]
  change x ∈ (residualQuotientMap (p := p) relator).ker ↔
    Q.quotientMap x ∈ residualKernel p G
  rw [ker_residual_quotient]
  rw [comap_target_universal
    Q hquot hUniversal]
  rfl

lemma residually_injective_universal
    (hquot : RCFact.PQuot.IsTopologicalQuotient Q)
    (hUniversal : Q.FinitePUniversal p) :
    RFP p G ↔
      Function.Injective
        (RRQuot.PQuot.residualProjection
          relator Q hUniversal) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [projection_p_universal
    Q hquot hUniversal]
  rfl

end RSCorr
end Towers
