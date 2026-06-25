import Towers.Group.FinitePRelator.ContinuousFactorization


open scoped Topology

noncomputable section

namespace Towers
namespace RSFact

open PRFact
open RCFact

universe u

/--
One homomorphism is a surjective continuous quotient of another homomorphism
when the induced target map is continuous and onto.
-/
def SFThroug
    {F G P : Type u}
    [Group F]
    [Group G]
    [TopologicalSpace G]
    [Group P]
    [TopologicalSpace P]
    (q : F →* G)
    (α : F →* P) :
    Prop :=
  ∃ β : G →* P, Continuous β ∧ Function.Surjective β ∧ β.comp q = α

/--
One homomorphism is a unique surjective continuous quotient of another
homomorphism when the induced target map is unique among continuous onto
factor maps.
-/
def SCThroug
    {F G P : Type u}
    [Group F]
    [Group G]
    [TopologicalSpace G]
    [Group P]
    [TopologicalSpace P]
    (q : F →* G)
    (α : F →* P) :
    Prop :=
  ∃! β : G →* P, Continuous β ∧ Function.Surjective β ∧ β.comp q = α

variable
    {F G P : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [Group G]
    [TopologicalSpace G]
    [Group P]
    [TopologicalSpace P]
    (q : F →* G)
    (α : F →* P)

omit [TopologicalSpace F] [IsTopologicalGroup F] in
/--
A surjective continuous factorization is in particular an ordinary
factorization.
-/
lemma SFThroug.factorsThrough
    (hfactor : SFThroug q α) :
    FactorsThrough q α := by
  rcases hfactor with ⟨β, _hβcontinuous, _hβsurjective, hβ⟩
  exact ⟨β, hβ⟩

omit [TopologicalSpace F] [IsTopologicalGroup F] in
/--
A surjective continuous factorization is in particular a continuous
factorization.
-/
lemma SFThroug.continuouslyFactorsThrough
    (hfactor : SFThroug q α) :
    CFThroug q α := by
  rcases hfactor with ⟨β, hβcontinuous, _hβsurjective, hβ⟩
  exact ⟨β, hβcontinuous, hβ⟩

omit [TopologicalSpace F] [IsTopologicalGroup F] in
/--
A unique surjective continuous factorization is in particular an ordinary
surjective continuous factorization.
-/
lemma SCThroug.surjec_conti_facto
    (hfactor : SCThroug q α) :
    SFThroug q α := by
  rcases hfactor with ⟨β, hβ, _hunique⟩
  exact ⟨β, hβ⟩

omit [TopologicalSpace F] [IsTopologicalGroup F] [TopologicalSpace G] [TopologicalSpace P] in
/--
Any factor map of an onto target map is onto.
-/
lemma factor_surjective_comp
    (β : G →* P)
    (hβ : β.comp q = α)
    (hαsurj : Function.Surjective α) :
    Function.Surjective β := by
  intro y
  rcases hαsurj y with ⟨x, rfl⟩
  exact ⟨q x, DFunLike.congr_fun hβ x⟩

omit [TopologicalSpace F] [IsTopologicalGroup F] in
/--
For an onto target map, continuous factorization and surjective continuous
factorization are the same condition.
-/
lemma surjectively_continuously_surjective
    (hαsurj : Function.Surjective α) :
    SFThroug q α ↔
      CFThroug q α := by
  constructor
  · exact SFThroug.continuouslyFactorsThrough q α
  · rintro ⟨β, hβcontinuous, hβ⟩
    exact ⟨β, hβcontinuous,
      factor_surjective_comp q α β hβ hαsurj,
      hβ⟩

omit [TopologicalSpace F] [IsTopologicalGroup F] in
/--
For an onto target map, continuous unique factorization and surjective
continuous unique factorization are the same condition.
-/
lemma surjective_unique_factorization
    (hαsurj : Function.Surjective α) :
    SCThroug q α ↔
      ContinuouslyFactorsUniquely q α := by
  constructor
  · rintro ⟨β, hβ, hunique⟩
    refine ⟨β, ⟨hβ.1, hβ.2.2⟩, ?_⟩
    intro γ hγ
    apply hunique γ
    exact ⟨hγ.1,
      factor_surjective_comp q α γ hγ.2 hαsurj,
      hγ.2⟩
  · rintro ⟨β, hβ, hunique⟩
    refine ⟨β, ?_, ?_⟩
    · exact ⟨hβ.1,
        factor_surjective_comp q α β hβ.2 hαsurj,
        hβ.2⟩
    · intro γ hγ
      exact hunique γ ⟨hγ.1, hγ.2.2⟩

omit [TopologicalSpace F] [IsTopologicalGroup F] in
/--
A surjective continuous factorization forces source-kernel containment.
-/
lemma ker_surjectively_through
    (hfactor : SFThroug q α) :
    q.ker ≤ α.ker := by
  exact ker_factors_through q α hfactor.factorsThrough

omit [IsTopologicalGroup F] [TopologicalSpace P] in
/--
If the target map is onto, then the canonical continuous factor through a
quotient map is also onto.
-/
lemma continuous_factor_surjective
    (hquot : Topology.IsQuotientMap q)
    (hker : q.ker ≤ α.ker)
    (hαsurj : Function.Surjective α) :
    Function.Surjective (continuousFactorQuotient q α hquot hker) := by
  intro y
  rcases hαsurj y with ⟨x, rfl⟩
  exact ⟨q x, DFunLike.congr_fun
    (continuous_quotient_comp q α hquot hker)
    x⟩

omit [IsTopologicalGroup F] in
/--
Kernel containment through a quotient map gives a surjective continuous
factorization whenever the target map itself is onto.
-/
lemma surjectively_continuously_factors
    (hquot : Topology.IsQuotientMap q)
    (hα : Continuous α)
    (hαsurj : Function.Surjective α)
    (hker : q.ker ≤ α.ker) :
    SFThroug q α := by
  exact ⟨continuousFactorQuotient q α hquot hker,
    continuous_factor_quotient q α hquot hα hker,
    continuous_factor_surjective q α hquot hker hαsurj,
    continuous_quotient_comp q α hquot hker⟩

omit [IsTopologicalGroup F] in
/--
For an onto target map, surjective continuous factorization through a quotient
map is exactly source-kernel containment.
-/
lemma surjectively_through_surjective
    (hquot : Topology.IsQuotientMap q)
    (hα : Continuous α)
    (hαsurj : Function.Surjective α) :
    SFThroug q α ↔ q.ker ≤ α.ker := by
  constructor
  · exact ker_surjectively_through q α
  · exact surjectively_continuously_factors
      q α hquot hα hαsurj

omit [IsTopologicalGroup F] in
/--
For an onto target map, unique surjective continuous factorization through a
quotient map is exactly source-kernel containment.
-/
lemma surjectively_continuously_uniquely
    (hquot : Topology.IsQuotientMap q)
    (hα : Continuous α)
    (hαsurj : Function.Surjective α) :
    SCThroug q α ↔ q.ker ≤ α.ker := by
  rw [surjective_unique_factorization
    q α hαsurj]
  exact continuously_uniquely_ker q α hquot hα

end RSFact
end Towers
