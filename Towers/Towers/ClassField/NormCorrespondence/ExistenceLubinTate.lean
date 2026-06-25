import Towers.ClassField.NormCorrespondence.GroupClassification

/-!
# Local existence from the Lubin--Tate finite levels

This is the paragraph immediately following Theorem I.1.15.  Every open
finite-index subgroup contains a standard subgroup.  The finite-level
calculation identifies that standard subgroup with a norm group, and
Corollary I.1.2(e) then shows that the original subgroup is a norm group.
-/

namespace Towers.CField.NCorr

open Towers.CField.LFTheory

noncomputable section

universe u

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- The finite Lubin--Tate--unramified norm calculation completes the Local
Existence Theorem.  The hypotheses are the same containment and degree facts
used in Theorem I.1.15. -/
theorem existence_levels_valuation
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (pi : Kˣ)
    (Knm : ℕ → ℕ → FASubext K)
    (hcontain : ∀ n m,
      standardOpenSubgroup K pi n m ≤ (Knm n m).normGroup)
    (hdegree : ∀ n m, (standardOpenSubgroup K pi n m).index =
      Module.finrank K (Knm n m).finiteIntermediateField) :
    LocalExistenceTheorem K := by
  intro H
  constructor
  · rintro ⟨L, rfl⟩
    have hindex :=
      finrank_induces_reciprocity
        phi L (hphi L)
    have hfinite : L.normGroup.FiniteIndex :=
      (Subgroup.finiteIndex_iff).2 (by
        rw [hindex]
        exact (Module.finrank_pos (R := K)
          (M := L.finiteIntermediateField)).ne')
    letI : L.normGroup.FiniteIndex := hfinite
    letI : (normSubgroup K L.finiteIntermediateField).FiniteIndex := by
      change L.normGroup.FiniteIndex
      infer_instance
    exact ⟨norm_subgroup K L.finiteIntermediateField,
      hfinite⟩
  · rintro ⟨hopen, hfinite⟩
    obtain ⟨n, hn⟩ := standard_open_subgroup
      K H hopen pi
    have hnorm : standardOpenSubgroup K pi n H.index =
        (Knm n H.index).normGroup :=
      standard_open_degree
        K phi hphi pi n H.index (Knm n H.index)
          (hcontain n H.index) (hdegree n H.index)
    exact supergroup_subextension_group
      phi hphi (Knm n H.index) H (hnorm ▸ hn)

end

section CanonicalValuation

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Canonical-valuation form of the Lubin--Tate input used to finish local
existence. -/
def LevelsGiveExistence : Prop :=
  letI : ValuativeRel K :=
    ValuativeRel.ofValuation (NormedField.valuation (K := K))
  letI : Valuation.Compatible (NormedField.valuation (K := K)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := K))
  ∀ [IsNonarchimedeanLocalField K],
    ∀ (phi : Kˣ →* AbsoluteAbelianGalois K),
    (∀ L : FASubext K,
      InducesLocalReciprocity K phi L) →
    ∀ (pi : Kˣ) (Knm : ℕ → ℕ → FASubext K),
    (∀ n m, standardOpenSubgroup K pi n m ≤ (Knm n m).normGroup) →
    (∀ n m, (standardOpenSubgroup K pi n m).index =
      Module.finrank K (Knm n m).finiteIntermediateField) →
    LocalExistenceTheorem K

/-- The paragraph after Theorem I.1.15, stated with the canonical valuation
and hence without an auxiliary compatibility assumption. -/
theorem existence_standard_levels :
    LevelsGiveExistence K := by
  letI : ValuativeRel K :=
    ValuativeRel.ofValuation (NormedField.valuation (K := K))
  letI : Valuation.Compatible (NormedField.valuation (K := K)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := K))
  dsimp only [LevelsGiveExistence]
  intro _ phi hphi pi Knm hcontain hdegree
  exact existence_levels_valuation
    K phi hphi pi Knm hcontain hdegree

end CanonicalValuation

end Towers.CField.NCorr
