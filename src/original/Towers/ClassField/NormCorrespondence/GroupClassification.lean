import Towers.ClassField.NormCorrespondence.InverseLimit
import Towers.ClassField.NormCorrespondence.FiniteLevelArgument

/-!
# Class Field Theory, Chapter I, Theorem 1.15

The finite Lubin--Tate--unramified composita are cofinal among all finite
abelian subextensions.  Since the maximal abelian extension is the union of
its finite Galois subextensions, their supremum is the full maximal abelian
extension.  This is the local Kronecker--Weber theorem in the form used in
Milne's proof.
-/

namespace Towers.CField.NCorr

open Towers.CField.LFTheory

noncomputable section

universe u

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- **Theorem I.1.15 (Local Kronecker--Weber).**

Here `Knm n m` is the finite compositum `K_{π,n} K_m`.  The containment
hypothesis is condition (d) for the constructed Lubin--Tate Artin map after
Claim I.1.14, and the degree hypothesis is the displayed calculation
`[K_{π,n}K_m : K] = (Kˣ : U_{n,m})`.  The conclusion says that the union
of these finite composita is the maximal abelian extension. -/
theorem of_compatibleValuation
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ L : FASubext K,
      InducesLocalReciprocity K phi L)
    (pi : Kˣ)
    (Knm : ℕ → ℕ → FASubext K)
    (hcontain : ∀ n m,
      standardOpenSubgroup K pi n m ≤ (Knm n m).normGroup)
    (hdegree : ∀ n m, (standardOpenSubgroup K pi n m).index =
      Module.finrank K (Knm n m).finiteIntermediateField) :
    maximalAbelianIntermediate K =
      ⨆ n, ⨆ m, (Knm n m).intermediateField := by
  apply le_antisymm
  · intro x hx
    let xM : maximalAbelianIntermediate K := ⟨x, hx⟩
    let E : FiniteGaloisIntermediateField K
        (maximalAbelianIntermediate K) :=
      FiniteGaloisIntermediateField.adjoin K ({xM} : Set _)
    let L : FASubext K :=
      maximalAbelianSubextension K E
    obtain ⟨n, hn⟩ := standard_norm_level
      K phi hphi pi Knm hcontain hdegree L
    have hxE : xM ∈ E.toIntermediateField :=
      FiniteGaloisIntermediateField.subset_adjoin K ({xM} : Set _) (by simp)
    have hxL : x ∈ L.intermediateField := by
      change x ∈ IntermediateField.lift E.toIntermediateField
      exact (IntermediateField.mem_lift xM).2 hxE
    apply (le_iSup (fun n ↦ ⨆ m, (Knm n m).intermediateField) n)
    apply (le_iSup (fun m ↦ (Knm n m).intermediateField)
      L.normGroup.index)
    exact hn hxL
  · refine iSup_le fun n ↦ iSup_le fun m ↦ ?_
    exact subextension_maximal_intermediate
      K (Knm n m)

end

section CanonicalValuation

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Hypothesis-minimal statement of Theorem I.1.15.  The valuative relation
and its compatibility are canonically induced by the norm valuation, rather
than exposed as additional assumptions. -/
def LocalNormClassification : Prop :=
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
    maximalAbelianIntermediate K =
      ⨆ n, ⨆ m, (Knm n m).intermediateField

/-- **Theorem I.1.15**, with the canonical valuation and no added
compatibility hypothesis. -/
theorem localNormClassification : LocalNormClassification K := by
  letI : ValuativeRel K :=
    ValuativeRel.ofValuation (NormedField.valuation (K := K))
  letI : Valuation.Compatible (NormedField.valuation (K := K)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := K))
  dsimp only [LocalNormClassification]
  intro _ phi hphi pi Knm hcontain hdegree
  exact of_compatibleValuation
    K phi hphi pi Knm hcontain hdegree

end CanonicalValuation

end Towers.CField.NCorr
