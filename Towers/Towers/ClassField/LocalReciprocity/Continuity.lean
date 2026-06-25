import Towers.ClassField.NormCorrespondence.SubgroupOpenClosed
import Towers.ClassField.LocalReciprocity.CupPairing

/-!
# Continuity of the finite abelian local Artin homomorphism

The norm-residue definition makes the kernel exactly the norm subgroup.
Lemma I.1.3 proves that subgroup open, so the homomorphism to the finite
discrete Galois group is continuous.
-/

namespace Towers.CField.LRecip

open Towers.CField.LFTheory

noncomputable section

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance continuityValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance continuityCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] [IsMulCommutative Gal(L/K)]

/-- The kernel of the finite abelian local Artin homomorphism is exactly the
field-norm subgroup. -/
theorem abelian_artin_ker :
    (abelianArtinHom K L).ker = normSubgroup K L := by
  ext x
  rw [MonoidHom.mem_ker]
  change abelianLocalArtin K L
      (QuotientGroup.mk' (normSubgroup K L) x) = 1 ↔
    x ∈ normSubgroup K L
  constructor
  · intro hx
    apply (QuotientGroup.eq_one_iff x).1
    apply (abelianLocalArtin K L).injective
    simpa using hx
  · intro hx
    have hq : QuotientGroup.mk' (normSubgroup K L) x = 1 :=
      (QuotientGroup.eq_one_iff x).2 hx
    calc
      abelianLocalArtin K L
          (QuotientGroup.mk' (normSubgroup K L) x) =
          abelianLocalArtin K L 1 := congrArg _ hq
      _ = 1 := map_one (abelianLocalArtin K L)

/-- The finite abelian local Artin homomorphism is continuous. -/
theorem abelian_artin_continuous :
    Continuous (abelianArtinHom K L) := by
  letI : Finite (Kˣ ⧸ normSubgroup K L) :=
    Finite.of_injective (abelianLocalArtin K L)
      (abelianLocalArtin K L).injective
  letI : (normSubgroup K L).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, nhds_discrete Gal(L/K), map_one,
    Filter.tendsto_pure]
  change ((abelianArtinHom K L).ker : Set Kˣ) ∈ nhds 1
  have hopen : IsOpen
      ((abelianArtinHom K L).ker : Set Kˣ) := by
    rw [abelian_artin_ker K L]
    exact norm_subgroup K L
  exact hopen.mem_nhds (by simp)

end

end Towers.CField.LRecip
