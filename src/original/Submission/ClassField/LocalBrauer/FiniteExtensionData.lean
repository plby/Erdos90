import Submission.ClassField.LocalBrauer.FiniteExtensionNorm
import Submission.ClassField.LocalBrauer.UnramifiedNormSurjectivity

/-!
# Canonical norm data for finite local extensions

For the canonical spectral local-field structure on a finite Galois
extension, continuity and the coefficient formula for the integer-unit norm
are automatic.  Thus the unramified norm argument only needs the substantive
residue norm and the successive principal-unit corrections supplied by
trace surjectivity.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open ValuativeRel

namespace FLExt

variable (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]

/-- For the canonical finite-extension topology, the residue congruences
upgrade to the complete local norm data used by successive approximation. -/
theorem unramified_data_unit :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : IsNonarchimedeanLocalField L :=
      nonarchimedeanLocalField K L
    ∀ (hResidueAlgebra : Algebra
        (IsLocalRing.ResidueField 𝒪[K])
        (IsLocalRing.ResidueField 𝒪[L])),
      letI : Algebra
          (IsLocalRing.ResidueField 𝒪[K])
          (IsLocalRing.ResidueField 𝒪[L]) := hResidueAlgebra
      UnramifiedUnitData K L (integerUnitNorm K L) →
        UnramifiedLocalData K L (integerUnitNorm K L) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    nonarchimedeanLocalField K L
  intro hResidueAlgebra
  letI : Algebra
      (IsLocalRing.ResidueField 𝒪[K])
      (IsLocalRing.ResidueField 𝒪[L]) := hResidueAlgebra
  intro hN
  exact
    { hN with
      continuous_norm := continuous_integer_norm K L
      coe_norm := integer_norm_coe K L }

end FLExt

end

end Submission.CField.LBrauer
