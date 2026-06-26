import Submission.ClassField.FormalGroups.FirstVariable
import Submission.ClassField.FormalGroups.LubinTateRemarks

/-!
# The Lubin--Tate block inserted in ANT Chapter 2

The current `ANT.tex` contains, immediately after Remark 2.17, a block on
Lubin--Tate formal groups numbered Example 2.18 through Exercise 2.21.  Its
definitions and proofs are developed in the Class Field Theory part of this
project.  This module records the ANT correspondence inside the algebraic
number theory development without duplicating that substantial theory.

The aliases below include the explicit p-adic binomial endomorphism, all
three assertions of Remark 2.19, the existence and uniqueness assertion of
Summary 2.20, and the formal inverse of Exercise 2.21.
-/

namespace Submission.NumberTheory.Milne

open Submission.CField.FGroups
open MvPowerSeries

/-- A normalized logarithm for a one-parameter formal group law: its linear
coefficient is one and it carries the formal group operation to addition. -/
def FormalGroupLogarithm {K : Type*} [CommRing K]
    (F : FGLaw K) (log : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff log = 0 ∧
    PowerSeries.coeff 1 log = 1 ∧
      PowerSeries.subst F.law log =
        PowerSeries.subst FGLaw.binaryX log +
          PowerSeries.subst FGLaw.binaryY log

/-- The formal-logarithm existence and uniqueness theorem cited in the Notes
after Exercise 2.21.  The source delegates this theorem to an external
reference, so it is exposed as an explicit proposition rather than an axiom. -/
def FormalLogarithmTheorem : Prop :=
  ∀ (K : Type*) [Field K] [Algebra ℚ K] (F : FGLaw K),
    ∃! log : PowerSeries K, FormalGroupLogarithm F log

/-- The second formal-logarithm assertion in the source's Notes: a normalized
logarithm conjugates an endomorphism with linear coefficient `a` to scalar
multiplication by `a`.  As above, this is the externally cited proposition. -/
def LogarithmLinearizesEndomorphisms : Prop :=
  ∀ (K : Type*) [Field K] [Algebra ℚ K]
    (F : FGLaw K) (log : PowerSeries K),
      FormalGroupLogarithm F log →
        ∀ (h : FGLaw.Hom F F) (a : K),
          homogeneousComponent 1 h.toSeries = mvLinearForm (fun _ : Fin 1 ↦ a) →
            PowerSeries.subst h.toSeries log = a • powerSeriesUnary log

alias milne_padicCyclotomic_law :=
  formal_law_multiplicative

alias milne_padicBinomialEndomorphism_nat :=
  binomial_endomorphism_nat

alias milne_padicBinomialEndomorphism_subst_commute :=
  endomorphism_subst_commute

alias milne_padicBinomialEndomorphism_eq_scalarIntertwiner :=
  unary_endomorphism_intertwiner

alias milne_uniformizer :=
  lubin_intertwiner_uniformizer

alias milne_scalarAction_injective :=
  lubin_endomorphism_injective

alias milne_canonicalIso_commutes :=
  lubin_iso_commutes

alias antSummary2_20_existsUnique_formalGroupLaw :=
  unique_formal_law

alias milne_existsUnique_inverseSeries :=
  FGSeries.unique_inverse_series

end Submission.NumberTheory.Milne
