import Submission.ClassField.CohomologyOps.ShortComplexMap

/-!
# Milne, Class Field Theory, Remark II.1.35

The first edge sequence of the Hochschild--Serre spectral sequence is the
degree-one case of inflation--restriction.  This file records that part with
the actual inflation and restriction maps constructed in Proposition 1.34.

The longer seven-term sequence in Remark 1.35(a) additionally requires a
group-cohomological Hochschild--Serre spectral sequence and its transgression
maps; those interfaces are not currently present in Mathlib.
-/

namespace Submission.CField.COps

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

variable (A : Rep k G) (H : Subgroup G) [H.Normal]

omit [H.Normal] in
private theorem no_positive_below
    (j : ℕ) (hj : 0 < j) (hj1 : j < 1) :
    IsZero (groupCohomology (Rep.res H.subtype A) j) := by
  omega

/-- The actual complex

`H¹(G/H, Aᴴ) → H¹(G, A) → H¹(H, A)`

appearing as the first edge sequence in Remark II.1.35(b). -/
noncomputable abbrev initialComplex :
    ShortComplex (ModuleCat k) :=
  restrictionCochainsComplex A H 1 (by omega)
    (no_positive_below A H)

/-- **Remark II.1.35(b), first edge sequence.** Inflation is injective and
the degree-one inflation--restriction complex is exact. -/
theorem initial_exact_mono :
    (initialComplex A H).Exact ∧
      Mono (initialComplex A H).f :=
  cochains_short_mono A H 1 (by omega)
    (no_positive_below A H)

/-- Proposition-valued form of the first Hochschild--Serre edge sequence. -/
def InitialExactSequence : Prop :=
  (initialComplex A H).Exact ∧
    Mono (initialComplex A H).f

theorem initialExactSequence :
    InitialExactSequence A H :=
  initial_exact_mono A H

end

end Submission.CField.COps
