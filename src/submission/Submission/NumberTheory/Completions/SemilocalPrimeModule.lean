import Submission.NumberTheory.Completions.SemilocalAtPrime
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Finiteness

/-!
# The semilocal upper ring as a module over the lower local ring

Localizing a finite torsion-free extension at a lower prime again gives a
finite torsion-free extension.  Since the lower localization is a DVR, the
semilocal upper ring is free and admits a finite basis.  These facts are
used to choose the integral basis in the completion argument.
-/

namespace Submission.NumberTheory.Milne

open Module

noncomputable section

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  [IsDomain R] [IsDomain S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

omit [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S] in
/-- The semilocal upper ring is torsion-free over the lower local ring. -/
theorem semilocalization_torsion_free
    (p : Ideal R) [p.IsPrime] :
    Module.IsTorsionFree (Localization.AtPrime p)
      (SemilocalizationAtPrime S p) := by
  exact Module.IsTorsionFree.of_isLocalization
    R S p.primeCompl_le_nonZeroDivisors

omit [IsDomain R] [IsDomain S] [IsDedekindDomain R]
  [IsDedekindDomain S] [Module.IsTorsionFree R S] in
/-- The semilocal upper ring is finite over the lower local ring. -/
theorem semilocalization_prime_module
    (p : Ideal R) [p.IsPrime] :
    Module.Finite (Localization.AtPrime p)
      (SemilocalizationAtPrime S p) := by
  infer_instance

omit [IsDedekindDomain S] in
/-- The semilocal upper ring is free over the lower DVR. -/
theorem semilocalization_module_free
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    Module.Free (Localization.AtPrime p)
      (SemilocalizationAtPrime S p) := by
  letI : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      R hp (Localization.AtPrime p)
  letI : Module.IsTorsionFree (Localization.AtPrime p)
      (SemilocalizationAtPrime S p) :=
    semilocalization_torsion_free p
  letI : Module.Finite (Localization.AtPrime p)
      (SemilocalizationAtPrime S p) :=
    semilocalization_prime_module p
  exact Module.free_of_finite_type_torsion_free'

omit [IsDedekindDomain S] in
/-- The index type of a chosen semilocal integral basis is finite. -/
theorem semilocalization_choose_basis
    (p : Ideal R) [p.IsPrime] :
    Finite (Module.Free.ChooseBasisIndex (Localization.AtPrime p)
      (SemilocalizationAtPrime S p)) := by
  letI : Module.IsTorsionFree (Localization.AtPrime p)
      (SemilocalizationAtPrime S p) :=
    semilocalization_torsion_free p
  letI : Module.Finite (Localization.AtPrime p)
      (SemilocalizationAtPrime S p) :=
    semilocalization_prime_module p
  infer_instance

omit [IsDedekindDomain S] in
/-- A chosen finite integral basis for the semilocal upper ring. -/
noncomputable def semilocalizationPrimeBasis
    (p : Ideal R) [p.IsPrime] :
    Basis (Module.Free.ChooseBasisIndex (Localization.AtPrime p)
      (SemilocalizationAtPrime S p))
      (Localization.AtPrime p) (SemilocalizationAtPrime S p) := by
  letI : Module.IsTorsionFree (Localization.AtPrime p)
      (SemilocalizationAtPrime S p) :=
    semilocalization_torsion_free p
  letI : Module.Finite (Localization.AtPrime p)
      (SemilocalizationAtPrime S p) :=
    semilocalization_prime_module p
  exact Module.Free.chooseBasis _ _

end

end Submission.NumberTheory.Milne
