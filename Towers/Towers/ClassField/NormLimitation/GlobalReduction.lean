import Towers.ClassField.NormLimitation.NormLimitation
import Towers.ClassField.NormLimitation.PrimeReduction
import Towers.ClassField.GlobalClass.GaloisClosure

/-!
# Theorem VII.9.5 from norm limitation

The preceding files prove the induction from Lemmas 9.1, 9.3, and 9.4.
Theorem VIII.4.8 supplies the only additional input needed to discharge
Lemma 9.4.
-/

namespace Towers.CField.NLimita

open NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.GClass

noncomputable section

universe u

/-- **Theorem VII.9.5.**  The idèlic existence theorem follows from
Lemmas 9.1 and 9.3 together with the existential consequence of norm
limitation. -/
theorem globalLimitationStatement
    (h91 : (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V))
    (h93 : ExistenceStatementInterface.{u})
    (h48 : ExistentialNormLimitation.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K]
      (U : Subgroup
        (IdeleClassGroup (RingOfIntegers K) K)),
      IsOpen (U : Set (IdeleClassGroup (RingOfIntegers K) K)) →
      U.FiniteIndex → IdeleNormGroup K U :=
  prime_reduction_lemmas h91 h93
    (normLimitationStatement h91 h48)

/-- Field-specific form of Theorem VII.9.5 from norm limitation. -/
theorem global_norm_limitation
    (K : Type u) [Field K] [NumberField K]
    (h91 : (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V))
    (h93 : ExistenceStatementInterface.{u})
    (h48 : ExistentialNormLimitation.{u}) :
    EveryIndexGroup K := by
  intro U hUopen hUfinite
  exact globalLimitationStatement
    h91 h93 h48 K U hUopen hUfinite

/-- Lemma VII.9.4 with norm limitation expanded into the preceding global
cohomological theorems. -/
theorem limitation_bridge_cohomology
    (h91 : (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V))
    (h51 : Towers.CField.CIdeles.IdeleCohomologyClaims.{u})
    (h47 : RelativeInvariantGenerator.{u})
    (hTate : TateNegBridge.{u})
    (hcore : CorestrictionCokernelBridge.{u}) :
    (∀ (K K' : Type u) [Field K] [NumberField K]
          [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
          (U : Subgroup (IdeleClassGroup (NumberField.RingOfIntegers K) K)),
          IsOpen (U : Set (IdeleClassGroup (NumberField.RingOfIntegers K) K)) → U.FiniteIndex →
          IdeleNormGroup K'
            (U.comap (canonicalIdeleNorm (K := K) (L := K'))) →
          IdeleNormGroup K U) :=
  normLimitationStatement h91
    (existential_limitation_results
      h51 h47 hTate hcore)

/-- **Theorem VII.9.5**, with norm limitation expanded into the exact
cohomological inputs used in Milne's proof. -/
theorem limitation_existence_cohomology
    (h91 : (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V))
    (h93 : ExistenceStatementInterface.{u})
    (h51 : Towers.CField.CIdeles.IdeleCohomologyClaims.{u})
    (h47 : RelativeInvariantGenerator.{u})
    (hTate : TateNegBridge.{u})
    (hcore : CorestrictionCokernelBridge.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K]
      (U : Subgroup
        (IdeleClassGroup (RingOfIntegers K) K)),
      IsOpen (U : Set (IdeleClassGroup (RingOfIntegers K) K)) →
      U.FiniteIndex → IdeleNormGroup K U :=
  globalLimitationStatement h91 h93
    (existential_limitation_results
      h51 h47 hTate hcore)

end

end Towers.CField.NLimita
