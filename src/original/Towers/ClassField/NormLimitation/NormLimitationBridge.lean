import Towers.ClassField.NormLimitation.SubgroupQuotientMap

/-!
# Chapter VII, Section 9, Lemma 9.4

If the inverse image of `U` under the idèle-class norm from a finite
extension `K'/K` is a norm group, then `U` is a norm group.  The sole
arithmetic input is the norm-limitation theorem identifying the image of the
upper norm group with the norm group of the maximal abelian subextension over
`K`; the remaining containment is `map (comap U) ≤ U`.
-/

namespace Towers.CField.NLimita

open NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip

noncomputable section

universe u

private abbrev CK (K : Type u) [Field K] [NumberField K] :=
  IdeleClassGroup (RingOfIntegers K) K

/-- The norm-limitation input in the exact form used by Lemma 9.4.  It does
not mention `U`: it says that the norm of a finite abelian norm group over
`K'` is itself the norm group of a finite abelian extension of `K`. -/
def NormLimitationBridge : Prop :=
  ∀ (K K' : Type u) [Field K] [NumberField K]
    [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
    (L : FASubext K'),
    ∃ M : FASubext K,
      ideleClassSubgroup M =
        (ideleClassSubgroup L).map
          (canonicalIdeleNorm (K := K) (L := K'))

/-- Lemma 9.4 from norm limitation and Lemma 9.1. -/
theorem limitation_statement_bridges
    (h91 : (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V))
    (hlimit : NormLimitationBridge.{u}) :
    (∀ (K K' : Type u) [Field K] [NumberField K]
          [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
          (U : Subgroup (CK K)),
          IsOpen (U : Set (CK K)) → U.FiniteIndex →
          IdeleNormGroup K'
            (U.comap (canonicalIdeleNorm (K := K) (L := K'))) →
          IdeleNormGroup K U) := by
  intro K K' _ _ _ _ _ _ U _hopen _hfinite hpreimage
  obtain ⟨L, hL⟩ := hpreimage
  obtain ⟨M, hM⟩ := hlimit K K' L
  apply h91 K (ideleClassSubgroup M) U
  · exact ⟨M, rfl⟩
  · rw [hM, hL]
    exact Subgroup.map_comap_le
      (canonicalIdeleNorm (K := K) (L := K')) U

end

end Towers.CField.NLimita
