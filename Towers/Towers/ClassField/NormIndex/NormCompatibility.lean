import Towers.ClassField.LocalBrauer.CohomologyTransport
import Towers.ClassField.Ideles.IdeleClassNorm
import Towers.ClassField.NormIndex.ClassCokernelComparison

/-!
# Norm compatibility for the idèle-class fixed-point comparison

The numerator in Corollary VII.4.4 is the quotient of the fixed idèle
classes by the group-action norm.  Lemma VII.4.1 identifies the fixed
classes with `C_K`; to identify the norm subgroup under that isomorphism one
uses the formula

`ext (Nm x) = ∏ σ, σ • x`.

This file records that formula at the level of the already defined concrete
idèle maps and proves its exact consequence on idèle classes. The property
is kept separate from `fixedDescentStatement`: it is a
compatibility of the canonical coordinatewise extension map, not an additional
assertion of the fixed-point lemma itself.
-/

namespace Towers.CField.NIndex

open IsDedekindDomain NumberField
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.ICohomo
open scoped BigOperators

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance normCompatibilityGaloisFintype :
    Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)

/-- The coordinatewise extension of a norm idèle is the product of all
Galois conjugates of the original idèle. -/
def IEData.NormCompatible
    (E : IEData (K := K) (L := L)) : Prop :=
  ∀ x : IdeleGroup (NumberField.RingOfIntegers L) L,
    E.toMonoidHom (ideleNorm (K := K) (L := L) x) =
      ∏ sigma : Gal(L/K),
        (idelesGaloisAction (K := K) (L := L)).smul sigma x

/-- Norm compatibility descends from idèles to their classes. -/
theorem IEData.classmap_canonidele_classnorm
    (E : IEData (K := K) (L := L))
    (hE : E.NormCompatible)
    (c : IdeleClassGroup (NumberField.RingOfIntegers L) L) :
    E.classMap (canonicalIdeleNorm (K := K) (L := L) c) =
      ∏ sigma : Gal(L/K),
        (ideleDistribAction (K := K) (L := L)).smul sigma c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (principalIdeles (NumberField.RingOfIntegers L) L) c
  rw [canonical_idele_mk, E.classMap_mk, hE, map_prod]
  rfl

/-- Equivalently, the canonical idèle-class norm becomes the norm for the
finite multiplicative Galois action after applying the fixed-class map. -/
theorem IEData.classm_idele_eqact
    (E : IEData (K := K) (L := L))
    (hE : E.NormCompatible)
    (c : IdeleClassGroup (NumberField.RingOfIntegers L) L) :
    letI := ideleDistribAction (K := K) (L := L)
    E.classMap (canonicalIdeleNorm (K := K) (L := L) c) =
      ((FMAct.norm Gal(L/K)
        (IdeleClassGroup (NumberField.RingOfIntegers L) L) c :
          FMAct.invariants Gal(L/K)
            (IdeleClassGroup (NumberField.RingOfIntegers L) L)) :
        IdeleClassGroup (NumberField.RingOfIntegers L) L) := by
  letI := ideleDistribAction (K := K) (L := L)
  exact E.classmap_canonidele_classnorm hE c

end

end Towers.CField.NIndex
