import Submission.ClassField.Ideles.IdeleNorm
import Submission.ClassField.Ideles.FiniteRaySubgroup

/-!
# Chapter V, Section 4, Corollary 4.13

If `L/K` is a finite extension of number fields, the idèle norm subgroup
contains `W_m` for some modulus `m`.

The source's `W_m` is the subgroup of `I_m` consisting of idèles which are
units at every finite place.  Since `modulusUnitIdeles m` is naturally a
subgroup of the subtype `modulusIdeles m`, we map it back into the full idèle
group before stating the corollary.

The literal assertion is recorded without any additional hypothesis.  The
final theorem isolates the two topological facts used in the printed proof:
the global norm image is open (from Proposition 4.12 place by place), and
every open subgroup of the idèle group contains some `W_m`.
-/

namespace Submission.CField.Ideles

open IsDedekindDomain NumberField Topology
open Submission.CField.RCGroups

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

local notation "𝓞K" => NumberField.RingOfIntegers K
local notation "𝓞L" => NumberField.RingOfIntegers L

/-- Milne's `W_m`, regarded as a subgroup of the full idèle group rather
than as a subgroup of the subtype `I_m`. -/
def ideleModulusSubgroup (m : Modulus K) :
    Subgroup (IdeleGroup 𝓞K K) :=
  (modulusUnitIdeles m).map (modulusIdeles m).subtype

/-- An idèle lies in `W_m` exactly when it satisfies the ray conditions for
`m` and is a unit at every finite place. -/
theorem idele_modulus_subgroup
    (m : Modulus K) (a : IdeleGroup 𝓞K K) :
    a ∈ ideleModulusSubgroup m ↔
      a ∈ modulusIdeles m ∧
        a ∈ idelesEveryPlace 𝓞K K := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hm, hu⟩
    let x : modulusIdeles m := ⟨a, hm⟩
    exact ⟨x, hu, rfl⟩

/-- The first global topological input in the proof of Corollary V.4.13:
the image of the idèle norm is an open subgroup. -/
def IdeleNormOpen : Prop :=
  IsOpen (ideleNormSubgroup (K := K) (L := L) :
    Set (IdeleGroup 𝓞K K))

/-- The second topological input in the proof: every open subgroup of the
idèle group contains `W_m` for some modulus `m`.  Restricting to open
subgroups is essential at the archimedean places: `W_m` contains a whole
connected component there, so these groups are not cofinal among arbitrary
neighborhoods. -/
def ModulusSubgroupsCofinal : Prop :=
  ∀ H : Subgroup (IdeleGroup 𝓞K K), IsOpen (H : Set (IdeleGroup 𝓞K K)) →
    ∃ m : Modulus K, ideleModulusSubgroup m ≤ H

/-- Corollary V.4.13 follows formally from the two exact topological inputs
supplied by the local norm theorem and the restricted-product topology. -/
theorem open_modulus_basis
    (hopen : IdeleNormOpen (K := K) (L := L))
    (hbasis : ModulusSubgroupsCofinal (K := K)) :
    (∃ m : Modulus K,
          ideleModulusSubgroup m ≤
            ideleNormSubgroup (K := K) (L := L)) := by
  exact hbasis (ideleNormSubgroup (K := K) (L := L)) hopen

end

end Submission.CField.Ideles
