import Towers.ClassField.Ideles.ModulusUnitSubgroup

/-!
# Chapter VII, Section 2, Proposition 2.8

The proposition repeats the global topological norm assertion used in
Chapter V: the image of the idèle norm contains an open subgroup and hence is
itself open.
-/

namespace Towers.CField.ICohomo

open IsDedekindDomain NumberField Topology
open Towers.CField.Ideles

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- **Proposition VII.2.8 (source statement).** -/
abbrev IdeleSubgroupOpen : Prop :=
  IsOpen (ideleNormSubgroup (K := K) (L := L) :
    Set (IdeleGroup (NumberField.RingOfIntegers K) K))

/-- The source proposition is exactly the open-norm-subgroup input already
isolated for Corollary V.4.13. -/
theorem norm_subgroup_open
    (hopen : IdeleNormOpen (K := K) (L := L)) :
    IdeleSubgroupOpen (K := K) (L := L) :=
  hopen

end

end Towers.CField.ICohomo
