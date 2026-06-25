import Towers.Group.Edmonton.SubnormalCorollaries

/-!
# The Edmonton Notes on Nilpotent Groups: Burnside-Wielandt

This file formalizes Hall's Theorem 2.7.
-/

namespace Towers
namespace Edmonton

open Group

universe u

variable {G : Type u} [Group G]

/-- **Hall, Theorem 2.7 (Burnside-Wielandt).** For a finite group, the
following are equivalent: every maximal subgroup is normal, the group is the
direct product of its Sylow subgroups, and the group is nilpotent. -/
theorem subgroups_sylow_nilpotent [Finite G] :
    List.TFAE
      [∀ H : Subgroup G, IsCoatom H → H.Normal,
        Nonempty
          ((∀ p : (Nat.card G).primeFactors,
              ∀ P : Sylow p G, (P : Subgroup G)) ≃* G),
        Group.IsNilpotent G] := by
  tfae_have 1 → 2 :=
    ((Group.isNilpotent_of_finite_tfae (G := G)).out 2 4).mp
  tfae_have 2 → 3 :=
    ((Group.isNilpotent_of_finite_tfae (G := G)).out 4 0).mp
  tfae_have 3 → 1 :=
    ((Group.isNilpotent_of_finite_tfae (G := G)).out 0 2).mp
  tfae_finish

end Edmonton
end Towers
