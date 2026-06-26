import Towers.ClassField.SimpleAlgebras.AlgebraSemisimpleRing

/-!
# Milne, Class Field Theory, Theorem IV.1.19

For a semisimple algebra, simplicity, isotypy of the regular module, and
uniqueness of the simple module up to isomorphism are equivalent.
-/

namespace Towers.CField.SAlgebr

universe u v

/-- Condition (c) of Theorem IV.1.19, for modules in a fixed universe. -/
def SimpleModulesIsomorphic (A : Type u) [Ring A] : Prop :=
  ∀ (S T : Type u) [AddCommGroup S] [AddCommGroup T]
    [Module A S] [Module A T] [IsSimpleModule A S] [IsSimpleModule A T],
    Nonempty (S ≃ₗ[A] T)

variable (A : Type u) [Ring A] [Nontrivial A] [IsSemisimpleRing A]

/-- Conditions (a) and (b) of Theorem IV.1.19 are equivalent. -/
theorem simple_regular_isotypic :
    IsSimpleRing A ↔ IsIsotypic A A := by
  constructor
  · intro h
    letI : IsSimpleRing A := h
    exact IsSimpleRing.isIsotypic A A
  · intro h
    exact (isSimpleRing_isArtinianRing_iff.mpr
      ⟨inferInstance, h, inferInstance⟩).1

omit [Nontrivial A] in
/-- The implication (b) to (c), without a universe restriction on the two
simple modules. -/
theorem simple_modules_isotypic
    (h : IsIsotypic A A)
    (S T : Type v) [AddCommGroup S] [AddCommGroup T]
    [Module A S] [Module A T] [IsSimpleModule A S] [IsSimpleModule A T] :
    Nonempty (S ≃ₗ[A] T) := by
  obtain ⟨I, ⟨eS⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A S
  obtain ⟨J, ⟨eT⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A T
  letI : IsSimpleModule A I := (eS.isSimpleModule_iff).mp inferInstance
  letI : IsSimpleModule A J := (eT.isSimpleModule_iff).mp inferInstance
  exact ⟨eS.trans ((h I J).some.symm.trans eT.symm)⟩

omit [Nontrivial A] in
/-- Isotypy of the regular module implies that any two simple modules are
isomorphic. -/
theorem modules_isomorphic_isotypic
    (h : IsIsotypic A A) : SimpleModulesIsomorphic A := by
  intro S T _ _ _ _ _ _
  exact simple_modules_isotypic A h S T

omit [Nontrivial A] [IsSemisimpleRing A] in
/-- Pairwise uniqueness of simple modules implies isotypy of the regular
module. -/
theorem isotypic_modules_isomorphic
    (h : SimpleModulesIsomorphic A) : IsIsotypic A A := by
  intro S _ T _
  exact h T S

/-- **Theorem IV.1.19.** The three conditions are equivalent. -/
theorem tfae : List.TFAE
    [IsSimpleRing A, IsIsotypic A A, SimpleModulesIsomorphic A] := by
  tfae_have 1 ↔ 2 := simple_regular_isotypic A
  tfae_have 2 → 3 := modules_isomorphic_isotypic A
  tfae_have 3 → 2 := isotypic_modules_isomorphic A
  tfae_finish

end Towers.CField.SAlgebr
