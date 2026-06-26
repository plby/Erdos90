import Towers.ClassField.Shifting.KernelImageComplex
import Towers.ClassField.LocalClass.FiniteTrivialInt

/-!
# Herbrand transfer for Lemma III.2.5

This file records the formal part of Milne's argument that an open acyclic
submodule has the same Herbrand quotient as the ambient module.  In the
local-field application the cokernel is finite because the subgroup is open
in the compact unit group.
-/

namespace Towers.CField.LClass

open CategoryTheory CategoryTheory.Limits
open Shifting

noncomputable section

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

@[reducible]
private noncomputable def finiteCohomologyZero
    (A : Rep R G) (r : ℕ) (h : IsZero (groupCohomology A r)) :
    Finite (groupCohomology A r) := by
  letI : Subsingleton (groupCohomology A r) :=
    ModuleCat.subsingleton_of_isZero h
  infer_instance

omit [Fintype G] in
/-- The Herbrand quotient of a module whose first and second cohomology
vanish. -/
noncomputable def acyclicHerbrandQuotient
    (A : Rep R G)
    (h₁ : IsZero (groupCohomology A 1))
    (h₂ : IsZero (groupCohomology A 2)) : ℚˣ := by
  letI : Finite (groupCohomology A 1) :=
    finiteCohomologyZero A 1 h₁
  letI : Finite (groupCohomology A 2) :=
    finiteCohomologyZero A 2 h₂
  exact herbrandQuotient A

omit [Fintype G] in
/-- An acyclic module has Herbrand quotient one. -/
theorem acyclic_herbrand_one
    (A : Rep R G)
    (h₁ : IsZero (groupCohomology A 1))
    (h₂ : IsZero (groupCohomology A 2)) :
    (acyclicHerbrandQuotient A h₁ h₂ : ℚ) = 1 := by
  letI : Subsingleton (groupCohomology A 1) :=
    ModuleCat.subsingleton_of_isZero h₁
  letI : Subsingleton (groupCohomology A 2) :=
    ModuleCat.subsingleton_of_isZero h₂
  letI : Finite (groupCohomology A 1) :=
    finiteCohomologyZero A 1 h₁
  letI : Finite (groupCohomology A 2) :=
    finiteCohomologyZero A 2 h₂
  simp [acyclicHerbrandQuotient, herbrandQuotient,
    card_unit_val]

/-- The Herbrand quotient of the codomain of a finite-kernel,
finite-cokernel map out of an acyclic module. -/
noncomputable def cokernelHerbrandQuotient
    {A B : Rep R G} (f : A ⟶ B)
    [Finite ↑(kernel f : Rep R G)] [Finite ↑(cokernel f : Rep R G)]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (h₁ : IsZero (groupCohomology A 1))
    (h₂ : IsZero (groupCohomology A 2)) : ℚˣ := by
  letI : Finite (groupCohomology A 1) :=
    finiteCohomologyZero A 1 h₁
  letI : Finite (groupCohomology A 2) :=
    finiteCohomologyZero A 2 h₂
  let hB := herbrand_codomain_cokernel
    f g hg
  letI : Finite (groupCohomology B 1) := hB.1
  letI : Finite (groupCohomology B 2) := hB.2
  exact herbrandQuotient B

/-- Milne's finite-index step: a module reached from an acyclic module by a
map with finite kernel and cokernel has Herbrand quotient one. -/
theorem cokernel_herbrand_one
    {A B : Rep R G} (f : A ⟶ B)
    [Finite ↑(kernel f : Rep R G)] [Finite ↑(cokernel f : Rep R G)]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (h₁ : IsZero (groupCohomology A 1))
    (h₂ : IsZero (groupCohomology A 2)) :
    (cokernelHerbrandQuotient f g hg h₁ h₂ : ℚ) = 1 := by
  letI : Subsingleton (groupCohomology A 1) :=
    ModuleCat.subsingleton_of_isZero h₁
  letI : Subsingleton (groupCohomology A 2) :=
    ModuleCat.subsingleton_of_isZero h₂
  letI : Finite (groupCohomology A 1) :=
    finiteCohomologyZero A 1 h₁
  letI : Finite (groupCohomology A 2) :=
    finiteCohomologyZero A 2 h₂
  let hB := herbrand_codomain_cokernel
    f g hg
  letI : Finite (groupCohomology B 1) := hB.1
  letI : Finite (groupCohomology B 2) := hB.2
  change (herbrandQuotient B : ℚ) = 1
  rw [← herbrand_quotient_cokernel f g hg]
  simpa [acyclicHerbrandQuotient] using
    acyclic_herbrand_one A h₁ h₂

end

end Towers.CField.LClass
