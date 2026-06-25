import Mathlib

/-!
# Milne, Algebraic Number Theory, Exercise 1-1

This file characterizes saturated multiplicative subsets by prime ideals and describes the smallest
saturated multiplicative subset containing a given submonoid.
-/

namespace Submission.NumberTheory.Milne

/-- A multiplicative subset of an integral domain is saturated exactly when every element outside
it belongs to a prime ideal disjoint from it. Equivalently, its complement is a union of prime
ideals. This is Exercise 1-1(a). -/
theorem mul_saturated_not
    {R : Type*} [CommRing R] [IsDomain R] (S : Submonoid R) :
    S.MulSaturated ↔
      ∀ x, x ∉ S ↔
        ∃ P : Ideal R, P.IsPrime ∧ Disjoint (P : Set R) S ∧ x ∈ P := by
  constructor
  · intro hS x
    constructor
    · intro hx
      have hdisjoint : Disjoint ((Ideal.span ({x} : Set R) : Set R)) S := by
        rw [Set.disjoint_left]
        intro y hy hyS
        change y ∈ Ideal.span ({x} : Set R) at hy
        rw [Ideal.mem_span_singleton] at hy
        obtain ⟨z, rfl⟩ := hy
        exact hx (hS hyS).1
      obtain ⟨P, hP, hspan, hdisjointP⟩ :=
        (Ideal.span ({x} : Set R)).exists_le_prime_disjoint S hdisjoint
      exact ⟨P, hP, hdisjointP, hspan (Ideal.mem_span_singleton_self x)⟩
    · rintro ⟨P, -, hdisjoint, hxP⟩ hxS
      exact Set.disjoint_left.mp hdisjoint hxP hxS
  · intro h x y hxy
    constructor
    · by_contra hx
      obtain ⟨P, -, hdisjoint, hxP⟩ := (h x).mp hx
      exact Set.disjoint_left.mp hdisjoint (P.mul_mem_right y hxP) hxy
    · by_contra hy
      obtain ⟨P, -, hdisjoint, hyP⟩ := (h y).mp hy
      exact Set.disjoint_left.mp hdisjoint (P.mul_mem_left x hyP) hxy

/-- An element belongs to the saturation of `S` exactly when it belongs to no prime ideal disjoint
from `S`. Thus the saturation is the complement of the union of all such primes, as asserted in
Exercise 1-1(b). -/
theorem saturation_forall_not
    {R : Type*} [CommRing R] [IsDomain R] (S : Submonoid R) (x : R) :
    x ∈ S.saturation ↔
      ∀ P : Ideal R, P.IsPrime → Disjoint (P : Set R) S → x ∉ P := by
  constructor
  · rw [Submonoid.mem_saturation_iff]
    rintro ⟨y, hxy⟩ P - hdisjoint hxP
    exact Set.disjoint_left.mp hdisjoint (P.mul_mem_right y hxP) hxy
  · intro h
    by_contra hx
    obtain ⟨P, hP, hdisjoint, hxP⟩ :=
      ((mul_saturated_not S.saturation.toSubmonoid).mp
        S.saturation.mulSaturated x).mp hx
    apply h P hP
    · rw [Set.disjoint_left] at hdisjoint ⊢
      exact fun y hyP hyS ↦
        hdisjoint hyP (Submonoid.le_toSubmonoid_saturation hyS)
    · exact hxP

/-- Localizing at a multiplicative subset or at its saturation gives canonically isomorphic
`R`-algebras. This is the final assertion of Exercise 1-1(b). -/
noncomputable def localizationSaturationAlg
    {R : Type*} [CommRing R] (S : Submonoid R) :
    Localization S ≃ₐ[R] Localization S.saturation.toSubmonoid := by
  letI : IsLocalization S.saturation.toSubmonoid (Localization S) :=
    IsLocalization.of_le_of_exists_dvd S S.saturation.toSubmonoid
      Submonoid.le_toSubmonoid_saturation fun x hx ↦
        (Submonoid.mem_saturation_iff_exists_dvd.mp hx)
  exact IsLocalization.algEquiv S.saturation.toSubmonoid _ _

/-- Localizing any `R`-module at a multiplicative subset or at its saturation gives canonically
isomorphic `R`-modules.  This is the module-level assertion in Exercise 1-1(b). -/
noncomputable def localizedModuleSaturation
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (S : Submonoid R) :
    LocalizedModule S M ≃ₗ[R] LocalizedModule S.saturation.toSubmonoid M := by
  let f : M →ₗ[R] LocalizedModule S M := LocalizedModule.mkLinearMap S M
  let g : M →ₗ[R] LocalizedModule S.saturation.toSubmonoid M :=
    LocalizedModule.mkLinearMap S.saturation.toSubmonoid M
  letI : IsLocalizedModule S.saturation.toSubmonoid f :=
    IsLocalizedModule.of_exists_mul_mem S S.saturation.toSubmonoid
      Submonoid.le_toSubmonoid_saturation (fun x ↦ by
        obtain ⟨y, hyS, z, hz⟩ := Submonoid.mem_saturation_iff_exists_dvd.mp x.2
        refine ⟨z, ?_⟩
        rw [mul_comm, ← hz]
        exact hyS) f
  exact IsLocalizedModule.linearEquiv S.saturation.toSubmonoid f g

end Submission.NumberTheory.Milne
