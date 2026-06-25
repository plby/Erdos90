import Mathlib.Topology.Instances.AddCircle.Defs
import Towers.ClassField.CrossedProducts.CocycleRepresentatives
import Towers.ClassField.LocalBrauer.DivisionAlgebraOrder


/-!
# Chapter IV, Section 4: the local invariant of a division algebra

Let `L` be an unramified maximal subfield of a central division algebra `D`
and let `sigma` be its Frobenius automorphism.  Skolem--Noether supplies a
unit implementing `sigma`.  Its normalized order modulo `Z` is independent
of the implementer.  We parameterize the unramified input by the precise
property used in Milne's proof: units of the embedded copy of `L` have
integral order in `D`.
-/

namespace Towers.CField.LBrauer

noncomputable section

open ValuativeRel
open CProduca

universe u

variable (K L D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [DivisionRing D] [Algebra K D]
  [Algebra.IsCentral K D] [Module.Finite K D]

/-- The target `Q/Z` of the local invariant. -/
abbrev LocalInvariant := AddCircle (1 : ℚ)

/-- The class modulo `Z` of the normalized order of a unit of `D`. -/
def implementerInvariant (u : Dˣ) : LocalInvariant :=
  (divisionUnitOrder K D (Additive.ofMul u) : ℚ)

/-- A unit implements an automorphism of an embedded subfield when
conjugation by it acts as that automorphism. -/
def ImplementsSubfieldAutomorphism (i : L →ₐ[K] D) (sigma : Gal(L/K))
    (u : Dˣ) : Prop :=
  ∀ a : L, (u : D) * i a = i (sigma a) * (u : D)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [IsGalois K L] in
/-- Skolem--Noether supplies an implementer for the chosen Frobenius
automorphism. -/
theorem subfield_automorphism_implementer
    (i : L →ₐ[K] D) (sigma : Gal(L/K)) :
    ∃ u : Dˣ, ImplementsSubfieldAutomorphism K L D i sigma u := by
  exact ⟨galoisConjugator K L D i sigma,
    conjugator_mul_scalar K L D i sigma⟩

/-- The chosen Skolem--Noether implementer defines the parameterized local
invariant. -/
def divisionAlgebraInvariant (i : L →ₐ[K] D) (sigma : Gal(L/K)) :
    LocalInvariant :=
  implementerInvariant K D (galoisConjugator K L D i sigma)

private theorem rational_integer_invariant (z : ℤ) :
    (((z : ℚ) : LocalInvariant)) = 0 := by
  simp

omit [FiniteDimensional K L] [IsGalois K L] in
/-- **Milne IV.4, independence of the implementer.** If `L` is maximal in
`D` and every element of its unit group has integral normalized order, then
all units implementing the same Frobenius automorphism have the same order
class in `Q/Z`. -/
theorem implementerInvariant_eq
    (i : L →ₐ[K] D)
    (hdim : Module.finrank K D = (Module.finrank K L) ^ 2)
    (hIntegral : ∀ c : Lˣ, ∃ z : ℤ,
      divisionUnitOrder K D
          (Additive.ofMul (scalarUnits K L D i c)) = (z : ℚ))
    (sigma : Gal(L/K)) (u v : Dˣ)
    (hu : ImplementsSubfieldAutomorphism K L D i sigma u)
    (hv : ImplementsSubfieldAutomorphism K L D i sigma v) :
    implementerInvariant K D u = implementerInvariant K D v := by
  obtain ⟨c, hc, _⟩ :=
    unique_scalar_units K L D i hdim sigma u v hu hv
  obtain ⟨z, hz⟩ := hIntegral c
  rw [hc]
  change
    ((divisionUnitOrder K D
      (Additive.ofMul (scalarUnits K L D i c * v)) : ℚ) :
        LocalInvariant) = _
  change
    ((divisionUnitOrder K D
      (Additive.ofMul (scalarUnits K L D i c) + Additive.ofMul v) : ℚ) :
        LocalInvariant) = _
  rw [map_add, hz, AddCircle.coe_add, rational_integer_invariant]
  simp [implementerInvariant]

omit [IsGalois K L] in
/-- The chosen definition agrees with every implementer, so it does not
depend on the Skolem--Noether choice. -/
theorem division_invariant_implements
    (i : L →ₐ[K] D)
    (hdim : Module.finrank K D = (Module.finrank K L) ^ 2)
    (hIntegral : ∀ c : Lˣ, ∃ z : ℤ,
      divisionUnitOrder K D
          (Additive.ofMul (scalarUnits K L D i c)) = (z : ℚ))
    (sigma : Gal(L/K)) (u : Dˣ)
    (hu : ImplementsSubfieldAutomorphism K L D i sigma u) :
    divisionAlgebraInvariant K L D i sigma =
      implementerInvariant K D u := by
  exact implementerInvariant_eq K L D i hdim hIntegral sigma
    (galoisConjugator K L D i sigma) u
    (conjugator_mul_scalar K L D i sigma) hu

section Isomorphism

variable (D' : Type u) [DivisionRing D'] [Algebra K D']
  [Algebra.IsCentral K D'] [Module.Finite K D']

/-- Transport an embedded subfield across an algebra isomorphism. -/
def transportSubfieldEmbedding (e : D ≃ₐ[K] D') (i : L →ₐ[K] D) : L →ₐ[K] D' :=
  e.toAlgHom.comp i

/-- Transport a unit across an algebra isomorphism. -/
def transportDivisionUnit (e : D ≃ₐ[K] D') : Dˣ →* D'ˣ :=
  Units.map e.toRingHom.toMonoidHom

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L] [Algebra.IsCentral K D] [Module.Finite K D]
  [Algebra.IsCentral K D'] [Module.Finite K D'] in
@[simp]
theorem transport_division_units
    (e : D ≃ₐ[K] D') (i : L →ₐ[K] D) (c : Lˣ) :
    transportDivisionUnit K D D' e (scalarUnits K L D i c) =
      scalarUnits K L D' (transportSubfieldEmbedding K L D D' e i) c := by
  apply Units.ext
  rfl

omit [Algebra.IsCentral K D] [Algebra.IsCentral K D'] in
omit [Module.Finite K D] [Module.Finite K D'] in
/-- Algebra isomorphisms preserve the normalized order on division-algebra
units. -/
theorem division_algebra_alg
    (e : D ≃ₐ[K] D') (u : Dˣ) :
    divisionUnitOrder K D'
        (Additive.ofMul (transportDivisionUnit K D D' e u)) =
      divisionUnitOrder K D (Additive.ofMul u) := by
  have hnorm :
      Units.map (Algebra.norm K) (transportDivisionUnit K D D' e u) =
        Units.map (Algebra.norm K) u := by
    apply Units.ext
    change Algebra.norm K (e (u : D)) = Algebra.norm K (u : D)
    exact Algebra.norm_eq_of_algEquiv e (u : D)
  rw [division_unit_order, division_unit_order,
    regular_unit_order, regular_unit_order]
  change
    ((localUnitOrder K
      (Additive.ofMul
        (Units.map (Algebra.norm K) (transportDivisionUnit K D D' e u))) : ℤ) : ℚ) /
        (Module.finrank K D' : ℚ) = _
  rw [hnorm, ← e.toLinearEquiv.finrank_eq]
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L] [Algebra.IsCentral K D] [Module.Finite K D]
  [Algebra.IsCentral K D'] [Module.Finite K D'] in
/-- Transporting an implementer across an algebra isomorphism transports
its conjugation identity. -/
theorem transport_division_implements
    (e : D ≃ₐ[K] D') (i : L →ₐ[K] D) (sigma : Gal(L/K))
    (u : Dˣ) (hu : ImplementsSubfieldAutomorphism K L D i sigma u) :
    ImplementsSubfieldAutomorphism K L D'
      (transportSubfieldEmbedding K L D D' e i) sigma
      (transportDivisionUnit K D D' e u) := by
  intro a
  have h := congrArg e (hu a)
  simpa [transportDivisionUnit, transportSubfieldEmbedding] using h

omit [IsGalois K L] in
/-- **Milne IV.4, isomorphism invariance.** The local invariant is unchanged
under a `K`-algebra isomorphism of division algebras. -/
theorem division_invariant_alg
    (e : D ≃ₐ[K] D') (i : L →ₐ[K] D)
    (hdim : Module.finrank K D = (Module.finrank K L) ^ 2)
    (hIntegral : ∀ c : Lˣ, ∃ z : ℤ,
      divisionUnitOrder K D
          (Additive.ofMul (scalarUnits K L D i c)) = (z : ℚ))
    (sigma : Gal(L/K)) :
    divisionAlgebraInvariant K L D'
        (transportSubfieldEmbedding K L D D' e i) sigma =
      divisionAlgebraInvariant K L D i sigma := by
  let u := galoisConjugator K L D i sigma
  have hu : ImplementsSubfieldAutomorphism K L D i sigma u :=
    conjugator_mul_scalar K L D i sigma
  have hu' := transport_division_implements K L D D' e i sigma u hu
  have hdim' : Module.finrank K D' = (Module.finrank K L) ^ 2 := by
    rw [← e.toLinearEquiv.finrank_eq]
    exact hdim
  have hIntegral' : ∀ c : Lˣ, ∃ z : ℤ,
      divisionUnitOrder K D'
          (Additive.ofMul
            (scalarUnits K L D'
              (transportSubfieldEmbedding K L D D' e i) c)) = (z : ℚ) := by
    intro c
    obtain ⟨z, hz⟩ := hIntegral c
    refine ⟨z, ?_⟩
    rw [← transport_division_units K L D D' e i c,
      division_algebra_alg K D D' e, hz]
  rw [division_invariant_implements K L D'
    (transportSubfieldEmbedding K L D D' e i) hdim' hIntegral' sigma
    (transportDivisionUnit K D D' e u) hu']
  change
    ((divisionUnitOrder K D'
      (Additive.ofMul (transportDivisionUnit K D D' e u)) : ℚ) :
        LocalInvariant) = _
  rw [division_algebra_alg K D D' e]
  rfl

end Isomorphism

end

end Towers.CField.LBrauer
