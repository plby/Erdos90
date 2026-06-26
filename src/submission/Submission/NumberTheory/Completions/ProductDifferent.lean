import Submission.NumberTheory.Completions.DifferentCompletionTrace


/-!
# Differents in finite products of fraction fields

The different is only defined for domain extensions, so it cannot be formed
directly for a nontrivial product of rings.  This file records the replacement
needed in completion arguments: the trace dual of the product of the integral
lattices is the product of the inverse different ideals of the factors.
-/

namespace Submission.NumberTheory.Milne

open Module

noncomputable section

universe u v

/-- A product of submodules determines every coordinate submodule. -/
theorem submodule_pi_injective
    {A ι : Type*} {M : ι → Type*}
    [Semiring A]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module A (M i)]
    {N N' : ∀ i, Submodule A (M i)}
    (h : Submodule.pi Set.univ N = Submodule.pi Set.univ N') :
    N = N' := by
  classical
  funext i
  ext x
  let y : ∀ j, M j := Pi.single i x
  have hy (P : ∀ j, Submodule A (M j)) :
      y ∈ Submodule.pi Set.univ P ↔ x ∈ P i := by
    rw [Submodule.mem_pi]
    constructor
    · intro hx
      simpa [y] using hx i (Set.mem_univ i)
    · intro hx j _
      by_cases hji : j = i
      · subst j
        simpa [y] using hx
      · simp [y, Pi.single_eq_of_ne hji]
  rw [← hy N, h, hy N']

section Product

variable {A K ι : Type*} [CommRing A] [IsDomain A] [Field K]
  [Finite ι]
variable (B L : ι → Type u)
  [∀ i, CommRing (B i)] [∀ i, Field (L i)]
  [Algebra A K] [∀ i, Algebra A (B i)] [∀ i, Algebra (B i) (L i)]
  [∀ i, Algebra K (L i)] [∀ i, Algebra A (L i)]
  [∀ i, IsScalarTower A K (L i)] [∀ i, IsScalarTower A (B i) (L i)]
  [∀ i, Module.Free K (L i)] [∀ i, Module.Finite K (L i)]
  [IsFractionRing A K] [∀ i, Algebra.IsSeparable K (L i)]
  [IsIntegrallyClosed A] [∀ i, IsDedekindDomain (B i)]
  [∀ i, IsTorsionFree A (B i)] [∀ i, IsFractionRing (B i) (L i)]
  [∀ i, IsIntegralClosure (B i) A (L i)]

noncomputable local instance : Fintype ι := Fintype.ofFinite ι
noncomputable local instance : DecidableEq ι := Classical.decEq ι

/-- The underlying `A`-lattice of the integral ring in one factor. -/
private abbrev integralLattice (i : ι) : Submodule A (L i) :=
  (1 : Submodule (B i) (L i)).restrictScalars A

/-- The inverse different, regarded as an `A`-lattice in one factor. -/
private abbrev inverseDifferentLattice (i : ι) : Submodule A (L i) :=
  (((((differentIdeal A (B i) : Ideal (B i)) :
      FractionalIdeal (nonZeroDivisors (B i)) (L i))⁻¹ :
        FractionalIdeal (nonZeroDivisors (B i)) (L i)) :
          Submodule (B i) (L i)).restrictScalars A)

/-- The trace dual of a finite product of integral lattices is the product
of the inverse different ideals of the domain factors. -/
theorem dual_lattice_different :
    (Algebra.traceForm K (∀ i, L i)).dualSubmodule
        (Submodule.pi Set.univ (fun i ↦ integralLattice (A := A) B L i)) =
      Submodule.pi Set.univ
        (fun i ↦ inverseDifferentLattice (A := A) B L i) := by
  rw [dual_submodule_pi L]
  congr 1
  funext i
  change (Submodule.traceDual A K (1 : Submodule (B i) (L i))).restrictScalars A = _
  rw [← FractionalIdeal.coe_dual_one]
  change ((FractionalIdeal.dual A K
          (1 : FractionalIdeal (nonZeroDivisors (B i)) (L i)) :
        Submodule (B i) (L i)).restrictScalars A) =
    (((((differentIdeal A (B i) : Ideal (B i)) :
        FractionalIdeal (nonZeroDivisors (B i)) (L i))⁻¹ :
          FractionalIdeal (nonZeroDivisors (B i)) (L i)) :
            Submodule (B i) (L i)).restrictScalars A)
  rw [coeIdeal_differentIdeal A K (L i) (B i), inv_inv]

/-- Suppose fractional ideals from auxiliary fraction fields are mapped into
the factors and their inverse lattices present the product trace dual.  Then
the image of each fractional ideal is the corresponding different ideal.

The use of a ring homomorphism here is tailored to maps such as
`FractionalIdeal.extendedHom`; `map_inv₀` turns the transported inverse
into the inverse of the transported ideal before coordinates are extracted. -/
theorem mapped_fractional_dual
    {C M : ι → Type v}
    [∀ i, CommRing (C i)] [∀ i, IsDomain (C i)]
    [∀ i, IsDedekindDomain (C i)] [∀ i, Field (M i)]
    [∀ i, Algebra (C i) (M i)] [∀ i, IsFractionRing (C i) (M i)]
    (f : ∀ i,
      FractionalIdeal (nonZeroDivisors (C i)) (M i) →+*
        FractionalIdeal (nonZeroDivisors (B i)) (L i))
    (D : ∀ i, FractionalIdeal (nonZeroDivisors (C i)) (M i))
    (h : Submodule.pi Set.univ
          (fun i ↦
            (((f i ((D i)⁻¹) :
                FractionalIdeal (nonZeroDivisors (B i)) (L i)) :
                  Submodule (B i) (L i)).restrictScalars A)) =
        (Algebra.traceForm K (∀ i, L i)).dualSubmodule
          (Submodule.pi Set.univ
            (fun i ↦ integralLattice (A := A) B L i))) :
    ∀ i, f i (D i) =
      ((differentIdeal A (B i) : Ideal (B i)) :
        FractionalIdeal (nonZeroDivisors (B i)) (L i)) := by
  have h' : Submodule.pi Set.univ
          (fun i ↦
            (((((f i (D i))⁻¹ :
                FractionalIdeal (nonZeroDivisors (B i)) (L i))) :
                  Submodule (B i) (L i)).restrictScalars A)) =
        (Algebra.traceForm K (∀ i, L i)).dualSubmodule
          (Submodule.pi Set.univ
            (fun i ↦ integralLattice (A := A) B L i)) := by
    rw [← h]
    congr 1
    funext i
    exact congrArg
      (fun J : FractionalIdeal (nonZeroDivisors (B i)) (L i) ↦
        ((J : Submodule (B i) (L i)).restrictScalars A))
      (map_inv₀ (f i) (D i)).symm
  have hpi : Submodule.pi Set.univ
          (fun i ↦
            (((((f i (D i))⁻¹ :
                FractionalIdeal (nonZeroDivisors (B i)) (L i))) :
                  Submodule (B i) (L i)).restrictScalars A)) =
      Submodule.pi Set.univ
        (fun i ↦ inverseDifferentLattice (A := A) B L i) := by
    rw [h', dual_lattice_different B L]
  have hcoord := submodule_pi_injective hpi
  intro i
  apply inv_injective
  apply FractionalIdeal.coeToSubmodule_injective
  ext x
  have hi := congrFun hcoord i
  exact Submodule.ext_iff.mp hi x

/-- If a family of ideals presents the product trace dual through its
coordinatewise inverses, each ideal is the corresponding different ideal.

This is the form used after transporting a completed trace-dual equality to
the product of the completed fraction fields. -/
theorem ideals_different_dual
    (D : ∀ i, Ideal (B i))
    (h : Submodule.pi Set.univ
          (fun i ↦
            (((((D i : Ideal (B i)) :
                FractionalIdeal (nonZeroDivisors (B i)) (L i))⁻¹ :
                  FractionalIdeal (nonZeroDivisors (B i)) (L i)) :
                    Submodule (B i) (L i)).restrictScalars A)) =
        (Algebra.traceForm K (∀ i, L i)).dualSubmodule
          (Submodule.pi Set.univ
            (fun i ↦ integralLattice (A := A) B L i))) :
    D = fun i ↦ differentIdeal A (B i) := by
  have hpi : Submodule.pi Set.univ
          (fun i ↦
            (((((D i : Ideal (B i)) :
                FractionalIdeal (nonZeroDivisors (B i)) (L i))⁻¹ :
                  FractionalIdeal (nonZeroDivisors (B i)) (L i)) :
                    Submodule (B i) (L i)).restrictScalars A)) =
      Submodule.pi Set.univ
        (fun i ↦ inverseDifferentLattice (A := A) B L i) := by
    rw [h, dual_lattice_different B L]
  have hcoord := submodule_pi_injective hpi
  funext i
  apply FractionalIdeal.coeIdeal_injective (K := L i)
  apply inv_injective
  apply FractionalIdeal.coeToSubmodule_injective
  ext x
  have hi := congrFun hcoord i
  exact Submodule.ext_iff.mp hi x

end Product

end

end Submission.NumberTheory.Milne
