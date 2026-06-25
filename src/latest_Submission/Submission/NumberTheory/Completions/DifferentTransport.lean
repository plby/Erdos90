import Submission.NumberTheory.Completions.DifferentCompletionBasis
import Submission.NumberTheory.Completions.ProductDifferent


/-!
# Transporting trace duals to completed product factors

An algebra equivalence preserves the trace pairing, hence carries the trace
dual of a lattice to the trace dual of its image.  Combining this with the
coordinate description of the different packages the final algebraic step
in a completion argument: once the extended integral lattice and the image
of its trace dual have been identified in a product of fields, the mapped
ideals in every factor are the local different ideals.
-/

namespace Submission.NumberTheory.Milne

open Module

noncomputable section

universe u v

section TraceDualTransport

variable {C F X Y : Type*}
  [CommRing C] [Field F] [CommRing X] [CommRing Y]
  [Algebra C F] [Algebra F X] [Algebra F Y]
  [Algebra C X] [Algebra C Y]
  [IsScalarTower C F X] [IsScalarTower C F Y]

/-- An algebra equivalence carries a lattice's trace dual to the trace dual
of the transported lattice. -/
theorem dual_submodule_alg
    (e : X ≃ₐ[F] Y) (N : Submodule C X) :
    ((Algebra.traceForm F X).dualSubmodule N).map
        (e.toLinearEquiv.restrictScalars C).toLinearMap =
      (Algebra.traceForm F Y).dualSubmodule
        (N.map (e.toLinearEquiv.restrictScalars C).toLinearMap) := by
  let eC : X ≃ₗ[C] Y := e.toLinearEquiv.restrictScalars C
  ext z
  rw [Submodule.mem_map_equiv]
  change (e.symm z ∈ (Algebra.traceForm F X).dualSubmodule N) ↔ _
  rw [LinearMap.BilinForm.mem_dualSubmodule,
    LinearMap.BilinForm.mem_dualSubmodule]
  constructor
  · rintro hz _ ⟨y, hy, rfl⟩
    have hzy := hz y hy
    rw [Algebra.traceForm_apply] at hzy ⊢
    have htrace : Algebra.trace F Y (z * e y) =
        Algebra.trace F X (e.symm z * y) := by
      calc
        Algebra.trace F Y (z * e y) =
            Algebra.trace F Y (e (e.symm z * y)) := by
          congr 1
          rw [map_mul e, e.apply_symm_apply]
        _ = Algebra.trace F X (e.symm z * y) :=
          Algebra.trace_eq_of_algEquiv e _
    change Algebra.trace F Y (z * e y) ∈ (1 : Submodule C F)
    rwa [htrace]
  · intro hz x hx
    have hzx := hz (e x) ⟨x, hx, rfl⟩
    rw [Algebra.traceForm_apply] at hzx ⊢
    have htrace : Algebra.trace F X (e.symm z * x) =
        Algebra.trace F Y (z * e x) := by
      calc
        Algebra.trace F X (e.symm z * x) =
            Algebra.trace F Y (e (e.symm z * x)) :=
          (Algebra.trace_eq_of_algEquiv e _).symm
        _ = Algebra.trace F Y (z * e x) := by
          congr 1
          rw [map_mul e, e.apply_symm_apply]
    rwa [htrace]

end TraceDualTransport

section ProductRecovery

variable {C F ι X : Type*}
  [CommRing C] [IsDomain C] [Field F]
  [Finite ι]
variable (B L : ι → Type u)
  [∀ i, CommRing (B i)] [∀ i, Field (L i)]
  [Algebra C F] [∀ i, Algebra C (B i)] [∀ i, Algebra (B i) (L i)]
  [∀ i, Algebra F (L i)] [∀ i, Algebra C (L i)]
  [∀ i, IsScalarTower C F (L i)] [∀ i, IsScalarTower C (B i) (L i)]
  [∀ i, Module.Free F (L i)] [∀ i, Module.Finite F (L i)]
  [IsFractionRing C F] [∀ i, Algebra.IsSeparable F (L i)]
  [IsIntegrallyClosed C] [∀ i, IsDedekindDomain (B i)]
  [∀ i, IsTorsionFree C (B i)] [∀ i, IsFractionRing (B i) (L i)]
  [∀ i, IsIntegralClosure (B i) C (L i)]
  [CommRing X] [Algebra F X] [Algebra C X] [IsScalarTower C F X]

noncomputable local instance : Fintype ι := Fintype.ofFinite ι
noncomputable local instance : DecidableEq ι := Classical.decEq ι

set_option synthInstance.maxHeartbeats 100000 in
-- The dependent product carries both the `F`- and restricted `C`-module structures.
set_option maxHeartbeats 800000 in
/-- Recover the different in every product factor from a transported
trace-dual equality.

`hN` says that the equivalence carries the scalar-extended integral lattice
to the product of the factor integer rings.  `hdual` is the basis-level
calculation saying that it carries the source trace dual to the product of
the mapped inverse ideals. -/
theorem mapped_ideals_dual
    {R₀ Q₀ : ι → Type v}
    [∀ i, CommRing (R₀ i)] [∀ i, IsDomain (R₀ i)]
    [∀ i, IsDedekindDomain (R₀ i)] [∀ i, Field (Q₀ i)]
    [∀ i, Algebra (R₀ i) (Q₀ i)] [∀ i, IsFractionRing (R₀ i) (Q₀ i)]
    (e : X ≃ₐ[F] (∀ i, L i))
    (N : Submodule C X)
    (f : ∀ i,
      FractionalIdeal (nonZeroDivisors (R₀ i)) (Q₀ i) →+*
        FractionalIdeal (nonZeroDivisors (B i)) (L i))
    (D : ∀ i, FractionalIdeal (nonZeroDivisors (R₀ i)) (Q₀ i))
    (hN : N.map (e.toLinearEquiv.restrictScalars C).toLinearMap =
      Submodule.pi Set.univ
        (fun i ↦ (1 : Submodule (B i) (L i)).restrictScalars C))
    (hdual : ((Algebra.traceForm F X).dualSubmodule N).map
        (e.toLinearEquiv.restrictScalars C).toLinearMap =
      Submodule.pi Set.univ
        (fun i ↦
          (((f i ((D i)⁻¹) :
              FractionalIdeal (nonZeroDivisors (B i)) (L i)) :
                Submodule (B i) (L i)).restrictScalars C))) :
    ∀ i, f i (D i) =
      ((differentIdeal C (B i) : Ideal (B i)) :
        FractionalIdeal (nonZeroDivisors (B i)) (L i)) := by
  classical
  apply mapped_fractional_dual
    (A := C) (K := F) B L f D
  calc
    Submodule.pi Set.univ
          (fun i ↦
            (((f i ((D i)⁻¹) :
                FractionalIdeal (nonZeroDivisors (B i)) (L i)) :
                  Submodule (B i) (L i)).restrictScalars C)) =
        ((Algebra.traceForm F X).dualSubmodule N).map
          (e.toLinearEquiv.restrictScalars C).toLinearMap := hdual.symm
    _ = (Algebra.traceForm F (∀ i, L i)).dualSubmodule
          (N.map (e.toLinearEquiv.restrictScalars C).toLinearMap) :=
      dual_submodule_alg e N
    _ = (Algebra.traceForm F (∀ i, L i)).dualSubmodule
          (Submodule.pi Set.univ
            (fun i ↦ (1 : Submodule (B i) (L i)).restrictScalars C)) := by
      rw [hN]

end ProductRecovery

end

end Submission.NumberTheory.Milne
