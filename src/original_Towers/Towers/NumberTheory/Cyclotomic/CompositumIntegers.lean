import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Rings of integers in a linearly disjoint compositum

This file formalizes Milne's Lemma 6.5.  The product `O_K O_L` is represented by the
`ℤ`-submodule spanned by products of the two rings of integers inside a common ambient
number field.
-/

open scoped Kronecker Pointwise
open Algebra IntermediateField Module NumberField Submodule

namespace Milne

section

variable {E : Type*} [Field E] [NumberField E]

private theorem trace_linear_disjoint
    (K L : IntermediateField ℚ E) (hlin : K.LinearDisjoint L) (hsup : K ⊔ L = ⊤)
    (x : K) (y : L) :
    Algebra.trace ℚ E (algebraMap K E x * algebraMap L E y) =
      Algebra.trace ℚ K x * Algebra.trace ℚ L y := by
  rw [← Algebra.trace_trace (S := K)]
  change Algebra.trace ℚ K (Algebra.trace K E (x • algebraMap L E y)) = _
  rw [map_smul, hlin.trace_algebraMap hsup]
  simp only [smul_eq_mul]
  rw [mul_comm x, ← Algebra.smul_def, map_smul]
  exact mul_comm _ _

open scoped Classical in
/-- The determinant calculation in Milne, Remark 6.6(c), at the level of arbitrary
rational bases.  The trace matrix of the pairwise products is the Kronecker product of
the two original trace matrices. -/
theorem discr_linear_disjoint
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K L : IntermediateField ℚ E) (hlin : K.LinearDisjoint L) (hsup : K ⊔ L = ⊤)
    (bK : Basis ι ℚ K) (bL : Basis κ ℚ L) :
    Algebra.discr ℚ (fun ij : ι × κ ↦
      algebraMap K E (bK ij.1) * algebraMap L E (bL ij.2)) =
      Algebra.discr ℚ bK ^ Fintype.card κ *
        Algebra.discr ℚ bL ^ Fintype.card ι := by
  classical
  rw [Algebra.discr_def, Algebra.discr_def, Algebra.discr_def]
  have hmatrix :
      Algebra.traceMatrix ℚ (fun ij : ι × κ ↦
        algebraMap K E (bK ij.1) * algebraMap L E (bL ij.2)) =
        Algebra.traceMatrix ℚ bK ⊗ₖ Algebra.traceMatrix ℚ bL := by
    ext ij kl
    rcases ij with ⟨i₁, j₁⟩
    rcases kl with ⟨i₂, j₂⟩
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.kronecker_apply]
    rw [show
      (algebraMap K E (bK i₁) * algebraMap L E (bL j₁)) *
          (algebraMap K E (bK i₂) * algebraMap L E (bL j₂)) =
        algebraMap K E (bK i₁ * bK i₂) * algebraMap L E (bL j₁ * bL j₂) by
          simp only [map_mul]
          ring]
    exact trace_linear_disjoint K L hlin hsup (bK i₁ * bK i₂) (bL j₁ * bL j₂)
  rw [hmatrix, Matrix.det_kronecker]

open scoped Classical in
/-- **Milne, Remark 6.6(c).** If integral bases of `K` and `L` have pairwise products
forming an integral basis of their compositum `E`, then the signed discriminant of `E`
is the indicated product.  In particular, no absolute values or orientation choices are
needed: discriminants of integral bases are exactly basis-independent over `ℤ`. -/
theorem discr_integral_basis
    {ι κ : Type*} [Finite ι] [Finite κ]
    (K L : IntermediateField ℚ E) (hlin : K.LinearDisjoint L) (hsup : K ⊔ L = ⊤)
    (bK : Basis ι ℤ (𝓞 K)) (bL : Basis κ ℤ (𝓞 L))
    (bE : Basis (ι × κ) ℤ (𝓞 E))
    (hprod : ∀ ij, algebraMap (𝓞 E) E (bE ij) =
      algebraMap (𝓞 K) E (bK ij.1) * algebraMap (𝓞 L) E (bL ij.2)) :
    discr E = discr K ^ finrank ℚ L * discr L ^ finrank ℚ K := by
  classical
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite κ
  let bKℚ : Basis ι ℚ K :=
    bK.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  let bLℚ : Basis κ ℚ L :=
    bL.localizationLocalization ℚ (nonZeroDivisors ℤ) L
  let bEℚ : Basis (ι × κ) ℚ E :=
    bE.localizationLocalization ℚ (nonZeroDivisors ℤ) E
  have hbE : (bEℚ : ι × κ → E) = fun ij ↦
      algebraMap K E (bKℚ ij.1) * algebraMap L E (bLℚ ij.2) := by
    funext ij
    simpa only [bEℚ, bKℚ, bLℚ, Basis.localizationLocalization_apply,
      IsScalarTower.algebraMap_apply] using hprod ij
  have h := discr_linear_disjoint K L hlin hsup bKℚ bLℚ
  rw [← hbE] at h
  rw [Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) E bE,
    Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) K bK,
    Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) L bL,
    NumberField.discr_eq_discr E bE,
    NumberField.discr_eq_discr K bK,
    NumberField.discr_eq_discr L bL] at h
  have hcard : discr E = discr K ^ Fintype.card κ * discr L ^ Fintype.card ι := by
    exact_mod_cast h
  simpa [← RingOfIntegers.rank K, ← RingOfIntegers.rank L,
    finrank_eq_card_basis bK, finrank_eq_card_basis bL] using hcard

/-- The integral lattice of an intermediate number field, embedded in `E`. -/
def integerLattice (K : IntermediateField ℚ E) : Submodule ℤ E :=
  LinearMap.range (IsScalarTower.toAlgHom ℤ (𝓞 K) E).toLinearMap

/-- The product `O_K * O_L` inside a common ambient number field. -/
def integerProduct (K L : IntermediateField ℚ E) : Submodule ℤ E :=
  integerLattice K * integerLattice L

/-- The lattice `O_E` inside its fraction field. -/
def ringIntegersLattice : Submodule ℤ E :=
  LinearMap.range ((Algebra.linearMap (𝓞 E) E).restrictScalars ℤ)

@[simp]
theorem integer_lattice {K : IntermediateField ℚ E} {x : E} :
    x ∈ integerLattice K ↔ ∃ a : 𝓞 K, algebraMap (𝓞 K) E a = x :=
  Iff.rfl

private theorem discr_ring_integers
    (K : Type*) [Field K] [NumberField K]
    {x : K} (hx : x ∈ traceDual ℤ ℚ (1 : Submodule (𝓞 K) K)) :
    ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = algebraMap ℤ K (discr K) * x := by
  have hx' : IsIntegral ℤ (algebraMap ℤ K (discr K) * x) := by
    have h := isIntegral_discr_mul_of_mem_traceDual
      (A := ℤ) (K := ℚ) (B := 𝓞 K) (L := K)
      (1 : Submodule (𝓞 K) K)
      (b := integralBasis K) (fun i => by
        rw [integralBasis_apply]
        exact RingOfIntegers.isIntegral_coe _)
      (a := 1) (x := x) (by simp) hx
    rw [← NumberField.coe_discr] at h
    simpa [Algebra.smul_def] using h
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 K)).mp hx'

private theorem integer_product_left
    (K L : IntermediateField ℚ E) (a : 𝓞 K) {x : E}
    (hx : x ∈ integerProduct K L) :
    algebraMap (𝓞 K) E a * x ∈ integerProduct K L := by
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm n hn
    rw [← mul_assoc]
    apply Submodule.mul_mem_mul _ hn
    rcases hm with ⟨b, rfl⟩
    exact ⟨a * b, by simp⟩
  · intro x y hx hy
    simpa [mul_add] using Submodule.add_mem (integerProduct K L) hx hy

/-- Multiplication by the discriminant of the right-hand field clears every denominator
coming from the integral closure of the compositum. -/
theorem discr_integer_product
    (K L : IntermediateField ℚ E) (hlin : K.LinearDisjoint L) (hsup : K ⊔ L = ⊤)
    (a : 𝓞 E) :
    algebraMap ℤ E (discr L) * algebraMap (𝓞 E) E a ∈ integerProduct K L := by
  let x : E := algebraMap (𝓞 E) E a
  have hxone : x ∈ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_one]
    exact ⟨a, rfl⟩
  have hxdual : x ∈ traceDual (𝓞 K) K (1 : Submodule (𝓞 E) E) :=
    Submodule.one_le_traceDual_one hxone
  have hxspan : x ∈
      span (𝓞 K) (algebraMap L E '' traceDual ℤ ℚ (1 : Submodule (𝓞 L) L)) :=
    Submodule.traceDual_le_span_map_traceDual ℤ (𝓞 E) (𝓞 K) (𝓞 L) hlin hsup hxdual
  change algebraMap ℤ E (discr L) * x ∈ integerProduct K L
  refine Submodule.span_induction (p := fun y _ =>
    algebraMap ℤ E (discr L) * y ∈ integerProduct K L) ?_ ?_ ?_ ?_ hxspan
  · intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    obtain ⟨b, hb⟩ := discr_ring_integers L hz
    have hbE : algebraMap (𝓞 L) E b =
        algebraMap ℤ E (discr L) * algebraMap L E z := by
      calc
        algebraMap (𝓞 L) E b = algebraMap L E (algebraMap (𝓞 L) L b) := by
          rw [IsScalarTower.algebraMap_apply (𝓞 L) L E]
        _ = algebraMap L E (algebraMap ℤ L (discr L) * z) :=
          congrArg (algebraMap L E) hb
        _ = algebraMap ℤ E (discr L) * algebraMap L E z := by
          rw [map_mul, IsScalarTower.algebraMap_apply ℤ L E]
    rw [← hbE]
    have h1 : (1 : E) ∈ integerLattice K :=
      integer_lattice.mpr ⟨1, by simp⟩
    have hbmem : algebraMap (𝓞 L) E b ∈ integerLattice L :=
      integer_lattice.mpr ⟨b, rfl⟩
    simpa using Submodule.mul_mem_mul (M := integerLattice K) (N := integerLattice L) h1 hbmem
  · simp [integerProduct]
  · intro y z _ _ ihy ihz
    simpa [mul_add] using Submodule.add_mem (integerProduct K L) ihy ihz
  · intro c y _ ih
    rw [Algebra.smul_def]
    convert integer_product_left K L c ih using 1
    ring

/-- The symmetric denominator-clearing statement for the left-hand field. -/
theorem discr_left_integer
    (K L : IntermediateField ℚ E) (hlin : K.LinearDisjoint L) (hsup : K ⊔ L = ⊤)
    (a : 𝓞 E) :
    algebraMap ℤ E (discr K) * algebraMap (𝓞 E) E a ∈ integerProduct K L := by
  have hlin' : L.LinearDisjoint K := hlin.symm
  have hsup' : L ⊔ K = ⊤ := by rwa [sup_comm]
  simpa [integerProduct, mul_comm] using
    discr_integer_product L K hlin' hsup' a

/-- Milne's Lemma 6.5 in denominator-cleared form.  The natural number `Int.gcd` is
coerced to `ℤ`: multiplication by this gcd carries `O_E` into `O_K O_L`. -/
theorem gcd_discr_integer
    (K L : IntermediateField ℚ E) (hlin : K.LinearDisjoint L) (hsup : K ⊔ L = ⊤)
    (a : 𝓞 E) :
    algebraMap ℤ E (Int.gcd (discr K) (discr L) : ℤ) * algebraMap (𝓞 E) E a ∈
      integerProduct K L := by
  let x : E := algebraMap (𝓞 E) E a
  have hK : algebraMap ℤ E (discr K) * x ∈ integerProduct K L :=
    discr_left_integer K L hlin hsup a
  have hL : algebraMap ℤ E (discr L) * x ∈ integerProduct K L :=
    discr_integer_product K L hlin hsup a
  have hKa := Submodule.smul_mem (integerProduct K L)
    (Int.gcdA (discr K) (discr L)) hK
  have hLb := Submodule.smul_mem (integerProduct K L)
    (Int.gcdB (discr K) (discr L)) hL
  have hadd := Submodule.add_mem (integerProduct K L) hKa hLb
  change algebraMap ℤ E (Int.gcd (discr K) (discr L) : ℤ) * x ∈ integerProduct K L
  convert hadd using 1
  rw [Int.gcd_eq_gcd_ab]
  simp only [map_add, map_mul, Algebra.smul_def]
  ring

theorem integer_integers_lattice
    (K L : IntermediateField ℚ E) :
    integerProduct K L ≤ ringIntegersLattice := by
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm n hn
    rcases hm with ⟨a, rfl⟩
    rcases hn with ⟨b, rfl⟩
    refine ⟨algebraMap (𝓞 K) (𝓞 E) a * algebraMap (𝓞 L) (𝓞 E) b, ?_⟩
    change algebraMap (𝓞 E) E
        (algebraMap (𝓞 K) (𝓞 E) a * algebraMap (𝓞 L) (𝓞 E) b) =
      algebraMap (𝓞 K) E a * algebraMap (𝓞 L) E b
    rw [map_mul]
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 E) E,
      IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 E) E]
  · intro x y hx hy
    exact Submodule.add_mem ringIntegersLattice hx hy

/-- The right-hand side `d⁻¹ O_K O_L` from Milne's statement, as a `ℤ`-submodule of `E`. -/
noncomputable def inverseGcdScaled
    (K L : IntermediateField ℚ E) : Submodule ℤ E :=
  (algebraMap ℤ E (Int.gcd (discr K) (discr L) : ℤ))⁻¹ • integerProduct K L

/-- **Milne, Lemma 6.5.** If `K` and `L` are linearly disjoint and generate `E`, then
`O_E ⊆ d⁻¹ O_K O_L`, where `d = gcd(disc K, disc L)`. -/
theorem integers_gcd_scaled
    (K L : IntermediateField ℚ E) (hlin : K.LinearDisjoint L) (hsup : K ⊔ L = ⊤) :
    ringIntegersLattice ≤ inverseGcdScaled K L := by
  intro x hx
  rcases hx with ⟨a, rfl⟩
  let d : ℤ := Int.gcd (discr K) (discr L)
  have hdNat : Int.gcd (discr K) (discr L) ≠ 0 :=
    (Int.gcd_pos_of_ne_zero_left (discr L) (discr_ne_zero K)).ne'
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast hdNat
  have hdE : algebraMap ℤ E d ≠ 0 := by
    simpa using (algebraMap ℤ E).injective_int.ne hd
  rw [inverseGcdScaled, Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨algebraMap ℤ E d * algebraMap (𝓞 E) E a,
    gcd_discr_integer K L hlin hsup a, ?_⟩
  change (algebraMap ℤ E d)⁻¹ *
    (algebraMap ℤ E d * algebraMap (𝓞 E) E a) = algebraMap (𝓞 E) E a
  exact inv_mul_cancel_left₀ hdE _

/-- **Milne, Lemma 6.5**, with Milne's degree hypothesis written literally.  The assumption
`K ⊔ L = ⊤` identifies `E` with the compositum, and the finrank equality is
`[KL : ℚ] = [K : ℚ] [L : ℚ]`. -/
theorem lattice_gcd_scaled
    (K L : IntermediateField ℚ E) (hsup : K ⊔ L = ⊤)
    (hdegree : finrank ℚ E = finrank ℚ K * finrank ℚ L) :
    ringIntegersLattice ≤ inverseGcdScaled K L := by
  have hdegree' : finrank ℚ ↥(K ⊔ L) = finrank ℚ K * finrank ℚ L := by
    rw [hsup]
    simpa using hdegree
  exact integers_gcd_scaled K L
    (IntermediateField.LinearDisjoint.of_finrank_sup hdegree') hsup

/-- Coprime discriminants give the equality `O_E = O_K O_L` used in Theorem 6.4. -/
theorem integers_lattice_discr
    (K L : IntermediateField ℚ E) (hlin : K.LinearDisjoint L) (hsup : K ⊔ L = ⊤)
    (hcop : IsCoprime (discr K) (discr L)) :
    integerProduct K L = ringIntegersLattice := by
  apply le_antisymm (integer_integers_lattice K L)
  intro x hx
  rcases hx with ⟨a, rfl⟩
  have h := gcd_discr_integer K L hlin hsup a
  rw [Int.isCoprime_iff_gcd_eq_one.mp hcop] at h
  simpa using h

/-- The coprime-discriminant consequence used in Milne's proof of Theorem 6.4, again with
the degree-product hypothesis rather than a separate linear-disjointness assumption. -/
theorem lattice_coprime_discr
    (K L : IntermediateField ℚ E) (hsup : K ⊔ L = ⊤)
    (hdegree : finrank ℚ E = finrank ℚ K * finrank ℚ L)
    (hcop : IsCoprime (discr K) (discr L)) :
    integerProduct K L = ringIntegersLattice := by
  have hdegree' : finrank ℚ ↥(K ⊔ L) = finrank ℚ K * finrank ℚ L := by
    rw [hsup]
    simpa using hdegree
  exact integers_lattice_discr K L
    (IntermediateField.LinearDisjoint.of_finrank_sup hdegree') hsup hcop

end

end Milne
