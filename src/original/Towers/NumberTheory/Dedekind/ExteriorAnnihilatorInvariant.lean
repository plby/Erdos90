import Towers.NumberTheory.Dedekind.DeterminantLine
import Towers.NumberTheory.Dedekind.InvariantFactorsQuotient
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Exterior-power annihilator invariants

Linear equivalences preserve the annihilators of all exterior powers.  This is the functorial
half of the exterior-power proof of uniqueness for invariant-factor chains.
-/

namespace Towers.NumberTheory.Milne

open scoped DirectSum

/-- A linear equivalence preserves the annihilator of every exterior power. -/
theorem exterior_annihilator_linear
    (R M N : Type*) [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (k : ℕ) (e : M ≃ₗ[R] N) :
    Module.annihilator R (⋀[R]^k M) = Module.annihilator R (⋀[R]^k N) := by
  exact (exteriorLinearEquiv R M N k e).annihilator_eq

/-- An embedding of `k` coordinates into `m` coordinates hits one of the first `m-k+1`
coordinates. -/
theorem embedding_hits_initial
    {k m : ℕ} (hk : 0 < k) (hkm : k ≤ m) (f : Fin k ↪ Fin m) :
    ∃ i, (f i).val ≤ m - k := by
  by_contra h
  push Not at h
  let g : Fin k → Fin (k - 1) := fun i ↦
    ⟨(f i).val - (m - k + 1), by
      have hlow := h i
      have hupp := (f i).isLt
      omega⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply f.injective
    apply Fin.ext
    have hi := h i
    have hj := h j
    have hij' := congrArg Fin.val hij
    simp only [g] at hij'
    omega
  have hcard := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin] at hcard
  omega

/-- The standard coordinate generator of a finite product of cyclic quotient modules. -/
noncomputable def quotientPiGenerator
    (A : Type*) [CommRing A] {m : ℕ} (I : Fin m → Ideal A) (i : Fin m) :
    ∀ j, A ⧸ I j :=
  Pi.single i (Ideal.Quotient.mk (I i) 1)

/-- For a descending chain of cyclic quotients, the ideal in position `q` annihilates the
`k`th exterior power, where the total number of factors is `q + k`. -/
theorem exterior_pi_quotients
    (A : Type*) [CommRing A]
    (q k : ℕ) (hk : 0 < k) (I : Fin (q + k) → Ideal A) (hI : Antitone I) :
    I ⟨q, by omega⟩ ≤ Module.annihilator A (⋀[A]^k (∀ i, A ⧸ I i)) := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  let g : Fin (q + k) → (∀ i, A ⧸ I i) := quotientPiGenerator A I
  have hg : Submodule.span A (Set.range g) = ⊤ := by
    simpa [g, quotientPiGenerator] using
      pi_single_top A (Fin (q + k)) I
  let S : Set (⋀[A]^k (∀ i, A ⧸ I i)) :=
    exteriorPower.ιMulti A k '' {v | Set.range v ⊆ Set.range g}
  have hS : Submodule.span A S = ⊤ := by
    exact exteriorPower.ιMulti_span_of_span A k _ hg
  have hx : x ∈ Submodule.span A S := by
    rw [hS]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun y _ ↦ r • y = 0) ?_ (by simp)
      (fun y z _ _ hy hz ↦ by simp [hy, hz])
      (fun a y _ hy ↦ by
        calc
          r • (a • y) = a • (r • y) := smul_comm r a y
          _ = 0 := by rw [hy, smul_zero]) hx
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  have hv' : ∀ t, ∃ i, v t = g i := fun t ↦ by
    obtain ⟨i, hi⟩ := Set.mem_range.mp (hv (Set.mem_range_self t))
    exact ⟨i, hi.symm⟩
  choose f hf using hv'
  by_cases hinj : Function.Injective f
  · let fe : Fin k ↪ Fin (q + k) := ⟨f, hinj⟩
    obtain ⟨t, ht⟩ := embedding_hits_initial hk (by omega) fe
    have hqt : f t ≤ ⟨q, by omega⟩ := by
      exact Fin.mk_le_mk.mpr (by simpa using ht)
    have hrt : r ∈ I (f t) := hI hqt hr
    have hkill : r • v t = 0 := by
      rw [hf t]
      ext j
      by_cases hj : j = f t
      · subst j
        simp only [g, quotientPiGenerator, Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply]
        simpa [Algebra.smul_def] using
          (Ideal.Quotient.eq_zero_iff_mem.mpr hrt)
      · simp [g, quotientPiGenerator, hj]
    have hmap := (exteriorPower.ιMulti A k).map_update_smul v t r (v t)
    simp only [Function.update_eq_self] at hmap
    rw [← hmap, hkill]
    simp
  · have hz : exteriorPower.ιMulti A k v = 0 :=
      AlternatingMap.map_eq_zero_of_not_injective _ _ (fun h ↦ hinj <| by
        intro i j hij
        apply h
        rw [hf i, hf j, hij])
    simp [hz]

/-- The inclusion of the final `k` coordinates in a tuple of length `q + k`. -/
def finTailIndex (q k : ℕ) (j : Fin k) : Fin (q + k) :=
  ⟨q + j, by omega⟩

/-- The quotient map induced by an inclusion of ideals. -/
noncomputable def quotientLinear
    (A : Type*) [CommRing A] (I J : Ideal A) (h : I ≤ J) :
    (A ⧸ I) →ₗ[A] (A ⧸ J) :=
  I.liftQ J.mkQ (by simpa using h)

@[simp]
theorem quotient_linear_mk
    (A : Type*) [CommRing A] (I J : Ideal A) (h : I ≤ J) (a : A) :
    quotientLinear A I J h (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J a := by
  rfl

/-- Projection to the final `k` cyclic factors, followed by their natural maps to the quotient
by the ideal in position `q`. -/
noncomputable def invariantTailCoordinates
    (A : Type*) [CommRing A]
    (q k : ℕ) (hk : 0 < k) (I : Fin (q + k) → Ideal A) (hI : Antitone I) :
    (∀ i, A ⧸ I i) →ₗ[A] (Fin k → A ⧸ I ⟨q, by omega⟩) :=
  LinearMap.pi fun j ↦
    (quotientLinear A (I (finTailIndex q k j)) (I ⟨q, by omega⟩)
      (hI (by
        apply Fin.mk_le_mk.mpr
        omega))).comp
      (LinearMap.proj (finTailIndex q k j))

@[simp]
theorem invariant_coordinates_generator
    (A : Type*) [CommRing A]
    (q k : ℕ) (hk : 0 < k) (I : Fin (q + k) → Ideal A) (hI : Antitone I)
    (j : Fin k) :
    invariantTailCoordinates A q k hk I hI
        (quotientPiGenerator A I (finTailIndex q k j)) =
      Pi.single j (Ideal.Quotient.mk (I ⟨q, by omega⟩) 1) := by
  ext l
  by_cases hlj : l = j
  · subst l
    simp only [invariantTailCoordinates, LinearMap.pi_apply, LinearMap.comp_apply,
      quotientPiGenerator, LinearMap.proj_apply, Pi.single_eq_same]
    change quotientLinear A _ _ _ (Ideal.Quotient.mk _ 1) =
      Ideal.Quotient.mk _ 1
    exact quotient_linear_mk A _ _ _ 1
  · have hidx : finTailIndex q k l ≠ finTailIndex q k j := by
      intro h
      apply hlj
      exact Fin.ext (by simpa [finTailIndex] using congrArg Fin.val h)
    simp [invariantTailCoordinates, quotientPiGenerator, hlj, hidx]

/-- The determinant on matrices over an `A`-algebra, regarded as an `A`-alternating map in its
rows. -/
noncomputable def detRowScalars
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) :
    (Fin k → B) [⋀^Fin k]→ₗ[A] B where
  toMultilinearMap :=
    (Matrix.detRowAlternating : (Fin k → B) [⋀^Fin k]→ₗ[B] B).toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' v _ _ h hij :=
    (Matrix.detRowAlternating : (Fin k → B) [⋀^Fin k]→ₗ[B] B).map_eq_zero_of_eq v h hij

/-- The determinant functional on the final `k` quotient coordinates. -/
noncomputable def invariantTailDet
    (A : Type*) [CommRing A]
    (q k : ℕ) (hk : 0 < k) (I : Fin (q + k) → Ideal A) (hI : Antitone I) :
    (∀ i, A ⧸ I i) [⋀^Fin k]→ₗ[A] (A ⧸ I ⟨q, by omega⟩) :=
  (detRowScalars A (A ⧸ I ⟨q, by omega⟩) k).compLinearMap
    (invariantTailCoordinates A q k hk I hI)

/-- The tail determinant sends the wedge of the final coordinate generators to `1`. -/
theorem invariant_det_generators
    (A : Type*) [CommRing A]
    (q k : ℕ) (hk : 0 < k) (I : Fin (q + k) → Ideal A) (hI : Antitone I) :
    invariantTailDet A q k hk I hI
        (fun j ↦ quotientPiGenerator A I (finTailIndex q k j)) = 1 := by
  change Matrix.det
      (fun j ↦ invariantTailCoordinates A q k hk I hI
        (quotientPiGenerator A I (finTailIndex q k j))) = 1
  rw [show (fun j ↦ invariantTailCoordinates A q k hk I hI
      (quotientPiGenerator A I (finTailIndex q k j))) =
      (1 : Matrix (Fin k) (Fin k) (A ⧸ I ⟨q, by omega⟩)) by
    ext i j
    rw [invariant_coordinates_generator]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]]
  exact Matrix.det_one

/-- The annihilator of the `k`th exterior power of a descending cyclic presentation is
contained in the ideal in position `q`. -/
theorem annihilator_exterior_pi
    (A : Type*) [CommRing A]
    (q k : ℕ) (hk : 0 < k) (I : Fin (q + k) → Ideal A) (hI : Antitone I) :
    Module.annihilator A (⋀[A]^k (∀ i, A ⧸ I i)) ≤ I ⟨q, by omega⟩ := by
  intro r hr
  let v : Fin k → (∀ i, A ⧸ I i) :=
    fun j ↦ quotientPiGenerator A I (finTailIndex q k j)
  let F : (⋀[A]^k (∀ i, A ⧸ I i)) →ₗ[A] (A ⧸ I ⟨q, by omega⟩) :=
    exteriorPower.alternatingMapLinearEquiv (invariantTailDet A q k hk I hI)
  have hann := Module.mem_annihilator.mp hr (exteriorPower.ιMulti A k v)
  have happ := congrArg F hann
  simp only [map_smul, map_zero, F, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    v, invariant_det_generators] at happ
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa [Algebra.smul_def] using happ

/-- Exterior-power annihilators recover every entry of a descending cyclic presentation. -/
theorem annihilator_exterior_quotients
    (A : Type*) [CommRing A]
    (q k : ℕ) (hk : 0 < k) (I : Fin (q + k) → Ideal A) (hI : Antitone I) :
    Module.annihilator A (⋀[A]^k (∀ i, A ⧸ I i)) = I ⟨q, by omega⟩ := by
  apply le_antisymm
  · exact annihilator_exterior_pi A q k hk I hI
  · exact exterior_pi_quotients A q k hk I hI

/-- Equality of exterior-power annihilators recovers the ideal in any specified slot of two
equal-length descending cyclic presentations. -/
theorem invariant_pi_linear
    (A : Type*) [CommRing A]
    (q k : ℕ) (hk : 0 < k)
    (I J : Fin (q + k) → Ideal A) (hI : Antitone I) (hJ : Antitone J)
    (e : (∀ i, A ⧸ I i) ≃ₗ[A] (∀ i, A ⧸ J i)) :
    I ⟨q, by omega⟩ = J ⟨q, by omega⟩ := by
  rw [← annihilator_exterior_quotients A q k hk I hI,
    ← annihilator_exterior_quotients A q k hk J hJ]
  exact exterior_annihilator_linear A _ _ k e

/-- Full-chain uniqueness for equal-length antitone presentations by cyclic quotients. -/
theorem invariant_factors_linear
    (A : Type*) [CommRing A]
    (n : ℕ) (I J : Fin n → Ideal A) (hI : Antitone I) (hJ : Antitone J)
    (e : (⨁ i, A ⧸ I i) ≃ₗ[A] (⨁ i, A ⧸ J i)) :
    I = J := by
  classical
  let ePi : (∀ i, A ⧸ I i) ≃ₗ[A] (∀ i, A ⧸ J i) :=
    (DirectSum.linearEquivFunOnFintype A (Fin n) (fun i ↦ A ⧸ I i)).symm ≪≫ₗ
      e ≪≫ₗ
      DirectSum.linearEquivFunOnFintype A (Fin n) (fun i ↦ A ⧸ J i)
  funext i
  let k := n - i.val
  have hk : 0 < k := by
    dsimp [k]
    omega
  have hsum : i.val + k = n := by
    dsimp [k]
    omega
  let σ : Fin (i.val + k) ≃ Fin n := finCongr hsum
  let I' : Fin (i.val + k) → Ideal A := fun a ↦ I (σ a)
  let J' : Fin (i.val + k) → Ideal A := fun a ↦ J (σ a)
  have hσ : Monotone σ := by
    intro a b hab
    apply Fin.mk_le_mk.mpr
    exact Fin.mk_le_mk.mp hab
  have hI' : Antitone I' := by
    simpa [I'] using hI.comp_monotone hσ
  have hJ' : Antitone J' := by
    simpa [J'] using hJ.comp_monotone hσ
  let rI : (∀ a, A ⧸ I' a) ≃ₗ[A] (∀ a, A ⧸ I (σ a)) := LinearEquiv.refl A _
  let rJ : (∀ a, A ⧸ J' a) ≃ₗ[A] (∀ a, A ⧸ J (σ a)) := LinearEquiv.refl A _
  let cI : (∀ a, A ⧸ I (σ a)) ≃ₗ[A] (∀ j, A ⧸ I j) :=
    LinearEquiv.piCongrLeft A (fun j ↦ A ⧸ I j) σ
  let cJ : (∀ a, A ⧸ J (σ a)) ≃ₗ[A] (∀ j, A ⧸ J j) :=
    LinearEquiv.piCongrLeft A (fun j ↦ A ⧸ J j) σ
  have hslot := invariant_pi_linear A i.val k hk I' J' hI' hJ'
    (rI ≪≫ₗ cI ≪≫ₗ ePi ≪≫ₗ cJ.symm ≪≫ₗ rJ.symm)
  change I (σ ⟨i.val, by omega⟩) = J (σ ⟨i.val, by omega⟩) at hslot
  simpa [σ, Fin.ext_iff] using hslot

end Towers.NumberTheory.Milne
