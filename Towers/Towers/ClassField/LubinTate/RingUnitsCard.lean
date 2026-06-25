import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Data.Set.Card
import Towers.NumberTheory.Locals.TotallyRamifiedEisenstein
import Towers.ClassField.LubinTate.BallModel
import Towers.ClassField.LubinTate.NatCompX

/-!
# Class Field Theory, Chapter I, Theorem 3.6

Algebraic and finite-cardinality ingredients for the Lubin--Tate extension
theorem.  The local-field tower itself requires additional infrastructure for
evaluating the formal group on algebraic elements, but the quotient and unit
counts used in the degree comparison are intrinsic to the coefficient DVR.
-/

namespace Towers.CField.LTate

noncomputable section

open Polynomial
open Towers.CField.FGroups

/-- In a finite local ring, the units are the complement of the maximal
ideal, so their cardinality is obtained by subtraction. -/
theorem ring_units_card
    (R : Type*) [CommRing R] [IsLocalRing R] [Finite R] :
    Nat.card Rˣ = Nat.card R -
      (IsLocalRing.maximalIdeal R : Set R).ncard := by
  calc
    Nat.card Rˣ = Nat.card (IsUnit.submonoid R) :=
      Nat.card_congr Submonoid.unitsTypeEquivIsUnitSubmonoid.toEquiv
    _ = ({x : R | IsUnit x} : Set R).ncard := by
      rw [← Nat.card_coe_set_eq]
      rfl
    _ = ((IsLocalRing.maximalIdeal R : Set R)ᶜ).ncard := by
      congr 1
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, SetLike.mem_coe,
        IsLocalRing.notMem_maximalIdeal]
    _ = Nat.card R - (IsLocalRing.maximalIdeal R : Set R).ncard := by
      rw [Set.ncard_compl]

/-- Powers of a uniformizer in a DVR have quotient cardinality equal to the
corresponding power of the residue-field cardinality. -/
theorem card_span_pow
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {pi : A} (hpi : Irreducible pi) [Finite (A ⧸ Ideal.span {pi})]
    (n : ℕ) :
    Nat.card (A ⧸ Ideal.span {pi ^ n}) =
      Nat.card (A ⧸ Ideal.span {pi}) ^ n := by
  let P : Ideal A := Ideal.span {pi}
  letI : P.IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible hpi).isPrime
  have hP : P ≠ ⊥ := by
    change Ideal.span {pi} ≠ ⊥
    intro h
    exact hpi.ne_zero (Ideal.span_singleton_eq_bot.mp h)
  rw [← Ideal.span_singleton_pow, ← Submodule.cardQuot_apply,
    cardQuot_pow_of_prime hP, Submodule.cardQuot_apply]

/-- The unit group of the quotient by `pi^(n+1)` has cardinality
`(q - 1) * q^n`, where `q` is the cardinality of the residue field. -/
theorem card_units_succ
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {pi : A} (hpi : Irreducible pi) [Finite (A ⧸ Ideal.span {pi})]
    (n : ℕ) :
    Nat.card (A ⧸ Ideal.span {pi ^ (n + 1)})ˣ =
      (Nat.card (A ⧸ Ideal.span {pi}) - 1) *
        Nat.card (A ⧸ Ideal.span {pi}) ^ n := by
  let P : Ideal A := Ideal.span {pi}
  let I : Ideal A := P ^ (n + 1)
  let q : ℕ := Nat.card (A ⧸ P)
  letI : P.IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible hpi).isPrime
  have hP_bot : P ≠ ⊥ := by
    change Ideal.span {pi} ≠ ⊥
    intro h
    exact hpi.ne_zero (Ideal.span_singleton_eq_bot.mp h)
  have hP_top : P ≠ ⊤ :=
    (PrincipalIdealRing.isMaximal_of_irreducible hpi).ne_top
  letI : Nontrivial (A ⧸ P) :=
    Ideal.Quotient.nontrivial_iff.mpr hP_top
  have hq : q ≠ 0 := by
    exact Nat.ne_zero_of_lt (Nat.card_pos)
  have hIP : I ≤ P := by
    exact Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hI_top : I ≠ ⊤ := by
    intro hI
    apply hP_top
    apply top_unique
    simpa only [hI] using hIP
  letI : Finite (A ⧸ I) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian P) (n + 1)
  letI : Nontrivial (A ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr hI_top
  letI : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hmax : IsLocalRing.maximalIdeal (A ⧸ I) =
      P.map (Ideal.Quotient.mk I) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      hpi.maximalIdeal_eq]
  have hquot_card : Nat.card (A ⧸ I) = q ^ (n + 1) := by
    simpa only [I, P, q, Ideal.span_singleton_pow] using
      card_span_pow hpi (n + 1)
  have hmap_relation :
      Nat.card (Submodule.map I.mkQ (P : Submodule A A)) * q =
        q ^ n * q := by
    calc
      Nat.card (Submodule.map I.mkQ (P : Submodule A A)) * q =
          Nat.card (A ⧸ I) := by
        simpa only [q] using
          Submodule.card_quotient_mul_card_quotient P I hIP
      _ = q ^ (n + 1) := hquot_card
      _ = q ^ n * q := by rw [pow_succ]
  have hmap_card : Nat.card (Submodule.map I.mkQ (P : Submodule A A)) =
      q ^ n := by
    apply (mul_right_inj' hq).mp
    simpa only [mul_comm] using hmap_relation
  have hmap_carrier :
      (P.map (Ideal.Quotient.mk I) : Set (A ⧸ I)) =
        (Submodule.map I.mkQ (P : Submodule A A) : Set (A ⧸ I)) := by
    ext z
    change z ∈ P.map (Ideal.Quotient.mk I) ↔
      z ∈ Submodule.map I.mkQ (P : Submodule A A)
    rw [Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    · rintro hz
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
      exact ⟨x, hx, rfl⟩
  have hmax_card :
      (IsLocalRing.maximalIdeal (A ⧸ I) : Set (A ⧸ I)).ncard = q ^ n := by
    rw [hmax]
    change (P.map (Ideal.Quotient.mk I) : Set (A ⧸ I)).ncard = q ^ n
    rw [hmap_carrier, ← Nat.card_coe_set_eq]
    exact hmap_card
  calc
    Nat.card (A ⧸ Ideal.span {pi ^ (n + 1)})ˣ =
        Nat.card (A ⧸ I)ˣ := by
      rw [← Ideal.span_singleton_pow]
    _ = Nat.card (A ⧸ I) -
        (IsLocalRing.maximalIdeal (A ⧸ I) : Set (A ⧸ I)).ncard :=
      ring_units_card (A ⧸ I)
    _ = q ^ (n + 1) - q ^ n := by rw [hquot_card, hmax_card]
    _ = (q - 1) * q ^ n := by
      rw [pow_succ, mul_comm (q ^ n) q, Nat.sub_mul, one_mul]
    _ = (Nat.card (A ⧸ Ideal.span {pi}) - 1) *
        Nat.card (A ⧸ Ideal.span {pi}) ^ n := by rfl

/-- The unit-count formula in the indexing used in Theorem 3.6. -/
theorem card_units_pow
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {pi : A} (hpi : Irreducible pi) [Finite (A ⧸ Ideal.span {pi})]
    {n : ℕ} (hn : n ≠ 0) :
    Nat.card (A ⧸ Ideal.span {pi ^ n})ˣ =
      (Nat.card (A ⧸ Ideal.span {pi}) - 1) *
        Nat.card (A ⧸ Ideal.span {pi}) ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa only [Nat.succ_eq_add_one, Nat.succ_sub_one] using
    card_units_succ hpi m

/-- The automorphism group of the abstract torsion kernel has the order used
as the Galois-group upper bound in Theorem 3.6. -/
theorem card_torsion_aut
    {A M : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [AddCommGroup M] [Module A M]
    {pi : A} (hpi : Irreducible pi) [Finite (A ⧸ Ideal.span {pi})]
    (hsurj : Function.Surjective fun x : M ↦ pi • x)
    (hcard : Nat.card (torsionKernel (M := M) pi 1) =
      Nat.card (A ⧸ Ideal.span {pi}))
    {n : ℕ} (hn : n ≠ 0) :
    Nat.card (torsionKernel (M := M) pi n ≃ₗ[A]
      torsionKernel (M := M) pi n) =
        (Nat.card (A ⧸ Ideal.span {pi}) - 1) *
          Nat.card (A ⧸ Ideal.span {pi}) ^ (n - 1) := by
  rw [Nat.card_congr
    (torsionAutUnits hpi hsurj hcard n).toEquiv]
  exact card_units_pow hpi hn

/-- The automorphism-count conclusion used in Theorem 3.6, with the
surjectivity and first-level cardinality hypotheses supplied by the open-ball
model from Proposition 3.4. -/
theorem ball_model_aut
    {A M L Γ : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [AddCommGroup M] [Module A M]
    [Field L] [Algebra A L] [FaithfulSMul A L] [IsAlgClosed L]
    [LinearOrderedCommGroupWithZero Γ]
    {v : Valuation L Γ} {pi : A} {q : ℕ}
    [Finite (A ⧸ Ideal.span {pi})]
    (model : LBModel A M L Γ v pi q)
    (hpiVal : v (algebraMap A L pi) < 1)
    (hpi : Irreducible pi)
    (hresidue : Nat.card (A ⧸ Ideal.span {pi}) = q)
    {n : ℕ} (hn : n ≠ 0) :
    Nat.card (torsionKernel (M := M) pi n ≃ₗ[A]
      torsionKernel (M := M) pi n) =
        (q - 1) * q ^ (n - 1) := by
  simpa only [hresidue] using card_torsion_aut hpi
    (model.uniformizer_surjective
      (LBModel.one_residue_card hpi hresidue) hpiVal)
    (model.torsion_kernel_residue hpiVal hpi hresidue) hn

/-- An action on a set of field generators is faithful when evaluation of
the action agrees with the field automorphism action. -/
theorem galois_action_generates
    {K E A M : Type*} [Field K] [Field E] [Algebra K E]
    [CommRing A] [AddCommGroup M] [Module A M]
    (point : M → E)
    (ρ : (E ≃ₐ[K] E) →* (M ≃ₗ[A] M))
    (hpoint : ∀ σ x, point (ρ σ x) = σ (point x))
    (hgen : Algebra.adjoin K (Set.range point) = ⊤) :
    Function.Injective ρ := by
  intro σ τ hστ
  apply AlgEquiv.ext
  intro x
  apply (AlgHom.mem_equalizer σ.toAlgHom τ.toAlgHom x).mp
  have hequalizer : AlgHom.equalizer σ.toAlgHom τ.toAlgHom = ⊤ := by
    rw [← top_le_iff, ← hgen, Algebra.adjoin_le_iff]
    rintro _ ⟨m, rfl⟩
    change σ (point m) = τ (point m)
    rw [← hpoint σ m, ← hpoint τ m, hστ]
  exact (SetLike.ext_iff.mp hequalizer x).mpr Algebra.mem_top

/-- Once the Galois action on a Lubin--Tate torsion module has been shown
faithful and linear, its automorphism count gives Milne's upper bound for the
extension degree. -/
theorem galois_action_aut
    {K E A M : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    [CommRing A] [AddCommGroup M] [Module A M]
    [Finite (M ≃ₗ[A] M)]
    (ρ : (E ≃ₐ[K] E) →* (M ≃ₗ[A] M))
    (hρ : Function.Injective ρ) :
    Module.finrank K E ≤ Nat.card (M ≃ₗ[A] M) := by
  rw [← IsGalois.card_aut_eq_finrank K E]
  exact Nat.card_le_card_of_injective ρ hρ

/-- If the faithful linear action has the same cardinality as the extension
degree, the Galois group is the full linear automorphism group.  This is the
cardinality squeeze in Theorem 3.6(b). -/
noncomputable def galoisActionAut
    {K E A M : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    [CommRing A] [AddCommGroup M] [Module A M]
    [Finite (M ≃ₗ[A] M)]
    (ρ : (E ≃ₐ[K] E) →* (M ≃ₗ[A] M))
    (hρ : Function.Injective ρ)
    (hcard : Nat.card (M ≃ₗ[A] M) = Module.finrank K E) :
    (E ≃ₐ[K] E) ≃* (M ≃ₗ[A] M) := by
  apply MulEquiv.ofBijective ρ
  refine ⟨hρ, ?_⟩
  have he : Nonempty ((E ≃ₐ[K] E) ≃ (M ≃ₗ[A] M)) :=
    Finite.card_eq.mp <|
      (IsGalois.card_aut_eq_finrank K E).trans hcard.symm
  exact hρ.surjective_of_finite (Classical.choice he)

/-- Milne's complete degree squeeze: a root-generated subfield of degree
`d`, together with a faithful Galois action on a module whose automorphism
group has cardinality `d`, is already the whole ambient extension. -/
theorem action_cardinality_squeeze
    {K E A M : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    [CommRing A] [AddCommGroup M] [Module A M]
    [Finite (M ≃ₗ[A] M)]
    (ρ : (E ≃ₐ[K] E) →* (M ≃ₗ[A] M))
    (hρ : Function.Injective ρ) (d : ℕ)
    (hcard : Nat.card (M ≃ₗ[A] M) = d)
    (x : E)
    (hrootDegree :
      Module.finrank K (IntermediateField.adjoin K {x}) = d) :
    Module.finrank K E = d ∧
      IntermediateField.adjoin K {x} = ⊤ := by
  have hupper : Module.finrank K E ≤ d := by
    rw [← hcard]
    exact galois_action_aut ρ hρ
  have hlower : d ≤ Module.finrank K E := by
    calc
      d = Module.finrank K (IntermediateField.adjoin K {x}) :=
        hrootDegree.symm
      _ ≤ Module.finrank K (⊤ : IntermediateField K E) :=
        IntermediateField.finrank_le_of_le_right
          (F := IntermediateField.adjoin K {x})
          (E := (⊤ : IntermediateField K E)) le_top
      _ = Module.finrank K E := IntermediateField.finrank_top'
  have hdegree : Module.finrank K E = d :=
    Nat.le_antisymm hupper hlower
  refine ⟨hdegree, ?_⟩
  apply IntermediateField.eq_of_le_of_finrank_eq le_top
  calc
    Module.finrank K (IntermediateField.adjoin K {x}) = d := hrootDegree
    _ = Module.finrank K E := hdegree.symm
    _ = Module.finrank K (⊤ : IntermediateField K E) :=
      IntermediateField.finrank_top'.symm

/-- The polynomial called `f^[n+1]` in Milne: first iterate `f` `n`
times, then apply `f / X`. -/
def reducedLubinIterate
    {R : Type*} [CommSemiring R] (f : R[X]) (n : ℕ) : R[X] :=
  f.divX.comp (f.comp^[n] Polynomial.X)

/-- Reduced Lubin--Tate iterates commute with a change of coefficients. -/
theorem lubin_tate_iterate
    {A B : Type*} [CommRing A] [CommRing B]
    (g : A →+* B) (f : A[X]) (n : ℕ) :
    (reducedLubinIterate f n).map g =
      reducedLubinIterate (f.map g) n := by
  have hdivmap : f.divX.map g = (f.map g).divX := by
    ext i
    simp only [Polynomial.coeff_map, Polynomial.coeff_divX]
  have hiter : (f.comp^[n] X).map g = (f.map g).comp^[n] X := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Polynomial.map_comp, ih]
  rw [reducedLubinIterate, reducedLubinIterate,
    Polynomial.map_comp, hdivmap, hiter]

/-- If `f(0)=0`, every compositional iterate of `f` applied to `X` also
has zero constant coefficient. -/
theorem coeff_comp_x
    {R : Type*} [CommSemiring R] (f : R[X])
    (hf0 : f.coeff 0 = 0) (n : ℕ) :
    (f.comp^[n] Polynomial.X).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.iterate_comp_eval]
  have hfix : f.eval 0 = 0 := by
    simpa only [← Polynomial.coeff_zero_eq_eval_zero] using hf0
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hfix]

/-- The constant coefficient of Milne's reduced iterate is the linear
coefficient of `f`. -/
theorem reduced_iterate_coeff
    {R : Type*} [CommSemiring R] (f : R[X])
    (hf0 : f.coeff 0 = 0) (n : ℕ) :
    (reducedLubinIterate f n).coeff 0 = f.coeff 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, reducedLubinIterate,
    Polynomial.eval_comp, ← Polynomial.coeff_zero_eq_eval_zero,
    coeff_comp_x f hf0 n]
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simpa only [Nat.zero_add] using
    (Polynomial.coeff_divX (p := f) (n := 0))

/-- The degree calculation in Theorem 3.6(c). -/
theorem reduced_iterate_degree
    {R : Type*} [CommSemiring R] [Nontrivial R] [NoZeroDivisors R]
    (f : R[X]) (n : ℕ) :
    (reducedLubinIterate f n).natDegree =
      (f.natDegree - 1) * f.natDegree ^ n := by
  rw [reducedLubinIterate, Polynomial.natDegree_comp,
    Polynomial.natDegree_divX_eq_natDegree_tsub_one,
    Polynomial.natDegree_iterate_comp, Polynomial.natDegree_X, mul_one]

/-- Dividing a monic polynomial with zero constant coefficient by `X`
preserves monicity. -/
theorem monic_div_x
    {R : Type*} [CommRing R] [IsDomain R] {f : R[X]}
    (hf : f.Monic) (hf0 : f.coeff 0 = 0) : f.divX.Monic := by
  have hmul : Polynomial.X * f.divX = f := by
    simpa only [hf0, Polynomial.C_0, add_zero] using
      Polynomial.X_mul_divX_add f
  apply Polynomial.Monic.of_mul_monic_left Polynomial.monic_X
  rw [hmul]
  exact hf

/-- Under the polynomial Lubin--Tate coefficient conditions, `f / X` is
Eisenstein at the uniformizer ideal.  This is the first step of the recursive
Eisenstein tower in Theorem 3.6. -/
theorem div_eisenstein_uniformizer
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {pi : A} (hpi : Irreducible pi) {f : A[X]}
    (hf : f.Monic) (hf0 : f.coeff 0 = 0) (hf1 : f.coeff 1 = pi)
    (hdeg : 1 < f.natDegree)
    (hcoeff : ∀ {i : ℕ}, i < f.natDegree →
      f.coeff i ∈ Ideal.span {pi}) :
    f.divX.IsEisensteinAt (Ideal.span {pi}) := by
  have hdivMonic : f.divX.Monic := monic_div_x hf hf0
  constructor
  · rw [hdivMonic.leadingCoeff]
    intro h1
    exact (PrincipalIdealRing.isMaximal_of_irreducible hpi).ne_top
      ((Ideal.eq_top_iff_one _).mpr h1)
  · intro i hi
    rw [Polynomial.coeff_divX]
    apply hcoeff
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one] at hi
    omega
  · rw [Polynomial.coeff_divX, Nat.zero_add, hf1,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    have hdvd' : pi ^ 2 ∣ pi ^ 1 := by simpa using hdvd
    have hle : (2 : ℕ) ≤ 1 :=
      (pow_dvd_pow_iff (a := pi) (n := 2) (m := 1)
        hpi.ne_zero hpi.not_isUnit).mp hdvd'
    omega

/-- Consequently, `f / X` is irreducible over the fraction field of the
coefficient DVR. -/
theorem div_x_irreducible
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {pi : A} (hpi : Irreducible pi) {f : A[X]}
    (hf : f.Monic) (hf0 : f.coeff 0 = 0) (hf1 : f.coeff 1 = pi)
    (hdeg : 1 < f.natDegree)
    (hcoeff : ∀ {i : ℕ}, i < f.natDegree →
      f.coeff i ∈ Ideal.span {pi}) :
    Irreducible (f.divX.map (algebraMap A K)) := by
  have heis := div_eisenstein_uniformizer
    hpi hf hf0 hf1 hdeg hcoeff
  have hmonic := monic_div_x hf hf0
  apply Towers.NumberTheory.Milne.eisenstein_irreducible_fraction
    (PrincipalIdealRing.isMaximal_of_irreducible hpi).isPrime
    heis hmonic
  rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
  omega

/-- Subtracting a constant of valuation exactly one from a monic polynomial
whose lower coefficients lie in `P` gives an Eisenstein polynomial.  This is
the algebraic pattern for the higher recursive steps `f(T)-pi_(n-1)`. -/
theorem sub_c_eisenstein
    {R : Type*} [CommRing R] [IsDomain R]
    {P : Ideal R} (hP : P ≠ ⊤) {f : R[X]} (hf : f.Monic)
    (hdeg : f.natDegree ≠ 0) (hf0 : f.coeff 0 = 0)
    (hcoeff : ∀ {i : ℕ}, i < f.natDegree → f.coeff i ∈ P)
    {a : R} (ha : a ∈ P) (ha2 : a ∉ P ^ 2) :
    (f - Polynomial.C a).IsEisensteinAt P := by
  have hdegree : (Polynomial.C a).degree < f.degree := by
    apply lt_of_le_of_lt Polynomial.degree_C_le
    rw [Polynomial.degree_eq_natDegree hf.ne_zero]
    exact WithBot.coe_pos.mpr (Nat.pos_of_ne_zero hdeg)
  have hmonic : (f - Polynomial.C a).Monic := hf.sub_of_left hdegree
  constructor
  · rw [hmonic.leadingCoeff]
    exact fun h1 ↦ hP ((Ideal.eq_top_iff_one _).mpr h1)
  · intro i hi
    rw [Polynomial.natDegree_sub_C] at hi
    by_cases hi0 : i = 0
    · subst i
      simp only [Polynomial.coeff_sub, hf0, Polynomial.coeff_C_zero,
        zero_sub]
      exact P.neg_mem ha
    · simp only [Polynomial.coeff_sub, Polynomial.coeff_C,
        if_neg hi0, sub_zero]
      exact hcoeff hi
  · simp only [Polynomial.coeff_sub, hf0, Polynomial.coeff_C_zero,
      zero_sub, Ideal.neg_mem_iff]
    exact ha2

/-- Milne's reduced iterate is monic. -/
theorem reduced_iterate_monic
    {R : Type*} [CommRing R] [IsDomain R] {f : R[X]}
    (hf : f.Monic) (hf0 : f.coeff 0 = 0)
    (hdeg : f.natDegree ≠ 0) (n : ℕ) :
    (reducedLubinIterate f n).Monic := by
  apply (monic_div_x hf hf0).comp
    (monic_iterate_x hf hdeg n)
  rw [Polynomial.natDegree_iterate_comp, Polynomial.natDegree_X, mul_one]
  exact pow_ne_zero n hdeg

/-- Modulo the uniformizer, Milne's reduced level polynomial is a pure
power.  This is the coefficient calculation behind the Eisenstein argument
in Theorem 3.6(a). -/
theorem reduced_iterate_uniformizer
    {A : Type*} [CommRing A] {pi : A} {f : A[X]} {q n : ℕ}
    (hq0 : q ≠ 0)
    (hmod : f.map (Ideal.Quotient.mk (Ideal.span {pi})) = X ^ q) :
    (reducedLubinIterate f n).map
        (Ideal.Quotient.mk (Ideal.span {pi})) =
      X ^ ((q - 1) * q ^ n) := by
  let g := Ideal.Quotient.mk (Ideal.span {pi})
  have hdivmap : f.divX.map g = (f.map g).divX := by
    ext i
    simp only [Polynomial.coeff_map, Polynomial.coeff_divX]
  have hiter : (f.comp^[n] X).map g = X ^ (q ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', Polynomial.map_comp, hmod, ih]
        rw [Polynomial.X_pow_comp, ← pow_mul, pow_succ, mul_comm]
  rw [reducedLubinIterate, Polynomial.map_comp, hdivmap, hmod, hiter]
  rw [Polynomial.divX_X_pow, if_neg hq0, Polynomial.X_pow_comp,
    ← pow_mul, mul_comm]

/-- Every reduced Lubin--Tate level polynomial is Eisenstein at the
uniformizer. -/
theorem reduced_eisenstein_uniformizer
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {pi : A} (hpi : Irreducible pi) {f : A[X]} {q : ℕ}
    (hf : f.Monic) (hf0 : f.coeff 0 = 0) (hf1 : f.coeff 1 = pi)
    (hq : f.natDegree = q) (hqgt : 1 < q)
    (hmod : f.map (Ideal.Quotient.mk (Ideal.span {pi})) = X ^ q)
    (n : ℕ) :
    (reducedLubinIterate f n).IsEisensteinAt
      (Ideal.span {pi}) := by
  let P : Ideal A := Ideal.span {pi}
  have hmonic : (reducedLubinIterate f n).Monic :=
    reduced_iterate_monic hf hf0 (by omega) n
  have hdeg : (reducedLubinIterate f n).natDegree =
      (q - 1) * q ^ n := by
    rw [reduced_iterate_degree, hq]
  have hmap :=
    reduced_iterate_uniformizer
      (n := n) (by omega) hmod
  constructor
  · rw [hmonic.leadingCoeff]
    exact fun h1 =>
      (PrincipalIdealRing.isMaximal_of_irreducible hpi).ne_top
        ((Ideal.eq_top_iff_one _).mpr h1)
  · intro i hi
    have hi' : i < (q - 1) * q ^ n := by
      simpa [hdeg] using hi
    have hcoeffzero :
        ((reducedLubinIterate f n).map
          (Ideal.Quotient.mk P)).coeff i = 0 := by
      rw [hmap]
      simp [hi'.ne]
    rw [Polynomial.coeff_map,
      Ideal.Quotient.eq_zero_iff_mem] at hcoeffzero
    exact hcoeffzero
  · change (reducedLubinIterate f n).coeff 0 ∉
      (Ideal.span {pi}) ^ 2
    rw [reduced_iterate_coeff f hf0 n, hf1,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    have hdvd' : pi ^ 2 ∣ pi ^ 1 := by
      simpa using hdvd
    have hle : (2 : ℕ) ≤ 1 :=
      (pow_dvd_pow_iff (a := pi) (n := 2) (m := 1)
        hpi.ne_zero hpi.not_isUnit).mp hdvd'
    omega

/-- Source-facing form of the preceding theorem: a monic polynomial in
Milne's set `ℱ_π`, of degree `q`, has Eisenstein reduced iterates. -/
theorem reduced_iterate_eisenstein
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {pi : A} (hpi : Irreducible pi) {f : A[X]} {q : ℕ}
    (hf : f.Monic) (hq : f.natDegree = q) (hqgt : 1 < q)
    (hLT : LubinSeries pi q (f : PowerSeries A)) (n : ℕ) :
    (reducedLubinIterate f n).IsEisensteinAt
      (Ideal.span {pi}) := by
  have hf0 : f.coeff 0 = 0 := by
    simpa using hLT.1
  have hf1 : f.coeff 1 = pi := by
    simpa using hLT.2.1
  have hmod : f.map (Ideal.Quotient.mk (Ideal.span {pi})) = X ^ q := by
    apply Polynomial.coe_injective
    simpa only [Polynomial.polynomial_map_coe, Polynomial.coe_X,
      Polynomial.coe_pow] using hLT.2.2
  exact reduced_eisenstein_uniformizer
    hpi hf hf0 hf1 hq hqgt hmod n

/-- The reduced level polynomial remains irreducible after passing from the
coefficient DVR to its fraction field. -/
theorem reduced_iterate_irreducible
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {pi : A} (hpi : Irreducible pi) {f : A[X]} {q : ℕ}
    (hf : f.Monic) (hf0 : f.coeff 0 = 0) (hf1 : f.coeff 1 = pi)
    (hq : f.natDegree = q) (hqgt : 1 < q)
    (hmod : f.map (Ideal.Quotient.mk (Ideal.span {pi})) = X ^ q)
    (n : ℕ) :
    Irreducible ((reducedLubinIterate f n).map (algebraMap A K)) := by
  have heis := reduced_eisenstein_uniformizer
    hpi hf hf0 hf1 hq hqgt hmod n
  have hmonic := reduced_iterate_monic hf hf0 (by omega) n
  apply Towers.NumberTheory.Milne.eisenstein_irreducible_fraction
    (PrincipalIdealRing.isMaximal_of_irreducible hpi).isPrime heis hmonic
  rw [reduced_iterate_degree, hq]
  apply Nat.mul_pos
  · omega
  · exact pow_pos (by omega) n

/-- A root of the reduced level polynomial generates an extension of the
degree asserted in Theorem 3.6(a). -/
theorem adjoin_reduced_iterate
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    {pi : A} (hpi : Irreducible pi) {f : A[X]} {q : ℕ}
    (hf : f.Monic) (hf0 : f.coeff 0 = 0) (hf1 : f.coeff 1 = pi)
    (hq : f.natDegree = q) (hqgt : 1 < q)
    (hmod : f.map (Ideal.Quotient.mk (Ideal.span {pi})) = X ^ q)
    (n : ℕ) (x : L)
    (hroot : Polynomial.aeval x
      ((reducedLubinIterate f n).map (algebraMap A K)) = 0) :
    Module.finrank K (IntermediateField.adjoin K {x}) =
      (q - 1) * q ^ n := by
  let p := (reducedLubinIterate f n).map (algebraMap A K)
  have hpmonic : p.Monic :=
    (reduced_iterate_monic hf hf0 (by omega) n).map _
  have hpirreducible : Irreducible p :=
    reduced_iterate_irreducible
      hpi hf hf0 hf1 hq hqgt hmod n
  have hmin : minpoly K x = p :=
    (minpoly.eq_of_irreducible_of_monic hpirreducible hroot hpmonic).symm
  have hx : IsIntegral K x := ⟨p, hpmonic, hroot⟩
  rw [IntermediateField.adjoin.finrank hx, hmin]
  dsimp only [p]
  rw [(reduced_iterate_monic hf hf0 (by omega) n).natDegree_map,
    reduced_iterate_degree, hq]

/-- For a polynomial Lubin--Tate series, the field generated by any root of
the reduced level polynomial has degree `(q - 1) * q ^ n`. -/
theorem reduced_lubin_iterate
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    {pi : A} (hpi : Irreducible pi) {f : A[X]} {q : ℕ}
    (hf : f.Monic) (hq : f.natDegree = q) (hqgt : 1 < q)
    (hLT : LubinSeries pi q (f : PowerSeries A))
    (n : ℕ) (x : L)
    (hroot : Polynomial.aeval x
      ((reducedLubinIterate f n).map (algebraMap A K)) = 0) :
    Module.finrank K (IntermediateField.adjoin K {x}) =
      (q - 1) * q ^ n := by
  have hf0 : f.coeff 0 = 0 := by
    simpa using hLT.1
  have hf1 : f.coeff 1 = pi := by
    simpa using hLT.2.1
  have hmod : f.map (Ideal.Quotient.mk (Ideal.span {pi})) = X ^ q := by
    apply Polynomial.coe_injective
    simpa only [Polynomial.polynomial_map_coe, Polynomial.coe_X,
      Polynomial.coe_pow] using hLT.2.2
  exact adjoin_reduced_iterate
    hpi hf hf0 hf1 hq hqgt hmod n x hroot

/-- Evaluation of the polynomial iterate agrees with iteration of the
function `x ↦ f(x)`. -/
theorem reduced_iterate_eval
    {R : Type*} [CommSemiring R] (f : R[X]) (n : ℕ) (x : R) :
    (reducedLubinIterate f n).eval x =
      f.divX.eval ((fun z ↦ f.eval z)^[n] x) := by
  rw [reducedLubinIterate, Polynomial.eval_comp,
    Polynomial.iterate_comp_eval]
  simp

/-- If the `n`-fold iterate of `x` is a nonzero root of `f`, then `x` is a
root of Milne's reduced level-`n+1` polynomial. -/
theorem reduced_tate_iterate
    {R : Type*} [CommRing R] [IsDomain R]
    (f : R[X]) (hf0 : f.coeff 0 = 0) (n : ℕ) (x : R)
    (hne : (fun z ↦ f.eval z)^[n] x ≠ 0)
    (hroot : f.eval ((fun z ↦ f.eval z)^[n] x) = 0) :
    (reducedLubinIterate f n).eval x = 0 := by
  let z := (fun z ↦ f.eval z)^[n] x
  have hmul : Polynomial.X * f.divX = f := by
    simpa only [hf0, Polynomial.C_0, add_zero] using
      Polynomial.X_mul_divX_add f
  have heval := congrArg (fun p : R[X] ↦ p.eval z) hmul
  simp only [Polynomial.eval_mul, Polynomial.eval_X] at heval
  have hdiv : f.divX.eval z = 0 := by
    exact (mul_eq_zero.mp (heval.trans hroot)).resolve_left hne
  rw [reduced_iterate_eval, show (fun y ↦ f.eval y)^[n] x = z from rfl,
    hdiv]

/-- Milne's degree argument in Theorem 3.6(c): a reduced iterate that
annihilates a power-basis generator and has the full extension degree is its
minimal polynomial. -/
theorem minpoly_reduced_lubin
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (pb : PowerBasis K L) (f : K[X])
    (hf : f.Monic) (hf0 : f.coeff 0 = 0)
    (hdeg : f.natDegree ≠ 0) (n : ℕ)
    (hroot : Polynomial.aeval pb.gen (reducedLubinIterate f n) = 0)
    (hdim : pb.dim = (f.natDegree - 1) * f.natDegree ^ n) :
    minpoly K pb.gen = reducedLubinIterate f n := by
  have hmonic : (reducedLubinIterate f n).Monic :=
    reduced_iterate_monic hf hf0 hdeg n
  have hdvd : minpoly K pb.gen ∣ reducedLubinIterate f n :=
    minpoly.dvd K pb.gen hroot
  have hnatDegree : (minpoly K pb.gen).natDegree =
      (reducedLubinIterate f n).natDegree := by
    calc
      (minpoly K pb.gen).natDegree = pb.dim := pb.natDegree_minpoly
      _ = (f.natDegree - 1) * f.natDegree ^ n := hdim
      _ = (reducedLubinIterate f n).natDegree :=
        (reduced_iterate_degree f n).symm
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic pb.isIntegral_gen) hmonic hdvd hnatDegree.ge).symm

/-- Once the reduced iterate has been identified with the minimal polynomial,
the norm is its signed constant coefficient.  This is the algebraic norm
calculation in Theorem 3.6(c). -/
theorem minpoly_reduced_iterate
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (pb : PowerBasis K L) (f : K[X]) (hf0 : f.coeff 0 = 0)
    (n : ℕ)
    (hmin : minpoly K pb.gen = reducedLubinIterate f n) :
    Algebra.norm K pb.gen =
      (-1) ^ ((f.natDegree - 1) * f.natDegree ^ n) * f.coeff 1 := by
  have hdim : pb.dim = (f.natDegree - 1) * f.natDegree ^ n := by
    calc
      pb.dim = (minpoly K pb.gen).natDegree := pb.natDegree_minpoly.symm
      _ = (reducedLubinIterate f n).natDegree := by rw [hmin]
      _ = (f.natDegree - 1) * f.natDegree ^ n :=
        reduced_iterate_degree f n
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hmin, hdim,
    reduced_iterate_coeff f hf0 n]

/-- The signed norm formula in Theorem 3.6(c), derived directly from Milne's
root and degree argument rather than from an assumed minimal-polynomial
identity. -/
theorem gen_reduced_iterate
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (pb : PowerBasis K L) (f : K[X])
    (hf : f.Monic) (hf0 : f.coeff 0 = 0)
    (hdeg : f.natDegree ≠ 0) (n : ℕ)
    (hroot : Polynomial.aeval pb.gen (reducedLubinIterate f n) = 0)
    (hdim : pb.dim = (f.natDegree - 1) * f.natDegree ^ n) :
    Algebra.norm K pb.gen =
      (-1) ^ ((f.natDegree - 1) * f.natDegree ^ n) * f.coeff 1 :=
  minpoly_reduced_iterate pb f hf0 n
    (minpoly_reduced_lubin
      pb f hf hf0 hdeg n hroot hdim)

/-- The uniformizer coefficient is a norm.  Negating the generator cancels
the sign in the usual constant-coefficient norm formula in every degree, so
no parity exception is needed for this existential conclusion. -/
theorem reduced_iterate_root
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (pb : PowerBasis K L) (f : K[X])
    (hf : f.Monic) (hf0 : f.coeff 0 = 0)
    (hdeg : f.natDegree ≠ 0) (n : ℕ)
    (hroot : Polynomial.aeval pb.gen (reducedLubinIterate f n) = 0)
    (hdim : pb.dim = (f.natDegree - 1) * f.natDegree ^ n) :
    ∃ y : L, Algebra.norm K y = f.coeff 1 := by
  have hnorm := gen_reduced_iterate
    pb f hf hf0 hdeg n hroot hdim
  refine ⟨-pb.gen, ?_⟩
  rw [show -pb.gen = algebraMap K L (-1) * pb.gen by simp,
    (Algebra.norm K).map_mul, Algebra.norm_algebraMap, hnorm, pb.finrank, hdim,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- Theorem 3.6(c) in source-facing form: if a root of a reduced
Lubin--Tate level polynomial generates the ambient finite extension, then the
uniformizer is a norm from that extension. -/
theorem algebra_uniformizer_generates
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [FiniteDimensional K L]
    {pi : A} (hpi : Irreducible pi) {f : A[X]} {q : ℕ}
    (hf : f.Monic) (hq : f.natDegree = q) (hqgt : 1 < q)
    (hLT : LubinSeries pi q (f : PowerSeries A))
    (n : ℕ) (x : L)
    (hroot : Polynomial.aeval x
      ((reducedLubinIterate f n).map (algebraMap A K)) = 0)
    (hgen : IntermediateField.adjoin K {x} = ⊤) :
    ∃ y : L, Algebra.norm K y = algebraMap A K pi := by
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hgenAlg : Algebra.adjoin K ({x} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic x), hgen]
    rfl
  let pb : PowerBasis K L := PowerBasis.ofAdjoinEqTop hx hgenAlg
  have hpgen : pb.gen = x := PowerBasis.ofAdjoinEqTop_gen hx hgenAlg
  have hf0 : f.coeff 0 = 0 := by
    simpa using hLT.1
  have hf1 : f.coeff 1 = pi := by
    simpa using hLT.2.1
  have hroot' : Polynomial.aeval pb.gen
      (reducedLubinIterate (f.map (algebraMap A K)) n) = 0 := by
    rw [hpgen, ← lubin_tate_iterate]
    exact hroot
  have hrootDegree :=
    reduced_lubin_iterate
      hpi hf hq hqgt hLT n x hroot
  have hfinrank : Module.finrank K L = (q - 1) * q ^ n := by
    calc
      Module.finrank K L =
          Module.finrank K (⊤ : IntermediateField K L) :=
        IntermediateField.finrank_top'.symm
      _ = Module.finrank K (IntermediateField.adjoin K {x}) := by
        rw [hgen]
      _ = (q - 1) * q ^ n := hrootDegree
  have hdim : pb.dim =
      ((f.map (algebraMap A K)).natDegree - 1) *
        (f.map (algebraMap A K)).natDegree ^ n := by
    rw [← pb.finrank, hf.natDegree_map, hq, hfinrank]
  simpa only [Polynomial.coeff_map, hf1] using
    reduced_iterate_root
      pb (f.map (algebraMap A K)) (hf.map _) (by simp [hf0])
      (by rw [hf.natDegree_map, hq]; omega) n hroot' hdim

end

end Towers.CField.LTate
