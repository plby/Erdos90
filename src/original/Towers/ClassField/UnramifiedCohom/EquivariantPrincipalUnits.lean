import Mathlib.Algebra.Group.Action.Units
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Unramified.LocalRing
import Towers.ClassField.UnramifiedCohom.EquivariantUnits
import Towers.ClassField.UnramifiedCohom.PrincipalUnits

/-!
# Milne, Class Field Theory, Lemma III.1.3: equivariant principal units

The canonical `u ↦ u - 1` isomorphism from successive principal units to
the corresponding successive ideal quotient is equivariant for every action
on the local ring by ring automorphisms.
-/

namespace Towers.CField.UCohom

open IsLocalRing

noncomputable section

universe u v

variable (G : Type u) [Group G]
variable (R : Type v) [CommRing R] [IsLocalRing R] [MulSemiringAction G R]

local instance : MulDistribMulAction G Rˣ :=
  Units.mulDistribMulActionRight

private abbrev principalUnits (m : ℕ) : Subgroup Rˣ :=
  Edmonton.idealUnitSubgroup (maximalIdeal R) m

/-- The action on a local ring restricts to every principal-unit subgroup. -/
@[implicit_reducible]
private noncomputable def principalDistribAction (m : ℕ) :
    MulDistribMulAction G (principalUnits R m) where
  smul g x := ⟨g • x.1, by
    change ((g • x.1 : Rˣ) : R) - 1 ∈ maximalIdeal R ^ m
    have hx := smul_maximal_pow G R g m x.2
    simpa only [Units.coe_smul, smul_sub, smul_one] using hx⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)
  smul_mul g x y := Subtype.ext (smul_mul' g x.1 y.1)
  smul_one g := Subtype.ext (smul_one g)

/-- The action on the `m`th principal units descends modulo the `(m+1)`st
principal units. -/
@[implicit_reducible]
private noncomputable def successivePrincipalAction (m : ℕ) :
    letI : MulDistribMulAction G (principalUnits R m) :=
      principalDistribAction G R m
    MulAction.QuotientAction G
      ((principalUnits R (m + 1)).subgroupOf (principalUnits R m)) := by
  letI : MulDistribMulAction G (principalUnits R m) :=
    principalDistribAction G R m
  refine ⟨?_⟩
  intro g x y hxy
  have hxy' : ((x⁻¹ * y : principalUnits R m) : Rˣ) ∈
      principalUnits R (m + 1) := hxy
  have hsD : g • (x⁻¹ * y) ∈
      (principalUnits R (m + 1)).subgroupOf (principalUnits R m) := by
    change (((g • ((x⁻¹ * y : principalUnits R m) : Rˣ)) : Rˣ) : R) - 1 ∈
      maximalIdeal R ^ (m + 1)
    have hs := smul_maximal_pow G R g (m + 1) hxy'
    simpa only [Units.coe_smul, smul_sub, smul_one] using hs
  simpa only [smul_mul', smul_inv'] using hsD

/-- The descended action acts by group automorphisms. -/
@[implicit_reducible]
private noncomputable def successivePrincipalDistrib (m : ℕ) :
    letI : MulDistribMulAction G (principalUnits R m) :=
      principalDistribAction G R m
    letI : MulAction.QuotientAction G
        ((principalUnits R (m + 1)).subgroupOf (principalUnits R m)) :=
      successivePrincipalAction G R m
    MulDistribMulAction G
      (principalUnits R m ⧸
        (principalUnits R (m + 1)).subgroupOf (principalUnits R m)) := by
  letI : MulDistribMulAction G (principalUnits R m) :=
    principalDistribAction G R m
  letI : MulAction.QuotientAction G
      ((principalUnits R (m + 1)).subgroupOf (principalUnits R m)) :=
    successivePrincipalAction G R m
  letI : MulAction G
      (principalUnits R m ⧸
        (principalUnits R (m + 1)).subgroupOf (principalUnits R m)) := inferInstance
  exact
    { smul_mul := by
        intro g x y
        induction x using QuotientGroup.induction_on with
        | _ x =>
          induction y using QuotientGroup.induction_on with
          | _ y => simp only [← QuotientGroup.mk_mul,
              MulAction.Quotient.smul_mk, smul_mul']
      smul_one := by
        intro g
        rw [← QuotientGroup.mk_one, MulAction.Quotient.smul_mk, smul_one] }

/-- The action on the ring restricts to a semilinear additive action on an
ideal power, viewed only as an additive group. -/
@[implicit_reducible]
private noncomputable def idealDistribAction (m : ℕ) :
    DistribMulAction G (maximalIdeal R ^ m : Ideal R) where
  smul g x := ⟨g • (x : R), smul_maximal_pow G R g m x.2⟩
  one_smul x := Subtype.ext (one_smul G (x : R))
  mul_smul g h x := Subtype.ext (mul_smul g h (x : R))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g x y := Subtype.ext (smul_add g (x : R) (y : R))

/-- The semilinear action on `𝔪^m` descends to the additive quotient
`𝔪^m / 𝔪^(m+1)`. -/
@[implicit_reducible]
private noncomputable def successiveDistribAction (m : ℕ) :
    letI : DistribMulAction G (maximalIdeal R ^ m : Ideal R) :=
      idealDistribAction G R m
    DistribMulAction G
      (IdealSuccessiveQuotient R (maximalIdeal R) m) := by
  letI : DistribMulAction G (maximalIdeal R ^ m : Ideal R) :=
    idealDistribAction G R m
  let P := idealSuccessiveDenominator R (maximalIdeal R) m
  let smulQ : G → IdealSuccessiveQuotient R (maximalIdeal R) m →
      IdealSuccessiveQuotient R (maximalIdeal R) m :=
    fun g q ↦ Quotient.map' (g • ·) (by
      intro x y hxy
      apply (Submodule.quotientRel_def (p := P)).2
      rw [← smul_sub]
      change g • ((x : R) - (y : R)) ∈ maximalIdeal R ^ (m + 1)
      apply smul_maximal_pow G R g (m + 1)
      exact (Submodule.quotientRel_def (p := P)).1 hxy) q
  exact
    { smul := smulQ
      one_smul := by
        intro q
        induction q using Submodule.Quotient.induction_on with
        | _ x =>
          exact congrArg (fun z : (maximalIdeal R ^ m : Ideal R) ↦
            Submodule.Quotient.mk z) (Subtype.ext (one_smul G (x : R)))
      mul_smul := by
        intro g h q
        induction q using Submodule.Quotient.induction_on with
        | _ x =>
          exact congrArg (fun z : (maximalIdeal R ^ m : Ideal R) ↦
            Submodule.Quotient.mk z) (Subtype.ext (mul_smul g h (x : R)))
      smul_zero := by
        intro g
        exact congrArg (fun z : (maximalIdeal R ^ m : Ideal R) ↦
          Submodule.Quotient.mk z) (Subtype.ext (smul_zero g))
      smul_add := by
        intro g x y
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          induction y using Submodule.Quotient.induction_on with
          | _ y =>
            exact congrArg (fun z : (maximalIdeal R ^ m : Ideal R) ↦
              Submodule.Quotient.mk z)
                (Subtype.ext (smul_add g (x : R) (y : R))) }

/-- Multiplicative notation transports the additive action on a successive
ideal quotient to an action by group automorphisms. -/
@[implicit_reducible]
private noncomputable def multiplicativeSuccessiveDistrib (m : ℕ) :
    letI : DistribMulAction G (maximalIdeal R ^ m : Ideal R) :=
      idealDistribAction G R m
    letI : DistribMulAction G
        (IdealSuccessiveQuotient R (maximalIdeal R) m) :=
      successiveDistribAction G R m
    MulDistribMulAction G
      (Multiplicative (IdealSuccessiveQuotient R (maximalIdeal R) m)) := by
  letI : DistribMulAction G (maximalIdeal R ^ m : Ideal R) :=
    idealDistribAction G R m
  letI : DistribMulAction G
      (IdealSuccessiveQuotient R (maximalIdeal R) m) :=
    successiveDistribAction G R m
  exact
    { smul := fun g x ↦ Multiplicative.ofAdd (g • x.toAdd)
      one_smul := fun x ↦ Multiplicative.toAdd.injective (one_smul G x.toAdd)
      mul_smul := fun g h x ↦
        Multiplicative.toAdd.injective (mul_smul g h x.toAdd)
      smul_one := fun g ↦ Multiplicative.toAdd.injective (smul_zero g)
      smul_mul := fun g x y ↦
        Multiplicative.toAdd.injective (smul_add g x.toAdd y.toAdd) }

/-- The explicit trivialization of a successive ideal quotient determined
by a chosen generator `π` of the maximal ideal.  In contrast with the
choice-based general equivalence in `Lemma13PrincipalUnits`, this version
remembers the generator, which is essential for equivariance. -/
private noncomputable def residueSuccessiveData [IsDomain R]
    (π : R) (hπ : maximalIdeal R = Ideal.span {π}) (hπ0 : π ≠ 0) (m : ℕ) :
    { e : ResidueField R ≃ₗ[R]
        IdealSuccessiveQuotient R (maximalIdeal R) m //
      ∀ a : R, e (residue R a) =
        Submodule.Quotient.mk
          (show (maximalIdeal R ^ m : Ideal R) from
            ⟨a * π ^ m, by
              rw [hπ]
              exact Ideal.mul_mem_left _ a
                (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) m)⟩) } := by
  let I := maximalIdeal R
  let P := idealSuccessiveDenominator R I m
  let Q : Submodule R (I ^ m : Ideal R) := I • ⊤
  let f : (I ^ m : Ideal R) →ₗ[R] (I ^ m : Ideal R) ⧸ Q :=
    Submodule.mkQ Q
  have hπm : π ^ m ∈ I ^ m := by
    change π ^ m ∈ maximalIdeal R ^ m
    rw [hπ]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) m
  let g : R →ₗ[R] (I ^ m : Ideal R) :=
    (LinearMap.mulRight R π ^ m).codRestrict _ fun x ↦ by
      simpa only [LinearMap.pow_mulRight, LinearMap.mulRight_apply] using
        Ideal.mul_mem_left (I ^ m) x hπm
  have hker : I = LinearMap.ker (f.comp g) := by
    ext x
    simp only [LinearMap.codRestrict, LinearMap.pow_mulRight,
      LinearMap.mulRight_apply, LinearMap.mem_ker, LinearMap.coe_comp,
      LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_top_iff, smul_eq_mul, f, g, Q]
    constructor
    · intro hx
      exact Submodule.mul_mem_mul hx hπm
    · intro hx
      rw [← pow_succ'] at hx
      change x * π ^ m ∈ maximalIdeal R ^ (m + 1) at hx
      change x ∈ maximalIdeal R
      rw [hπ, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at hx
      obtain ⟨y, hy⟩ := hx
      rw [mul_comm, pow_succ, mul_assoc,
        mul_right_inj' (pow_ne_zero m hπ0)] at hy
      rw [hπ, Ideal.mem_span_singleton]
      exact ⟨y, hy⟩
  let e₀ : (R ⧸ I) ≃ₗ[R] R ⧸ LinearMap.ker (f.comp g) :=
    Submodule.quotEquivOfEq I (LinearMap.ker (f.comp g)) hker
  have hsurj : Function.Surjective (f.comp g) := by
    refine (Submodule.mkQ_surjective Q).comp ?_
    rintro ⟨x, hx⟩
    change x ∈ maximalIdeal R ^ m at hx
    rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨y, rfl⟩ := hx
    refine ⟨y, ?_⟩
    simp [g, LinearMap.codRestrict, mul_comm]
  let e₁ : (R ⧸ I) ≃ₗ[R] ((I ^ m : Ideal R) ⧸ Q) :=
    e₀.trans ((f.comp g).quotKerEquivOfSurjective hsurj)
  let eP :
      ((I ^ m : Ideal R) ⧸ P) ≃ₗ[R] ((I ^ m : Ideal R) ⧸ Q) :=
    Submodule.quotEquivOfEq P Q
      (successive_denominator_top R I m)
  refine ⟨e₁.trans eP.symm, ?_⟩
  intro a
  apply eP.injective
  change eP (eP.symm (e₁ (residue R a))) = _
  rw [LinearEquiv.apply_symm_apply]
  dsimp only [e₁]
  change (f.comp g).quotKerEquivOfSurjective hsurj
      (Submodule.Quotient.mk a) = _
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
  change f (g a) = eP (Submodule.Quotient.mk _)
  rw [Submodule.quotEquivOfEq_mk]
  dsimp only [f, Submodule.mkQ_apply]
  apply congrArg (fun z : (I ^ m : Ideal R) ↦
    (Submodule.Quotient.mk z : (I ^ m : Ideal R) ⧸ Q))
  apply Subtype.ext
  dsimp only [g, LinearMap.codRestrict_apply]
  rw [LinearMap.pow_mulRight, LinearMap.mulRight_apply]

/-- The explicit trivialization of a successive ideal quotient determined
by a chosen generator of the maximal ideal. -/
noncomputable def residueSuccessiveGenerator [IsDomain R]
    (π : R) (hπ : maximalIdeal R = Ideal.span {π}) (hπ0 : π ≠ 0) (m : ℕ) :
    ResidueField R ≃ₗ[R]
      IdealSuccessiveQuotient R (maximalIdeal R) m :=
  (residueSuccessiveData R π hπ hπ0 m).1

/-- On a residue class, the explicit generator-dependent equivalence is
multiplication by `π^m`. -/
@[simp]
theorem residue_successive_generator
    [IsDomain R] (π : R) (hπ : maximalIdeal R = Ideal.span {π})
    (hπ0 : π ≠ 0) (m : ℕ) (a : R) :
    residueSuccessiveGenerator R π hπ hπ0 m
        (residue R a) =
      Submodule.Quotient.mk
        (show (maximalIdeal R ^ m : Ideal R) from
          ⟨a * π ^ m, by
            rw [hπ]
            exact Ideal.mul_mem_left _ a
              (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) m)⟩) := by
  exact (residueSuccessiveData
    R π hπ hπ0 m).2 a

/-- If the chosen generator of the maximal ideal is fixed by `G`, the
explicit trivialization of every successive ideal quotient is equivariant. -/
theorem residue_successive_equivariant
    [IsDomain R] (π : R) (hπ : maximalIdeal R = Ideal.span {π})
    (hπ0 : π ≠ 0) (hfix : ∀ g : G, g • π = π) (m : ℕ)
    (g : G) (x : ResidueField R) :
    letI : DistribMulAction G (maximalIdeal R ^ m : Ideal R) :=
      idealDistribAction G R m
    letI : DistribMulAction G
        (IdealSuccessiveQuotient R (maximalIdeal R) m) :=
      successiveDistribAction G R m
    residueSuccessiveGenerator R π hπ hπ0 m (g • x) =
      g • residueSuccessiveGenerator R π hπ hπ0 m x := by
  letI : DistribMulAction G (maximalIdeal R ^ m : Ideal R) :=
    idealDistribAction G R m
  letI : DistribMulAction G
      (IdealSuccessiveQuotient R (maximalIdeal R) m) :=
    successiveDistribAction G R m
  obtain ⟨a, rfl⟩ := residue_surjective x
  rw [← IsLocalRing.ResidueField.residue_smul G,
    residue_successive_generator,
    residue_successive_generator]
  change Submodule.Quotient.mk _ = g • Submodule.Quotient.mk _
  dsimp only [successiveDistribAction]
  apply congrArg (fun z : (maximalIdeal R ^ m : Ideal R) ↦
    (Submodule.Quotient.mk z :
      IdealSuccessiveQuotient R (maximalIdeal R) m))
  apply Subtype.ext
  change (g • a) * π ^ m = g • (a * π ^ m)
  rw [smul_mul', smul_pow', hfix]

/-- A fixed generator identifies the multiplicative form of the successive
ideal quotient with the additive residue field as integral `G`-modules. -/
noncomputable def successiveGModule [IsDomain R]
    (π : R) (hπ : maximalIdeal R = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hfix : ∀ g : G, g • π = π) (m : ℕ) :
    letI : DistribMulAction G (maximalIdeal R ^ m : Ideal R) :=
      idealDistribAction G R m
    letI : DistribMulAction G
        (IdealSuccessiveQuotient R (maximalIdeal R) m) :=
      successiveDistribAction G R m
    letI : MulDistribMulAction G
        (Multiplicative (IdealSuccessiveQuotient R (maximalIdeal R) m)) :=
      multiplicativeSuccessiveDistrib G R m
    Rep.ofMulDistribMulAction G
        (Multiplicative (IdealSuccessiveQuotient R (maximalIdeal R) m)) ≅
      Rep.ofDistribMulAction ℤ G (ResidueField R) := by
  letI : DistribMulAction G (maximalIdeal R ^ m : Ideal R) :=
    idealDistribAction G R m
  letI : DistribMulAction G
      (IdealSuccessiveQuotient R (maximalIdeal R) m) :=
    successiveDistribAction G R m
  letI : MulDistribMulAction G
      (Multiplicative (IdealSuccessiveQuotient R (maximalIdeal R) m)) :=
    multiplicativeSuccessiveDistrib G R m
  let e := residueSuccessiveGenerator R π hπ hπ0 m
  let eAdd :
      Additive (Multiplicative
        (IdealSuccessiveQuotient R (maximalIdeal R) m)) ≃+
        ResidueField R :=
    (AddEquiv.additiveMultiplicative _).trans e.symm.toAddEquiv
  let eRep :
      (Rep.ofMulDistribMulAction G
        (Multiplicative
          (IdealSuccessiveQuotient R (maximalIdeal R) m))).ρ.Equiv
      (Rep.ofDistribMulAction ℤ G (ResidueField R)).ρ :=
    Representation.Equiv.mk eAdd.toIntLinearEquiv (by
      intro (g : G)
      apply LinearMap.ext
      rintro (q : Additive (Multiplicative
        (IdealSuccessiveQuotient R (maximalIdeal R) m)))
      change e.symm (g • q.toMul.toAdd) = g • e.symm q.toMul.toAdd
      apply e.injective
      rw [e.apply_symm_apply,
        residue_successive_equivariant,
        e.apply_symm_apply]
      all_goals assumption)
  exact Rep.mkIso eRep

/-- **Lemma III.1.3, canonical equivariant second isomorphism.** For `m>0`,
the map induced by `u ↦ u-1` identifies successive principal units with
`𝔪^m/𝔪^(m+1)` as integral `G`-representations. -/
noncomputable def principalSuccessiveG (m : ℕ) (hm : 0 < m) :
    letI : MulDistribMulAction G (principalUnits R m) :=
      principalDistribAction G R m
    letI : MulAction.QuotientAction G
        ((principalUnits R (m + 1)).subgroupOf (principalUnits R m)) :=
      successivePrincipalAction G R m
    letI : MulDistribMulAction G
        (principalUnits R m ⧸
          (principalUnits R (m + 1)).subgroupOf (principalUnits R m)) :=
      successivePrincipalDistrib G R m
    letI : DistribMulAction G (maximalIdeal R ^ m : Ideal R) :=
      idealDistribAction G R m
    letI : DistribMulAction G
        (IdealSuccessiveQuotient R (maximalIdeal R) m) :=
      successiveDistribAction G R m
    letI : MulDistribMulAction G
        (Multiplicative (IdealSuccessiveQuotient R (maximalIdeal R) m)) :=
      multiplicativeSuccessiveDistrib G R m
    Rep.ofMulDistribMulAction G
        (principalUnits R m ⧸
          (principalUnits R (m + 1)).subgroupOf (principalUnits R m)) ≅
      Rep.ofMulDistribMulAction G
        (Multiplicative (IdealSuccessiveQuotient R (maximalIdeal R) m)) := by
  letI : MulDistribMulAction G (principalUnits R m) :=
    principalDistribAction G R m
  letI : MulAction.QuotientAction G
      ((principalUnits R (m + 1)).subgroupOf (principalUnits R m)) :=
    successivePrincipalAction G R m
  letI : MulDistribMulAction G
      (principalUnits R m ⧸
        (principalUnits R (m + 1)).subgroupOf (principalUnits R m)) :=
    successivePrincipalDistrib G R m
  letI : DistribMulAction G (maximalIdeal R ^ m : Ideal R) :=
    idealDistribAction G R m
  letI : DistribMulAction G
      (IdealSuccessiveQuotient R (maximalIdeal R) m) :=
    successiveDistribAction G R m
  letI : MulDistribMulAction G
      (Multiplicative (IdealSuccessiveQuotient R (maximalIdeal R) m)) :=
    multiplicativeSuccessiveDistrib G R m
  let e := principalSuccessiveEquiv R m hm
  let eRep :
      (Rep.ofMulDistribMulAction G
        (principalUnits R m ⧸
          (principalUnits R (m + 1)).subgroupOf (principalUnits R m))).ρ.Equiv
      (Rep.ofMulDistribMulAction G
        (Multiplicative
          (IdealSuccessiveQuotient R (maximalIdeal R) m))).ρ :=
    Representation.Equiv.mk e.toAdditive.toIntLinearEquiv (by
    intro (g : G)
    apply LinearMap.ext
    rintro (q : Additive
      (principalUnits R m ⧸
        (principalUnits R (m + 1)).subgroupOf (principalUnits R m)))
    apply Additive.toMul.injective
    change e (g • q.toMul) = g • e q.toMul
    induction q.toMul using QuotientGroup.induction_on with
    | _ u =>
      rw [MulAction.Quotient.smul_mk]
      dsimp only [e]
      rw [principal_successive_mk,
        principal_successive_mk]
      dsimp only [multiplicativeSuccessiveDistrib]
      apply Multiplicative.toAdd.injective
      change (Submodule.Quotient.mk
          (show (maximalIdeal R ^ m : Ideal R) from
            ⟨(((g • u).1 : Rˣ) : R) - 1, (g • u).2⟩) :
          IdealSuccessiveQuotient R (maximalIdeal R) m) =
        g • (Submodule.Quotient.mk
          (show (maximalIdeal R ^ m : Ideal R) from
            ⟨((u.1 : Rˣ) : R) - 1, u.2⟩) :
          IdealSuccessiveQuotient R (maximalIdeal R) m)
      dsimp only [successiveDistribAction]
      apply congrArg (fun z : (maximalIdeal R ^ m : Ideal R) ↦
        (Submodule.Quotient.mk z :
          IdealSuccessiveQuotient R (maximalIdeal R) m))
      apply Subtype.ext
      dsimp only [principalDistribAction, idealDistribAction]
      change g • (((u.1 : Rˣ) : R)) - 1 =
        g • ((((u.1 : Rˣ) : R)) - 1)
      rw [smul_sub, smul_one])
  exact Rep.mkIso eRep

/-- **Lemma III.1.3, second displayed isomorphism with an explicit fixed
uniformizer.** Successive principal units are the additive residue field as
integral `G`-modules. -/
noncomputable def successiveGIso
    [IsDomain R] (π : R) (hπ : maximalIdeal R = Ideal.span {π})
    (hπ0 : π ≠ 0) (hfix : ∀ g : G, g • π = π)
    (m : ℕ) (hm : 0 < m) :
    letI : MulDistribMulAction G (principalUnits R m) :=
      principalDistribAction G R m
    letI : MulAction.QuotientAction G
        ((principalUnits R (m + 1)).subgroupOf (principalUnits R m)) :=
      successivePrincipalAction G R m
    letI : MulDistribMulAction G
        (principalUnits R m ⧸
          (principalUnits R (m + 1)).subgroupOf (principalUnits R m)) :=
      successivePrincipalDistrib G R m
    Rep.ofMulDistribMulAction G
        (principalUnits R m ⧸
          (principalUnits R (m + 1)).subgroupOf (principalUnits R m)) ≅
      Rep.ofDistribMulAction ℤ G (ResidueField R) := by
  letI : MulDistribMulAction G (principalUnits R m) :=
    principalDistribAction G R m
  letI : MulAction.QuotientAction G
      ((principalUnits R (m + 1)).subgroupOf (principalUnits R m)) :=
    successivePrincipalAction G R m
  letI : MulDistribMulAction G
      (principalUnits R m ⧸
        (principalUnits R (m + 1)).subgroupOf (principalUnits R m)) :=
    successivePrincipalDistrib G R m
  exact (principalSuccessiveG G R m hm).trans
    (successiveGModule G R π hπ hπ0 hfix m)

/-- **Lemma III.1.3, second displayed isomorphism for an unramified finite
Galois extension of discrete valuation rings.** No uniformizer occurs in the
statement: one is chosen in the base DVR, and formal unramifiedness says its
image generates the upstairs maximal ideal.  The Galois group fixes that
image because it comes from the base. -/
noncomputable def successiveGUnramified
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsDomain R]
    [Algebra A R] [IsLocalHom (algebraMap A R)]
    [Module.Finite A R] [Module.IsTorsionFree A R]
    [Algebra.FormallyUnramified A R] [IsGaloisGroup G A R]
    (m : ℕ) (hm : 0 < m) :
    letI : MulDistribMulAction G (principalUnits R m) :=
      principalDistribAction G R m
    letI : MulAction.QuotientAction G
        ((principalUnits R (m + 1)).subgroupOf (principalUnits R m)) :=
      successivePrincipalAction G R m
    letI : MulDistribMulAction G
        (principalUnits R m ⧸
          (principalUnits R (m + 1)).subgroupOf (principalUnits R m)) :=
      successivePrincipalDistrib G R m
    Rep.ofMulDistribMulAction G
        (principalUnits R m ⧸
          (principalUnits R (m + 1)).subgroupOf (principalUnits R m)) ≅
      Rep.ofDistribMulAction ℤ G (ResidueField R) := by
  let πA : A := (IsDiscreteValuationRing.exists_irreducible A).choose
  have hπA : Irreducible πA :=
    (IsDiscreteValuationRing.exists_irreducible A).choose_spec
  let π : R := algebraMap A R πA
  have hπ : maximalIdeal R = Ideal.span {π} := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A) (S := R),
      hπA.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hπ0 : π ≠ 0 := by
    simpa only [π, map_zero] using
      (FaithfulSMul.algebraMap_injective A R).ne hπA.ne_zero
  have hfix : ∀ g : G, g • π = π := by
    intro g
    exact smul_algebraMap g πA
  exact successiveGIso
    G R π hπ hπ0 hfix m hm

end

end Towers.CField.UCohom
