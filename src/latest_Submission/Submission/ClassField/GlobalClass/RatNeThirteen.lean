import Submission.NumberTheory.Galois.PlaceCompletionDegree
import Submission.NumberTheory.Completions.UnramifiedCompletion
import Submission.NumberTheory.Galois.GaloisOrbitFactorization
import Submission.NumberTheory.Quadratic.IntegralElements
import Submission.ClassField.GlobalClass.LocalDegreeLCM

/-!
# Chapter VIII, Section 4, Example 4.5

This file uses the nested coordinate model

`Q(sqrt 13, sqrt 17) = Q(sqrt 13)[sqrt 17]`.

The global algebra and group theory are proved here.  The elementary local
arithmetic in Milne's example (quadratic residues and Hensel lifting at
`13` and `17`, together with the unramified calculation elsewhere) is kept
as an explicit input structure.  From that input we derive the assertion
that every finite completion has degree one or two.
-/

namespace Submission.CField.GClass

open AbsoluteValue IsDedekindDomain NumberField Polynomial
open Submission.NumberTheory
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo

noncomputable section

attribute [-instance] DivisionRing.toRatAlgebra

/-- The concrete nested-coordinate model of `Q(sqrt 13, sqrt 17)`. -/
abbrev Field :=
  QuadraticAlgebra (QFModel 13)
    (17 : QFModel 13) 0

private theorem rat_sq_thirteen (q : ℚ) : q ^ 2 ≠ 13 := by
  intro h
  have hsquare : IsSquare (13 : ℚ) := ⟨q, by simpa [pow_two] using h.symm⟩
  norm_num at hsquare

private theorem rat_sq_seventeen (q : ℚ) : q ^ 2 ≠ 17 := by
  intro h
  have hsquare : IsSquare (17 : ℚ) := ⟨q, by simpa [pow_two] using h.symm⟩
  norm_num at hsquare

private theorem thirteen_sq_seventeen (q : ℚ) :
    13 * q ^ 2 ≠ 17 := by
  intro h
  have hsquare : IsSquare (17 / 13 : ℚ) := ⟨q, by
    field_simp
    nlinarith⟩
  norm_num at hsquare

local instance sqrtThirteen_irreducible :
    Fact (∀ r : ℚ, r ^ 2 ≠ (13 : ℚ) + 0 * r) :=
  ⟨fun r hr ↦ rat_sq_thirteen r (by simpa using hr)⟩

private theorem no_seventeen_thirteen
    (r : QFModel 13) : r ^ 2 ≠ 17 := by
  intro hr
  have hre := congrArg QuadraticAlgebra.re hr
  have him := congrArg QuadraticAlgebra.im hr
  norm_num [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] at hre him
  have hprod : r.re * r.im = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with hre0 | him0
  · rw [hre0] at hre
    exact thirteen_sq_seventeen r.im (by
      norm_num [pow_two, mul_assoc] at hre ⊢
      exact hre)
  · rw [him0] at hre
    exact rat_sq_seventeen r.re (by simpa [pow_two] using hre)

local instance biquadratic_irreducible :
    Fact (∀ r : QFModel 13,
      r ^ 2 ≠ (17 : QFModel 13) + 0 * r) :=
  ⟨fun r hr ↦ no_seventeen_thirteen r (by simpa using hr)⟩

local instance sqrtThirteen_moduleFinite :
    Module.Finite ℚ (QFModel 13) :=
  Module.Finite.of_basis (QuadraticAlgebra.basis (13 : ℚ) 0)

local instance relative_moduleFinite :
    Module.Finite (QFModel 13) Field :=
  Module.Finite.of_basis
    (QuadraticAlgebra.basis (17 : QFModel 13) 0)

local instance moduleFinite : Module.Finite ℚ Field :=
  Module.Finite.trans (QFModel 13) Field

local instance numberField : NumberField Field :=
  NumberField.of_module_finite ℚ Field

/-- The element `sqrt 13` in the nested-coordinate model. -/
def sqrtThirteen : Field :=
  ⟨⟨0, 1⟩, 0⟩

/-- The element `sqrt 17` in the nested-coordinate model. -/
def sqrtSeventeen : Field :=
  ⟨0, 1⟩

/-- Change the sign of `sqrt 13` and leave `sqrt 17` fixed. -/
def innerFlip : Field ≃ₐ[ℚ] Field where
  toFun z := ⟨star z.re, star z.im⟩
  invFun z := ⟨star z.re, star z.im⟩
  left_inv z := by apply QuadraticAlgebra.ext <;> simp
  right_inv z := by apply QuadraticAlgebra.ext <;> simp
  map_mul' x y := by
    apply QuadraticAlgebra.ext <;>
      simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  map_add' x y := by apply QuadraticAlgebra.ext <;> simp
  commutes' q := by
    apply QuadraticAlgebra.ext
    · change star (algebraMap ℚ (QFModel 13) q) =
        algebraMap ℚ (QFModel 13) q
      apply QuadraticAlgebra.ext <;> simp
    · change star (0 : QFModel 13) = 0
      exact star_zero _

/-- Change the sign of `sqrt 17` and leave `sqrt 13` fixed. -/
def outerFlip : Field ≃ₐ[ℚ] Field where
  toFun z := star z
  invFun z := star z
  left_inv := star_involutive
  right_inv := star_involutive
  map_mul' x y := by rw [star_mul, mul_comm]
  map_add' := star_add
  commutes' q := by apply QuadraticAlgebra.ext <;> simp

/-- The four independent choices of signs of the two square roots. -/
def signAutomorphism : Bool × Bool → Gal(Field/ℚ)
  | (false, false) => AlgEquiv.refl
  | (true, false) => innerFlip
  | (false, true) => outerFlip
  | (true, true) => innerFlip.trans outerFlip

private theorem sign_thirteen_probe (s₁ s₂ : Bool) :
    (signAutomorphism (s₁, s₂) sqrtThirteen).re.im =
      if s₁ then -1 else 1 := by
  cases s₁ <;> cases s₂ <;>
    norm_num [signAutomorphism, innerFlip, outerFlip,
      sqrtThirteen, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

private theorem sign_seventeen_probe (s₁ s₂ : Bool) :
    (signAutomorphism (s₁, s₂) sqrtSeventeen).im.re =
      if s₂ then -1 else 1 := by
  cases s₁ <;> cases s₂ <;>
    norm_num [signAutomorphism, innerFlip, outerFlip,
      sqrtSeventeen, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem signAutomorphism_injective :
    Function.Injective signAutomorphism := by
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  have h₁₃ : (if a₁ then (-1 : ℚ) else 1) = if b₁ then -1 else 1 := by
    rw [← sign_thirteen_probe,
      ← sign_thirteen_probe]
    exact congrArg
      (fun f : Gal(Field/ℚ) ↦ (f sqrtThirteen).re.im) h
  have h₁₇ : (if a₂ then (-1 : ℚ) else 1) = if b₂ then -1 else 1 := by
    rw [← sign_seventeen_probe,
      ← sign_seventeen_probe]
    exact congrArg
      (fun f : Gal(Field/ℚ) ↦ (f sqrtSeventeen).im.re) h
  have ha₁ : a₁ = b₁ := by
    cases a₁ <;> cases b₁
    · rfl
    · norm_num at h₁₃
    · norm_num at h₁₃
    · rfl
  have ha₂ : a₂ = b₂ := by
    cases a₂ <;> cases b₂
    · rfl
    · norm_num at h₁₇
    · norm_num at h₁₇
    · rfl
  exact Prod.ext ha₁ ha₂

theorem finrank : Module.finrank ℚ Field = 4 := by
  calc
    Module.finrank ℚ Field =
        Module.finrank ℚ (QFModel 13) *
          Module.finrank (QFModel 13) Field :=
      (Module.finrank_mul_finrank ℚ (QFModel 13) Field).symm
    _ = 2 * 2 := by
      rw [QuadraticAlgebra.finrank_eq_two, QuadraticAlgebra.finrank_eq_two]
    _ = 4 := by norm_num

/-- The four sign changes exhaust the global automorphism group. -/
theorem galoisGroup_card : Nat.card Gal(Field/ℚ) = 4 := by
  rw [Nat.card_eq_fintype_card]
  apply Nat.le_antisymm
  · simpa [finrank] using
      (AlgEquiv.card_le (F := ℚ) (K := Field))
  · have h := Fintype.card_le_of_injective signAutomorphism
        signAutomorphism_injective
    norm_num at h ⊢
    exact h

private theorem signAutomorphism_surjective :
    Function.Surjective signAutomorphism := by
  have hcard : Fintype.card (Bool × Bool) =
      Fintype.card Gal(Field/ℚ) := by
    calc
      Fintype.card (Bool × Bool) = 4 := by
        simp [Fintype.card_prod, Fintype.card_bool]
      _ = Fintype.card Gal(Field/ℚ) := by
        rw [← Nat.card_eq_fintype_card, galoisGroup_card]
  exact ((Fintype.bijective_iff_injective_and_card signAutomorphism).2
    ⟨signAutomorphism_injective, hcard⟩).2

local instance isGalois : IsGalois ℚ Field :=
  IsGalois.of_card_aut_eq_finrank ℚ Field <| by
    rw [galoisGroup_card, finrank]

/-- A primitive element used to control the completed factors. -/
def primitiveElement : Field :=
  sqrtThirteen + sqrtSeventeen

private theorem automorphism_thirteen_probe
    (s₁ s₂ : Bool) :
    (signAutomorphism (s₁, s₂) primitiveElement).re.im =
      if s₁ then -1 else 1 := by
  cases s₁ <;> cases s₂ <;>
    norm_num [primitiveElement, signAutomorphism,
      innerFlip, outerFlip, sqrtThirteen,
      sqrtSeventeen, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star]

private theorem automorphism_seventeen_probe
    (s₁ s₂ : Bool) :
    (signAutomorphism (s₁, s₂) primitiveElement).im.re =
      if s₂ then -1 else 1 := by
  cases s₁ <;> cases s₂ <;>
    norm_num [primitiveElement, signAutomorphism,
      innerFlip, outerFlip, sqrtThirteen,
      sqrtSeventeen, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one]

private theorem sign_automorphism_primitive :
    Function.Injective
      (fun s : Bool × Bool ↦
        signAutomorphism s primitiveElement) := by
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  have h₁₃ : (if a₁ then (-1 : ℚ) else 1) = if b₁ then -1 else 1 := by
    rw [← automorphism_thirteen_probe,
      ← automorphism_thirteen_probe]
    exact congrArg (fun z : Field ↦ z.re.im) h
  have h₁₇ : (if a₂ then (-1 : ℚ) else 1) = if b₂ then -1 else 1 := by
    rw [← automorphism_seventeen_probe,
      ← automorphism_seventeen_probe]
    exact congrArg (fun z : Field ↦ z.im.re) h
  have ha₁ : a₁ = b₁ := by
    cases a₁ <;> cases b₁
    · rfl
    · norm_num at h₁₃
    · norm_num at h₁₃
    · rfl
  have ha₂ : a₂ = b₂ := by
    cases a₂ <;> cases b₂
    · rfl
    · norm_num at h₁₇
    · norm_num at h₁₇
    · rfl
  exact Prod.ext ha₁ ha₂

private theorem primitive_element_range :
    MulAction.orbit Gal(Field/ℚ) primitiveElement =
      Set.range (fun s : Bool × Bool ↦
        signAutomorphism s primitiveElement) := by
  ext z
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨s, rfl⟩ := signAutomorphism_surjective g
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨signAutomorphism s, rfl⟩

private theorem primitive_element_minpoly :
    (minpoly ℚ primitiveElement).natDegree = 4 := by
  calc
    (minpoly ℚ primitiveElement).natDegree =
        Set.ncard
          (MulAction.orbit Gal(Field/ℚ) primitiveElement) :=
      (card_galois_minpoly
        (K := ℚ) primitiveElement).symm
    _ = Set.ncard (Set.range (fun s : Bool × Bool ↦
        signAutomorphism s primitiveElement)) := by
      rw [primitive_element_range]
    _ = Nat.card (Bool × Bool) :=
      Set.ncard_range_of_injective
        sign_automorphism_primitive
    _ = 4 := by
      rw [Nat.card_eq_fintype_card]
      simp [Fintype.card_prod, Fintype.card_bool]

private theorem primitive_adjoin_top :
    Algebra.adjoin ℚ ({primitiveElement} : Set Field) = ⊤ := by
  have hintermediate : IntermediateField.adjoin ℚ {primitiveElement} = ⊤ :=
    (Field.primitive_element_iff_minpoly_natDegree_eq
      ℚ primitiveElement).2 <| by
        rw [primitive_element_minpoly, finrank]
  have h := congrArg IntermediateField.toSubalgebra hintermediate
  rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ ↦ IsAlgebraic.of_finite ℚ x), IntermediateField.top_toSubalgebra] at h
  exact h

private theorem signAutomorphism_sq (s : Bool × Bool) :
    signAutomorphism s ^ 2 = 1 := by
  rcases s with ⟨s₁, s₂⟩
  cases s₁ <;> cases s₂
  all_goals
    ext z <;>
      simp [signAutomorphism, innerFlip, outerFlip]

/-- Every global automorphism of `Q(sqrt 13, sqrt 17)` is killed by two. -/
theorem galois_exponent_two
    (g : Gal(Field/ℚ)) : g ^ 2 = 1 := by
  obtain ⟨s, rfl⟩ := signAutomorphism_surjective g
  exact signAutomorphism_sq s

private theorem sqrtThirteen_sq : sqrtThirteen ^ 2 = 13 := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      norm_num [sqrtThirteen, pow_two, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat]
  · norm_num [sqrtThirteen, pow_two, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.im_ofNat]

private theorem sqrtSeventeen_sq : sqrtSeventeen ^ 2 = 17 := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      norm_num [sqrtSeventeen, pow_two, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.im_mul, QuadraticAlgebra.re_ofNat,
        QuadraticAlgebra.im_ofNat]
  · norm_num [sqrtSeventeen, pow_two, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.im_ofNat]

set_option maxHeartbeats 2000000 in
-- The completion/minimal-polynomial equivalence unfolds several nested
-- completion and scalar-tower instances.
set_option synthInstance.maxHeartbeats 200000 in
private theorem finrank_quadratic_relation
    (p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (w : CompletionPlacesAbove (L := Field) (FinitePlace.mk p).val)
    (x d : (FinitePlace.mk p).val.Completion)
    (hrel :
      let z := completionEmbedding w.1 primitiveElement
      let mx := completionLies (FinitePlace.mk p).val w.1 w.2 x
      let md := completionLies (FinitePlace.mk p).val w.1 w.2 d
      (z - mx) ^ 2 = md ∨ (z + mx) ^ 2 = md) :
    letI : Algebra (FinitePlace.mk p).val.Completion w.1.Completion :=
      (completionLies (FinitePlace.mk p).val w.1 w.2).toAlgebra
    Module.finrank (FinitePlace.mk p).val.Completion w.1.Completion ≤ 2 := by
  let v := (FinitePlace.mk p).val
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial p⟩
  letI : IsUltrametricDist v.Completion := placeUltrametricDist p
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  let z : w.1.Completion := completionEmbedding w.1 primitiveElement
  have hmin : (minpoly v.Completion z).natDegree ≤ 2 := by
    rcases hrel with hrel | hrel
    · let q : v.Completion[X] := (X - C x) ^ 2 - C d
      have heval : Polynomial.aeval z q = 0 := by
        simpa [q, z] using sub_eq_zero.mpr hrel
      have hq : q ≠ 0 := by
        intro h
        have := congrArg Polynomial.natDegree h
        simp [q, Polynomial.natDegree_sub_eq_left_of_natDegree_lt,
          Polynomial.natDegree_pow] at this
      have hdeg : q.natDegree = 2 := by
        simp [q, Polynomial.natDegree_sub_eq_left_of_natDegree_lt,
          Polynomial.natDegree_pow]
      exact (Polynomial.natDegree_le_of_dvd
        (minpoly.dvd v.Completion z heval) hq).trans_eq hdeg
    · let q : v.Completion[X] := (X + C x) ^ 2 - C d
      have heval : Polynomial.aeval z q = 0 := by
        simpa [q, z] using sub_eq_zero.mpr hrel
      have hq : q ≠ 0 := by
        intro h
        have := congrArg Polynomial.natDegree h
        simp [q, Polynomial.natDegree_sub_eq_left_of_natDegree_lt,
          Polynomial.natDegree_pow] at this
      have hdeg : q.natDegree = 2 := by
        simp [q, Polynomial.natDegree_sub_eq_left_of_natDegree_lt,
          Polynomial.natDegree_pow]
      exact (Polynomial.natDegree_le_of_dvd
        (minpoly.dvd v.Completion z heval) hq).trans_eq hdeg
  let e := completionAdjoinMinpoly v primitiveElement
    primitive_adjoin_top w
  let f := minpoly v.Completion z
  have hf : f ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral z)
  let pb : PowerBasis v.Completion (AdjoinRoot f) := AdjoinRoot.powerBasis hf
  calc
    Module.finrank v.Completion w.1.Completion =
        Module.finrank v.Completion (AdjoinRoot f) :=
      e.toLinearEquiv.finrank_eq.symm
    _ = pb.dim := pb.finrank
    _ = f.natDegree := AdjoinRoot.powerBasis_dim hf
    _ ≤ 2 := hmin

set_option maxHeartbeats 2000000 in
-- Rewriting the completed roots uses the nested quadratic and completion towers.
private theorem completion_finrank_square
    (p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (w : CompletionPlacesAbove (L := Field) (FinitePlace.mk p).val)
    (hsquare :
      (∃ x : (FinitePlace.mk p).val.Completion, x ^ 2 = 13) ∨
      (∃ x : (FinitePlace.mk p).val.Completion, x ^ 2 = 17)) :
    letI : Algebra (FinitePlace.mk p).val.Completion w.1.Completion :=
      (completionLies (FinitePlace.mk p).val w.1 w.2).toAlgebra
    Module.finrank (FinitePlace.mk p).val.Completion w.1.Completion ≤ 2 := by
  let v := (FinitePlace.mk p).val
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial p⟩
  letI : IsUltrametricDist v.Completion := placeUltrametricDist p
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  let z : w.1.Completion := completionEmbedding w.1 primitiveElement
  let m : v.Completion →+* w.1.Completion := completionLies v w.1 w.2
  have hz : z = completionEmbedding w.1 sqrtThirteen +
      completionEmbedding w.1 sqrtSeventeen := by
    exact map_add (completionEmbedding w.1) _ _
  have hz13 : (completionEmbedding w.1 sqrtThirteen) ^ 2 = 13 := by
    rw [← map_pow, sqrtThirteen_sq]
    exact map_natCast (completionEmbedding w.1) 13
  have hz17 : (completionEmbedding w.1 sqrtSeventeen) ^ 2 = 17 := by
    rw [← map_pow, sqrtSeventeen_sq]
    exact map_natCast (completionEmbedding w.1) 17
  rcases hsquare with ⟨x, hx⟩ | ⟨x, hx⟩
  · have hmx : (m x) ^ 2 = 13 := by
      rw [← map_pow, hx]
      exact map_natCast m 13
    have heq := sq_eq_sq_iff_eq_or_eq_neg.mp (hz13.trans hmx.symm)
    apply finrank_quadratic_relation p w x 17
    rcases heq with heq | heq
    · left
      change (z - m x) ^ 2 = m 17
      rw [hz, heq]
      convert hz17.trans (map_natCast m 17).symm using 1; ring
    · right
      change (z + m x) ^ 2 = m 17
      rw [hz, heq]
      convert hz17.trans (map_natCast m 17).symm using 1; ring
  · have hmx : (m x) ^ 2 = 17 := by
      rw [← map_pow, hx]
      exact map_natCast m 17
    have heq := sq_eq_sq_iff_eq_or_eq_neg.mp (hz17.trans hmx.symm)
    apply finrank_quadratic_relation p w x 13
    rcases heq with heq | heq
    · left
      change (z - m x) ^ 2 = m 13
      rw [hz, heq]
      convert hz13.trans (map_natCast m 13).symm using 1; ring
    · right
      change (z + m x) ^ 2 = m 13
      rw [hz, heq]
      convert hz13.trans (map_natCast m 13).symm using 1; ring

/-- A rational finite prime is exceptional in Example 4.5 when it contains
`13` or `17`.  Over `ℚ` these are precisely the two indicated rational
primes. -/
def ExceptionalPrime
    (p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) : Prop :=
  (13 : NumberField.RingOfIntegers ℚ) ∈ p.asIdeal ∨
    (17 : NumberField.RingOfIntegers ℚ) ∈ p.asIdeal

/-- The elementary local arithmetic used in Example 4.5.

The first field is the discriminant/ramification calculation away from
`13` and `17`.  The last two fields are literally the two explicit
quadratic-residue and Hensel calculations in the text. -/
structure LocalArithmetic where
  unramified_away :
    ∀ (p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
      (Q : HeightOneSpectrum (NumberField.RingOfIntegers Field)),
      ¬ ExceptionalPrime p →
      Q.asIdeal.LiesOver p.asIdeal →
      Algebra.IsUnramifiedAt (NumberField.RingOfIntegers ℚ) Q.asIdeal
  seventeen_square_thirteen :
    ∀ p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      (13 : NumberField.RingOfIntegers ℚ) ∈ p.asIdeal →
      ∃ x : (FinitePlace.mk p).val.Completion, x ^ 2 = 17
  thirteen_square_seventeen :
    ∀ p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      (17 : NumberField.RingOfIntegers ℚ) ∈ p.asIdeal →
      ∃ x : (FinitePlace.mk p).val.Completion, x ^ 2 = 13

private theorem subgroup_or_two
    (H : Subgroup Gal(Field/ℚ))
    (hH : IsCyclic H ∨ H ≠ ⊤) :
    Nat.card H = 1 ∨ Nat.card H = 2 := by
  rcases hH with hcyclic | hproper
  · letI : IsCyclic H := hcyclic
    exact cyclic_or_two
      galois_exponent_two H
  · have hdiv : Nat.card H ∣ 4 := by
      have h := H.card_subgroup_dvd_card
      rw [galoisGroup_card] at h
      exact h
    have hpos : 0 < Nat.card H := Nat.card_pos
    have hle : Nat.card H ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
    interval_cases hcard : Nat.card H
    · exact Or.inl rfl
    · exact Or.inr rfl
    · norm_num [hcard] at hdiv
    · exfalso
      apply hproper
      apply H.eq_top_of_card_eq
      exact hcard.trans galoisGroup_card.symm

private theorem decomposition_group_unramified
    (harithmetic : LocalArithmetic)
    (p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (w : CompletionPlacesAbove (L := Field) (FinitePlace.mk p).val)
    (hp : ¬ ExceptionalPrime p) :
    IsCyclic
      (absoluteValueDecomposition (FinitePlace.mk p).val w.1) := by
  let v := (FinitePlace.mk p).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial p⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist p
  have hw : w.1.IsNontrivial := absolute_extension_nontrivial v w
  have hwna : IsNonarchimedean w.1 :=
    absolute_extension_nonarchimedean v w
  let Q := nonarchimedeanHeightSpectrum w.1 hw hwna
  letI : Q.asIdeal.LiesOver p.asIdeal :=
    nonarchimedean_spectrum_lies p w.1 w.2 hw hwna
  have hQ : Algebra.IsUnramifiedAt
      (NumberField.RingOfIntegers ℚ) Q.asIdeal :=
    harithmetic.unramified_away p Q hp inferInstance
  letI : MulSemiringAction Gal(Field/ℚ)
      (NumberField.RingOfIntegers Field) :=
    IsIntegralClosure.MulSemiringAction
      (NumberField.RingOfIntegers ℚ) ℚ Field
      (NumberField.RingOfIntegers Field)
  letI : MulSemiringAction Gal(Field/ℚ)
      (Ideal (NumberField.RingOfIntegers Field)) :=
    Ideal.pointwiseMulSemiringAction
  have hcyclic : IsCyclic (MulAction.stabilizer Gal(Field/ℚ) Q.asIdeal) :=
    decomposition_cyclic_unramified p Q hQ
  rw [← centered_stabilizer_decomposition v w.1 hw hwna]
  exact hcyclic

set_option synthInstance.maxHeartbeats 200000 in
-- The finite-completion module instance passes through the chosen place algebra.
/-- **Milne, Chapter VIII, Example 4.5.**  Subject only to the isolated
elementary local arithmetic above, the concrete extension
`Q(sqrt 13, sqrt 17) / Q` has global degree four, whereas every finite local
degree is one or two. -/
theorem finiteCompletionStatement
    (harithmetic : LocalArithmetic) :
    (Module.finrank ℚ Field = 4 ∧
          ∀ (p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
            (w : CompletionPlacesAbove (L := Field) (FinitePlace.mk p).val),
            letI : Algebra (FinitePlace.mk p).val.Completion w.1.Completion :=
              (completionLies (FinitePlace.mk p).val w.1 w.2).toAlgebra
            Module.finrank (FinitePlace.mk p).val.Completion w.1.Completion = 1 ∨
              Module.finrank (FinitePlace.mk p).val.Completion w.1.Completion = 2) := by
  refine ⟨finrank, ?_⟩
  intro p w
  letI : Fact (FinitePlace.mk p).val.IsNontrivial :=
    ⟨absolute_value_nontrivial p⟩
  letI : IsUltrametricDist (FinitePlace.mk p).val.Completion :=
    placeUltrametricDist p
  letI : Algebra (FinitePlace.mk p).val.Completion w.1.Completion :=
    (completionLies (FinitePlace.mk p).val w.1 w.2).toAlgebra
  letI : FiniteDimensional (FinitePlace.mk p).val.Completion w.1.Completion :=
    placeCompletionDimensional (FinitePlace.mk p).val w
  by_cases hp : ExceptionalPrime p
  · have hsquare :
        (∃ x : (FinitePlace.mk p).val.Completion, x ^ 2 = 13) ∨
        (∃ x : (FinitePlace.mk p).val.Completion, x ^ 2 = 17) := by
      rcases hp with hp13 | hp17
      · exact Or.inr (harithmetic.seventeen_square_thirteen p hp13)
      · exact Or.inl (harithmetic.thirteen_square_seventeen p hp17)
    have hle := completion_finrank_square p w hsquare
    have hpos : 0 < Module.finrank
        (FinitePlace.mk p).val.Completion w.1.Completion := Module.finrank_pos
    omega
  · let D := absoluteValueDecomposition (FinitePlace.mk p).val w.1
    have hD : Nat.card D = 1 ∨ Nat.card D = 2 := by
      letI : IsCyclic D :=
        decomposition_group_unramified
          harithmetic p w hp
      exact cyclic_or_two
        galois_exponent_two D
    rw [finrank_decomposition_card p w]
    exact hD

/-- At an infinite place above the (real) place of `ℚ`, the completion
degree is its archimedean multiplicity, hence is one or two. -/
theorem infinitePlaceMultiplicity
    (w : NumberField.InfinitePlace Field) :
    NumberField.InfinitePlace.mult w = 1 ∨
      NumberField.InfinitePlace.mult w = 2 := by
  unfold NumberField.InfinitePlace.mult
  split_ifs <;> simp

/-- **Milne, Chapter VIII, Example 4.5 (all places).** -/
theorem ratThirteenStatement
    (harithmetic : LocalArithmetic) :
    (Module.finrank ℚ Field = 4 ∧
          ∀ (p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
            (w : CompletionPlacesAbove (L := Field) (FinitePlace.mk p).val),
            letI : Algebra (FinitePlace.mk p).val.Completion w.1.Completion :=
              (completionLies (FinitePlace.mk p).val w.1 w.2).toAlgebra
            Module.finrank (FinitePlace.mk p).val.Completion w.1.Completion = 1 ∨
              Module.finrank (FinitePlace.mk p).val.Completion w.1.Completion = 2) ∧
    ∀ w : NumberField.InfinitePlace Field,
      NumberField.InfinitePlace.mult w = 1 ∨
        NumberField.InfinitePlace.mult w = 2
  :=
  ⟨finiteCompletionStatement harithmetic,
    infinitePlaceMultiplicity⟩

end

end Submission.CField.GClass
