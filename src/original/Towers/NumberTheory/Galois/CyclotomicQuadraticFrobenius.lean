import Towers.NumberTheory.Galois.FrobeniusElement
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois


/-!
# Milne, Examples 8.18 and 8.19

This file records the finite-residue-field computations behind Milne's
cyclotomic and quadratic Frobenius examples.  On a primitive `n`th root,
Frobenius acts by the cardinality power, and its iterates are detected by the
order of that cardinality modulo `n`.  On a square root in an odd-characteristic
quadratic extension, Frobenius acts through the quadratic character.
-/

namespace Towers.NumberTheory.Milne

open Module
open scoped NumberField

noncomputable section

section GlobalCyclotomic

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain S] [Group G] [Finite G] [MulSemiringAction G S]
  [IsGaloisGroup G R S]

/-- Milne, Example 8.18 in the global Galois group: arithmetic Frobenius
sends a primitive root of unity to its residue-cardinality power. -/
theorem arith_frob_root
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    {n : ℕ} (ζ : S) (hζ : IsPrimitiveRoot ζ n) (hn : (n : S) ∉ P) :
    arithFrobAt R G P • ζ = ζ ^ Nat.card (R ⧸ P.under R) := by
  change MulSemiringAction.toAlgHom R S (arithFrobAt R G P) ζ = _
  exact (IsArithFrobAt.arithFrobAt R G P).apply_of_pow_eq_one hζ.1 hn

/-- The `f`th global Frobenius power fixes a primitive `n`th root exactly
when the residue-field cardinality raised to `f` is one modulo `n`. -/
theorem arith_frob_primitive
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    {n : ℕ} [NeZero n] (ζ : S) (hζ : IsPrimitiveRoot ζ n)
    (hn : (n : S) ∉ P) (f : ℕ) :
    arithFrobAt R G P ^ f • ζ = ζ ↔
      Nat.card (R ⧸ P.under R) ^ f ≡ 1 [MOD n] := by
  let sigma := arithFrobAt R G P
  let q := Nat.card (R ⧸ P.under R)
  have hsigma : sigma • ζ = ζ ^ q :=
    arith_frob_root (R := R) (G := G) P ζ hζ hn
  have hpow : ∀ m : ℕ, sigma ^ m • ζ = ζ ^ (q ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ', mul_smul, ih, smul_pow', hsigma]
        simp only [pow_mul, Nat.pow_succ, Nat.mul_comm]
  rw [hpow]
  simpa only [pow_one, ← hζ.eq_orderOf] using
    ((hζ.isOfFinOrder (NeZero.ne n)).pow_eq_pow_iff_modEq
      (n := q ^ f) (m := 1))

end GlobalCyclotomic

section CyclotomicNumberField

variable {K : Type*} [Field K] [NumberField K]
  {p n : ℕ} [Fact p.Prime] [NeZero n]
  [IsCyclotomicExtension {n} ℚ K]

/-- Milne, Example 8.18, including its arithmetic conclusion for a prime not
dividing the chosen cyclotomic level `n`: every prime above `p` has ramification
index one and residue degree equal to the multiplicative order of `p` modulo `n`.

The book's preceding assertion that every prime dividing `n` ramifies needs a
conductor qualification: for odd `m`, the cyclotomic fields of conductors
`2 * m` and `m` coincide. -/
theorem inertia_ramification_dvd
    (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hp : ¬ p ∣ n) :
    Ideal.inertiaDeg (Ideal.span {(p : ℤ)}) P = orderOf (p : ZMod n) ∧
      Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) P = 1 := by
  exact ⟨
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p K P hp,
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p K P hp⟩

/-- Arithmetic Frobenius at a prime of a cyclotomic number field, with the
integral Galois action constructed internally. -/
noncomputable def cyclotomicArithFrob
    (P : Ideal (𝓞 K)) [P.IsPrime] : Gal(K/ℚ) := by
  if hP0 : P = ⊥ then
    exact 1
  else
    letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
    letI : IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K) :=
      IsGaloisGroup.of_isFractionRing Gal(K/ℚ) ℤ (𝓞 K) ℚ K
    letI : Finite (𝓞 K ⧸ P) :=
      Ring.HasFiniteQuotients.finiteQuotient hP0
    exact arithFrobAt ℤ Gal(K/ℚ) P

/-- Milne, Examples 8.18 and 8.34: if `P` lies over the rational prime `p`
and `p` is prime to `n`, then arithmetic Frobenius at `P` corresponds to the
unit class `[p]` under
`Gal(Q(zeta_n)/Q) ≃ (Z/nZ)^×`. -/
theorem gal_arith_frob
    (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hp : p.Coprime n) :
    IsCyclotomicExtension.Rat.galEquivZMod n K
        (cyclotomicArithFrob (n := n) P) =
      ZMod.unitOfCoprime p hp := by
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  letI : IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing Gal(K/ℚ) ℤ (𝓞 K) ℚ K
  have hP0 : P ≠ ⊥ := by
    apply Ideal.ne_bot_of_mem_primesOver
      (Ideal.span_singleton_eq_bot.not.mpr (by
        exact Int.ofNat_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
    exact ⟨inferInstance, inferInstance⟩
  letI : Finite (𝓞 K ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient hP0
  simp only [cyclotomicArithFrob, dif_neg hP0]
  let ζ : 𝓞 K :=
    (IsCyclotomicExtension.zeta_spec n ℚ K).toInteger
  have hζ : IsPrimitiveRoot ζ n :=
    (IsCyclotomicExtension.zeta_spec n ℚ K).toInteger_isPrimitiveRoot
  have hnP : (n : 𝓞 K) ∉ P := by
    intro hnP
    have hnspan : (n : ℤ) ∈ Ideal.span {(p : ℤ)} :=
      (Ideal.mem_of_liesOver
        (P := P) (p := Ideal.span {(p : ℤ)}) (n : ℤ)).2 (by simpa using hnP)
    have hpdivInt : (p : ℤ) ∣ n := by
      simpa only [Ideal.mem_span_singleton] using hnspan
    have hpdiv : p ∣ n := by exact_mod_cast hpdivInt
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hp) hpdiv
  have hcard : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [← Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)})]
    exact Int.card_ideal_quot p
  have hfrob : arithFrobAt ℤ Gal(K/ℚ) P • ζ = ζ ^ p := by
    simpa only [hcard] using
      arith_frob_root
        (R := ℤ) (G := Gal(K/ℚ)) P ζ hζ hnP
  have hgal :=
    IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq n K
      (arithFrobAt ℤ Gal(K/ℚ) P) hζ.pow_eq_one
  have hpow :
      ζ ^ (IsCyclotomicExtension.Rat.galEquivZMod n K
        (arithFrobAt ℤ Gal(K/ℚ) P)).val.val = ζ ^ p := by
    exact hgal.symm.trans hfrob
  have hmod :
      (IsCyclotomicExtension.Rat.galEquivZMod n K
          (arithFrobAt ℤ Gal(K/ℚ) P)).val.val ≡ p [MOD n] := by
    simpa only [hζ.eq_orderOf] using
      (hζ.isOfFinOrder (NeZero.ne n)).pow_eq_pow_iff_modEq.mp hpow
  apply Units.ext
  change
    (IsCyclotomicExtension.Rat.galEquivZMod n K
        (arithFrobAt ℤ Gal(K/ℚ) P)).val = (p : ZMod n)
  simpa using
    (ZMod.natCast_eq_natCast_iff'
      (IsCyclotomicExtension.Rat.galEquivZMod n K
        (arithFrobAt ℤ Gal(K/ℚ) P)).val.val p n).2 hmod

end CyclotomicNumberField

section Quadratic

variable (k L : Type*) [Field k] [Fintype k] [DecidableEq k] [Field L] [Fintype L]
  [Algebra k L] [Algebra.IsAlgebraic k L]

omit [Fintype L] in
/-- Milne, Example 8.19 on residue fields: if `alpha^2 = d`, Frobenius sends
`alpha` to the quadratic-character sign of `d` times `alpha`. -/
theorem quadratic_frobenius_apply (hchar : ringChar k ≠ 2) (d : k) (alpha : L)
    (halpha : alpha ^ 2 = algebraMap k L d) :
    FiniteField.frobeniusAlgEquivOfAlgebraic k L alpha =
      algebraMap k L (quadraticChar k d : k) * alpha := by
  classical
  rw [field_frobenius_element]
  have hcard := FiniteField.odd_card_of_char_ne_two hchar
  conv_lhs => rw [← Nat.two_mul_div_two_add_one_of_odd (Nat.odd_iff.mpr hcard)]
  rw [pow_add, pow_mul, halpha]
  rw [quadraticChar_eq_pow_of_char_ne_two' hchar, map_pow, pow_one]

omit [DecidableEq k] [Fintype L] in
/-- In the quadratic case, Frobenius fixes a nonzero square root exactly
when its radicand is already a square in the residue field. -/
theorem quadratic_frobenius_square (hchar : ringChar k ≠ 2)
    (d : k) (hd : d ≠ 0) (alpha : L) (halpha : alpha ^ 2 = algebraMap k L d)
    (halpha0 : alpha ≠ 0) :
    FiniteField.frobeniusAlgEquivOfAlgebraic k L alpha = alpha ↔ IsSquare d := by
  classical
  rw [quadratic_frobenius_apply k L hchar d alpha halpha]
  rw [quadraticChar_eq_pow_of_char_ne_two' hchar, map_pow]
  calc
    algebraMap k L d ^ (Fintype.card k / 2) * alpha = alpha ↔
        algebraMap k L d ^ (Fintype.card k / 2) = 1 := by
          constructor
          · intro h
            apply mul_right_cancel₀ halpha0
            simpa using h
          · intro h
            simp [h]
    _ ↔ d ^ (Fintype.card k / 2) = 1 := by
      constructor
      · intro h
        apply (algebraMap k L).injective
        simpa using h
      · intro h
        rw [← map_pow, h, map_one]
    _ ↔ IsSquare d := (FiniteField.isSquare_iff hchar hd).symm

end Quadratic

section GlobalQuadratic

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain S] [Group G] [Finite G] [MulSemiringAction G S]
  [IsGaloisGroup G R S]

/-- Milne, Example 8.19 in the global Galois group: at an odd unramified
prime where the chosen square root is nonzero modulo the prime, arithmetic
Frobenius fixes that square root exactly when its radicand is a square in the
base residue field. -/
theorem arith_frob_square
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    [Algebra.IsUnramifiedAt R P]
    (hchar : ringChar (R ⧸ P.under R) ≠ 2)
    (d : R) (α : S) (hα : α ^ 2 = algebraMap R S d) (hαP : α ∉ P) :
    arithFrobAt R G P • α = α ↔
      IsSquare (Ideal.Quotient.mk (P.under R) d) := by
  classical
  let sigma := arithFrobAt R G P
  let p := P.under R
  have hsigma : IsArithFrobAt R sigma P :=
    IsArithFrobAt.arithFrobAt R G P
  letI : Finite (R ⧸ p) := hsigma.finite_quotient
  letI : p.IsMaximal :=
    Ideal.Quotient.maximal_of_isField p (Finite.isField_of_domain (R ⧸ p))
  letI : P.IsMaximal :=
    Ideal.Quotient.maximal_of_isField P (Finite.isField_of_domain (S ⧸ P))
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (R ⧸ p) := Fintype.ofFinite (R ⧸ p)
  letI : Fintype (S ⧸ P) := Fintype.ofFinite (S ⧸ P)
  let dbar : R ⧸ p := Ideal.Quotient.mk p d
  let abar : S ⧸ P := Ideal.Quotient.mk P α
  have habar0 : abar ≠ 0 := by
    exact mt Ideal.Quotient.eq_zero_iff_mem.mp hαP
  have hαbar : abar ^ 2 = algebraMap (R ⧸ p) (S ⧸ P) dbar := by
    simpa only [abar, dbar, map_pow, Ideal.Quotient.algebraMap_mk_of_liesOver] using
      congrArg (Ideal.Quotient.mk P) hα
  have hdbar0 : dbar ≠ 0 := by
    intro hdbar
    have : abar ^ 2 = 0 := by simpa [hdbar] using hαbar
    exact pow_ne_zero 2 habar0 this
  have hfrobquot : Ideal.Quotient.mk P (sigma • α) =
      FiniteField.frobeniusAlgEquivOfAlgebraic (R ⧸ p) (S ⧸ P) abar := by
    simpa only [sigma, p, abar, field_frobenius_element,
      Fintype.card_eq_nat_card] using hsigma.mk_apply α
  have hquad := quadratic_frobenius_square
    (R ⧸ p) (S ⧸ P) hchar dbar hdbar0 abar hαbar habar0
  constructor
  · intro hfix
    apply hquad.mp
    rw [← hfrobquot, hfix]
  · intro hsquare
    have hquotfix : Ideal.Quotient.mk P (sigma • α) = abar :=
      hfrobquot.trans (hquad.mpr hsquare)
    have hsq : (sigma • α) ^ 2 = α ^ 2 := by
      rw [← smul_pow', hα, smul_algebraMap, ← hα]
    rcases eq_or_eq_neg_of_sq_eq_sq (sigma • α) α hsq with hfix | hneg
    · exact hfix
    · exfalso
      have hnegbar : -abar = abar := by
        simpa only [hneg, map_neg, abar] using hquotfix
      have hnegone : (-1 : S ⧸ P) = 1 := by
        apply mul_right_cancel₀ habar0
        simpa only [neg_one_mul, one_mul] using hnegbar
      have hcharTop : ringChar (S ⧸ P) ≠ 2 := by
        rwa [← Algebra.ringChar_eq (R ⧸ p) (S ⧸ P)]
      exact (Ring.neg_one_ne_one_of_char_ne_two hcharTop) hnegone

open Classical in
/-- Equivalently, the global arithmetic Frobenius acts on the chosen square
root by the sign determined by quadratic residuosity. -/
theorem arith_frob_sqrt
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    [Algebra.IsUnramifiedAt R P]
    (hchar : ringChar (R ⧸ P.under R) ≠ 2)
    (d : R) (α : S) (hα : α ^ 2 = algebraMap R S d) (hαP : α ∉ P) :
    arithFrobAt R G P • α =
      if IsSquare (Ideal.Quotient.mk (P.under R) d) then α else -α := by
  classical
  by_cases hsquare : IsSquare (Ideal.Quotient.mk (P.under R) d)
  · rw [if_pos hsquare]
    exact (arith_frob_square P hchar d α hα hαP).mpr hsquare
  · rw [if_neg hsquare]
    have hsq : (arithFrobAt R G P • α) ^ 2 = α ^ 2 := by
      rw [← smul_pow', hα, smul_algebraMap, ← hα]
    rcases eq_or_eq_neg_of_sq_eq_sq (arithFrobAt R G P • α) α hsq with hfix | hneg
    · exact (hsquare
        ((arith_frob_square P hchar d α hα hαP).mp hfix)).elim
    · exact hneg

end GlobalQuadratic

section Cyclotomic

variable (p n : ℕ) [Fact p.Prime] [NeZero n]
variable (L : Type*) [Field L] [Fintype L] [Algebra (ZMod p) L]
  [Algebra.IsAlgebraic (ZMod p) L]

omit [NeZero n] [Fintype L] in
/-- Milne, Example 8.18: on a primitive root of unity, arithmetic Frobenius
acts by raising to the residue characteristic.  When `p ∤ n`, its image is
again a primitive `n`th root. -/
theorem cyclotomic_frobenius_apply (hp : ¬p ∣ n) (ζ : L) (hζ : IsPrimitiveRoot ζ n) :
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) L ζ = ζ ^ p ∧
      IsPrimitiveRoot (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) L ζ) n := by
  have hact : FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) L ζ = ζ ^ p := by
    rw [field_frobenius_element]
    simp
  exact ⟨hact, hact.symm ▸ hζ.pow_of_prime Fact.out hp⟩

omit [Fintype L] in
/-- The `f`th Frobenius iterate fixes a primitive `n`th root exactly when
`p ^ f ≡ 1 (mod n)`.  Equivalently, its order on the cyclotomic generator is
the multiplicative order of `p` modulo `n`. -/
theorem cyclotomic_frobenius_fixed (ζ : L) (hζ : IsPrimitiveRoot ζ n) (f : ℕ) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) L ^ f) ζ = ζ ↔
      p ^ f ≡ 1 [MOD n] := by
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  simp only [ZMod.card]
  simpa only [pow_one, ← hζ.eq_orderOf] using
    ((hζ.isOfFinOrder (NeZero.ne n)).pow_eq_pow_iff_modEq (n := p ^ f) (m := 1))

end Cyclotomic

section Recip

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

/-- The quadratic-reciprocity formula obtained in Milne after comparing the
cyclotomic and quadratic Frobenius computations. -/
theorem quadratic_reciprocity_examples (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q p = (-1) ^ (p / 2 * (q / 2)) * legendreSym p q :=
  legendreSym.quadratic_reciprocity' hp hq

/-- The supplementary law for `2` in the residue-class form used in
Milne's Example 8.19: `2` is a quadratic residue modulo an odd prime exactly
in the congruence classes `1` and `7` modulo `8`. -/
theorem legendre_if_eight (hp : p ≠ 2) :
    legendreSym p 2 = if p % 8 = 1 ∨ p % 8 = 7 then 1 else -1 := by
  rw [legendreSym.at_two hp, ZMod.χ₈_nat_eq_if_mod_eight]
  have hpodd : p % 2 = 1 :=
    (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp
  norm_num [hpodd]

/-- Milne, Example 8.19, second supplementary law, in the book's displayed
form: for an odd prime `p`, the Legendre symbol of `2` is
`(-1)^((p^2-1)/8)`. -/
theorem legendre_sym_neg (hp : p ≠ 2) :
    legendreSym p 2 = (-1 : ℤ) ^ ((p ^ 2 - 1) / 8) := by
  rw [legendre_if_eight hp, neg_one_pow_eq_ite]
  congr 1
  have hpodd : p % 2 = 1 :=
    (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp
  have hp16odd : p % 16 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 16), hpodd]
  have hone : 1 ≤ p ^ 2 % 16 := by
    rw [Nat.pow_mod]
    have hp16lt : p % 16 < 16 := Nat.mod_lt p (by norm_num)
    interval_cases h : p % 16 <;>
      norm_num [h] at hp16odd <;>
      norm_num [h]
  rw [Nat.even_iff, ← Nat.mod_mul_right_div_self]
  norm_num only [Nat.reduceMul]
  rw [← Nat.mod_sub_of_le hone, Nat.pow_mod,
    ← Nat.mod_mod_of_dvd p (by norm_num : 8 ∣ 16)]
  have hp16lt : p % 16 < 16 := Nat.mod_lt p (by norm_num)
  interval_cases h : p % 16 <;>
    norm_num [h] at hp16odd <;>
    norm_num [h]

end Recip

end

end Towers.NumberTheory.Milne
