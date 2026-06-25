import Submission.NumberTheory.Galois.QuinticPolynomial
import Submission.NumberTheory.Galois.DedekindCyclePartition
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# The Galois group in Milne's Example 8.25

This file connects the mod-`2` and mod-`3` factorizations proved in
`Example8_25` to the actual permutation representation of the polynomial
Galois group.
-/

namespace Submission.NumberTheory.Milne

open Equiv Finset Polynomial
open NumberField
open scoped NumberField

noncomputable section

abbrev quinticGaloisQ : ℚ[X] := X ^ 5 - X - 1
abbrev PolynomialZ : ℤ[X] := X ^ 5 - X - 1
abbrev QuinticGaloisSplitting := quinticGaloisQ.SplittingField

local instance : NumberField QuinticGaloisSplitting :=
  NumberField.of_module_finite ℚ QuinticGaloisSplitting

local instance : IsSplittingField ℚ QuinticGaloisSplitting
    quinticGaloisQ :=
  Polynomial.IsSplittingField.splittingField quinticGaloisQ

local instance : IsGalois ℚ QuinticGaloisSplitting :=
  IsGalois.of_separable_splitting_field (p := quinticGaloisQ)
    irreducible_over_rat.separable

local instance : IsGaloisGroup quinticGaloisQ.Gal ℚ
    QuinticGaloisSplitting :=
  IsGaloisGroup.of_isGalois ℚ QuinticGaloisSplitting

local instance : Fact ((quinticGaloisQ.map
    (algebraMap ℚ QuinticGaloisSplitting)).Splits) :=
  ⟨Polynomial.SplittingField.splits quinticGaloisQ⟩

local instance : DecidableEq QuinticGaloisSplitting := Classical.decEq _

/-- The actual permutation representation of the quintic's polynomial
Galois group on its roots in the splitting field. -/
def GalActionHom : quinticGaloisQ.Gal →*
    Equiv.Perm (quinticGaloisQ.rootSet QuinticGaloisSplitting) :=
  Polynomial.Gal.galActionHom quinticGaloisQ
    QuinticGaloisSplitting

/-- The untransported action on the roots in the canonical splitting field. -/
private def CanonicalGalAction :
    quinticGaloisQ.Gal →*
      Equiv.Perm (quinticGaloisQ.rootSet
        quinticGaloisQ.SplittingField) :=
  @MulAction.toPermHom _ _ _
    (Polynomial.Gal.galActionAux (p := quinticGaloisQ))

private theorem PolynomialZ_monic :
    PolynomialZ.Monic := by
  rw [show PolynomialZ = X ^ 5 + (-X - 1) by
    simp only [PolynomialZ]; ring]
  exact ((isMonicOfDegree_X_pow ℤ 5).add_right (by
    compute_degree
    norm_num)).monic

private theorem PolynomialQ_monic :
    quinticGaloisQ.Monic := by
  rw [show quinticGaloisQ = X ^ 5 + (-X - 1) by
    simp only [quinticGaloisQ]; ring]
  exact ((isMonicOfDegree_X_pow ℚ 5).add_right (by
    compute_degree
    norm_num)).monic

private theorem z_nat_degree :
    PolynomialZ.natDegree = 5 := by
  rw [show PolynomialZ = X ^ 5 + (-X - 1) by
    simp only [PolynomialZ]; ring]
  exact ((isMonicOfDegree_X_pow ℤ 5).add_right (by
    compute_degree
    norm_num)).natDegree_eq

private theorem z_splits_integers :
    (PolynomialZ.map
      (algebraMap ℤ (𝓞 QuinticGaloisSplitting))).Splits := by
  apply Polynomial.Splits.of_splits_map_of_injective
      (i := algebraMap (𝓞 QuinticGaloisSplitting)
        QuinticGaloisSplitting)
      (FaithfulSMul.algebraMap_injective _ _)
  · convert Polynomial.SplittingField.splits quinticGaloisQ using 1
    ext n
    simp [PolynomialZ, quinticGaloisQ]
  · intro a ha
    have hpoly :
        (PolynomialZ.map
          (algebraMap ℤ (𝓞 QuinticGaloisSplitting))).map
            (algebraMap (𝓞 QuinticGaloisSplitting)
              QuinticGaloisSplitting) =
          PolynomialZ.map
            (algebraMap ℤ QuinticGaloisSplitting) := by
      ext n
      simp
    have ha' : a ∈ PolynomialZ.aroots
        QuinticGaloisSplitting := by
      rw [Polynomial.aroots_def]
      rwa [hpoly] at ha
    exact ⟨⟨a, roots_mem_integralClosure
      PolynomialZ_monic ha'⟩, rfl⟩

/-- Integral roots of the monic integer polynomial are exactly its roots in
the splitting field. -/
def IntegralRootsEquiv :
    PolynomialZ.rootSet (𝓞 QuinticGaloisSplitting) ≃
      quinticGaloisQ.rootSet QuinticGaloisSplitting where
  toFun x := ⟨(x : 𝓞 QuinticGaloisSplitting), by
    rw [PolynomialQ_monic.mem_rootSet]
    have hx := PolynomialZ_monic.mem_rootSet.mp x.2
    have hx' := congrArg
      (algebraMap (𝓞 QuinticGaloisSplitting)
        QuinticGaloisSplitting) hx
    simpa [PolynomialZ, quinticGaloisQ] using hx'⟩
  invFun y := by
    have hyroot : (y : QuinticGaloisSplitting) ∈
        PolynomialZ.aroots QuinticGaloisSplitting := by
      rw [Polynomial.aroots_def, mem_roots
        (PolynomialZ_monic.map _).ne_zero]
      have hy := PolynomialQ_monic.mem_rootSet.mp y.2
      simpa [IsRoot, eval_map, aeval_def, PolynomialZ,
        quinticGaloisQ] using hy
    let z : 𝓞 QuinticGaloisSplitting :=
      ⟨y, roots_mem_integralClosure PolynomialZ_monic hyroot⟩
    exact ⟨z, by
      rw [PolynomialZ_monic.mem_rootSet]
      apply NumberField.RingOfIntegers.coe_injective
      simpa [z, PolynomialZ, quinticGaloisQ] using
        PolynomialQ_monic.mem_rootSet.mp y.2⟩
  left_inv x := by rfl
  right_inv y := by rfl

/-- The integral-root equivalence followed by Mathlib's chosen transport from
the splitting-field roots to the roots used by `galActionHom`. -/
def IntegralRootsGal :
    PolynomialZ.rootSet (𝓞 QuinticGaloisSplitting) ≃
      quinticGaloisQ.rootSet QuinticGaloisSplitting :=
  IntegralRootsEquiv.trans
    (Polynomial.Gal.rootsEquivRoots quinticGaloisQ
      QuinticGaloisSplitting)

private theorem roots_gal_intertwines
    (sigma : quinticGaloisQ.Gal)
    (x : PolynomialZ.rootSet
      (𝓞 QuinticGaloisSplitting)) :
    IntegralRootsGal
        (arithmeticRootPerm PolynomialZ sigma x) =
      GalActionHom sigma
        (IntegralRootsGal x) := by
  have hraw : IntegralRootsEquiv (sigma • x) =
      CanonicalGalAction sigma
        (IntegralRootsEquiv x) := by
    apply Subtype.ext
    change ((sigma • (x : 𝓞 QuinticGaloisSplitting) :
      𝓞 QuinticGaloisSplitting) : QuinticGaloisSplitting) =
        sigma • ((x.1 : 𝓞 QuinticGaloisSplitting) :
          QuinticGaloisSplitting)
    exact integralClosure.coe_smul sigma x.1
  let e := Polynomial.Gal.rootsEquivRoots quinticGaloisQ
    QuinticGaloisSplitting
  change e (IntegralRootsEquiv (sigma • x)) =
    e (CanonicalGalAction sigma
      (e.symm (e (IntegralRootsEquiv x))))
  rw [e.symm_apply_apply, hraw]

private theorem rootSet_card :
    Fintype.card
      (quinticGaloisQ.rootSet QuinticGaloisSplitting) = 5 := by
  have h := Polynomial.card_rootSet_eq_natDegree
    (K := QuinticGaloisSplitting)
    irreducible_over_rat.separable
    (Polynomial.SplittingField.splits quinticGaloisQ)
  simpa only [quinticGaloisQ] using h.trans (by
    compute_degree
    norm_num)

private theorem reduction_mod_irreducible :
    Irreducible (PolynomialZ.map
      (Ideal.Quotient.mk (Ideal.span ({(3 : ℤ)} : Set ℤ)))) := by
  let e := Int.quotientSpanNatEquivZMod 3
  apply (MulEquiv.irreducible_iff (Polynomial.mapEquiv e)).mp
  rw [Polynomial.mapEquiv_apply]
  have hpoly :
      (PolynomialZ.map
        (Ideal.Quotient.mk (Ideal.span ({(3 : ℤ)} : Set ℤ)))).map e =
        (X ^ 5 - X - 1 : (ZMod 3)[X]) := by
    ext n
    simp [PolynomialZ]
  rw [hpoly]
  exact irreducible_mod_three

private theorem reduction_mod_monic :
    (PolynomialZ.map
      (Ideal.Quotient.mk (Ideal.span ({(3 : ℤ)} : Set ℤ)))).Monic :=
  PolynomialZ_monic.map _

private abbrev ModTwoQuadratic :
    (ℤ ⧸ Ideal.span ({(2 : ℤ)} : Set ℤ))[X] :=
  X ^ 2 + X + 1

private abbrev ModTwoCubic :
    (ℤ ⧸ Ideal.span ({(2 : ℤ)} : Set ℤ))[X] :=
  X ^ 3 + X ^ 2 + 1

private theorem reduction_mod_factorization :
    PolynomialZ.map
        (Ideal.Quotient.mk (Ideal.span ({(2 : ℤ)} : Set ℤ))) =
      ModTwoQuadratic * ModTwoCubic := by
  let e := Int.quotientSpanNatEquivZMod 2
  apply (Polynomial.mapEquiv e).injective
  simpa [Polynomial.mapEquiv_apply, PolynomialZ,
    ModTwoQuadratic, ModTwoCubic] using
      factorization_mod_two

private theorem mod_quadratic_irreducible :
    Irreducible ModTwoQuadratic := by
  let e := Int.quotientSpanNatEquivZMod 2
  apply (MulEquiv.irreducible_iff (Polynomial.mapEquiv e)).mp
  simpa [Polynomial.mapEquiv_apply, ModTwoQuadratic] using
    quadratic_factor_irreducible

private theorem mod_cubic_irreducible :
    Irreducible ModTwoCubic := by
  let e := Int.quotientSpanNatEquivZMod 2
  apply (MulEquiv.irreducible_iff (Polynomial.mapEquiv e)).mp
  simpa [Polynomial.mapEquiv_apply, ModTwoCubic] using
    cubic_factor_irreducible

private theorem mod_quadratic_monic :
    ModTwoQuadratic.Monic := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  letI : Field (ℤ ⧸ Ideal.span ({(2 : ℤ)} : Set ℤ)) :=
    Ideal.Quotient.field _
  let e := Int.quotientSpanNatEquivZMod 2
  apply Polynomial.monic_of_injective
    (e : (ℤ ⧸ Ideal.span ({(2 : ℤ)} : Set ℤ)) →+* ZMod 2).injective
  have h : (X ^ 2 + X + 1 : (ZMod 2)[X]).Monic := by
    rw [show (X ^ 2 + X + 1 : (ZMod 2)[X]) = X ^ 2 + (X + 1) by ring]
    exact ((isMonicOfDegree_X_pow (ZMod 2) 2).add_right (by
      compute_degree
      norm_num)).monic
  simpa [ModTwoQuadratic] using h

private theorem mod_cubic_monic :
    ModTwoCubic.Monic := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  letI : Field (ℤ ⧸ Ideal.span ({(2 : ℤ)} : Set ℤ)) :=
    Ideal.Quotient.field _
  let e := Int.quotientSpanNatEquivZMod 2
  apply Polynomial.monic_of_injective
    (e : (ℤ ⧸ Ideal.span ({(2 : ℤ)} : Set ℤ)) →+* ZMod 2).injective
  have h : (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).Monic := by
    rw [show (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]) =
      X ^ 3 + (X ^ 2 + 1) by ring]
    exact ((isMonicOfDegree_X_pow (ZMod 2) 3).add_right (by
      compute_degree
      norm_num)).monic
  simpa [ModTwoCubic] using h

private theorem mod_quadratic_degree :
    ModTwoQuadratic.natDegree = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  letI : Field (ℤ ⧸ Ideal.span ({(2 : ℤ)} : Set ℤ)) :=
    Ideal.Quotient.field _
  rw [show ModTwoQuadratic = X ^ 2 + (X + 1) by
    simp only [ModTwoQuadratic]; ring]
  exact ((isMonicOfDegree_X_pow
    (ℤ ⧸ Ideal.span ({(2 : ℤ)} : Set ℤ)) 2).add_right (by
      compute_degree
      norm_num)).natDegree_eq

private theorem mod_cubic_degree :
    ModTwoCubic.natDegree = 3 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : (Ideal.span ({(2 : ℤ)} : Set ℤ)).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  letI : Field (ℤ ⧸ Ideal.span ({(2 : ℤ)} : Set ℤ)) :=
    Ideal.Quotient.field _
  rw [show ModTwoCubic = X ^ 3 + (X ^ 2 + 1) by
    simp only [ModTwoCubic]; ring]
  exact ((isMonicOfDegree_X_pow
    (ℤ ⧸ Ideal.span ({(2 : ℤ)} : Set ℤ)) 3).add_right (by
      compute_degree
      norm_num)).natDegree_eq

private theorem exists_full_cycle :
    ∃ sigma : quinticGaloisQ.Gal,
      (GalActionHom sigma).IsCycle ∧
        (GalActionHom sigma).support = Finset.univ := by
  classical
  let p : Ideal ℤ := Ideal.span ({(3 : ℤ)} : Set ℤ)
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : p.IsMaximal := by
    dsimp only [p]
    exact Int.ideal_span_isMaximal_of_prime 3
  letI : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  letI : Fintype (ℤ ⧸ p) := Fintype.ofFinite _
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 QuinticGaloisSplitting) p
  letI : Q.IsMaximal := hQmax
  letI : Q.IsPrime := Ideal.IsMaximal.isPrime hQmax
  letI : Q.LiesOver p := hQover
  letI : Field (𝓞 QuinticGaloisSplitting ⧸ Q) :=
    Ideal.Quotient.field Q
  letI : Fintype (𝓞 QuinticGaloisSplitting ⧸ Q) := Fintype.ofFinite _
  let red : (ℤ ⧸ p)[X] :=
    PolynomialZ.map (Ideal.Quotient.mk p)
  have hirr : Irreducible red := by
    simpa only [red, p] using reduction_mod_irreducible
  have hmonic : red.Monic := by
    simpa only [red, p] using reduction_mod_monic
  have hsep : red.Separable := PerfectField.separable_of_irreducible hirr
  have hsplitsRed :
      (red.map (algebraMap (ℤ ⧸ p)
        (𝓞 QuinticGaloisSplitting ⧸ Q))).Splits := by
    have h := z_splits_integers.map
      (Ideal.Quotient.mk Q)
    convert h using 1
    ext n
    simp only [red, Polynomial.coeff_map, Polynomial.coeff_map,
      Ideal.Quotient.algebraMap_mk_of_liesOver]
  obtain ⟨x, hxroot, -, hxcard⟩ :=
    frobenius_cycle_irreducible
      (ℤ ⧸ p) (𝓞 QuinticGaloisSplitting ⧸ Q)
      hirr hmonic hsplitsRed
  let xr : red.rootSet (𝓞 QuinticGaloisSplitting ⧸ Q) := ⟨x, hxroot⟩
  let sigma : quinticGaloisQ.Gal :=
    arithFrobAt ℤ quinticGaloisQ.Gal Q
  have hsigma : IsArithFrobAt ℤ sigma Q :=
    IsArithFrobAt.arithFrobAt ℤ quinticGaloisQ.Gal Q
  let s := liftedFrobeniusCycle (p := p) (Q := Q)
    PolynomialZ PolynomialZ_monic
    z_splits_integers hsep xr
  have hcycle : (arithmeticRootPerm
      (S := 𝓞 QuinticGaloisSplitting)
      PolynomialZ sigma).IsCycleOn
      (s : Set _) := by
    exact arithmetic_cycle_lifted
      PolynomialZ PolynomialZ_monic
      z_splits_integers hsep hsigma xr
  have hscard : s.card = 5 := by
    calc
      s.card = Set.ncard (frobeniusCycle (ℤ ⧸ p)
          (𝓞 QuinticGaloisSplitting ⧸ Q) xr) :=
        card_lifted_cycle
          PolynomialZ PolynomialZ_monic
          z_splits_integers hsep xr
      _ = red.natDegree := hxcard
      _ = 5 := by
        change (PolynomialZ.map (Ideal.Quotient.mk p)).natDegree = 5
        rw [PolynomialZ_monic.natDegree_map]
        exact z_nat_degree
  have hintCard : Fintype.card
      (PolynomialZ.rootSet
        (𝓞 QuinticGaloisSplitting)) = 5 := by
    rw [Fintype.card_congr IntegralRootsGal]
    exact rootSet_card
  have hsuniv : s = Finset.univ := by
    apply s.eq_univ_of_card
    rw [hscard, hintCard]
  have hgalCycleOn : (GalActionHom sigma).IsCycleOn
      (Set.univ : Set
        (quinticGaloisQ.rootSet QuinticGaloisSplitting)) := by
    have htransport := Equiv.Perm.IsCycleOn.transp_finse
      IntegralRootsGal s hcycle
      (roots_gal_intertwines sigma)
    rw [hsuniv] at htransport
    simpa using htransport
  obtain ⟨hcyc, hsupp⟩ :=
    cycle_support_univ
      (GalActionHom sigma) (by
        rw [rootSet_card]
        norm_num)
      hgalCycleOn
  exact ⟨sigma, hcyc, hsupp⟩

private theorem exists_cube_swap :
    ∃ rho : quinticGaloisQ.Gal,
      (GalActionHom rho ^ 3).IsSwap := by
  classical
  let p : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : p.IsMaximal := by
    dsimp only [p]
    exact Int.ideal_span_isMaximal_of_prime 2
  letI : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  letI : Fintype (ℤ ⧸ p) := Fintype.ofFinite _
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 QuinticGaloisSplitting) p
  letI : Q.IsMaximal := hQmax
  letI : Q.IsPrime := Ideal.IsMaximal.isPrime hQmax
  letI : Q.LiesOver p := hQover
  letI : Field (𝓞 QuinticGaloisSplitting ⧸ Q) :=
    Ideal.Quotient.field Q
  letI : Fintype (𝓞 QuinticGaloisSplitting ⧸ Q) := Fintype.ofFinite _
  let red : (ℤ ⧸ p)[X] :=
    PolynomialZ.map (Ideal.Quotient.mk p)
  let g : Bool → (ℤ ⧸ p)[X] := fun i =>
    if i then ModTwoCubic else ModTwoQuadratic
  have hfactor : red = ∏ i, g i := by
    simpa [red, g, p, mul_comm] using
      reduction_mod_factorization
  have hirr : ∀ i, Irreducible (g i) := by
    intro i
    cases i
    · simpa only [g, Bool.false_eq_true, ↓reduceIte, p] using
        mod_quadratic_irreducible
    · simpa only [g, ↓reduceIte, p] using
        mod_cubic_irreducible
  have hmonicFactor : ∀ i, (g i).Monic := by
    intro i
    cases i
    · simpa only [g, Bool.false_eq_true, ↓reduceIte, p] using
        mod_quadratic_monic
    · simpa only [g, ↓reduceIte, p] using
        mod_cubic_monic
  have hdegree : ∀ i, (g i).natDegree = if i then 3 else 2 := by
    intro i
    cases i
    · simpa only [g, Bool.false_eq_true, ↓reduceIte, p] using
        mod_quadratic_degree
    · simpa only [g, ↓reduceIte, p] using
        mod_cubic_degree
  have hinj : Function.Injective g := by
    intro i j hij
    by_contra hne
    have hdegreeEq := congrArg Polynomial.natDegree hij
    cases i <;> cases j <;> simp_all [g]
  have hcoprime : IsCoprime (g false) (g true) := by
    rcases (hirr false).isCoprime_or_dvd (g true) with h | h
    · exact h
    · have hassoc := (hirr false).associated_of_dvd (hirr true) h
      have heq := eq_of_monic_of_associated
        (hmonicFactor false) (hmonicFactor true) hassoc
      exact False.elim (Bool.false_ne_true (hinj heq))
  have hsep : red.Separable := by
    rw [hfactor]
    simpa [g, mul_comm] using
      (PerfectField.separable_of_irreducible (hirr false)).mul
        (PerfectField.separable_of_irreducible (hirr true)) hcoprime
  obtain ⟨rho, s, -, hcycle, hcard, hcover⟩ :=
    arithmetic_cycle_partition
      (R := ℤ) (S := 𝓞 QuinticGaloisSplitting)
      (G := quinticGaloisQ.Gal) (p := p) (Q := Q)
      PolynomialZ PolynomialZ_monic
      z_splits_integers hsep g hfactor hirr
      hmonicFactor hinj
  have hcoverIntegral : s false ∪ s true = Finset.univ := by
    simpa [Finset.union_comm] using hcover
  let t : Bool → Finset (quinticGaloisQ.rootSet
      QuinticGaloisSplitting) := fun i =>
    (s i).map IntegralRootsGal.toEmbedding
  have hcoverGal : t false ∪ t true = Finset.univ := by
    exact Finset.map_equivunion_equniv
      IntegralRootsGal hcoverIntegral
  have hcycleGal : ∀ i, (GalActionHom rho).IsCycleOn
      (t i : Set _) := by
    intro i
    exact Equiv.Perm.IsCycleOn.transp_finse
      IntegralRootsGal (s i) (hcycle i)
      (roots_gal_intertwines rho)
  have hcardTwo : (t false).card = 2 := by
    simp [t, hcard, hdegree]
  have hcardThree : (t true).card = 3 := by
    simp [t, hcard, hdegree]
  exact ⟨rho, swap_cycle_partition
    (GalActionHom rho) (t false) (t true) hcoverGal
    hcardTwo hcardThree (hcycleGal false) (hcycleGal true)⟩

/-- Milne, Example 8.25: the polynomial Galois group of
`X ^ 5 - X - 1` acts as the full symmetric group on its five roots. -/
theorem gal_action_top :
    GalActionHom.range = ⊤ := by
  obtain ⟨sigma, hsigmaCycle, hsigmaSupport⟩ :=
    exists_full_cycle
  obtain ⟨rho, hrhoSwap⟩ := exists_cube_swap
  apply perm_cycle_swap
    GalActionHom.range
    (by rw [rootSet_card]; norm_num)
    hsigmaCycle hsigmaSupport hrhoSwap
  · exact ⟨sigma, rfl⟩
  · exact Subgroup.pow_mem GalActionHom.range ⟨rho, rfl⟩ 3

/-- The usual abstract-group formulation of Example 8.25: the polynomial
Galois group is isomorphic to the symmetric group on its five roots. -/
theorem polynomial_gal_perm :
    Nonempty (quinticGaloisQ.Gal ≃*
      Equiv.Perm (quinticGaloisQ.rootSet
        QuinticGaloisSplitting)) := by
  let eRange : quinticGaloisQ.Gal ≃*
      GalActionHom.range :=
    MonoidHom.ofInjective
      (Polynomial.Gal.galActionHom_injective
        quinticGaloisQ QuinticGaloisSplitting)
  exact ⟨eRange.trans
    ((MulEquiv.subgroupCongr
      gal_action_top).trans Subgroup.topEquiv)⟩

/-- Example 8.25 with the roots numbered explicitly: the Galois group is
the standard symmetric group `S₅ = Equiv.Perm (Fin 5)`. -/
theorem gal_s_5 :
    Nonempty (quinticGaloisQ.Gal ≃* Equiv.Perm (Fin 5)) := by
  let eRoots :
      quinticGaloisQ.rootSet QuinticGaloisSplitting ≃ Fin 5 :=
    Fintype.equivFinOfCardEq rootSet_card
  exact ⟨Classical.choice polynomial_gal_perm |>.trans
    eRoots.permCongrHom⟩

end

end Submission.NumberTheory.Milne
