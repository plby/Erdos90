import Towers.ClassField.NormCorrespondence.LocalStatement
import Towers.ClassField.NormCorrespondence.LocalStatements
import Towers.ClassField.CohomologyOps.ExtensionsSecondCohomology
import Towers.ClassField.CrossedProducts.BrauerRestriction
import Towers.ClassField.CrossedProducts.MulApply
import Towers.ClassField.CrossedProducts.GaloisSubfieldAlgebra
import Towers.ClassField.CrossedProducts.Cohomology
import Towers.ClassField.ArtinReciprocity.Statements
import Towers.ClassField.Ideles.FinitePlaceCompletion
import Towers.ClassField.Reciprocity.ArtinMapStatements
import Towers.ClassField.IdeleCohomology.DecompositionStatements
import Towers.ClassField.CyclotomicBrauer.CohomologicalInjection
import Towers.ClassField.CyclotomicBrauer.LocalizationStatements
import Towers.ClassField.NormLimitation.ExistenceStatement
import Towers.ClassField.ReciprocityExistence.LawStatements
import Towers.ClassField.KummerTheory.KummerCorrespondence
import Towers.ClassField.GrunwaldWang.CyclicDivision
import Towers.ClassField.GrunwaldWang.GrunwaldWangStatement
import Towers.ClassField.GrunwaldWang.SimultaneousStatement
import Towers.ClassField.GlobalClass.BrauerSequenceStatements
import Towers.FieldTheory.Blueprint
import Towers.FieldTheory.CentralEmbeddingBrauer
import Towers.FieldTheory.CentralEmbeddingDescent
import Towers.FieldTheory.CentralFactorSet
import Towers.FieldTheory.CentralEmbeddingKummer
import Towers.FieldTheory.CentralSeparableClosure
import Towers.FieldTheory.CentralEmbeddingDecomposition
import Towers.FieldTheory.CentralEmbeddingObstruction
import Towers.FieldTheory.PrimeKernelBridge
import Towers.FieldTheory.CentralEmbeddingPresentation
import Towers.FieldTheory.FiniteGeneration
import Towers.FieldTheory.FiniteCompositumUnramified
import Towers.FieldTheory.RationalFinitePlace
import Towers.Group.ProPPresentation
import Towers.NumberTheory.CyclotomicCubic
import Towers.NumberTheory.LocalInertia
import Towers.NumberTheory.UnramifiedInertia
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

universe u v

open NumberField
open Towers.CField.Ideles

private instance rationalTameFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

/-- A chosen embedding of a rational cyclotomic field into the fixed
algebraic closure used to define `G_S(ℚ)(3)`. -/
noncomputable def rationalCyclotomicEmbedding (r : ℕ) :
    CyclotomicField r ℚ →ₐ[ℚ] AlgebraicClosure ℚ :=
  IsAlgClosed.lift

/-- The quadratic field `ℚ(ζ₃)`, embedded in the same fixed algebraic closure
as the rational tame pro-`3` extension. -/
noncomputable def rationalCubeField :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  (⊤ : IntermediateField ℚ (CyclotomicField 3 ℚ)).map
    (rationalCyclotomicEmbedding 3)

/-- The chosen model of `ℚ(ζ₃)` is equivalent to the abstract cyclotomic
field supplied by Mathlib. -/
noncomputable def rationalCubeRoot :
    CyclotomicField 3 ℚ ≃ₐ[ℚ] rationalCubeField := by
  simpa [rationalCubeField] using
    (((IntermediateField.topEquiv :
        (⊤ : IntermediateField ℚ (CyclotomicField 3 ℚ)) ≃ₐ[ℚ]
          CyclotomicField 3 ℚ).symm).trans
      (IntermediateField.equivMap
        (⊤ : IntermediateField ℚ (CyclotomicField 3 ℚ))
        (rationalCyclotomicEmbedding 3)))

noncomputable instance instCubeRoot :
    NumberField rationalCubeField :=
  NumberField.of_ringEquiv (CyclotomicField 3 ℚ) rationalCubeField
    rationalCubeRoot.toRingEquiv

noncomputable instance instRationalCube :
    IsGalois ℚ rationalCubeField := by
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  letI : IsGalois ℚ (CyclotomicField 3 ℚ) :=
    IsCyclotomicExtension.isGalois {3} ℚ (CyclotomicField 3 ℚ)
  exact IsGalois.of_algEquiv rationalCubeRoot

theorem rational_cube_finrank :
    Module.finrank ℚ rationalCubeField = 2 := by
  rw [← rationalCubeRoot.toLinearEquiv.finrank_eq]
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  rw [IsCyclotomicExtension.finrank (n := 3) (CyclotomicField 3 ℚ)
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  norm_num [Nat.totient_prime Nat.prime_three]

/-- The concrete field in the fixed algebraic closure contains a primitive
cube root of unity. -/
theorem rational_cube_primitive :
    (primitiveRoots 3 rationalCubeField).Nonempty := by
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let zeta := IsCyclotomicExtension.zeta 3 ℚ (CyclotomicField 3 ℚ)
  refine ⟨rationalCubeRoot zeta, ?_⟩
  exact (mem_primitiveRoots (by norm_num)).2
    ((IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)).map_of_injective
      rationalCubeRoot.injective)

/-- Every rational prime congruent to one modulo three has residue degree
one in the chosen copy of `ℚ(ζ₃)`.  This is the finite-prime input used when
the tame relation over `ℚ` is transported to the cyclotomic base: the local
residue cardinality stays equal to the displayed rational prime. -/
theorem rational_cube_deg
    {r : ℕ} (hr : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3])
    (P : Ideal (NumberField.RingOfIntegers rationalCubeField))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal r)] :
    (Ideal.rationalPrimeIdeal r).inertiaDeg P = 1 := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  letI : IsScalarTower ℤ ℚ (CyclotomicField 3 ℚ) := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro z
    simp
  let eZ : CyclotomicField 3 ℚ ≃ₐ[ℤ] rationalCubeField :=
    AlgEquiv.ofRingEquiv
      (f := rationalCubeRoot.toRingEquiv) (fun z => by simp)
  let e0 : NumberField.RingOfIntegers (CyclotomicField 3 ℚ) ≃ₐ[ℤ]
      NumberField.RingOfIntegers rationalCubeField :=
    eZ.mapIntegralClosure
  let Q : Ideal (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :=
    P.comap e0
  have hQover : Q ∈ (Ideal.rationalPrimeIdeal r).primesOver
      (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) := by
    refine ⟨inferInstance, ?_⟩
    rw [Ideal.liesOver_iff]
    ext z
    change z ∈ Ideal.rationalPrimeIdeal r ↔
      e0.toRingHom (algebraMap ℤ
        (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) z) ∈ P
    simpa using (Ideal.mem_of_liesOver
      (P := P) (p := Ideal.rationalPrimeIdeal r) z)
  letI : Q.IsPrime := hQover.1
  letI : Q.LiesOver (Ideal.rationalPrimeIdeal r) := hQover.2
  letI : Q.LiesOver (Ideal.span {(r : ℤ)}) := by
    simpa [Ideal.rationalPrimeIdeal] using hQover.2
  have hrnotdvd : ¬r ∣ 3 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with hr1 | hr3eq
    · exact hr.ne_one hr1
    · subst r
      norm_num at hr3
  have hQ : (Ideal.rationalPrimeIdeal r).inertiaDeg Q =
      orderOf (r : ZMod 3) :=
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
      (p := r) (K := CyclotomicField 3 ℚ) (P := Q) hrnotdvd
  have hrZ : (r : ZMod 3) = 1 := by
    rw [← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff r 1 3).mpr hr3
  calc
    (Ideal.rationalPrimeIdeal r).inertiaDeg P =
        (Ideal.rationalPrimeIdeal r).inertiaDeg Q := by
      symm
      exact (Ideal.rationalPrimeIdeal r).inertiaDeg_comap_eq e0 P
    _ = orderOf (r : ZMod 3) := hQ
    _ = 1 := orderOf_eq_one_iff.mpr hrZ

/-- The ninth cyclotomic field has a unique Galois cubic subfield.  This is
the conductor-`9` character used to remove unwanted ramification at `3`. -/
theorem unique_nine_subfield :
    ∃! E : IntermediateField ℚ (CyclotomicField 9 ℚ),
      GaloisCubicSubfield E := by
  let K := CyclotomicField 9 ℚ
  letI : NeZero (9 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (9 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {9} ℚ K :=
    CyclotomicField.isCyclotomicExtension 9 ℚ
  letI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois (S := {9}) (K := ℚ) (L := K)
  let e := IsCyclotomicExtension.Rat.galEquivZMod 9 K
  have hcycUnits : IsCyclic ((ZMod 9)ˣ) := by
    simpa using
      (ZMod.isCyclic_units_of_prime_pow 3 Nat.prime_three (by norm_num) 2)
  letI : IsCyclic Gal(K/ℚ) := (e.isCyclic).mpr hcycUnits
  letI : CommGroup Gal(K/ℚ) := IsCyclic.commGroup
  have hcard : Nat.card Gal(K/ℚ) = 6 := by
    calc
      Nat.card Gal(K/ℚ) = Nat.card ((ZMod 9)ˣ) := Nat.card_congr e.toEquiv
      _ = Fintype.card ((ZMod 9)ˣ) := Nat.card_eq_fintype_card
      _ = Nat.totient 9 := ZMod.card_units_eq_totient 9
      _ = 6 := by
        rw [show (9 : ℕ) = 3 ^ (1 + 1) by norm_num,
          Nat.totient_prime_pow_succ Nat.prime_three]
        norm_num
  have hdiv : 3 ∣ Nat.card Gal(K/ℚ) := by rw [hcard]; norm_num
  obtain ⟨H, hHidx, hHuniq⟩ :=
    unique_index_three (G := Gal(K/ℚ)) hdiv
  refine ⟨IntermediateField.fixedField H, ?_, ?_⟩
  · constructor
    · rw [IntermediateField.finrank_eq_fixingSubgroup_index
        (L := IntermediateField.fixedField H),
        IntermediateField.fixingSubgroup_fixedField, hHidx]
    · letI : H.Normal := by infer_instance
      infer_instance
  · intro E hE
    have hEidx : E.fixingSubgroup.index = 3 := by
      rw [← hE.1, IntermediateField.finrank_eq_fixingSubgroup_index (L := E)]
    have hfix : E.fixingSubgroup = H := hHuniq E.fixingSubgroup hEidx
    calc
      E = IntermediateField.fixedField E.fixingSubgroup := by
        symm
        exact IsGalois.fixedField_fixingSubgroup E
      _ = IntermediateField.fixedField H := by rw [hfix]

/-- The canonical cubic subfield of `ℚ(ζ₉)`. -/
noncomputable def nineCubicSubfield :
    IntermediateField ℚ (CyclotomicField 9 ℚ) :=
  Classical.choose unique_nine_subfield

theorem nine_subfield_spec :
    GaloisCubicSubfield nineCubicSubfield :=
  (Classical.choose_spec unique_nine_subfield).1

/-- The conductor-`9` cubic field transported to the fixed algebraic
closure of `ℚ`. -/
noncomputable def rationalNineCubic :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  nineCubicSubfield.map (rationalCyclotomicEmbedding 9)

noncomputable instance instNineCubic :
    NumberField rationalNineCubic := by
  letI : NeZero (9 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (9 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {9} ℚ (CyclotomicField 9 ℚ) :=
    CyclotomicField.isCyclotomicExtension 9 ℚ
  letI : NumberField nineCubicSubfield := inferInstance
  let e : nineCubicSubfield ≃ₐ[ℚ]
      rationalNineCubic := by
    simpa [rationalNineCubic] using
      IntermediateField.equivMap nineCubicSubfield
        (rationalCyclotomicEmbedding 9)
  exact NumberField.of_ringEquiv
    (K := nineCubicSubfield)
    (L := rationalNineCubic) e.toRingEquiv

theorem rational_nine_galois :
    CyclicCubicQ rationalNineCubic := by
  letI : NeZero (9 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (9 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {9} ℚ (CyclotomicField 9 ℚ) :=
    CyclotomicField.isCyclotomicExtension 9 ℚ
  let C := nineCubicSubfield
  let D := rationalNineCubic
  let e : C ≃ₐ[ℚ] D := by
    simpa [C, D, rationalNineCubic] using
      IntermediateField.equivMap C (rationalCyclotomicEmbedding 9)
  have hC := nine_subfield_spec
  letI : IsGalois ℚ C := hC.2
  have hdegree : Module.finrank ℚ D = 3 := by
    rw [← e.toLinearEquiv.finrank_eq, hC.1]
  have hgalois : IsGalois ℚ D := IsGalois.of_algEquiv e
  have hcyclic : IsCyclic Gal(D/ℚ) := by
    have hcard : Nat.card Gal(D/ℚ) = 3 := by
      rw [IsGalois.card_aut_eq_finrank, hdegree]
    exact isCyclic_of_prime_card hcard
  exact ⟨hdegree, hgalois, hcyclic⟩

theorem nine_subfield_ramification :
    RationalRamificationIdx
      (S := NumberField.RingOfIntegers nineCubicSubfield) 3 3 := by
  let K := CyclotomicField 9 ℚ
  let E := nineCubicSubfield
  letI : NeZero (9 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (9 : ℚ) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : IsCyclotomicExtension {3 ^ (1 + 1)} ℚ K := by
    simpa using (CyclotomicField.isCyclotomicExtension 9 ℚ)
  let hTowerK : IsScalarTower ℤ ℚ K := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro z
    simp
  letI : IsScalarTower ℤ ℚ K := hTowerK
  letI : Algebra ℚ E := E.algebra'
  letI : IsScalarTower ℤ ℚ E := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro z
    simp
  letI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois (S := {3 ^ (1 + 1)}) (K := ℚ) (L := K)
  letI : IsGalois ℚ E := nine_subfield_spec.2
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ E
    (NumberField.RingOfIntegers E)
  let hTowerOK : IsScalarTower ℤ (NumberField.RingOfIntegers K) K := by
    with_reducible_and_instances exact inferInstance
  let hICK : IsIntegralClosure (NumberField.RingOfIntegers K) ℤ K := by
    exact integralClosure.isIntegralClosure ℤ K
  letI : MulSemiringAction Gal(K/ℚ) (NumberField.RingOfIntegers K) :=
    @IsIntegralClosure.MulSemiringAction ℤ ℚ K
      (NumberField.RingOfIntegers K) _ _ _ _ _ _ _ _ _ _
      hTowerK hTowerOK hICK _
  letI := IsIntegralClosure.MulSemiringAction
    (NumberField.RingOfIntegers E) E K (NumberField.RingOfIntegers K)
  letI : IsGaloisGroup Gal(E/ℚ) ℤ (NumberField.RingOfIntegers E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/ℚ) ℤ
      (NumberField.RingOfIntegers E) ℚ E
  letI : IsGaloisGroup Gal(K/ℚ) ℤ (NumberField.RingOfIntegers K) :=
    @IsGaloisGroup.of_isFractionRing Gal(K/ℚ) ℤ
      (NumberField.RingOfIntegers K) ℚ K
      _ _ _ _ _ _ _ _ _ _ _ _ _ hTowerK hTowerOK _ _ _ _ _
  letI : IsGaloisGroup Gal(K/E) (NumberField.RingOfIntegers E)
      (NumberField.RingOfIntegers K) :=
    IsGaloisGroup.of_isFractionRing Gal(K/E)
      (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers K) E K
  let p : Ideal ℤ := Ideal.rationalPrimeIdeal 3
  have hp0 : p ≠ ⊥ := rational_ne_bot Nat.prime_three
  letI : p.IsMaximal := rational_ideal_maximal Nat.prime_three
  have hcountK : (p.primesOver (NumberField.RingOfIntegers K)).ncard = 1 := by
    simpa [p, Ideal.rationalPrimeIdeal] using
      IsCyclotomicExtension.Rat.ncard_primesOver_of_prime_pow 3 1 K
  have hinertiaK : p.inertiaDegIn (NumberField.RingOfIntegers K) = 1 := by
    simpa [p, Ideal.rationalPrimeIdeal] using
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime_pow 3 1 K
  intro P hP
  letI : P.IsPrime := hP.1
  letI : P.LiesOver p := hP.2
  letI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := p) (P := P)
  have hcountE : (p.primesOver (NumberField.RingOfIntegers E)).ncard = 1 := by
    have hcountTower :=
      Ideal.ncard_primesOver_mul_ncard_primesOver
        (p := p) P Gal(E/ℚ) (NumberField.RingOfIntegers K)
          Gal(K/ℚ) Gal(K/E) hp0
    have hcountTower1 :
        (p.primesOver (NumberField.RingOfIntegers E)).ncard *
          (P.primesOver (NumberField.RingOfIntegers K)).ncard = 1 := by
      rwa [hcountK] at hcountTower
    exact Nat.eq_one_of_mul_eq_one_right hcountTower1
  have hinertiaE : p.inertiaDegIn (NumberField.RingOfIntegers E) = 1 := by
    have hmul := Ideal.inertiaDegIn_mul_inertiaDegIn
      (p := p) P Gal(E/ℚ) (NumberField.RingOfIntegers K)
        Gal(K/ℚ) Gal(K/E)
    have hmul1 : p.inertiaDegIn (NumberField.RingOfIntegers E) *
        P.inertiaDegIn (NumberField.RingOfIntegers K) = 1 := by
      rwa [hinertiaK] at hmul
    exact Nat.eq_one_of_mul_eq_one_right hmul1
  have hcardE : Nat.card Gal(E/ℚ) = Module.finrank ℚ E := by
    simpa using IsGaloisGroup.card_eq_finrank (G := Gal(E/ℚ)) (K := ℚ) (L := E)
  have hramEIn : p.ramificationIdxIn (NumberField.RingOfIntegers E) = 3 := by
    have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := p) hp0 (NumberField.RingOfIntegers E) Gal(E/ℚ)
    rw [hcardE, nine_subfield_spec.1, hcountE, hinertiaE] at hfund
    simpa using hfund
  calc
    Ideal.ramificationIdx p P =
        p.ramificationIdxIn (NumberField.RingOfIntegers E) := by
      symm
      exact Ideal.ramificationIdxIn_eq_ramificationIdx
        (p := p) (P := P) (G := Gal(E/ℚ))
    _ = 3 := hramEIn

theorem rational_nine_ramification :
    RationalRamificationIdx
      (S := NumberField.RingOfIntegers rationalNineCubic) 3 3 := by
  let C := nineCubicSubfield
  let D := rationalNineCubic
  let e : C ≃ₐ[ℚ] D := by
    simpa [C, D, rationalNineCubic] using
      IntermediateField.equivMap C (rationalCyclotomicEmbedding 9)
  let e0 : NumberField.RingOfIntegers C ≃ₐ[ℤ]
      NumberField.RingOfIntegers D :=
    (e.restrictScalars ℤ).mapIntegralClosure
  intro P hP
  let Q : Ideal (NumberField.RingOfIntegers C) := P.comap e0
  have hQ : Q ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal 3)
      (NumberField.RingOfIntegers C) := by
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.rationalPrimeIdeal 3) := hP.2
    exact ⟨inferInstance, inferInstance⟩
  calc
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal 3) P =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal 3) Q := by
      symm
      exact (Ideal.rationalPrimeIdeal 3).ramificationIdx_comap_eq e0 P
    _ = 3 := nine_subfield_ramification Q hQ

theorem rational_nine_away
    {q : ℕ} (hq : Nat.Prime q) (hq3 : q ≠ 3) :
    RationalPrimeUnramified
      (S := NumberField.RingOfIntegers rationalNineCubic) q := by
  let K := CyclotomicField 9 ℚ
  let C := nineCubicSubfield
  letI : NeZero (9 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (9 : ℚ) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  letI : IsCyclotomicExtension {9} ℚ K :=
    CyclotomicField.isCyclotomicExtension 9 ℚ
  letI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois (S := {9}) (K := ℚ) (L := K)
  letI : IsGalois ℚ C := nine_subfield_spec.2
  have hqndvd : ¬ q ∣ 9 := by
    intro h
    have hqeq : q = 3 := by
      have hqpow : q ∣ 3 ^ 2 := by simpa using h
      have hqdiv3 : q ∣ 3 := hq.dvd_of_dvd_pow hqpow
      exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hqdiv3
    exact hq3 hqeq
  have hKunram : RationalPrimeUnramified
      (S := NumberField.RingOfIntegers K) q := by
    intro P hP
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hP.2
    calc
      Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P =
          (Ideal.rationalPrimeIdeal q).ramificationIdxIn
            (NumberField.RingOfIntegers K) := by
        exact (Ideal.ramificationIdxIn_eq_ramificationIdx
          (p := Ideal.rationalPrimeIdeal q) (P := P) (G := Gal(K/ℚ))).symm
      _ = 1 := by
        simpa [Ideal.rationalPrimeIdeal] using
          IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd
            (m := 9) (p := q) (K := K) hqndvd
  have hCunram : RationalPrimeUnramified
      (S := NumberField.RingOfIntegers C) q :=
    rational_unramified_intermediate C hq hKunram
  let D := rationalNineCubic
  let e : C ≃ₐ[ℚ] D := by
    simpa [C, D, rationalNineCubic] using
      IntermediateField.equivMap C (rationalCyclotomicEmbedding 9)
  exact rational_unramified_alg e hCunram

/-- The canonical cyclic cubic subfield of `ℚ(ζ_r)`, transported into the
fixed algebraic closure. -/
noncomputable def rationalCyclotomicCubic
    (r : ℕ) (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) :
    IntermediateField ℚ (AlgebraicClosure ℚ) := by
  letI : NeZero r := ⟨hrp.ne_zero⟩
  letI : NeZero (r : ℚ) := ⟨Nat.cast_ne_zero.mpr hrp.ne_zero⟩
  letI : IsCyclotomicExtension {r} ℚ (CyclotomicField r ℚ) :=
    CyclotomicField.isCyclotomicExtension r ℚ
  exact
    (galoisCubicSubfield (K := CyclotomicField r ℚ) hrp hr3).map
      (rationalCyclotomicEmbedding r)

noncomputable instance instNumberCubic
    (r : ℕ) (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) :
    NumberField ↑(rationalCyclotomicCubic r hrp hr3) := by
  letI : NeZero r := ⟨hrp.ne_zero⟩
  letI : NeZero (r : ℚ) := ⟨Nat.cast_ne_zero.mpr hrp.ne_zero⟩
  letI : IsCyclotomicExtension {r} ℚ (CyclotomicField r ℚ) :=
    CyclotomicField.isCyclotomicExtension r ℚ
  let C : IntermediateField ℚ (CyclotomicField r ℚ) :=
    galoisCubicSubfield (K := CyclotomicField r ℚ) hrp hr3
  letI : NumberField ↑C := inferInstance
  let e : ↑C ≃ₐ[ℚ] ↑(rationalCyclotomicCubic r hrp hr3) := by
    simpa [rationalCyclotomicCubic, C] using
      (IntermediateField.equivMap C (rationalCyclotomicEmbedding r))
  exact NumberField.of_ringEquiv
    (K := ↑C)
    (L := ↑(rationalCyclotomicCubic r hrp hr3))
    e.toRingEquiv

theorem rational_cubic_galois
    (r : ℕ) (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) :
    CyclicCubicQ
      ↑(rationalCyclotomicCubic r hrp hr3) := by
  letI : NeZero r := ⟨hrp.ne_zero⟩
  letI : NeZero (r : ℚ) := ⟨Nat.cast_ne_zero.mpr hrp.ne_zero⟩
  letI : IsCyclotomicExtension {r} ℚ (CyclotomicField r ℚ) :=
    CyclotomicField.isCyclotomicExtension r ℚ
  let C : IntermediateField ℚ (CyclotomicField r ℚ) :=
    galoisCubicSubfield (K := CyclotomicField r ℚ) hrp hr3
  letI : Algebra ℚ ↑C := C.algebra'
  let e : ↑C ≃ₐ[ℚ] ↑(rationalCyclotomicCubic r hrp hr3) := by
    simpa [rationalCyclotomicCubic, C] using
      (IntermediateField.equivMap C (rationalCyclotomicEmbedding r))
  rcases galois_subfield_spec
    (K := CyclotomicField r ℚ) hrp hr3 with ⟨hdegree, hgalois⟩
  letI : IsGalois ℚ ↑C := hgalois
  have hdegree' :
      Module.finrank ℚ ↑(rationalCyclotomicCubic r hrp hr3) = 3 := by
    rw [← e.toLinearEquiv.finrank_eq, hdegree]
  have hgalois' :
      IsGalois ℚ ↑(rationalCyclotomicCubic r hrp hr3) :=
    IsGalois.of_algEquiv e
  have hcyclicC : IsCyclic Gal(↑C/ℚ) := by
    have hcard : Nat.card Gal(↑C/ℚ) = 3 := by
      rw [IsGalois.card_aut_eq_finrank, hdegree]
    exact isCyclic_of_prime_card hcard
  have hcyclic :
      IsCyclic Gal(↑(rationalCyclotomicCubic r hrp hr3)/ℚ) := by
    letI : IsCyclic Gal(↑C/ℚ) := hcyclicC
    exact isCyclic_of_surjective
      (AlgEquiv.autCongr e) (AlgEquiv.autCongr e).surjective
  exact ⟨hdegree', hgalois', hcyclic⟩

theorem cubic_ramification_idx
    (r : ℕ) (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) :
    RationalRamificationIdx
      (S := 𝓞 ↑(rationalCyclotomicCubic r hrp hr3)) r 3 := by
  letI : NeZero r := ⟨hrp.ne_zero⟩
  letI : NeZero (r : ℚ) := ⟨Nat.cast_ne_zero.mpr hrp.ne_zero⟩
  letI : IsCyclotomicExtension {r} ℚ (CyclotomicField r ℚ) :=
    CyclotomicField.isCyclotomicExtension r ℚ
  let C : IntermediateField ℚ (CyclotomicField r ℚ) :=
    galoisCubicSubfield (K := CyclotomicField r ℚ) hrp hr3
  letI : Algebra ℚ ↑C := C.algebra'
  let e : ↑C ≃ₐ[ℚ] ↑(rationalCyclotomicCubic r hrp hr3) := by
    simpa [rationalCyclotomicCubic, C] using
      (IntermediateField.equivMap C (rationalCyclotomicEmbedding r))
  let e0 : 𝓞 ↑C ≃ₐ[ℤ]
      𝓞 ↑(rationalCyclotomicCubic r hrp hr3) :=
    (e.restrictScalars ℤ).mapIntegralClosure
  intro P hP
  let Q : Ideal (𝓞 ↑C) := P.comap e0
  have hQ : Q ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal r) (𝓞 ↑C) := by
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.rationalPrimeIdeal r) := hP.2
    exact ⟨inferInstance, inferInstance⟩
  calc
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) Q := by
          symm
          exact (Ideal.rationalPrimeIdeal r).ramificationIdx_comap_eq e0 P
    _ = 3 :=
      subfield_ramification_idx
        (K := CyclotomicField r ℚ) hrp hr3 Q hQ

theorem rational_unramified_away
    (r : ℕ) (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3])
    {q : ℕ} (hqp : Nat.Prime q) (hqr : q ≠ r) :
    RationalPrimeUnramified
      (S := 𝓞 ↑(rationalCyclotomicCubic r hrp hr3)) q := by
  letI : NeZero r := ⟨hrp.ne_zero⟩
  letI : NeZero (r : ℚ) := ⟨Nat.cast_ne_zero.mpr hrp.ne_zero⟩
  letI : IsCyclotomicExtension {r} ℚ (CyclotomicField r ℚ) :=
    CyclotomicField.isCyclotomicExtension r ℚ
  let C : IntermediateField ℚ (CyclotomicField r ℚ) :=
    galoisCubicSubfield (K := CyclotomicField r ℚ) hrp hr3
  letI : Algebra ℚ ↑C := C.algebra'
  let e : ↑C ≃ₐ[ℚ] ↑(rationalCyclotomicCubic r hrp hr3) := by
    simpa [rationalCyclotomicCubic, C] using
      (IntermediateField.equivMap C (rationalCyclotomicEmbedding r))
  let e0 : 𝓞 ↑C ≃ₐ[ℤ]
      𝓞 ↑(rationalCyclotomicCubic r hrp hr3) :=
    (e.restrictScalars ℤ).mapIntegralClosure
  intro P hP
  let Q : Ideal (𝓞 ↑C) := P.comap e0
  have hQ : Q ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q) (𝓞 ↑C) := by
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hP.2
    exact ⟨inferInstance, inferInstance⟩
  have hC := galois_subfield_away
    (K := CyclotomicField r ℚ) hrp hr3 hqp hqr Q hQ
  calc
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) Q := by
          symm
          simpa [Q] using
            (Ideal.ramificationIdx_comap_eq
              (R := ℤ) (S := 𝓞 ↑C)
              (S₁ := 𝓞 ↑(rationalCyclotomicCubic r hrp hr3))
              (p := Ideal.rationalPrimeIdeal q) e0 P)
    _ = 1 := hC

/--
For an arbitrary finite set `S` of rational primes, the maximal pro-`3`
extension of `ℚ` unramified outside `S`, constructed inside the fixed
algebraic closure.
-/
noncomputable def rationalTameIntermediate
    (S : Finset ℕ) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  ⨆ E : {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
      IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E S},
    E.1.toIntermediateField

/-- The field `ℚ_S(3)` for a finite tame rational ramification set `S`. -/
abbrev rationalTameExtension
    (S : Finset ℕ) :=
  ↥(rationalTameIntermediate S)

noncomputable instance instThreeExtension
    (S : Finset ℕ) :
    Field (rationalTameExtension S) :=
  inferInstance

noncomputable instance instRatExtension
    (S : Finset ℕ) :
    Algebra ℚ (rationalTameExtension S) :=
  (rationalTameIntermediate S).algebra

instance instRationalExtension
    (S : Finset ℕ) :
    Normal ℚ (rationalTameExtension S) := by
  simpa [rationalTameExtension, rationalTameIntermediate] using
    (IntermediateField.normal_iSup
      (F := ℚ) (K := AlgebraicClosure ℚ)
      (t := fun E : {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
          IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E S} =>
        E.1.toIntermediateField)
      (h := fun E => by
        letI : IsGalois ℚ E.1 := E.1.isGalois
        simpa using
          (IsGalois.to_normal (F := ℚ) (E := E.1))))

instance instSeparableExtension
    (S : Finset ℕ) :
    Algebra.IsSeparable ℚ (rationalTameExtension S) := by
  simpa [rationalTameExtension, rationalTameIntermediate] using
    (IntermediateField.isSeparable_iSup
      (F := ℚ) (E := AlgebraicClosure ℚ)
      (t := fun E : {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
          IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E S} =>
        E.1.toIntermediateField)
      (h := fun E => by
        letI : IsGalois ℚ E.1 := E.1.isGalois
        simpa using
          (IsGalois.to_isSeparable (F := ℚ) (E := E.1))))

instance instTameExtension
    (S : Finset ℕ) :
    IsGalois ℚ (rationalTameExtension S) := by
  exact ⟨⟩

/-- The group `G_S(ℚ)(3)` for a finite tame rational ramification set `S`. -/
abbrev rationalTameGalois
    (S : Finset ℕ) :=
  Gal(rationalTameExtension S/ℚ)

theorem rational_cubic_tame
    {S : Finset ℕ} {r : ℕ}
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) (hrS : r ∈ S) :
    rationalCyclotomicCubic r hrp hr3 ≤
      rationalTameIntermediate S := by
  let C := rationalCyclotomicCubic r hrp hr3
  have hC := rational_cubic_galois r hrp hr3
  let E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    { toIntermediateField := C
      finiteDimensional := inferInstance
      isGalois := by simpa [C] using hC.2.1 }
  letI : FiniteDimensional ℚ ↑E := E.finiteDimensional
  letI : IsGalois ℚ ↑E := E.isGalois
  have hPGroup : IsPGroup 3 Gal(E/ℚ) := by
    apply IsPGroup.of_card (n := 1)
    have hdegree : Module.finrank ℚ ↑E = 3 := by
      simpa [E, C] using hC.1
    simpa using
      (IsGalois.card_aut_eq_finrank (E := ↑E) (F := ℚ)).trans hdegree
  have hUnramified : UnramifiedOutside E S := by
    intro q hqp hqS
    have hqr : q ≠ r := by
      intro h
      exact hqS (h ▸ hrS)
    simpa [E, C, UnramifiedOutside] using
      rational_unramified_away r hrp hr3 hqp hqr
  let x :
      {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
        IsPGroup 3 Gal(E/ℚ) ∧ UnramifiedOutside E S} :=
    ⟨E, hPGroup, hUnramified⟩
  simpa [x, E, C, rationalTameIntermediate] using
    (le_iSup
      (fun E : {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
          IsPGroup 3 Gal(E/ℚ) ∧ UnramifiedOutside E S} =>
        E.1.toIntermediateField)
      x)

/-- The canonical cubic field at `r`, now regarded as an intermediate field of
the maximal tame pro-`3` extension. -/
noncomputable def rationalTameCubic
    (S : Finset ℕ) (r : ℕ)
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) (hrS : r ∈ S) :
    IntermediateField ℚ (rationalTameExtension S) :=
  (IntermediateField.inclusion
    (rational_cubic_tame hrp hr3 hrS)).fieldRange

noncomputable instance instTameCubic
    (S : Finset ℕ) (r : ℕ)
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) (hrS : r ∈ S) :
    NumberField ↑(rationalTameCubic S r hrp hr3 hrS) := by
  let C := rationalCyclotomicCubic r hrp hr3
  let D := rationalTameCubic S r hrp hr3 hrS
  let e : ↑C ≃ₐ[ℚ] ↑D := by
    exact AlgEquiv.ofInjectiveField
      (IntermediateField.inclusion
        (rational_cubic_tame hrp hr3 hrS))
  exact NumberField.of_ringEquiv (K := ↑C) (L := ↑D) e.toRingEquiv

theorem rational_tame_galois
    (S : Finset ℕ) (r : ℕ)
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) (hrS : r ∈ S) :
    CyclicCubicQ
      ↑(rationalTameCubic S r hrp hr3 hrS) := by
  let C := rationalCyclotomicCubic r hrp hr3
  let D := rationalTameCubic S r hrp hr3 hrS
  let e : ↑C ≃ₐ[ℚ] ↑D := by
    exact AlgEquiv.ofInjectiveField
      (IntermediateField.inclusion
        (rational_cubic_tame hrp hr3 hrS))
  have hC := rational_cubic_galois r hrp hr3
  letI : IsGalois ℚ ↑C := by simpa [C] using hC.2.1
  have hdegree : Module.finrank ℚ ↑D = 3 := by
    rw [← e.toLinearEquiv.finrank_eq, hC.1]
  have hgalois : IsGalois ℚ ↑D := IsGalois.of_algEquiv e
  have hcyclic : IsCyclic Gal(↑D/ℚ) := by
    letI : IsCyclic Gal(↑C/ℚ) := by simpa [C] using hC.2.2
    exact isCyclic_of_surjective
      (AlgEquiv.autCongr e) (AlgEquiv.autCongr e).surjective
  exact ⟨hdegree, hgalois, hcyclic⟩

/-- The open normal subgroup cutting out the canonical cubic field at `r`. -/
noncomputable def rationalTameNormal
    (S : Finset ℕ) (r : ℕ)
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) (hrS : r ∈ S) :
    OpenNormalSubgroup (rationalTameGalois S) := by
  let D := rationalTameCubic S r hrp hr3 hrS
  have hD := rational_tame_galois S r hrp hr3 hrS
  letI : IsGalois ℚ ↑D := hD.2.1
  exact
    { toOpenSubgroup :=
        { toSubgroup := D.fixingSubgroup
          isOpen' :=
            (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois D).2
              ⟨FiniteDimensional.of_finrank_eq_succ hD.1, hD.2.1⟩ |>.1 }
      isNormal' :=
        (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois D).2
          ⟨FiniteDimensional.of_finrank_eq_succ hD.1, hD.2.1⟩ |>.2 }

theorem rational_tame_idx
    (S : Finset ℕ) (r : ℕ)
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) (hrS : r ∈ S) :
    RationalRamificationIdx
      (S := 𝓞 ↑(rationalTameCubic S r hrp hr3 hrS)) r 3 := by
  let C := rationalCyclotomicCubic r hrp hr3
  let D := rationalTameCubic S r hrp hr3 hrS
  let e : ↑C ≃ₐ[ℚ] ↑D :=
    AlgEquiv.ofInjectiveField
      (IntermediateField.inclusion
        (rational_cubic_tame hrp hr3 hrS))
  let e0 : 𝓞 ↑C ≃ₐ[ℤ] 𝓞 ↑D :=
    (e.restrictScalars ℤ).mapIntegralClosure
  intro P hP
  let Q : Ideal (𝓞 ↑C) := P.comap e0
  have hQ : Q ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal r) (𝓞 ↑C) := by
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.rationalPrimeIdeal r) := hP.2
    exact ⟨inferInstance, inferInstance⟩
  calc
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) P =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal r) Q := by
          symm
          exact (Ideal.rationalPrimeIdeal r).ramificationIdx_comap_eq e0 P
    _ = 3 :=
      cubic_ramification_idx
        r hrp hr3 Q hQ

theorem rational_cubic_away
    (S : Finset ℕ) (r : ℕ)
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) (hrS : r ∈ S)
    {q : ℕ} (hqp : Nat.Prime q) (hqr : q ≠ r) :
    RationalPrimeUnramified
      (S := 𝓞 ↑(rationalTameCubic S r hrp hr3 hrS)) q := by
  let C := rationalCyclotomicCubic r hrp hr3
  let D := rationalTameCubic S r hrp hr3 hrS
  let e : ↑C ≃ₐ[ℚ] ↑D :=
    AlgEquiv.ofInjectiveField
      (IntermediateField.inclusion
        (rational_cubic_tame hrp hr3 hrS))
  let e0 : 𝓞 ↑C ≃ₐ[ℤ] 𝓞 ↑D :=
    (e.restrictScalars ℤ).mapIntegralClosure
  intro P hP
  let Q : Ideal (𝓞 ↑C) := P.comap e0
  have hQ : Q ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q) (𝓞 ↑C) := by
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hP.2
    exact ⟨inferInstance, inferInstance⟩
  calc
    Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) P =
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal q) Q := by
          symm
          simpa [Q] using
            (Ideal.ramificationIdx_comap_eq
              (R := ℤ) (S := 𝓞 ↑C) (S₁ := 𝓞 ↑D)
              (p := Ideal.rationalPrimeIdeal q) e0 P)
    _ = 1 :=
      rational_unramified_away r hrp hr3 hqp hqr Q hQ

theorem rational_tame_cubic
    (S : Finset ℕ) (r : ℕ)
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) (hrS : r ∈ S) :
    IntermediateField.fixedField
        (rationalTameNormal S r hrp hr3 hrS :
          Subgroup (rationalTameGalois S)) =
      rationalTameCubic S r hrp hr3 hrS := by
  let D := rationalTameCubic S r hrp hr3 hrS
  letI : IsGalois ℚ ↑D :=
    (rational_tame_galois S r hrp hr3 hrS).2.1
  simpa [rationalTameNormal, D] using
    (InfiniteGalois.fixedField_fixingSubgroup D)

theorem rational_tame_card
    (S : Finset ℕ) (r : ℕ)
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) (hrS : r ∈ S) :
    Nat.card
        Gal(↑(IntermediateField.fixedField
          (rationalTameNormal S r hrp hr3 hrS :
            Subgroup (rationalTameGalois S))) / ℚ) = 3 := by
  rw [rational_tame_cubic]
  have hD := rational_tame_galois S r hrp hr3 hrS
  letI : IsGalois ℚ
      ↑(rationalTameCubic S r hrp hr3 hrS) := hD.2.1
  rw [IsGalois.card_aut_eq_finrank]
  exact hD.1

/--
The closed subgroup attached to an open-normal finite quotient of
`G_S(ℚ)(3)`.
-/
def rationalTameClosed
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    ClosedSubgroup (rationalTameGalois S) where
  toSubgroup := N
  isClosed' := N.toOpenSubgroup.isClosed

/--
The finite Galois layer of `ℚ_S(3)` fixed by an open-normal subgroup of
`G_S(ℚ)(3)`.
-/
abbrev rationalTameLayer
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :=
  ↥(IntermediateField.fixedField
    (rationalTameClosed S N).1)

/-- The finite layer, transported from the maximal tame extension back into
the fixed algebraic closure of `ℚ`. -/
noncomputable def rationalLayerClosure
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  (IntermediateField.fixedField
      (rationalTameClosed S N).1).map
    (rationalTameIntermediate S).val

/-- Transporting a finite layer into the fixed algebraic closure does not
change the field. -/
noncomputable def rationalTameClosure
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    rationalTameLayer S N ≃ₐ[ℚ]
      rationalLayerClosure S N :=
  IntermediateField.equivMap
    (IntermediateField.fixedField
      (rationalTameClosed S N).1)
    (rationalTameIntermediate S).val

instance instDimensionalClosure
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    FiniteDimensional ℚ (rationalLayerClosure S N) := by
  let H : ClosedSubgroup (rationalTameGalois S) :=
    rationalTameClosed S N
  have hsource : FiniteDimensional ℚ (rationalTameLayer S N) := by
    rw [← InfiniteGalois.isOpen_iff_finite
      (IntermediateField.fixedField H.1)]
    rw [InfiniteGalois.fixingSubgroup_fixedField H]
    exact N.toOpenSubgroup.isOpen
  letI : FiniteDimensional ℚ (rationalTameLayer S N) := hsource
  exact Module.Finite.equiv
    (rationalTameClosure S N).toLinearEquiv

instance instGaloisClosure
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    IsGalois ℚ (rationalLayerClosure S N) := by
  let H : ClosedSubgroup (rationalTameGalois S) :=
    rationalTameClosed S N
  letI : H.toSubgroup.Normal := by
    change (N : Subgroup (rationalTameGalois S)).Normal
    infer_instance
  letI : IsGalois ℚ (rationalTameLayer S N) :=
    IsGalois.of_fixedField_normal_subgroup H.1
  exact IsGalois.of_algEquiv
    (rationalTameClosure S N)

instance instTameClosure
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    NumberField (rationalLayerClosure S N) :=
  NumberField.of_module_finite ℚ (rationalLayerClosure S N)

set_option maxHeartbeats 3000000 in
-- A finite fixed field must first be trapped in a finite stage of the defining iSup.
set_option synthInstance.maxHeartbeats 500000 in
/-- Every finite fixed-field layer is unramified outside its defining set. -/
theorem rational_tame_outside
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    UnramifiedOutside (rationalLayerClosure S N) S := by
  classical
  let L := rationalLayerClosure S N
  let Component :=
    {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
      IsPGroup 3 Gal(E/ℚ) ∧ UnramifiedOutside E S}
  let family : Component → IntermediateField ℚ (AlgebraicClosure ℚ) :=
    fun E => E.1.toIntermediateField
  have hLle : L ≤ ⨆ E, family E := by
    change rationalLayerClosure S N ≤
      rationalTameIntermediate S
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.2
  have hLfg : L.FG := intermediate_fg_dimensional L
  obtain ⟨T, hLT⟩ :=
    intermediate_fg_i L hLfg family hLle
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := T.sup family
  have hLT' : L ≤ K := by
    rw [show K = T.sup family from rfl, finset_sup_bi]
    exact hLT
  letI : Algebra ℚ K := K.algebra'
  letI : FiniteDimensional ℚ K :=
    finset_sup_dimensional family T (fun E => E.1.finiteDimensional)
  letI : NumberField K := NumberField.of_module_finite ℚ K
  letI : IsGalois ℚ K :=
    finset_sup_galois family T (fun E => E.1.isGalois)
  let L' : IntermediateField ℚ K := L.restrict hLT'
  letI : Algebra ℚ L' := L'.algebra'
  let eL : L ≃ₐ[ℚ] L' := IntermediateField.restrict_algEquiv hLT'
  letI : FiniteDimensional ℚ L' := Module.Finite.equiv eL.toLinearEquiv
  letI : NumberField L' := NumberField.of_module_finite ℚ L'
  intro q hq hqS
  have hK : RationalPrimeUnramified
      (S := NumberField.RingOfIntegers K) q := by
    apply rational_finset_sup family
      (fun E => E.1.finiteDimensional)
      (fun E => E.1.isGalois) hq T
    intro E hET
    exact E.2.2 q hq hqS
  have hL' : RationalPrimeUnramified
      (S := NumberField.RingOfIntegers L') q :=
    rational_intermediate_canonical
      L' (by infer_instance) hq hK
  exact rational_unramified_alg eL.symm hL'

/-- Every finite layer has a finite `3`-group as its Galois group. -/
theorem rational_tame_closure
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S))
    (hpro : ProP.ProPGroup 3 (rationalTameGalois S)) :
    IsPGroup 3 Gal(rationalLayerClosure S N/ℚ) := by
  let H : ClosedSubgroup (rationalTameGalois S) :=
    rationalTameClosed S N
  letI : H.toSubgroup.Normal := by
    change (N : Subgroup (rationalTameGalois S)).Normal
    infer_instance
  let e : (rationalTameGalois S ⧸ N.toSubgroup) ≃*
      Gal(rationalLayerClosure S N/ℚ) :=
    (galoisFixedField H).trans
      (AlgEquiv.autCongr
        (rationalTameClosure S N))
  exact IsPGroup.of_equiv (hpro N) e

/-- A finite tame pro-`3` layer is linearly disjoint from `ℚ(ζ₃)`: their
degrees are respectively a power of `3` and `2`. -/
theorem rational_disjoint_cube
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S))
    (hpro : ProP.ProPGroup 3 (rationalTameGalois S)) :
    (rationalLayerClosure S N).LinearDisjoint
      rationalCubeField := by
  let L := rationalLayerClosure S N
  have hL : IsPGroup 3 Gal(L/ℚ) :=
    rational_tame_closure S N hpro
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hL
  have hdegreeL : Module.finrank ℚ L = 3 ^ n := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact hn
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  rw [hdegreeL, rational_cube_finrank]
  exact (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 3 2))

/-- The compositum of one finite tame pro-`3` layer with `ℚ(ζ₃)`. -/
noncomputable def rationalTameCompositum
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  rationalLayerClosure S N ⊔ rationalCubeField

instance instTameCompositum
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    FiniteDimensional ℚ (rationalTameCompositum S N) :=
  IntermediateField.finiteDimensional_sup
    (rationalLayerClosure S N) rationalCubeField

instance instCyclotomicCompositum
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    IsGalois ℚ (rationalTameCompositum S N) := by
  let hnormalL : Normal ℚ (rationalLayerClosure S N) :=
    (instGaloisClosure S N).to_normal
  let hseparableL : Algebra.IsSeparable ℚ
      (rationalLayerClosure S N) :=
    (instGaloisClosure S N).to_isSeparable
  let hnormalK : Normal ℚ rationalCubeField :=
    instRationalCube.to_normal
  let hseparableK : Algebra.IsSeparable ℚ rationalCubeField :=
    instRationalCube.to_isSeparable
  let hnormal : Normal ℚ (rationalTameCompositum S N) :=
    @IntermediateField.normal_sup ℚ (AlgebraicClosure ℚ)
      inferInstance inferInstance inferInstance
      (rationalLayerClosure S N) rationalCubeField
      hnormalL hnormalK
  let hseparable : Algebra.IsSeparable ℚ
      (rationalTameCompositum S N) :=
    @IntermediateField.isSeparable_sup ℚ (AlgebraicClosure ℚ)
      inferInstance inferInstance inferInstance
      (rationalLayerClosure S N) rationalCubeField
      hseparableL hseparableK
  exact { to_isSeparable := hseparable, to_normal := hnormal }

instance instNumberCompositum
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    NumberField (rationalTameCompositum S N) :=
  NumberField.of_module_finite ℚ (rationalTameCompositum S N)

set_option synthInstance.maxHeartbeats 200000 in
-- Extra heartbeats are needed to synthesize the nested intermediate-field tower instances.
set_option maxHeartbeats 2000000 in
-- The restricted scalar tower is finite, but finding that instance unfolds
-- several nested intermediate-field algebra structures.
/-- Inside the compositum, restriction identifies the Galois group over
`ℚ(ζ₃)` with the original finite-layer Galois group. -/
noncomputable def rationalTameCyclotomic
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S))
    (hpro : ProP.ProPGroup 3 (rationalTameGalois S)) :
    let M := rationalTameCompositum S N
    let L : IntermediateField ℚ M :=
      (rationalLayerClosure S N).restrict le_sup_left
    let K : IntermediateField ℚ M :=
      rationalCubeField.restrict le_sup_right
    Gal(M/K) ≃* Gal(L/ℚ) := by
  let M := rationalTameCompositum S N
  let L : IntermediateField ℚ M :=
    (rationalLayerClosure S N).restrict le_sup_left
  let K : IntermediateField ℚ M :=
    rationalCubeField.restrict le_sup_right
  have hsup : L ⊔ K = ⊤ := by
    apply (IntermediateField.lift_inj (L ⊔ K) ⊤).mp
    rw [IntermediateField.lift_sup ℚ M L K,
      IntermediateField.lift_restrict,
      IntermediateField.lift_restrict,
      IntermediateField.lift_top ℚ M]
    change rationalLayerClosure S N ⊔
      rationalCubeField = rationalTameCompositum S N
    rfl
  have hinf : L ⊓ K = ⊥ := by
    apply (IntermediateField.lift_inj (L ⊓ K) ⊥).mp
    rw [IntermediateField.lift_inf ℚ M L K,
      IntermediateField.lift_restrict,
      IntermediateField.lift_restrict,
      IntermediateField.lift_bot ℚ M]
    exact
      (rational_disjoint_cube S N hpro).inf_eq_bot
  have hLGalois : IsGalois ℚ L := by
    let hsource : IsGalois ℚ
        (rationalLayerClosure S N) :=
      instGaloisClosure S N
    exact @IsGalois.of_algEquiv ℚ
      (rationalLayerClosure S N)
      inferInstance inferInstance L inferInstance inferInstance inferInstance
      hsource
      (IntermediateField.restrict_algEquiv
        (show rationalLayerClosure S N ≤ M from le_sup_left))
  let eL : rationalLayerClosure S N ≃ₐ[ℚ] L :=
    IntermediateField.restrict_algEquiv
      (show rationalLayerClosure S N ≤ M from le_sup_left)
  let hLFinite : FiniteDimensional ℚ L :=
    Module.Finite.equiv eL.toLinearEquiv
  let hLNormal : Normal ℚ L := hLGalois.to_normal
  letI : Algebra K M := K.toAlgebra
  let hKMFinite : FiniteDimensional K M :=
    Module.Finite.of_restrictScalars_finite ℚ K M
  let hKMGalois : IsGalois K M :=
    @IsGalois.sup_right ℚ inferInstance M inferInstance inferInstance L K
      hLGalois hLFinite hsup
  exact @galoisCompositumEquiv ℚ M inferInstance inferInstance inferInstance
    L K hLNormal hLFinite hKMFinite hKMGalois hsup hinf

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed to synthesize the ramification tower instances.
set_option maxHeartbeats 3000000 in
-- Comparing ramification in the two compositum towers unfolds several
-- restricted intermediate-field algebra structures.
/-- Away from `S`, the cyclotomic compositum is unramified over the
cube-root field, including at the rational prime `3`. -/
theorem tame_unramified_outside
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S))
    (hpro : ProP.ProPGroup 3 (rationalTameGalois S))
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    let M := rationalTameCompositum S N
    let Kc : IntermediateField ℚ M :=
      rationalCubeField.restrict le_sup_right
    ∀ Q : Ideal (NumberField.RingOfIntegers M),
      ∀ (_ : Q.IsPrime) (_ : Q.LiesOver (Ideal.rationalPrimeIdeal q)),
        Q ≠ ⊥ →
          Algebra.IsUnramifiedAt
            (NumberField.RingOfIntegers Kc) Q := by
  let M := rationalTameCompositum S N
  let L0 := rationalLayerClosure S N
  let Lc : IntermediateField ℚ M := L0.restrict le_sup_left
  let Kc : IntermediateField ℚ M :=
    rationalCubeField.restrict le_sup_right
  dsimp only
  intro Q hQprime hQover hQ0
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver (Ideal.rationalPrimeIdeal q) := hQover
  letI : Algebra Kc M := Kc.toAlgebra
  letI : Algebra Lc M := Lc.toAlgebra
  letI : FiniteDimensional Kc M :=
    Module.Finite.of_restrictScalars_finite ℚ Kc M
  have hsup : Lc ⊔ Kc = ⊤ := by
    apply (IntermediateField.lift_inj (Lc ⊔ Kc) ⊤).mp
    rw [IntermediateField.lift_sup ℚ M Lc Kc,
      IntermediateField.lift_restrict,
      IntermediateField.lift_restrict,
      IntermediateField.lift_top ℚ M]
    rfl
  let eLc : L0 ≃ₐ[ℚ] Lc :=
    IntermediateField.restrict_algEquiv le_sup_left
  let eKc : rationalCubeField ≃ₐ[ℚ] Kc :=
    IntermediateField.restrict_algEquiv le_sup_right
  letI : FiniteDimensional ℚ Lc := Module.Finite.equiv eLc.toLinearEquiv
  letI : FiniteDimensional ℚ Kc := Module.Finite.equiv eKc.toLinearEquiv
  let hLcGalois : IsGalois ℚ Lc :=
    @IsGalois.of_algEquiv ℚ L0 inferInstance inferInstance Lc
      inferInstance inferInstance inferInstance
      (instGaloisClosure S N) eLc
  letI : IsGalois ℚ Lc := hLcGalois
  letI : IsGalois Kc M :=
    @IsGalois.sup_right ℚ inferInstance M inferInstance inferInstance Lc Kc
      hLcGalois (inferInstance : FiniteDimensional ℚ Lc) hsup
  letI : NumberField Kc := NumberField.of_module_finite ℚ Kc
  letI : NumberField Lc := NumberField.of_module_finite ℚ Lc
  have hL0p : IsPGroup 3 Gal(L0/ℚ) :=
    rational_tame_closure S N hpro
  have hLcp : IsPGroup 3 Gal(Lc/ℚ) :=
    hL0p.of_equiv eLc.autCongr
  have hMp : IsPGroup 3 Gal(M/Kc) :=
    hLcp.of_equiv
      (rationalTameCyclotomic S N hpro).symm
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hLcp
  have hfinLc : Module.finrank ℚ Lc = 3 ^ n := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact hn
  have hfinKc : Module.finrank ℚ Kc = 2 := by
    calc
      Module.finrank ℚ Kc = Module.finrank ℚ rationalCubeField :=
        LinearEquiv.finrank_eq eKc.symm.toLinearEquiv
      _ = 2 := rational_cube_finrank
  have hdisjoint : Lc.LinearDisjoint Kc := by
    apply IntermediateField.LinearDisjoint.of_finrank_coprime
    rw [hfinLc, hfinKc]
    exact Nat.Coprime.pow_left n (by norm_num)
  have hdegree : Module.finrank Lc M = 2 := by
    rw [hdisjoint.finrank_left_eq_finrank hsup, hfinKc]
  let R := Q.under (NumberField.RingOfIntegers Lc)
  let P := Q.under (NumberField.RingOfIntegers Kc)
  let qI := Ideal.rationalPrimeIdeal q
  letI : Q.LiesOver R := inferInstance
  letI : Q.LiesOver P := inferInstance
  letI : R.LiesOver qI := by
    rw [Ideal.liesOver_iff]
    simpa [R, qI, Ideal.under] using
      (show Q.LiesOver (Ideal.rationalPrimeIdeal q) from inferInstance).over
  letI : P.LiesOver qI := by
    rw [Ideal.liesOver_iff]
    simpa [P, qI, Ideal.under] using
      (show Q.LiesOver (Ideal.rationalPrimeIdeal q) from inferInstance).over
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  have hR0 : R ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqI0 R
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqI0 P
  letI : qI.IsMaximal := rational_ideal_maximal hq
  letI : R.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hR0
  letI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  have hL0Unramified : RationalPrimeUnramified
      (S := NumberField.RingOfIntegers L0) q :=
    rational_tame_outside S N q hq hqS
  have hLcUnramified : RationalPrimeUnramified
      (S := NumberField.RingOfIntegers Lc) q :=
    rational_unramified_alg eLc hL0Unramified
  have heR : qI.ramificationIdx R = 1 :=
    hLcUnramified R ⟨inferInstance, inferInstance⟩
  letI : NoZeroSMulDivisors (NumberField.RingOfIntegers Lc)
      (NumberField.RingOfIntegers M) := by
    refine ⟨?_⟩
    intro c x hcx
    exact smul_eq_zero.mp hcx
  have heRQ : R.ramificationIdx Q ≤ 2 := by
    rw [← hdegree]
    exact Ideal.ramificationIdx_le_finrank
      (NumberField.RingOfIntegers M) Lc M Q
  have htowerL :
      qI.ramificationIdx Q =
        qI.ramificationIdx R * R.ramificationIdx Q :=
    Ideal.ramificationIdx_algebra_tower' qI R Q
  have heQabs : qI.ramificationIdx Q ≤ 2 := by
    rw [htowerL, heR, one_mul]
    exact heRQ
  have htowerK :
      qI.ramificationIdx Q =
        qI.ramificationIdx P * P.ramificationIdx Q :=
    Ideal.ramificationIdx_algebra_tower' qI P Q
  have hpositive : 0 < qI.ramificationIdx P :=
    Nat.pos_iff_ne_zero.mpr
      (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hqI0)
  have hmul : qI.ramificationIdx P * P.ramificationIdx Q ≤ 2 := by
    rw [← htowerK]
    exact heQabs
  have heRel : P.ramificationIdx Q ≤ 2 := by nlinarith
  exact number_unramified_group
    hMp Q hQ0 (by simpa [P] using heRel)

set_option synthInstance.maxHeartbeats 1000000 in
-- Extra heartbeats are needed to synthesize the local Brauer base-change instances.
set_option maxHeartbeats 6000000 in
/-- At a finite place of the cyclotomic base lying over a rational prime
outside `S`, the relative Brauer class attached to a finite central extension
has trivial localization. -/
theorem rational_change_not
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S))
    (hpro : ProP.ProPGroup 3 (rationalTameGalois S))
    {Q G : Type v} [Group Q] [Group G]
    (projection : Q →* G) (hprojection : Function.Surjective projection)
    (hcentral : projection.ker ≤ Subgroup.center Q)
    (galoisEquiv :
      let M := rationalTameCompositum S N
      let Kc : IntermediateField ℚ M :=
        rationalCubeField.restrict le_sup_right
      Gal(M/Kc) ≃* G)
    (kernelToUnits :
      let M := rationalTameCompositum S N
      projection.ker →* Mˣ)
    (hfixed :
      let M := rationalTameCompositum S N
      let Kc : IntermediateField ℚ M :=
        rationalCubeField.restrict le_sup_right
      ∀ sigma : Gal(M/Kc), ∀ z : projection.ker,
        sigma • kernelToUnits z = kernelToUnits z)
    (n : ℕ) [NeZero n] (hkernel : ∀ z : projection.ker, z ^ n = 1)
    {r : ℕ} (hr : Nat.Prime r) (hrS : r ∉ S)
    (P :
      let M := rationalTameCompositum S N
      let Kc : IntermediateField ℚ M :=
        rationalCubeField.restrict le_sup_right
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers Kc))
    (hPover : P.asIdeal.LiesOver (Ideal.rationalPrimeIdeal r))
    (placeAbove :
      let M := rationalTameCompositum S N
      let _Kc : IntermediateField ℚ M :=
        rationalCubeField.restrict le_sup_right
      Towers.CField.ICohomo.CompletionPlacesAbove
        (L := M) (FinitePlace.mk P).val) :
    let M := rationalTameCompositum S N
    let Kc : IntermediateField ℚ M :=
      rationalCubeField.restrict le_sup_right
    let v := (FinitePlace.mk P).val
    letI : Algebra Kc v.Completion :=
      Towers.NumberTheory.Milne.completionBaseAlgebra v
    Towers.CField.BGroups.brauerBaseChange Kc v.Completion
        (extensionRelativeBrauer projection hprojection hcentral
          galoisEquiv kernelToUnits hfixed : BrauerGroup Kc) = 1 := by
  let M := rationalTameCompositum S N
  let Kc : IntermediateField ℚ M :=
    rationalCubeField.restrict le_sup_right
  letI : Algebra Kc M := Kc.toAlgebra
  letI : FiniteDimensional Kc M :=
    Module.Finite.of_restrictScalars_finite ℚ Kc M
  let Lc : IntermediateField ℚ M :=
    (rationalLayerClosure S N).restrict le_sup_left
  have hsup : Lc ⊔ Kc = ⊤ := by
    apply (IntermediateField.lift_inj (Lc ⊔ Kc) ⊤).mp
    rw [IntermediateField.lift_sup ℚ M Lc Kc,
      IntermediateField.lift_restrict,
      IntermediateField.lift_restrict,
      IntermediateField.lift_top ℚ M]
    rfl
  let eLc : rationalLayerClosure S N ≃ₐ[ℚ] Lc :=
    IntermediateField.restrict_algEquiv le_sup_left
  letI : FiniteDimensional ℚ Lc := Module.Finite.equiv eLc.toLinearEquiv
  have hLcGalois : IsGalois ℚ Lc :=
    @IsGalois.of_algEquiv ℚ
      (rationalLayerClosure S N)
      inferInstance inferInstance Lc inferInstance inferInstance inferInstance
      (instGaloisClosure S N) eLc
  letI : IsGalois ℚ Lc := hLcGalois
  letI : IsGalois Kc M :=
    @IsGalois.sup_right ℚ inferInstance M inferInstance inferInstance Lc Kc
      hLcGalois (inferInstance : FiniteDimensional ℚ Lc) hsup
  letI : NumberField Kc := NumberField.of_module_finite ℚ Kc
  let v := (FinitePlace.mk P).val
  let W := Towers.CField.ICohomo.CompletionPlacesAbove
    (L := M) v
  letI : Fact v.IsNontrivial :=
    ⟨Towers.CField.Ideles.absolute_value_nontrivial
      P⟩
  letI : IsUltrametricDist v.Completion :=
    Towers.CField.Ideles.placeUltrametricDist
      P
  letI : Finite W :=
    Towers.NumberTheory.Milne.absolute_extensions_separable
      v
  letI : Nonempty W := ⟨placeAbove⟩
  letI : MulAction.IsPretransitive Gal(M/Kc) W :=
    Towers.NumberTheory.Milne.completion_above_pretransitive P
  have hUnramified :
      ∀ upperPrime : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers M),
        upperPrime.asIdeal.LiesOver P.asIdeal →
          Algebra.IsUnramifiedAt
            (NumberField.RingOfIntegers Kc) upperPrime.asIdeal := by
    intro upperPrime hUpperOver
    have hUpperRational : upperPrime.asIdeal.LiesOver
        (Ideal.rationalPrimeIdeal r) :=
      Ideal.LiesOver.trans upperPrime.asIdeal P.asIdeal
        (Ideal.rationalPrimeIdeal r)
    exact tame_unramified_outside S N hpro hr hrS
      upperPrime.asIdeal upperPrime.isPrime hUpperRational upperPrime.ne_bot
  have hdata : CyclicUnramifiedCompletion P placeAbove :=
    cyclic_unramified_completion P placeAbove
      hUnramified
  exact brauer_change_completion
    projection hprojection hcentral galoisEquiv kernelToUnits hfixed n hkernel
    P placeAbove hdata

/-- Every nonzero prime of the ring of integers of a number field lies over
a rational prime. -/
theorem number_field_lies
    (F : Type*) [Field F] [NumberField F]
    (P : Ideal (NumberField.RingOfIntegers F)) [P.IsPrime] (hP0 : P ≠ ⊥) :
    ∃ r : ℕ, Nat.Prime r ∧ P.LiesOver (Ideal.rationalPrimeIdeal r) := by
  let p0 : Ideal ℤ := Ideal.under ℤ P
  have hp0prime : p0.IsPrime :=
    Ideal.comap_isPrime (algebraMap ℤ (NumberField.RingOfIntegers F)) P
  have hp0ne : p0 ≠ ⊥ := by
    intro hp0
    apply hP0
    exact Ideal.eq_bot_of_comap_eq_bot
      (R := ℤ) (S := NumberField.RingOfIntegers F) (I := P) hp0
  let g : ℤ := Submodule.IsPrincipal.generator p0
  have hspan : Ideal.span ({g} : Set ℤ) = p0 :=
    Ideal.span_singleton_generator p0
  have hgne : g ≠ 0 := by
    intro hg0
    apply hp0ne
    rw [← hspan, hg0]
    simp
  have hgprimeIdeal : (Ideal.span ({g} : Set ℤ)).IsPrime := by
    simpa [hspan] using hp0prime
  have hgprime : Prime g :=
    (Ideal.span_singleton_prime hgne).1 hgprimeIdeal
  let r : ℕ := Int.natAbs g
  have hrprime : Nat.Prime r :=
    (Int.prime_iff_natAbs_prime).mp hgprime
  refine ⟨r, hrprime, Ideal.LiesOver.mk ?_⟩
  calc
    Ideal.rationalPrimeIdeal r = Ideal.span ({g} : Set ℤ) := by
      exact (Ideal.span_singleton_eq_span_singleton).2
        (Int.associated_natAbs g).symm
    _ = Ideal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) P := by
      simpa [r, p0, Ideal.under] using hspan

/--
The fixed-field inclusion associated to containment of open-normal subgroups.
The direction reverses because larger subgroups fix smaller fields.
-/
noncomputable def rationalTameInclusion
    {S : Finset ℕ}
    {M N : OpenNormalSubgroup (rationalTameGalois S)}
    (hMN : M ≤ N) :
    rationalTameLayer S N →ₐ[ℚ]
      rationalTameLayer S M := by
  apply IntermediateField.inclusion
  apply IntermediateField.fixedField_le
  exact hMN

/--
The corresponding descent map on rings of integers.
-/
noncomputable def rationalIntegersInclusion
    {S : Finset ℕ}
    {M N : OpenNormalSubgroup (rationalTameGalois S)}
    (hMN : M ≤ N) :
    NumberField.RingOfIntegers (rationalTameLayer S N) →+*
      NumberField.RingOfIntegers (rationalTameLayer S M) :=
  NumberField.RingOfIntegers.mapRingHom
    (rationalTameInclusion hMN).toRingHom

instance instDimensionalTame
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    FiniteDimensional ℚ (rationalTameLayer S N) := by
  let H : ClosedSubgroup (rationalTameGalois S) :=
    rationalTameClosed S N
  have hfix :
      (IntermediateField.fixedField H.1).fixingSubgroup = H.1 := by
    exact InfiniteGalois.fixingSubgroup_fixedField H
  rw [← InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField H.1)]
  rw [hfix]
  exact N.toOpenSubgroup.isOpen

instance instRationalTame
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    IsGalois ℚ (rationalTameLayer S N) := by
  let H : ClosedSubgroup (rationalTameGalois S) :=
    rationalTameClosed S N
  letI : H.toSubgroup.Normal := by
    change (N : Subgroup (rationalTameGalois S)).Normal
    infer_instance
  exact IsGalois.of_fixedField_normal_subgroup H.1

instance instNumberTame
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    NumberField (rationalTameLayer S N) :=
  NumberField.of_module_finite ℚ (rationalTameLayer S N)

/-- The abstract fixed-field model of a finite layer is likewise unramified
outside its defining set. -/
theorem rational_unramified_outside
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    UnramifiedOutside (rationalTameLayer S N) S := by
  intro q hq hqS
  exact rational_unramified_alg
    (rationalTameClosure S N).symm
    (rational_tame_outside S N q hq hqS)

theorem rational_ramification_idx
    (S : Finset ℕ) (r : ℕ)
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) (hrS : r ∈ S) :
    RationalRamificationIdx
      (S := 𝓞 (rationalTameLayer S
        (rationalTameNormal S r hrp hr3 hrS))) r 3 := by
  change RationalRamificationIdx
    (S := 𝓞 ↑(IntermediateField.fixedField
      (rationalTameNormal S r hrp hr3 hrS :
        Subgroup (rationalTameGalois S)))) r 3
  rw [rational_tame_cubic]
  exact rational_tame_idx
    S r hrp hr3 hrS

theorem rational_tame_away
    (S : Finset ℕ) (r : ℕ)
    (hrp : Nat.Prime r) (hr3 : r ≡ 1 [MOD 3]) (hrS : r ∈ S)
    {q : ℕ} (hqp : Nat.Prime q) (hqr : q ≠ r) :
    RationalPrimeUnramified
      (S := 𝓞 (rationalTameLayer S
        (rationalTameNormal S r hrp hr3 hrS))) q := by
  change RationalPrimeUnramified
    (S := 𝓞 ↑(IntermediateField.fixedField
      (rationalTameNormal S r hrp hr3 hrS :
        Subgroup (rationalTameGalois S)))) q
  rw [rational_tame_cubic]
  exact rational_cubic_away
    S r hrp hr3 hrS hqp hqr

/--
The canonical finite-layer quotient map from `G_S(ℚ)(3)` to one open-normal
quotient.
-/
def rationalTameQuotient
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    rationalTameGalois S →*
      rationalTameGalois S ⧸ N.toSubgroup :=
  QuotientGroup.mk' N.toSubgroup

/--
The Galois-theoretic identification of an open-normal quotient of
`G_S(ℚ)(3)` with the Galois group of its fixed finite layer.
-/
noncomputable def rationalTameEquiv
    (S : Finset ℕ)
    (N : OpenNormalSubgroup (rationalTameGalois S)) :
    rationalTameGalois S ⧸ N.toSubgroup ≃*
      Gal(rationalTameLayer S N / ℚ) := by
  let H : ClosedSubgroup (rationalTameGalois S) :=
    rationalTameClosed S N
  letI : H.toSubgroup.Normal := by
    change (N : Subgroup (rationalTameGalois S)).Normal
    infer_instance
  exact galoisFixedField H

/--
Finite-layer certificates saying that a displayed element of `G_S(ℚ)(3)` is a
tame inertia generator at a displayed rational prime.

The `mapsFiniteLayer` field is the important constraint: in every finite
Galois layer, the image of the displayed ambient element is identified with a
generator of the inertia subgroup at a prime over `prime`.
-/
structure RationalInertiaData
    (S : Finset ℕ)
    (prime : ℕ)
    (generator : rationalTameGalois S) where
  prime_mem :
    prime ∈ S
  primeAbove :
    ∀ N : OpenNormalSubgroup (rationalTameGalois S),
      Ideal (NumberField.RingOfIntegers (rationalTameLayer S N))
  primeAbove_mem :
    ∀ N : OpenNormalSubgroup (rationalTameGalois S),
      primeAbove N ∈
        Ideal.primesOver
          (Ideal.rationalPrimeIdeal prime)
          (NumberField.RingOfIntegers (rationalTameLayer S N))
  primeAbove_comap :
    ∀ {M N : OpenNormalSubgroup (rationalTameGalois S)}
      (hMN : M ≤ N),
        Ideal.comap
            (rationalIntegersInclusion hMN)
            (primeAbove M) =
          primeAbove N
  inertiaGenerator :
    ∀ N : OpenNormalSubgroup (rationalTameGalois S),
      (primeAbove N).inertia
        (Gal(rationalTameLayer S N / ℚ))
  mapsFiniteLayer :
    ∀ N : OpenNormalSubgroup (rationalTameGalois S),
      rationalTameEquiv S N
          (rationalTameQuotient S N generator) =
        (inertiaGenerator N :
          Gal(rationalTameLayer S N / ℚ))
  inertiaGenerator_generates :
    ∀ N : OpenNormalSubgroup (rationalTameGalois S),
      Subgroup.closure
          ({(inertiaGenerator N :
            Gal(rationalTameLayer S N / ℚ))} : Set _) =
        (primeAbove N).inertia
          (Gal(rationalTameLayer S N / ℚ))

/--
The tame rational pro-`3` Koch relator attached to one rational prime.
With the project's commutator convention, this is
`x_i ^ (ℓ_i - 1) * ⁅x_i, y_i⁆`, i.e. the usual tame relation
`x_i ^ ℓ_i * y_i * x_i⁻¹ * y_i⁻¹`.
-/
def rationalTameRelator
    {d : ℕ}
    (free : ProP.FreeGroup.{u} 3 d)
    (prime : Fin d → ℕ)
    (frobeniusLift : Fin d → free.Carrier)
    (i : Fin d) :
    free.Carrier :=
  free.generator i ^ (prime i - 1) *
    ⁅free.generator i, frobeniusLift i⁆

/--
The lifted tame local relation in a target group after applying a homomorphism
from the free source.

Here `αE (free.generator i)` is the prescribed lift of tame inertia at
`prime i`, and `αE (frobeniusLift i)` is the prescribed lift of Frobenius.
-/
def RationalLiftedRelation
    {d : ℕ}
    (free : ProP.FreeGroup.{u} 3 d)
    (prime : Fin d → ℕ)
    (frobeniusLift : Fin d → free.Carrier)
    {E : Type v}
    [Group E]
    (αE : free.Carrier →* E)
    (i : Fin d) :
    Prop :=
  αE (free.generator i) ^ (prime i - 1) *
      ⁅αE (free.generator i), αE (frobeniusLift i)⁆ =
    1

/--
Killing one Koch relator is exactly the lifted tame local relation for the
corresponding prescribed inertia/Frobenius lifts.
-/
theorem killed_lifted_relation
    {d : ℕ}
    (free : ProP.FreeGroup.{u} 3 d)
    (prime : Fin d → ℕ)
    (frobeniusLift : Fin d → free.Carrier)
    {E : Type v}
    [Group E]
    (αE : free.Carrier →* E)
    (i : Fin d) :
    αE
        (rationalTameRelator
          free
          prime
          frobeniusLift
          i) =
      1 ↔
        RationalLiftedRelation
          free
          prime
          frobeniusLift
          αE
          i := by
  simp [
    RationalLiftedRelation,
    rationalTameRelator,
    map_commutatorElement
  ]

/--
Killing all Koch relators is exactly satisfying the lifted tame local relation
at each indexed ramified prime.
-/
theorem killed_lifted_relations
    {d : ℕ}
    (free : ProP.FreeGroup.{u} 3 d)
    (prime : Fin d → ℕ)
    (frobeniusLift : Fin d → free.Carrier)
    {E : Type v}
    [Group E]
    (αE : free.Carrier →* E) :
    (∀ i : Fin d,
      αE
          (rationalTameRelator
            free
            prime
            frobeniusLift
            i) =
        1) ↔
      ∀ i : Fin d,
        RationalLiftedRelation
          free
          prime
          frobeniusLift
          αE
          i := by
  constructor
  · intro hkill i
    exact
      (killed_lifted_relation
        free
        prime
        frobeniusLift
        αE
        i).mp (hkill i)
  · intro hlocal i
    exact
      (killed_lifted_relation
        free
        prime
        frobeniusLift
        αE
        i).mpr (hlocal i)

/--
Data identifying an arbitrary finite tame rational prime set with a displayed
free pro-`3` quotient of `G_S(ℚ)(3)`, before choosing the Frobenius lifts that
will be used in the Koch relators.

This is the narrow `k = ℚ`, `p = 3`, `T = ∅`, no-wild-primes setting of the
Koch-Shafarevich local-relator theorem, but only the generator-side arithmetic
data is fixed here.
-/
structure RationalTameSetup
    {d : ℕ}
    (S : Finset ℕ)
    (free : ProP.FreeGroup.{u} 3 d)
    (quotientMap : free.Carrier →*
      rationalTameGalois S)
    (prime : Fin d → ℕ) where
  prime_range :
    Finset.univ.image prime = S
  prime_injective :
    Function.Injective prime
  prime_isPrime :
    ∀ i : Fin d, Nat.Prime (prime i)
  prime_mod_three :
    ∀ i : Fin d, prime i ≡ 1 [MOD 3]
  quotientMap_continuous :
    Continuous quotientMap
  quotientMap_surjective :
    Function.Surjective quotientMap
  target_pro_three :
    ProP.ProPGroup 3 (rationalTameGalois S)
  generators_tame_inertia :
    ∀ i : Fin d,
      RationalInertiaData
        S
        (prime i)
        (quotientMap (free.generator i))

/--
Data identifying an arbitrary finite tame rational prime set with a displayed
free pro-`3` Koch quotient of `G_S(ℚ)(3)`, after choosing Frobenius lifts in
the free source.

The final two semantic fields mark the arithmetic provenance of the displayed
Frobenius lifts and the resulting local tame relators.
-/
structure RationalKochSetup
    {d : ℕ}
    (S : Finset ℕ)
    (free : ProP.FreeGroup.{u} 3 d)
    (quotientMap : free.Carrier →*
      rationalTameGalois S)
    (prime : Fin d → ℕ)
    (frobeniusLift : Fin d → free.Carrier) where
  prime_range :
    Finset.univ.image prime = S
  prime_injective :
    Function.Injective prime
  prime_isPrime :
    ∀ i : Fin d, Nat.Prime (prime i)
  prime_mod_three :
    ∀ i : Fin d, prime i ≡ 1 [MOD 3]
  quotientMap_continuous :
    Continuous quotientMap
  quotientMap_surjective :
    Function.Surjective quotientMap
  target_pro_three :
    ProP.ProPGroup 3 (rationalTameGalois S)
  generators_tame_inertia :
    ∀ i : Fin d,
      RationalInertiaData
        S
        (prime i)
        (quotientMap (free.generator i))
  frobenius_lift_arithmetic :
    ∀ (i : Fin d)
      (N : OpenNormalSubgroup (rationalTameGalois S)),
      IsArithFrobAt ℤ
        (rationalTameEquiv S N
          (rationalTameQuotient S N
            (quotientMap (frobeniusLift i))))
        ((generators_tame_inertia i).primeAbove N)
  tame_maps_one :
    ∀ i : Fin d,
      quotientMap
          (rationalTameRelator
            free
            prime
            frobeniusLift
            i) =
          1

/-- A homomorphism from a cyclic group of order three, specified by the image
of a chosen generator. -/
noncomputable def cyclicGeneratorValue
    {G K : Type*} [Group G] [Group K]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcardG : Nat.card G = 3)
    (eK : Multiplicative (ZMod 3) ≃* K)
    (value : K) : G →* K := by
  let eG : Multiplicative (ZMod 3) ≃* G :=
    zmodMulEquivOfGenerator hg hcardG
  let z : ZMod 3 := (eK.symm value).toAdd
  let scale : Multiplicative (ZMod 3) →* Multiplicative (ZMod 3) :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft z)
  exact eK.toMonoidHom.comp (scale.comp eG.symm.toMonoidHom)

@[simp]
theorem cyclic_generator_value
    {G K : Type*} [Group G] [Group K]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcardG : Nat.card G = 3)
    (eK : Multiplicative (ZMod 3) ≃* K)
    (value : K) :
    cyclicGeneratorValue g hg hcardG eK value g = value := by
  simp [cyclicGeneratorValue]

set_option synthInstance.maxHeartbeats 100000 in
-- Extra heartbeats are needed for the finite-layer character construction.
/-- Cubic characters of `G_S(ℚ)(3)` can be assigned arbitrary values on the
displayed tame inertia generators.  The proof uses the independent cyclic
cubic cyclotomic field ramified at each displayed prime. -/
theorem rational_character_control
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    {frobeniusLift : Fin d → free.Carrier}
    (hsetup :
      RationalKochSetup
        S free quotientMap prime frobeniusLift)
    {K : Type v}
    [Group K]
    [TopologicalSpace K]
    [DiscreteTopology K]
    [Finite K]
    (eK : Multiplicative (ZMod 3) ≃* K)
    (values : Fin d → K) :
    ∃ chi : rationalTameGalois S →* K,
      Continuous chi ∧
        ∀ i : Fin d,
          chi (quotientMap (free.generator i)) = values i := by
  classical
  letI : IsCyclic K :=
    isCyclic_of_surjective eK eK.surjective
  letI : CommGroup K := IsCyclic.commGroup
  have hprime_mem (i : Fin d) : prime i ∈ S := by
    rw [← hsetup.prime_range]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  let N (i : Fin d) :
      OpenNormalSubgroup (rationalTameGalois S) :=
    rationalTameNormal S (prime i)
      (hsetup.prime_isPrime i) (hsetup.prime_mod_three i) (hprime_mem i)
  let layerMap (i : Fin d) :
      rationalTameGalois S →*
        Gal(rationalTameLayer S (N i) / ℚ) :=
    (rationalTameEquiv S (N i)).toMonoidHom.comp
      (rationalTameQuotient S (N i))
  let inertia (i : Fin d) :
      Gal(rationalTameLayer S (N i) / ℚ) :=
    (hsetup.generators_tame_inertia i).inertiaGenerator (N i)
  have hlayer_card (i : Fin d) :
      Nat.card Gal(rationalTameLayer S (N i) / ℚ) = 3 := by
    change
      Nat.card Gal(rationalTameLayer S
        (rationalTameNormal S (prime i)
          (hsetup.prime_isPrime i) (hsetup.prime_mod_three i)
            (hprime_mem i)) / ℚ) = 3
    exact rational_tame_card
      S (prime i) (hsetup.prime_isPrime i)
        (hsetup.prime_mod_three i) (hprime_mem i)
  have hinertia_top (i : Fin d) :
      ((hsetup.generators_tame_inertia i).primeAbove (N i)).inertia
          Gal(rationalTameLayer S (N i) / ℚ) = ⊤ := by
    let P :=
      (hsetup.generators_tame_inertia i).primeAbove (N i)
    have hP :=
      (hsetup.generators_tame_inertia i).primeAbove_mem (N i)
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.rationalPrimeIdeal (prime i)) := hP.2
    have hcard := inertia_ramification_idx
      (L := rationalTameLayer S (N i))
      (hsetup.prime_isPrime i) P
    have hram :=
      rational_ramification_idx
        S (prime i) (hsetup.prime_isPrime i)
          (hsetup.prime_mod_three i) (hprime_mem i) P hP
    apply Subgroup.eq_top_of_card_eq
    exact (hcard.trans hram).trans (hlayer_card i).symm
  have hinertia_generates (i : Fin d) :
      ∀ x : Gal(rationalTameLayer S (N i) / ℚ),
        x ∈ Subgroup.zpowers (inertia i) := by
    have hclosure :=
      (hsetup.generators_tame_inertia i).inertiaGenerator_generates
        (N i)
    have hclosure_top :
        Subgroup.closure ({inertia i} : Set
          Gal(rationalTameLayer S (N i) / ℚ)) = ⊤ := by
      exact hclosure.trans (hinertia_top i)
    have hzpowers : Subgroup.zpowers (inertia i) = ⊤ :=
      (Subgroup.zpowers_eq_closure (inertia i)).trans hclosure_top
    intro x
    rw [hzpowers]
    exact Subgroup.mem_top x
  let coordinate (i : Fin d) :
      rationalTameGalois S →* K :=
    (cyclicGeneratorValue
      (inertia i) (hinertia_generates i) (hlayer_card i) eK (values i)).comp
        (layerMap i)
  have hcoordinate (i j : Fin d) :
      coordinate i (quotientMap (free.generator j)) =
        if i = j then values j else 1 := by
    have hmaps :=
      (hsetup.generators_tame_inertia j).mapsFiniteLayer (N i)
    change
      cyclicGeneratorValue
          (inertia i) (hinertia_generates i) (hlayer_card i) eK (values i)
        (rationalTameEquiv S (N i)
          (rationalTameQuotient S (N i)
            (quotientMap (free.generator j)))) = _
    rw [hmaps]
    by_cases hij : i = j
    · subst j
      simp [inertia]
    · have hprime_ne : prime j ≠ prime i := by
        exact fun h => hij (hsetup.prime_injective h).symm
      let P :=
        (hsetup.generators_tame_inertia j).primeAbove (N i)
      have hP :=
        (hsetup.generators_tame_inertia j).primeAbove_mem (N i)
      letI : P.IsPrime := hP.1
      letI : P.LiesOver (Ideal.rationalPrimeIdeal (prime j)) := hP.2
      have hunram :=
        rational_tame_away
          S (prime i) (hsetup.prime_isPrime i)
            (hsetup.prime_mod_three i) (hprime_mem i)
            (hsetup.prime_isPrime j) hprime_ne
      have hinertia_bot :
          P.inertia Gal(rationalTameLayer S (N i) / ℚ) = ⊥ :=
        number_bot_unramified
          (rationalTameLayer S (N i))
          (hsetup.prime_isPrime j) hunram P
      have hinertia_one :
          ((hsetup.generators_tame_inertia j).inertiaGenerator
            (N i) : Gal(rationalTameLayer S (N i) / ℚ)) = 1 := by
        have hmem :=
          ((hsetup.generators_tame_inertia j).inertiaGenerator
            (N i)).property
        have hmem_bot :
            ((hsetup.generators_tame_inertia j).inertiaGenerator
                (N i) : Gal(rationalTameLayer S (N i) / ℚ)) ∈
              (⊥ : Subgroup Gal(rationalTameLayer S (N i) / ℚ)) := by
          rw [← hinertia_bot]
          exact hmem
        exact Subgroup.mem_bot.mp hmem_bot
      rw [hinertia_one, map_one]
      simp [hij]
  have hcoordinate_continuous (i : Fin d) : Continuous (coordinate i) := by
    letI : DiscreteTopology
        (rationalTameGalois S ⧸ (N i).toSubgroup) :=
      pro_discrete_topology (N i)
    letI : Finite
        (rationalTameGalois S ⧸ (N i).toSubgroup) :=
      pro_p_open (N i)
    let finiteMap :
        (rationalTameGalois S ⧸ (N i).toSubgroup) →* K :=
      (cyclicGeneratorValue
        (inertia i) (hinertia_generates i) (hlayer_card i) eK (values i)).comp
          (rationalTameEquiv S (N i)).toMonoidHom
    have hfiniteMap : Continuous finiteMap := continuous_of_discreteTopology
    exact hfiniteMap.comp continuous_quotient_mk'
  let chi : rationalTameGalois S →* K :=
    ∏ i : Fin d, coordinate i
  have hchi_apply (x : rationalTameGalois S) :
      chi x = ∏ i : Fin d, coordinate i x := by
    change (∏ i : Fin d, coordinate i) x = _
    exact MonoidHom.finsetProd_apply coordinate Finset.univ x
  refine ⟨chi, ?_, ?_⟩
  · rw [show (chi : rationalTameGalois S → K) =
        fun x => ∏ i : Fin d, coordinate i x by
          funext x
          exact hchi_apply x]
    exact continuous_finsetProd Finset.univ fun i _ =>
      hcoordinate_continuous i
  · intro j
    rw [hchi_apply]
    rw [Finset.prod_eq_single j]
    · simpa using hcoordinate j j
    · intro i _ hij
      rw [hcoordinate i j]
      simp [hij]
    · simp

/--
Target-side local arithmetic data for the rational tame pro-`3`
Koch-Shafarevich setup.

This is the genuinely arithmetic part of choosing Frobenius elements: it lives
in `G_S(ℚ)(3)` itself and says that those elements are arithmetic Frobenii in
every finite layer and satisfy the tame local relation there.  Lifting these
target-side elements to the free source is a separate formal consequence of
surjectivity of `quotientMap`.
-/
structure RationalTameData
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    (hsetup :
      RationalTameSetup
        S
        free
        quotientMap
        prime) where
  frobenius :
    Fin d → rationalTameGalois S
  frobenius_maps_arithmetic :
    ∀ (i : Fin d)
      (N : OpenNormalSubgroup (rationalTameGalois S)),
      IsArithFrobAt ℤ
        (rationalTameEquiv S N
          (rationalTameQuotient S N
            (frobenius i)))
        ((hsetup.generators_tame_inertia i).primeAbove N)
  tameRelation :
    ∀ i : Fin d,
      quotientMap (free.generator i) ^ (prime i - 1) *
          ⁅quotientMap (free.generator i), frobenius i⁆ =
        1

/-- The finite-quotient factorization property for one chosen Koch relator family. -/
def RationalTameFactorization
    {d : ℕ}
    (S : Finset ℕ)
    (free : ProP.FreeGroup.{u} 3 d)
    (quotientMap : free.Carrier →*
      rationalTameGalois S)
    (prime : Fin d → ℕ)
    (frobeniusLift : Fin d → free.Carrier) :
    Prop :=
  ∀ {P : Type v}
    [Group P]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P],
    (α : free.Carrier →* P) →
    Continuous α →
    IsPGroup 3 P →
    (∀ i : Fin d,
      α
          (rationalTameRelator
            free
            prime
            frobeniusLift
            i) =
        1) →
    quotientMap.ker ≤ α.ker

/-- A central group extension, represented by a surjective homomorphism. -/
structure CGExt
    {E A : Type*} [Group E] [Group A]
    (π : E →* A) : Prop where
  surjective : Function.Surjective π
  kernel_le_center : π.ker ≤ Subgroup.center E

/--
The conjugation action on the kernel of a homomorphism is trivial.

For a central extension this is the group-action content behind saying that
the kernel is a trivial module for the quotient/Galois action.
-/
def ConjugationActionTrivial
    {E A : Type*} [Group E] [Group A]
    (π : E →* A) : Prop :=
  ∀ e : E, ∀ k : π.ker, e * (k : E) * e⁻¹ = (k : E)

namespace CGExt

theorem conjugationActionTrivial
    {E A : Type*} [Group E] [Group A]
    {π : E →* A}
    (hπ : CGExt π) :
    ConjugationActionTrivial π := by
  intro e k
  have hkcenter : (k : E) ∈ Subgroup.center E :=
    hπ.kernel_le_center k.property
  have hcomm : e * (k : E) = (k : E) * e :=
    (Subgroup.mem_center_iff.mp hkcenter) e
  calc
    e * (k : E) * e⁻¹ = (k : E) * e * e⁻¹ := by
      rw [hcomm]
    _ = (k : E) := by
      simp [mul_assoc]

end CGExt

/--
A finite central extension of finite `3`-groups whose kernel is cubic.

The `kernel_card` field is the formal `C₃` input; below we also package it as
an explicit multiplicative equivalence with `ZMod 3`.
-/
structure CCGroups
    {E A : Type*} [Group E] [Finite E] [Group A] [Finite A]
    (π : E →* A) : Prop where
  surjective : Function.Surjective π
  domain_p_group : IsPGroup 3 E
  codomain_p_group : IsPGroup 3 A
  kernel_le_center : π.ker ≤ Subgroup.center E
  kernel_card : Nat.card π.ker = 3

namespace CCGroups

theorem centralGroupExtension
    {E A : Type*} [Group E] [Finite E] [Group A] [Finite A]
    {π : E →* A}
    (hπ : CCGroups π) :
    CGExt π :=
  ⟨hπ.surjective, hπ.kernel_le_center⟩

theorem conjugationActionTrivial
    {E A : Type*} [Group E] [Finite E] [Group A] [Finite A]
    {π : E →* A}
    (hπ : CCGroups π) :
    ConjugationActionTrivial π :=
  hπ.centralGroupExtension.conjugationActionTrivial

theorem kernel_isCyclic
    {E A : Type*} [Group E] [Finite E] [Group A] [Finite A]
    {π : E →* A}
    (hπ : CCGroups π) :
    IsCyclic π.ker := by
  exact isCyclic_of_prime_card hπ.kernel_card

theorem kernel_zmod_three
    {E A : Type*} [Group E] [Finite E] [Group A] [Finite A]
    {π : E →* A}
    (hπ : CCGroups π) :
    Nonempty (π.ker ≃* Multiplicative (ZMod 3)) := by
  classical
  refine ⟨?_⟩
  exact (zmodCyclicMulEquiv (G := π.ker) hπ.kernel_isCyclic).symm.trans
    (ZMod.ringEquivCongr hπ.kernel_card).toAddEquiv.toMultiplicative

end CCGroups

/--
A group embedding problem: lift `baseMap : Γ → A` through
`projection : E → A`.
-/
structure GEProble
    (Γ E A : Type*) [Group Γ] [Group E] [Group A] where
  projection : E →* A
  baseMap : Γ →* A

namespace GEProble

/-- A solution of an embedding problem is a lift through the projection. -/
def IsSolution
    {Γ E A : Type*} [Group Γ] [Group E] [Group A]
    (P : GEProble Γ E A)
    (lift : Γ →* E) : Prop :=
  P.projection.comp lift = P.baseMap

/-- An embedding problem is central when its projection is a central extension. -/
def IsCentral
    {Γ E A : Type*} [Group Γ] [Group E] [Group A]
    (P : GEProble Γ E A) : Prop :=
  CGExt P.projection

/--
The kernel is a trivial `F₃`-kernel: conjugation on the kernel is trivial and
the kernel is explicitly a copy of the order-`3` cyclic group.
-/
def TrivialF3
    {Γ E A : Type*} [Group Γ] [Group E] [Finite E] [Group A] [Finite A]
    (P : GEProble Γ E A) : Prop :=
  ConjugationActionTrivial P.projection ∧
    Nonempty (P.projection.ker ≃* Multiplicative (ZMod 3))

theorem central_cubic_extension
    {Γ E A : Type*} [Group Γ] [Group E] [Finite E] [Group A] [Finite A]
    (P : GEProble Γ E A)
    (hP : CCGroups P.projection) :
    P.IsCentral :=
  hP.centralGroupExtension

theorem trivial_f_3
    {Γ E A : Type*} [Group Γ] [Group E] [Finite E] [Group A] [Finite A]
    (P : GEProble Γ E A)
    (hP : CCGroups P.projection) :
    P.TrivialF3 :=
  ⟨hP.conjugationActionTrivial, hP.kernel_zmod_three⟩

end GEProble

/--
Twist a lift by a character valued in the central kernel.

If `β : Γ → E` is a lift and `χ : Γ → ker π`, then the pointwise product
`χ γ * β γ` is again a homomorphism exactly because `ker π` is central.
-/
def centralKernelTwist
    {Γ E A : Type*} [Group Γ] [Group E] [Group A]
    (π : E →* A)
    (β : Γ →* E)
    (χ : Γ →* π.ker)
    (hkernel_central : π.ker ≤ Subgroup.center E) :
    Γ →* E where
  toFun γ := (χ γ : E) * β γ
  map_one' := by
    simp
  map_mul' γ δ := by
    rw [map_mul, map_mul]
    change ((χ γ : E) * (χ δ : E)) * (β γ * β δ) =
      ((χ γ : E) * β γ) * ((χ δ : E) * β δ)
    have hcenter : (χ δ : E) ∈ Subgroup.center E :=
      hkernel_central (χ δ).property
    have hcomm : β γ * (χ δ : E) = (χ δ : E) * β γ :=
      (Subgroup.mem_center_iff.mp hcenter) (β γ)
    calc
      ((χ γ : E) * (χ δ : E)) * (β γ * β δ)
          = (χ γ : E) * ((χ δ : E) * β γ) * β δ := by
            simp [mul_assoc]
      _ = (χ γ : E) * (β γ * (χ δ : E)) * β δ := by
            rw [hcomm.symm]
      _ = ((χ γ : E) * β γ) * ((χ δ : E) * β δ) := by
            simp [mul_assoc]

theorem central_twist_projection
    {Γ E A : Type*} [Group Γ] [Group E] [Group A]
    {π : E →* A}
    (β : Γ →* E)
    (χ : Γ →* π.ker)
    (hkernel_central : π.ker ≤ Subgroup.center E) :
    π.comp (centralKernelTwist π β χ hkernel_central) = π.comp β := by
  ext γ
  change π ((χ γ : E) * β γ) = π (β γ)
  rw [map_mul]
  have hχ : π (χ γ : E) = 1 := (χ γ).property
  simp [hχ]

theorem twist_comp_values
    {Γ F E A : Type*} [Group Γ] [Group F] [Group E] [Group A]
    {π : E →* A}
    (β : Γ →* E)
    (χ : Γ →* π.ker)
    (hkernel_central : π.ker ≤ Subgroup.center E)
    (q : F →* Γ)
    (α : F →* E)
    (hvalues : ∀ x : F,
      (χ (q x) : E) * β (q x) = α x) :
    (centralKernelTwist π β χ hkernel_central).comp q = α := by
  ext x
  exact hvalues x

/--
Conditional twisting statement.

Assume a global lift `β₀` of `βA` already exists.  If there is a
kernel-valued character `χ` whose values give exactly the correction from
`β₀ ∘ q` to the prescribed source map `α`, then twisting `β₀` by `χ`
produces a global lift realizing `α` exactly.
-/
theorem twist_realizing_values
    {Γ F E A : Type*} [Group Γ] [Group F] [Group E] [Group A]
    (π : E →* A)
    (hkernel_central : π.ker ≤ Subgroup.center E)
    (βA : Γ →* A)
    (β₀ : Γ →* E)
    (hβ₀ : π.comp β₀ = βA)
    (q : F →* Γ)
    (α : F →* E)
    (χ : Γ →* π.ker)
    (hvalues : ∀ x : F,
      (χ (q x) : E) * β₀ (q x) = α x) :
    ∃ β : Γ →* E,
      π.comp β = βA ∧ β.comp q = α := by
  let β := centralKernelTwist π β₀ χ hkernel_central
  refine ⟨β, ?_, ?_⟩
  · rw [central_twist_projection, hβ₀]
  · exact
      twist_comp_values
        β₀
        χ
        hkernel_central
        q
        α
        hvalues

/--
Rational tame specialization of the conditional twisting statement.

This is the formal remaining step after local-global solvability has produced
some global lift: a kernel character with the prescribed correction values on
the free Koch source twists that lift into one realizing `αE` exactly.
-/
theorem realizes_prescribed_values
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {A E : Type v}
    [Group A]
    [Group E]
    (π : E →* A)
    (hkernel_central : π.ker ≤ Subgroup.center E)
    (βA : rationalTameGalois S →* A)
    (β₀ : rationalTameGalois S →* E)
    (hβ₀ : π.comp β₀ = βA)
    (αE : free.Carrier →* E)
    (χ : rationalTameGalois S →* π.ker)
    (hvalues : ∀ x : free.Carrier,
      (χ (quotientMap x) : E) * β₀ (quotientMap x) = αE x) :
    ∃ βE : rationalTameGalois S →* E,
      π.comp βE = βA ∧ βE.comp quotientMap = αE := by
  exact
    twist_realizing_values
      π
      hkernel_central
      βA
      β₀
      hβ₀
      quotientMap
      αE
      χ
      hvalues

/--
The formal twisting step in the central cubic proof.

If class-field theory has produced one global lift `β₀` of `βA` and a
kernel-valued character `χ` whose values correct `β₀` to the prescribed free
source lift on the displayed tame inertia generators, then twisting `β₀` by
`χ` gives the required global lift with the prescribed generator values.
-/
theorem rational_tame_character
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    {frobeniusLift : Fin d → free.Carrier}
    (_hsetup :
      RationalKochSetup
        S
        free
        quotientMap
        prime
        frobeniusLift)
    {A E : Type v}
    [Group A]
    [TopologicalSpace A]
    [DiscreteTopology A]
    [Finite A]
    [Group E]
    [TopologicalSpace E]
    [DiscreteTopology E]
    [Finite E]
    (π : E →* A)
    (_hπ : Function.Surjective π)
    (_hE : IsPGroup 3 E)
    (_hA : IsPGroup 3 A)
    (hkernel_central : π.ker ≤ Subgroup.center E)
    (_hkernel_card : Nat.card π.ker = 3)
    (αE : free.Carrier →* E)
    (_hαE : Continuous αE)
    (_hkill :
      ∀ i : Fin d,
        αE
            (rationalTameRelator
              free
              prime
              frobeniusLift
              i) =
          1)
    (βA : rationalTameGalois S →* A)
    (_hcompat : βA.comp quotientMap = π.comp αE)
    (β₀ : rationalTameGalois S →* E)
    (hβ₀_continuous : Continuous β₀)
    (hβ₀_lift : π.comp β₀ = βA)
    (χ : rationalTameGalois S →* π.ker)
    (hχ_continuous : Continuous χ)
    (hχ_values :
      ∀ i : Fin d,
        (χ (quotientMap (free.generator i)) : E) *
            β₀ (quotientMap (free.generator i)) =
          αE (free.generator i)) :
    ∃ βE : rationalTameGalois S →* E,
      Continuous βE ∧
        π.comp βE = βA ∧
          ∀ i : Fin d,
            βE (quotientMap (free.generator i)) =
              αE (free.generator i) := by
  letI : IsTopologicalGroup E := inferInstance
  let βE : rationalTameGalois S →* E :=
    centralKernelTwist π β₀ χ hkernel_central
  have hβE_continuous : Continuous βE := by
    change Continuous
      (fun γ : rationalTameGalois S =>
        (χ γ : E) * β₀ γ)
    exact (continuous_subtype_val.comp hχ_continuous).mul hβ₀_continuous
  refine ⟨βE, hβE_continuous, ?_, ?_⟩
  · dsimp [βE]
    rw [central_twist_projection, hβ₀_lift]
  · intro i
    dsimp [βE, centralKernelTwist]
    exact hχ_values i

/--
Central cubic solvability from the character-control package that CFT is
expected to supply.

The packaged hypothesis consists of a preliminary global lift and a continuous
kernel character with the prescribed correction values on the displayed tame
inertia generators.
-/
theorem rational_tame_control
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    {frobeniusLift : Fin d → free.Carrier}
    (hsetup :
      RationalKochSetup
        S
        free
        quotientMap
        prime
        frobeniusLift)
    {A E : Type v}
    [Group A]
    [TopologicalSpace A]
    [DiscreteTopology A]
    [Finite A]
    [Group E]
    [TopologicalSpace E]
    [DiscreteTopology E]
    [Finite E]
    (π : E →* A)
    (hπ : Function.Surjective π)
    (hE : IsPGroup 3 E)
    (hA : IsPGroup 3 A)
    (hkernel_central : π.ker ≤ Subgroup.center E)
    (hkernel_card : Nat.card π.ker = 3)
    (αE : free.Carrier →* E)
    (hαE : Continuous αE)
    (hkill :
      ∀ i : Fin d,
        αE
            (rationalTameRelator
              free
              prime
              frobeniusLift
              i) =
          1)
    (βA : rationalTameGalois S →* A)
    (hcompat : βA.comp quotientMap = π.comp αE)
    (hcontrol :
      ∃ β₀ : rationalTameGalois S →* E,
        Continuous β₀ ∧
          π.comp β₀ = βA ∧
            ∃ χ : rationalTameGalois S →* π.ker,
              Continuous χ ∧
                ∀ i : Fin d,
                  (χ (quotientMap (free.generator i)) : E) *
                      β₀ (quotientMap (free.generator i)) =
                    αE (free.generator i)) :
    ∃ βE : rationalTameGalois S →* E,
      Continuous βE ∧
        π.comp βE = βA ∧
          ∀ i : Fin d,
            βE (quotientMap (free.generator i)) =
              αE (free.generator i) := by
  rcases hcontrol with
    ⟨β₀, hβ₀_continuous, hβ₀_lift, χ, hχ_continuous, hχ_values⟩
  exact
    rational_tame_character
      hsetup
      π
      hπ
      hE
      hA
      hkernel_central
      hkernel_card
      αE
      hαE
      hkill
      βA
      hcompat
      β₀
      hβ₀_continuous
      hβ₀_lift
      χ
      hχ_continuous
      hχ_values

/--
The formal version of the bookkeeping sentence used below:

if `π : E →* A` is a central extension of finite `3`-groups with kernel `C₃`,
then any lifting problem through `π` is a central embedding problem whose
kernel is a trivial `F₃`-kernel.
-/
theorem embedding_problem_extension
    {Γ E A : Type*} [Group Γ] [Group E] [Finite E] [Group A] [Finite A]
    (π : E →* A)
    (baseMap : Γ →* A)
    (hπ : Function.Surjective π)
    (hE : IsPGroup 3 E)
    (hA : IsPGroup 3 A)
    (hkernel_central : π.ker ≤ Subgroup.center E)
    (hkernel_card : Nat.card π.ker = 3) :
    let P : GEProble Γ E A :=
      { projection := π, baseMap := baseMap }
    P.IsCentral ∧ P.TrivialF3 ∧
      CCGroups π := by
  intro P
  have hcentralCubic :
      CCGroups π :=
    ⟨hπ, hE, hA, hkernel_central, hkernel_card⟩
  exact
    ⟨P.central_cubic_extension hcentralCubic,
      P.trivial_f_3 hcentralCubic,
      hcentralCubic⟩

/-- Every subgroup of the center is normal. -/
lemma subgroup_normal_center
    {G : Type*} [Group G]
    (N : Subgroup G)
    (hN : N ≤ Subgroup.center G) :
    N.Normal := by
  constructor
  intro n hn g
  have hcomm : g * n = n * g :=
    (Subgroup.mem_center_iff.mp (hN hn)) g
  simpa [hcomm, mul_assoc] using hn

/--
A nontrivial finite `3`-group has a central subgroup of order `3`.

This is the purely group-theoretic reduction step used to peel off one central
cubic layer in the finite embedding-problem induction.
-/
lemma central_order_subgroup
    {P : Type v} [Group P] [Finite P] [Nontrivial P]
    (hP : IsPGroup 3 P) :
    ∃ C : Subgroup P,
      C ≤ Subgroup.center P ∧ Nat.card C = 3 := by
  classical
  have hcenterP : IsPGroup 3 (Subgroup.center P) :=
    hP.to_subgroup (Subgroup.center P)
  have hcenterNontrivial : Nontrivial (Subgroup.center P) :=
    hP.center_nontrivial
  have hcenterCardOneLt :
      1 < Nat.card (Subgroup.center P) :=
    Finite.one_lt_card_iff_nontrivial.mpr hcenterNontrivial
  have hdiv : 3 ∣ Nat.card (Subgroup.center P) := by
    rcases hcenterP.card_eq_or_dvd with hcenterCard | hcenterDiv
    · rw [hcenterCard] at hcenterCardOneLt
      exact False.elim ((Nat.lt_irrefl 1) hcenterCardOneLt)
    · exact hcenterDiv
  obtain ⟨z, hz⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 3 hdiv
  refine ⟨Subgroup.zpowers (z : P), ?_, ?_⟩
  · exact Subgroup.zpowers_le_of_mem z.property
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]

/--
Two continuous homomorphisms out of a topologically generated source are equal
once they agree on the chosen dense generating family.

This is the universe-polymorphic form needed here: the free pro-`3` source and
the finite target of the embedding problem may live in different universes.
-/
theorem ext_topologically_generates
    {F : Type u} {H : Type v}
    [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    {ι : Type*} {s : ι → F}
    (hs : ProP.TopologicallyGenerates s)
    (f g : ProP.ContinuousHom F H)
    (h : ∀ i, f (s i) = g (s i)) :
    f = g := by
  let E : Subgroup F :=
    { carrier := {x | f x = g x}
      one_mem' := by
        change f 1 = g 1
        rw [show f 1 = 1 from f.toMonoidHom.map_one,
          show g 1 = 1 from g.toMonoidHom.map_one]
      mul_mem' := by
        intro x y hx hy
        change f.toMonoidHom (x * y) = g.toMonoidHom (x * y)
        rw [map_mul, map_mul]
        change f.toMonoidHom x = g.toMonoidHom x at hx
        change f.toMonoidHom y = g.toMonoidHom y at hy
        rw [hx, hy]
      inv_mem' := by
        intro x hx
        change f.toMonoidHom x⁻¹ = g.toMonoidHom x⁻¹
        rw [map_inv, map_inv]
        change f.toMonoidHom x = g.toMonoidHom x at hx
        rw [hx] }
  have hEclosed : IsClosed (E : Set F) := by
    change IsClosed {x | f x = g x}
    exact isClosed_eq f.continuous_toFun g.continuous_toFun
  have hclosure : Subgroup.closure (Set.range s) ≤ E := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  have htop : (⊤ : Subgroup F) ≤ E := by
    rw [← hs]
    exact Subgroup.topologicalClosure_minimal _ hclosure hEclosed
  apply ProP.ContinuousHom.instFunLike.coe_injective'
  funext x
  change f x = g x
  exact htop (by simp)

/--
Formal descent from the finite-quotient Koch factorization property to the
prescribed central cubic embedding problem.

This lemma contains no class-field theory.  It says exactly what the
arithmetic input must provide: once every finite `3`-group shadow killing the
chosen Koch relators factors through `G_S(ℚ)(3)`, the prescribed lift `αE`
descends to the global Galois group.  The central cubic hypotheses are retained
because this is the interface needed by the embedding-problem induction, but
the proof itself only uses the resulting finite `3`-group target `E`.
-/
theorem rational_tame_factorization
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    {frobeniusLift : Fin d → free.Carrier}
    (hsetup :
      RationalKochSetup
        S
        free
        quotientMap
        prime
        frobeniusLift)
    (hfactor :
      ∀ {P : Type v}
        [Group P]
        [TopologicalSpace P]
        [DiscreteTopology P]
        [Finite P],
        (α : free.Carrier →* P) →
        Continuous α →
        IsPGroup 3 P →
        (∀ i : Fin d,
          α
              (rationalTameRelator
                free
                prime
                frobeniusLift
                i) =
            1) →
        quotientMap.ker ≤ α.ker)
    {A E : Type v}
    [Group A]
    [TopologicalSpace A]
    [DiscreteTopology A]
    [Finite A]
    [Group E]
    [TopologicalSpace E]
    [DiscreteTopology E]
    [Finite E]
    (π : E →* A)
    (_hπ : Function.Surjective π)
    (hE : IsPGroup 3 E)
    (_hA : IsPGroup 3 A)
    (_hkernel_central : π.ker ≤ Subgroup.center E)
    (_hkernel_card : Nat.card π.ker = 3)
    (αE : free.Carrier →* E)
    (hαE : Continuous αE)
    (hkill :
      ∀ i : Fin d,
        αE
            (rationalTameRelator
              free
              prime
              frobeniusLift
              i) =
          1)
    (βA : rationalTameGalois S →* A)
    (hcompat : βA.comp quotientMap = π.comp αE) :
    ∃ βE : rationalTameGalois S →* E,
      Continuous βE ∧
        π.comp βE = βA ∧
          ∀ i : Fin d,
            βE (quotientMap (free.generator i)) =
              αE (free.generator i) := by
  classical
  have hker : quotientMap.ker ≤ αE.ker :=
    hfactor (P := E) αE hαE hE hkill
  have hquot :
      Topology.IsQuotientMap quotientMap :=
    IsQuotientMap.of_surjective_continuous
      hsetup.quotientMap_surjective
      hsetup.quotientMap_continuous
  let βE : rationalTameGalois S →* E :=
    (quotientMap.liftOfSurjective hsetup.quotientMap_surjective)
      ⟨αE, hker⟩
  have hβE_comp : βE.comp quotientMap = αE :=
    MonoidHom.liftOfRightInverse_comp
      (f := quotientMap)
      (f_inv := Function.surjInv hsetup.quotientMap_surjective)
      (Function.rightInverse_surjInv hsetup.quotientMap_surjective)
      (g := (⟨αE, hker⟩ :
        {g : free.Carrier →* E // quotientMap.ker ≤ g.ker}))
  have hβE_continuous : Continuous βE := by
    apply hquot.continuous_iff.mpr
    change Continuous ((βE.comp quotientMap : free.Carrier →* E))
    rw [hβE_comp]
    exact hαE
  refine ⟨βE, hβE_continuous, ?_, ?_⟩
  · apply MonoidHom.ext
    intro γ
    rcases hsetup.quotientMap_surjective γ with ⟨x, rfl⟩
    calc
      (π.comp βE) (quotientMap x) =
          (π.comp (βE.comp quotientMap)) x := rfl
      _ = (π.comp αE) x := by
        rw [hβE_comp]
      _ = (βA.comp quotientMap) x := by
        rw [hcompat]
      _ = βA (quotientMap x) := rfl
  · intro i
    have h := congrArg (fun φ : free.Carrier →* E => φ (free.generator i)) hβE_comp
    exact h

/--
The base map in a compatible finite embedding problem is automa
continuous.  Continuity can be checked after pulling back along the quotient
map from the free pro-`3` source.
-/
theorem rational_compatible_continuous
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    {frobeniusLift : Fin d → free.Carrier}
    (hsetup :
      RationalKochSetup
        S
        free
        quotientMap
        prime
        frobeniusLift)
    {A E : Type v}
    [Group A]
    [TopologicalSpace A]
    [DiscreteTopology A]
    [Finite A]
    [Group E]
    [TopologicalSpace E]
    [DiscreteTopology E]
    [Finite E]
    (π : E →* A)
    (αE : free.Carrier →* E)
    (hαE : Continuous αE)
    (βA : rationalTameGalois S →* A)
    (hcompat : βA.comp quotientMap = π.comp αE) :
    Continuous βA := by
  have hquot : Topology.IsQuotientMap quotientMap :=
    IsQuotientMap.of_surjective_continuous
      hsetup.quotientMap_surjective
      hsetup.quotientMap_continuous
  apply hquot.continuous_iff.mpr
  change Continuous ((βA.comp quotientMap : free.Carrier →* A))
  rw [hcompat]
  have hπ : Continuous (π : E → A) :=
    continuous_of_discreteTopology
  exact hπ.comp hαE

/--
The open normal subgroup, and hence finite Galois layer, cut out by the base
map of a compatible finite embedding problem.
-/
noncomputable def rational_tame_open
    {S : Finset ℕ}
    {A : Type v}
    [Group A]
    [TopologicalSpace A]
    [DiscreteTopology A]
    [Finite A]
    (βA : rationalTameGalois S →* A)
    (hβA : Continuous βA) :
    OpenNormalSubgroup (rationalTameGalois S) where
  toSubgroup := βA.ker
  isOpen' := by
    change IsOpen (βA ⁻¹' ({1} : Set A))
    exact (isOpen_discrete {1}).preimage hβA

/--
The finite Galois layer cut out by `βA` has Galois group canonically
isomorphic to the range of `βA`.
-/
noncomputable def rational_tame_range
    {S : Finset ℕ}
    {A : Type v}
    [Group A]
    [TopologicalSpace A]
    [DiscreteTopology A]
    [Finite A]
    (βA : rationalTameGalois S →* A)
    (hβA : Continuous βA) :
    Gal(rationalTameLayer S
          (rational_tame_open βA hβA) / ℚ) ≃*
      βA.range :=
  (rationalTameEquiv S
      (rational_tame_open βA hβA)).symm.trans
    (QuotientGroup.quotientKerEquivRange βA)

/-- After adjoining `ζ₃`, the finite layer cut out by `βA` still has Galois
group canonically identified with the range of `βA`. -/
noncomputable def rational_cyclotomic_range
    {S : Finset ℕ}
    {A : Type v}
    [Group A]
    [TopologicalSpace A]
    [DiscreteTopology A]
    [Finite A]
    (βA : rationalTameGalois S →* A)
    (hβA : Continuous βA)
    (hpro : ProP.ProPGroup 3 (rationalTameGalois S)) :
    let N := rational_tame_open βA hβA
    let M := rationalTameCompositum S N
    let L0 := rationalLayerClosure S N
    let _L : IntermediateField ℚ M := L0.restrict le_sup_left
    let K : IntermediateField ℚ M :=
      rationalCubeField.restrict le_sup_right
    Gal(M/K) ≃* βA.range := by
  let N := rational_tame_open βA hβA
  let M := rationalTameCompositum S N
  let L0 := rationalLayerClosure S N
  let L : IntermediateField ℚ M := L0.restrict le_sup_left
  let K : IntermediateField ℚ M :=
    rationalCubeField.restrict le_sup_right
  let eRestrict : L0 ≃ₐ[ℚ] L :=
    IntermediateField.restrict_algEquiv
      (show L0 ≤ M from le_sup_left)
  exact
    (rationalTameCyclotomic S N hpro).trans
      ((AlgEquiv.autCongr eRestrict).symm.trans
        ((AlgEquiv.autCongr
          (rationalTameClosure S N)).symm.trans
            (rational_tame_range βA hβA)))

/-- The fiber product of a projection `E → A` and a base map `Γ → A`. -/
def embeddingPullbackSubgroup
    {Γ E A : Type*}
    [Group Γ]
    [Group E]
    [Group A]
    (π : E →* A)
    (βA : Γ →* A) :
    Subgroup (Γ × E) where
  carrier := {x | βA x.1 = π x.2}
  one_mem' := by simp
  mul_mem' := by
    rintro ⟨γ, e⟩ ⟨δ, f⟩ hγ hδ
    change βA (γ * δ) = π (e * f)
    rw [map_mul, map_mul, hγ, hδ]
  inv_mem' := by
    rintro ⟨γ, e⟩ hγ
    change βA γ⁻¹ = π e⁻¹
    rw [map_inv, map_inv, hγ]

/-- The group underlying the pullback central embedding problem. -/
abbrev CentralEmbeddingPullback
    {Γ E A : Type*}
    [Group Γ]
    [Group E]
    [Group A]
    (π : E →* A)
    (βA : Γ →* A) :=
  embeddingPullbackSubgroup π βA

/-- Projection of the pullback embedding problem to its base group. -/
def embeddingPullbackProjection
    {Γ E A : Type*}
    [Group Γ]
    [Group E]
    [Group A]
    (π : E →* A)
    (βA : Γ →* A) :
    CentralEmbeddingPullback π βA →* Γ :=
  (MonoidHom.fst Γ E).comp
    (embeddingPullbackSubgroup π βA).subtype

/-- The pullback projection is surjective whenever the original projection is
surjective. -/
theorem pullback_projection_surjective
    {Γ E A : Type*}
    [Group Γ]
    [Group E]
    [Group A]
    (π : E →* A)
    (hπ : Function.Surjective π)
    (βA : Γ →* A) :
    Function.Surjective (embeddingPullbackProjection π βA) := by
  intro γ
  obtain ⟨e, he⟩ := hπ (βA γ)
  exact ⟨⟨(γ, e), he.symm⟩, rfl⟩

/-- Pulling back a central extension preserves centrality of the kernel. -/
theorem embedding_pullback_projection
    {Γ E A : Type*}
    [Group Γ]
    [Group E]
    [Group A]
    (π : E →* A)
    (βA : Γ →* A)
    (hcentral : π.ker ≤ Subgroup.center E) :
    (embeddingPullbackProjection π βA).ker ≤
      Subgroup.center (CentralEmbeddingPullback π βA) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply Prod.ext
  · have hxfirst : x.1.1 = 1 := by
      exact MonoidHom.mem_ker.mp hx
    simp [hxfirst]
  · have hxpi : x.1.2 ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      have hmem := x.property
      have hxfirst : x.1.1 = 1 := MonoidHom.mem_ker.mp hx
      simpa [hxfirst] using hmem.symm
    exact Subgroup.mem_center_iff.mp (hcentral hxpi) y.1.2

/-- A lift through `π` gives a splitting of the pullback extension. -/
def pullbackSplittingLift
    {Γ E A : Type*}
    [Group Γ]
    [Group E]
    [Group A]
    (π : E →* A)
    (βA : Γ →* A)
    (βE : Γ →* E)
    (hβE : π.comp βE = βA) :
    Γ →* CentralEmbeddingPullback π βA where
  toFun γ := ⟨(γ, βE γ), by
    exact (DFunLike.congr_fun hβE γ).symm⟩
  map_one' := by ext <;> simp
  map_mul' γ δ := by ext <;> simp

@[simp]
theorem pullback_projection_splitting
    {Γ E A : Type*}
    [Group Γ]
    [Group E]
    [Group A]
    (π : E →* A)
    (βA : Γ →* A)
    (βE : Γ →* E)
    (hβE : π.comp βE = βA) :
    (embeddingPullbackProjection π βA).comp
        (pullbackSplittingLift π βA βE hβE) =
      MonoidHom.id Γ := by
  ext γ
  rfl

/-- A splitting of the pullback extension gives a lift through `π`. -/
def embeddingPullbackSplitting
    {Γ E A : Type*}
    [Group Γ]
    [Group E]
    [Group A]
    (π : E →* A)
    (βA : Γ →* A)
    (s : Γ →* CentralEmbeddingPullback π βA) :
    Γ →* E :=
  (MonoidHom.snd Γ E).comp
    ((embeddingPullbackSubgroup π βA).subtype.comp s)

theorem embedding_pullback_splitting
    {Γ E A : Type*}
    [Group Γ]
    [Group E]
    [Group A]
    (π : E →* A)
    (βA : Γ →* A)
    (s : Γ →* CentralEmbeddingPullback π βA)
    (hs : (embeddingPullbackProjection π βA).comp s =
      MonoidHom.id Γ) :
    π.comp (embeddingPullbackSplitting π βA s) = βA := by
  ext γ
  have hmem := (s γ).property
  change βA (s γ).1.1 = π (s γ).1.2 at hmem
  have hfirst := DFunLike.congr_fun hs γ
  change (s γ).1.1 = γ at hfirst
  simpa [embeddingPullbackSplitting, hfirst] using hmem.symm

/-- Compatible free-source maps assemble into the canonical map to the full
preimage of the finite quotient range.  Its values are the local inertia and
Frobenius lifts used in the central obstruction. -/
def tamePreimageLift
    {d : ℕ} {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    (quotientMap : free.Carrier →* rationalTameGalois S)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A) (alphaE : free.Carrier →* E)
    (betaA : rationalTameGalois S →* A)
    (hcompat : betaA.comp quotientMap = pi.comp alphaE) :
    free.Carrier →* centralExtensionPreimage pi betaA.range where
  toFun x :=
    ⟨alphaE x, by
      change pi (alphaE x) ∈ betaA.range
      have hx := DFunLike.congr_fun hcompat x
      change betaA (quotientMap x) = pi (alphaE x) at hx
      rw [← hx]
      exact ⟨quotientMap x, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp]
theorem rational_preimage_coe
    {d : ℕ} {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    (quotientMap : free.Carrier →* rationalTameGalois S)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A) (alphaE : free.Carrier →* E)
    (betaA : rationalTameGalois S →* A)
    (hcompat : betaA.comp quotientMap = pi.comp alphaE)
    (x : free.Carrier) :
    (tamePreimageLift quotientMap pi alphaE betaA hcompat x : E) =
      alphaE x :=
  rfl

@[simp]
theorem preimage_lift_projection
    {d : ℕ} {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    (quotientMap : free.Carrier →* rationalTameGalois S)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A) (alphaE : free.Carrier →* E)
    (betaA : rationalTameGalois S →* A)
    (hcompat : betaA.comp quotientMap = pi.comp alphaE)
    (x : free.Carrier) :
    centralPreimageProjection pi betaA.range
        (tamePreimageLift
          quotientMap pi alphaE betaA hcompat x) =
      betaA.rangeRestrict (quotientMap x) := by
  apply Subtype.ext
  have hx := DFunLike.congr_fun hcompat x
  exact hx.symm

theorem preimage_kills_relator
    {d : ℕ} {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    (quotientMap : free.Carrier →* rationalTameGalois S)
    (prime : Fin d → ℕ) (frobeniusLift : Fin d → free.Carrier)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A) (alphaE : free.Carrier →* E)
    (betaA : rationalTameGalois S →* A)
    (hcompat : betaA.comp quotientMap = pi.comp alphaE)
    (hkill : ∀ i : Fin d,
      alphaE (rationalTameRelator
        free prime frobeniusLift i) = 1)
    (i : Fin d) :
    tamePreimageLift quotientMap pi alphaE betaA hcompat
        (rationalTameRelator free prime frobeniusLift i) = 1 := by
  apply Subtype.ext
  exact hkill i

theorem rational_preimage_relation
    {d : ℕ} {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    (quotientMap : free.Carrier →* rationalTameGalois S)
    (prime : Fin d → ℕ) (frobeniusLift : Fin d → free.Carrier)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A) (alphaE : free.Carrier →* E)
    (betaA : rationalTameGalois S →* A)
    (hcompat : betaA.comp quotientMap = pi.comp alphaE)
    (hkill : ∀ i : Fin d,
      alphaE (rationalTameRelator
        free prime frobeniusLift i) = 1)
    (i : Fin d) :
    let lift := tamePreimageLift
      quotientMap pi alphaE betaA hcompat
    lift (free.generator i) ^ (prime i - 1) *
        ⁅lift (free.generator i), lift (frobeniusLift i)⁆ = 1 := by
  let lift := tamePreimageLift
    quotientMap pi alphaE betaA hcompat
  have hrelator :=
    preimage_kills_relator
      quotientMap prime frobeniusLift pi alphaE betaA hcompat hkill i
  simpa [lift, rationalTameRelator, map_mul, map_pow,
    map_commutatorElement] using hrelator

/-- The killed Koch relation induces the canonical map from the abstract
two-generator tame local presentation to the pullback central extension. -/
def rationalPreimageLift
    {d : ℕ} {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    (quotientMap : free.Carrier →* rationalTameGalois S)
    (prime : Fin d → ℕ) (frobeniusLift : Fin d → free.Carrier)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A) (alphaE : free.Carrier →* E)
    (betaA : rationalTameGalois S →* A)
    (hcompat : betaA.comp quotientMap = pi.comp alphaE)
    (hkill : ∀ i : Fin d,
      alphaE (rationalTameRelator
        free prime frobeniusLift i) = 1)
    (i : Fin d) :
    (tameLocalPresentation (prime i)).Group →*
      centralExtensionPreimage pi betaA.range :=
  let lift := tamePreimageLift
    quotientMap pi alphaE betaA hcompat
  tamePresentationLift (prime i)
    (lift (free.generator i)) (lift (frobeniusLift i))
    (rational_preimage_relation
      quotientMap prime frobeniusLift pi alphaE betaA hcompat hkill i)

@[simp]
theorem rational_preimage_inertia
    {d : ℕ} {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    (quotientMap : free.Carrier →* rationalTameGalois S)
    (prime : Fin d → ℕ) (frobeniusLift : Fin d → free.Carrier)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A) (alphaE : free.Carrier →* E)
    (betaA : rationalTameGalois S →* A)
    (hcompat : betaA.comp quotientMap = pi.comp alphaE)
    (hkill : ∀ i : Fin d,
      alphaE (rationalTameRelator
        free prime frobeniusLift i) = 1)
    (i : Fin d) :
    rationalPreimageLift quotientMap prime frobeniusLift
        pi alphaE betaA hcompat hkill i
        ((tameLocalPresentation (prime i)).of
          (tameLocalInertia (prime i))) =
      tamePreimageLift
        quotientMap pi alphaE betaA hcompat (free.generator i) := by
  simp [rationalPreimageLift]

@[simp]
theorem rational_preimage_frobenius
    {d : ℕ} {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    (quotientMap : free.Carrier →* rationalTameGalois S)
    (prime : Fin d → ℕ) (frobeniusLift : Fin d → free.Carrier)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A) (alphaE : free.Carrier →* E)
    (betaA : rationalTameGalois S →* A)
    (hcompat : betaA.comp quotientMap = pi.comp alphaE)
    (hkill : ∀ i : Fin d,
      alphaE (rationalTameRelator
        free prime frobeniusLift i) = 1)
    (i : Fin d) :
    rationalPreimageLift quotientMap prime frobeniusLift
        pi alphaE betaA hcompat hkill i
        ((tameLocalPresentation (prime i)).of
          (tameFrobeniusGenerator (prime i))) =
      tamePreimageLift
        quotientMap pi alphaE betaA hcompat (frobeniusLift i) := by
  simp [rationalPreimageLift]

set_option synthInstance.maxHeartbeats 100000 in
-- Extra heartbeats are needed to synthesize the central-preimage tower instances.
/-- The tame lift obtained from a killed Koch relator really is a lift of the
corresponding tame presentation in the finite Galois quotient.  This is the
purely group-theoretic compatibility needed before passing to a decomposition
group and then to a completed local embedding problem. -/
theorem rational_preimage_projection
    {d : ℕ} {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    (quotientMap : free.Carrier →* rationalTameGalois S)
    (prime : Fin d → ℕ) (frobeniusLift : Fin d → free.Carrier)
    {A E : Type v} [Group A] [Group E]
    (pi : E →* A) (alphaE : free.Carrier →* E)
    (betaA : rationalTameGalois S →* A)
    (hcompat : betaA.comp quotientMap = pi.comp alphaE)
    (hkill : ∀ i : Fin d,
      alphaE (rationalTameRelator
        free prime frobeniusLift i) = 1)
    (i : Fin d) :
    let inertia := betaA.rangeRestrict (quotientMap (free.generator i))
    let frobenius := betaA.rangeRestrict (quotientMap (frobeniusLift i))
    let hrelation : inertia ^ (prime i - 1) * ⁅inertia, frobenius⁆ = 1 := by
      have h := congrArg
        (centralPreimageProjection pi betaA.range)
        (rational_preimage_relation
          quotientMap prime frobeniusLift pi alphaE betaA hcompat hkill i)
      simpa [map_mul, map_pow, map_commutatorElement] using h
    (centralPreimageProjection pi betaA.range).comp
        (rationalPreimageLift
          quotientMap prime frobeniusLift pi alphaE betaA hcompat hkill i) =
      tamePresentationLift (prime i) inertia frobenius hrelation := by
  dsimp only
  apply (tameLocalPresentation (prime i)).groupHom_ext
  intro j
  change Fin 2 at j
  fin_cases j
  · simp [MonoidHom.comp_apply, rationalPreimageLift,
      tamePresentationLift, tameLocalGenerator]
  · simp [MonoidHom.comp_apply, rationalPreimageLift,
      tamePresentationLift, tameLocalGenerator]

/-- Vanishing of the factor-set obstruction on the pullback extension gives
an algebraic solution of the original embedding problem. -/
theorem embedding_pullback_trivial
    {Γ E A : Type*}
    [Group Γ]
    [Group E]
    [Group A]
    (π : E →* A)
    (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center E)
    (βA : Γ →* A)
    (htrivial :
      let q := embeddingPullbackProjection π βA
      let hq := pullback_projection_surjective π hπ βA
      let hc := embedding_pullback_projection
        π βA hcentral
      (centralExtensionSet q hq hc).IsTrivial) :
    ∃ βE : Γ →* E, π.comp βE = βA := by
  let q := embeddingPullbackProjection π βA
  let hq : Function.Surjective q :=
    pullback_projection_surjective π hπ βA
  let hc : q.ker ≤ Subgroup.center (CentralEmbeddingPullback π βA) :=
    embedding_pullback_projection π βA hcentral
  let s : Γ →* CentralEmbeddingPullback π βA :=
    splittingSetTrivial q hq hc htrivial
  have hs : q.comp s = MonoidHom.id Γ :=
    splitting_trivial_maps q hq hc htrivial
  exact ⟨embeddingPullbackSplitting π βA s,
    embedding_pullback_splitting π βA s hs⟩

/-- Vanishing of the multiplicative `H²` obstruction of the pullback
extension gives an algebraic solution of the embedding problem. -/
theorem embedding_pullback_obstruction
    {Γ E A : Type*}
    [Group Γ]
    [Group E]
    [Group A]
    (π : E →* A)
    (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center E)
    (βA : Γ →* A)
    (hobstruction :
      let q := embeddingPullbackProjection π βA
      let hq := pullback_projection_surjective π hπ βA
      let hc := embedding_pullback_projection
        π βA hcentral
      letI : CommGroup q.ker :=
        centralExtensionComm q hc
      letI : MulDistribMulAction Γ q.ker :=
        trivialDistribAction Γ q.ker
      extensionObstructionClass q hq hc = 1) :
    ∃ βE : Γ →* E, π.comp βE = βA := by
  let q := embeddingPullbackProjection π βA
  let hq : Function.Surjective q :=
    pullback_projection_surjective π hπ βA
  let hc : q.ker ≤ Subgroup.center (CentralEmbeddingPullback π βA) :=
    embedding_pullback_projection π βA hcentral
  apply embedding_pullback_trivial
    π hπ hcentral βA
  exact
    (set_trivial_obstruction
      q hq hc).2 hobstruction

/-- Triviality of the finite factor set over the range of the base map gives
a continuous preliminary lift of the embedding problem. -/
theorem rational_preliminary_trivial
    {S : Finset ℕ}
    {A E : Type v}
    [Group A]
    [TopologicalSpace A]
    [DiscreteTopology A]
    [Finite A]
    [Group E]
    [TopologicalSpace E]
    [DiscreteTopology E]
    [Finite E]
    (pi : E →* A)
    (hpi : Function.Surjective pi)
    (hcentral : pi.ker ≤ Subgroup.center E)
    (betaA : rationalTameGalois S →* A)
    (hbetaA : Continuous betaA)
    (htrivial :
      let q := centralPreimageProjection pi betaA.range
      let hq := preimage_projection_surjective
        pi hpi betaA.range
      let hc := extension_preimage_projection
        pi betaA.range hcentral
      (centralExtensionSet q hq hc).IsTrivial) :
    ∃ beta0 : rationalTameGalois S →* E,
      Continuous beta0 ∧ pi.comp beta0 = betaA := by
  let q := centralPreimageProjection pi betaA.range
  let hq : Function.Surjective q :=
    preimage_projection_surjective pi hpi betaA.range
  let hc : q.ker ≤ Subgroup.center (centralExtensionPreimage pi betaA.range) :=
    extension_preimage_projection
      pi betaA.range hcentral
  let t : betaA.range →* centralExtensionPreimage pi betaA.range :=
    splittingSetTrivial q hq hc htrivial
  let beta0 : rationalTameGalois S →* E :=
    (centralExtensionPreimage pi betaA.range).subtype.comp
      (t.comp betaA.rangeRestrict)
  have ht : q.comp t = MonoidHom.id betaA.range :=
    splitting_trivial_maps q hq hc htrivial
  have hbeta0 : pi.comp beta0 = betaA := by
    ext gamma
    have ht_gamma := DFunLike.congr_fun ht (betaA.rangeRestrict gamma)
    exact congrArg Subtype.val ht_gamma
  have hbetaRange : Continuous betaA.rangeRestrict :=
    hbetaA.subtype_mk _
  have hfiniteMap : Continuous
      ((centralExtensionPreimage pi betaA.range).subtype.comp t) :=
    continuous_of_discreteTopology
  refine ⟨beta0, ?_, hbeta0⟩
  exact hfiniteMap.comp hbetaRange

/-- A trivial finite obstruction and cubic characters with arbitrary inertia
values give the prescribed central cubic lift. -/
theorem rational_tame_characters
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    {frobeniusLift : Fin d → free.Carrier}
    (hsetup :
      RationalKochSetup
        S free quotientMap prime frobeniusLift)
    {A E : Type v}
    [Group A]
    [TopologicalSpace A]
    [DiscreteTopology A]
    [Finite A]
    [Group E]
    [TopologicalSpace E]
    [DiscreteTopology E]
    [Finite E]
    (pi : E →* A)
    (hpi : Function.Surjective pi)
    (hE : IsPGroup 3 E)
    (hA : IsPGroup 3 A)
    (hkernel_central : pi.ker ≤ Subgroup.center E)
    (hkernel_card : Nat.card pi.ker = 3)
    (alphaE : free.Carrier →* E)
    (halphaE : Continuous alphaE)
    (hkill :
      ∀ i : Fin d,
        alphaE
            (rationalTameRelator
              free prime frobeniusLift i) = 1)
    (betaA : rationalTameGalois S →* A)
    (hcompat : betaA.comp quotientMap = pi.comp alphaE)
    (hfactor :
      let q := centralPreimageProjection pi betaA.range
      let hq := preimage_projection_surjective
        pi hpi betaA.range
      let hc := extension_preimage_projection
        pi betaA.range hkernel_central
      (centralExtensionSet q hq hc).IsTrivial)
    (hcharacters :
      ∀ values : Fin d → pi.ker,
        ∃ chi : rationalTameGalois S →* pi.ker,
          Continuous chi ∧
            ∀ i : Fin d,
              chi (quotientMap (free.generator i)) = values i) :
    ∃ betaE : rationalTameGalois S →* E,
      Continuous betaE ∧
        pi.comp betaE = betaA ∧
          ∀ i : Fin d,
            betaE (quotientMap (free.generator i)) =
              alphaE (free.generator i) := by
  have hbetaA : Continuous betaA :=
    rational_compatible_continuous
      hsetup pi alphaE halphaE betaA hcompat
  obtain ⟨beta0, hbeta0_continuous, hbeta0⟩ :=
    rational_preliminary_trivial
      pi hpi hkernel_central betaA hbetaA hfactor
  let values : Fin d → pi.ker := fun i =>
    ⟨alphaE (free.generator i) *
        (beta0 (quotientMap (free.generator i)))⁻¹,
      by
        change pi (alphaE (free.generator i) *
          (beta0 (quotientMap (free.generator i)))⁻¹) = 1
        have halpha := DFunLike.congr_fun hcompat (free.generator i)
        change betaA (quotientMap (free.generator i)) =
          pi (alphaE (free.generator i)) at halpha
        have hbeta := DFunLike.congr_fun hbeta0
          (quotientMap (free.generator i))
        change pi (beta0 (quotientMap (free.generator i))) =
          betaA (quotientMap (free.generator i)) at hbeta
        rw [map_mul, map_inv, ← halpha, hbeta]
        exact mul_inv_cancel _⟩
  obtain ⟨chi, hchi_continuous, hchi⟩ := hcharacters values
  apply rational_tame_character
    hsetup pi hpi hE hA hkernel_central hkernel_card
      alphaE halphaE hkill betaA hcompat beta0 hbeta0_continuous hbeta0
      chi hchi_continuous
  intro i
  rw [hchi i]
  change (alphaE (free.generator i) *
      (beta0 (quotientMap (free.generator i)))⁻¹) *
        beta0 (quotientMap (free.generator i)) =
    alphaE (free.generator i)
  group

/-- Once one continuous lift exists, explicit cubic characters from the
cyclotomic cubic layers adjust it to all prescribed inertia-generator values. -/
theorem rational_preliminary_lift
    {d : ℕ}
    {S : Finset ℕ}
    {free : ProP.FreeGroup.{u} 3 d}
    {quotientMap : free.Carrier →*
      rationalTameGalois S}
    {prime : Fin d → ℕ}
    {frobeniusLift : Fin d → free.Carrier}
    (hsetup :
      RationalKochSetup
        S free quotientMap prime frobeniusLift)
    {A E : Type v}
    [Group A]
    [TopologicalSpace A]
    [DiscreteTopology A]
    [Finite A]
    [Group E]
    [TopologicalSpace E]
    [DiscreteTopology E]
    [Finite E]
    (pi : E →* A)
    (hpi : Function.Surjective pi)
    (hE : IsPGroup 3 E)
    (hA : IsPGroup 3 A)
    (hkernel_central : pi.ker ≤ Subgroup.center E)
    (hkernel_card : Nat.card pi.ker = 3)
    (alphaE : free.Carrier →* E)
    (halphaE : Continuous alphaE)
    (hkill :
      ∀ i : Fin d,
        alphaE
            (rationalTameRelator
              free prime frobeniusLift i) = 1)
    (betaA : rationalTameGalois S →* A)
    (hcompat : betaA.comp quotientMap = pi.comp alphaE)
    (hpreliminary :
      ∃ beta0 : rationalTameGalois S →* E,
        Continuous beta0 ∧ pi.comp beta0 = betaA) :
    ∃ betaE : rationalTameGalois S →* E,
      Continuous betaE ∧
        pi.comp betaE = betaA ∧
          ∀ i : Fin d,
            betaE (quotientMap (free.generator i)) =
              alphaE (free.generator i) := by
  let hcentralCubic : CCGroups pi :=
    ⟨hpi, hE, hA, hkernel_central, hkernel_card⟩
  obtain ⟨eKernel⟩ := hcentralCubic.kernel_zmod_three
  obtain ⟨beta0, hbeta0_continuous, hbeta0⟩ := hpreliminary
  let values : Fin d → pi.ker := fun i =>
    ⟨alphaE (free.generator i) *
        (beta0 (quotientMap (free.generator i)))⁻¹,
      by
        change pi (alphaE (free.generator i) *
          (beta0 (quotientMap (free.generator i)))⁻¹) = 1
        have halpha := DFunLike.congr_fun hcompat (free.generator i)
        change betaA (quotientMap (free.generator i)) =
          pi (alphaE (free.generator i)) at halpha
        have hbeta := DFunLike.congr_fun hbeta0
          (quotientMap (free.generator i))
        change pi (beta0 (quotientMap (free.generator i))) =
          betaA (quotientMap (free.generator i)) at hbeta
        rw [map_mul, map_inv, ← halpha, hbeta]
        exact mul_inv_cancel _⟩
  obtain ⟨chi, hchi_continuous, hchi⟩ :=
    rational_character_control
      hsetup eKernel.symm values
  apply rational_tame_character
    hsetup pi hpi hE hA hkernel_central hkernel_card
      alphaE halphaE hkill betaA hcompat beta0 hbeta0_continuous hbeta0
      chi hchi_continuous
  intro i
  rw [hchi i]
  change (alphaE (free.generator i) *
      (beta0 (quotientMap (free.generator i)))⁻¹) *
        beta0 (quotientMap (free.generator i)) =
    alphaE (free.generator i)
  group

/-- There is no Grunwald--Wang exceptional case at the odd order `3`. -/
theorem no_wang_exception
    (K : Type u)
    [Field K]
    [NumberField K] :
    ¬Towers.CField.GWang.HasWangException K 3 := by
  rintro ⟨t, ht, hnoncyclic⟩
  cases t with
  | zero =>
      apply hnoncyclic
      have hirr : Irreducible (Polynomial.cyclotomic 1 K) := by
        simpa [Polynomial.cyclotomic_one] using
          (Polynomial.irreducible_X_sub_C (1 : K))
      letI : NeZero (1 : K) := ⟨one_ne_zero⟩
      letI : IsCyclotomicExtension {1} K (CyclotomicField 1 K) :=
        CyclotomicField.isCyclotomicExtension 1 K
      have hfinrank : Module.finrank K (CyclotomicField 1 K) = 1 := by
        simpa using
          (IsCyclotomicExtension.finrank (CyclotomicField 1 K) hirr)
      letI : Subsingleton Gal(CyclotomicField 1 K/K) := by
        constructor
        intro σ τ
        ext x
        obtain ⟨c, hc⟩ :=
          exists_smul_eq_of_finrank_eq_one hfinrank
            (one_ne_zero : (1 : CyclotomicField 1 K) ≠ 0) x
        rw [← hc]
        change σ (c • (1 : CyclotomicField 1 K)) =
          τ (c • (1 : CyclotomicField 1 K))
        simp [Algebra.smul_def]
      infer_instance
  | succ t =>
      have htwo_pow : 2 ∣ 2 ^ (t + 1) := by
        refine ⟨2 ^ t, ?_⟩
        simp [pow_succ, mul_comm]
      have : 2 ∣ 3 := htwo_pow.trans ht
      norm_num at this

/-- The order-three specialization of Grunwald--Wang has no exceptional case. -/
theorem grunwald_wang_three
    (K : Type u)
    [Field K]
    [NumberField K]
    (hGW : Towers.CField.GWang.GrunwaldWangTheorem K)
    (places : Finset
      (Towers.CField.GWang.Place K))
    (localCharacter : ∀ v : places,
      Towers.CField.GWang.OrderLocalCharacter
        K v.1)
    (horder :
      Finset.univ.lcm (fun v : places => orderOf (localCharacter v).1) = 3) :
    ∃ chi : Towers.CField.GWang.IdeleClassCharacter K,
      orderOf chi = 3 ∧
        ∀ v : places,
          Towers.CField.GWang.CharacterRestrictsTo
            K chi v.1 (localCharacter v).1 := by
  let n := Finset.univ.lcm
    (fun v : places => orderOf (localCharacter v).1)
  have hn : n = 3 := horder
  have hno :
      ¬Towers.CField.GWang.HasWangException K n := by
    simpa [hn] using no_wang_exception K
  obtain ⟨chi, hchiOrder, hchiLocal⟩ := hGW.2 places localCharacter hno
  exact ⟨chi, hchiOrder.trans horder, hchiLocal⟩

/-- Idelic reciprocity contains the product-reciprocity clause of
Theorem VII.8.1. -/
theorem reciprocity_law_idele
    (K : Type u)
    [Field K]
    [NumberField K]
    (hreciprocity :
      Towers.CField.Recip.IdeleReciprocityLaw
        (K := K)) :
    Towers.CField.RExist.GlobalReciprocityLaw K := by
  intro phi hphi
  exact (hreciprocity phi hphi).1

/-- The injective part of the global Brauer sequence detects the trivial
class from triviality after scalar extension to every completion. -/
theorem brauer_class_completions
    (K : Type u)
    [Field K]
    [NumberField K]
    (loc :
      Towers.CField.GClass.GlobalLocalizationData K)
    (placeInvariant :
      ∀ place : Towers.CField.Ideles.NumberFieldPlace K,
        Additive (BrauerGroup
            (Towers.CField.Ideles.placeCompletion
              K place)) →+
          Towers.CField.LBrauer.LocalInvariant)
    (hsequence :
      Towers.CField.GClass.GlobalBrauerSequence
        K loc placeInvariant)
    (x : BrauerGroup K)
    (hlocal :
      ∀ place : Towers.CField.Ideles.NumberFieldPlace K,
        Towers.CField.BGroups.brauerBaseChange
            K
            (Towers.CField.Ideles.placeCompletion K place)
            x =
          1) :
    x = 1 := by
  apply Additive.ofMul.injective
  apply hsequence.2.1
  apply DirectSum.ext
  intro place
  change
    DirectSum.component ℤ
        (Towers.CField.Ideles.NumberFieldPlace K)
        (fun v => Additive (BrauerGroup
          (Towers.CField.Ideles.placeCompletion K v)))
        place (loc.localization (Additive.ofMul x)) =
      DirectSum.component ℤ
        (Towers.CField.Ideles.NumberFieldPlace K)
        (fun v => Additive (BrauerGroup
          (Towers.CField.Ideles.placeCompletion K v)))
        place (loc.localization (Additive.ofMul 1))
  rw [loc.localization_apply, loc.localization_apply]
  rw [hsequence.1 x place, hsequence.1 1 place]
  exact congrArg Additive.ofMul
    ((hlocal place).trans
      (map_one
        (Towers.CField.BGroups.brauerBaseChange
          K
          (Towers.CField.Ideles.placeCompletion
            K place))).symm)


end TBluepr
end Towers
