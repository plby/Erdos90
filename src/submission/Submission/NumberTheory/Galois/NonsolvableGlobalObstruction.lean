import Submission.NumberTheory.Locals.RamificationGroups
import Submission.NumberTheory.Galois.FinitePlaceGroup
import Submission.NumberTheory.Completions.PrimitiveReducibility
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Nonsolvable global groups and local decomposition groups

The group-theoretic core of ANT, Remark 8.40(e), is that a nonsolvable global
Galois group cannot occur as a decomposition group over a local field.  At a
finite rational prime this follows from the solvability of decomposition
groups proved using the ramification filtration.

The source cites external constructions of `S_n`-extensions of `ℚ`; this file
takes such a Galois-group identification as input and proves the local
obstruction.
-/

namespace Submission.NumberTheory.Milne

open AbsoluteValue NumberField
open Submission.CField.ICohomo
open scoped Pointwise

noncomputable section

/-- The canonical action on a ring of integers and the integral-closure
action induce the same ring endomorphism. -/
private theorem ring_integers_hom
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (sigma : Gal(L/K)) :
    let canonicalAction :
        MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
      NumberField.RingOfIntegers.instMulSemiringAction L
    letI : MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
      canonicalAction
    MulSemiringAction.toRingHom Gal(L/K)
        (NumberField.RingOfIntegers L) sigma =
      (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) sigma).toRingHom := by
  dsimp only
  ext x
  exact (algebraMap_galRestrict_apply
    (A := NumberField.RingOfIntegers K) (K := K) (L := L)
    (B := NumberField.RingOfIntegers L) sigma x).symm

/-- Consequently, the two actions induce the same pointwise action on
ideals. -/
private theorem ring_integers_smul
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (sigma : Gal(L/K)) (P : Ideal (NumberField.RingOfIntegers L)) :
    let canonicalAction :
        MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
      NumberField.RingOfIntegers.instMulSemiringAction L
    let integralAction :
        MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
      IsIntegralClosure.MulSemiringAction
        (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L)
    let canonicalIdealAction : MulAction Gal(L/K)
        (Ideal (NumberField.RingOfIntegers L)) :=
      (@Ideal.pointwiseDistribMulAction Gal(L/K)
        (NumberField.RingOfIntegers L) _ _ canonicalAction).toMulAction
    let integralIdealAction : MulAction Gal(L/K)
        (Ideal (NumberField.RingOfIntegers L)) :=
      (@Ideal.pointwiseDistribMulAction Gal(L/K)
        (NumberField.RingOfIntegers L) _ _ integralAction).toMulAction
    @SMul.smul Gal(L/K) (Ideal (NumberField.RingOfIntegers L))
        canonicalIdealAction.toSMul sigma P =
      @SMul.smul Gal(L/K) (Ideal (NumberField.RingOfIntegers L))
        integralIdealAction.toSMul sigma P := by
  dsimp only
  change Ideal.map _ P = Ideal.map _ P
  exact congrArg (fun f => Ideal.map f P)
    (ring_integers_hom K L sigma)

/-- The corresponding ideal stabilizers are therefore equal. -/
private theorem ring_integers_stabilizers
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal (NumberField.RingOfIntegers L)) :
    let canonicalAction :
        MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
      NumberField.RingOfIntegers.instMulSemiringAction L
    let integralAction :
        MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
      IsIntegralClosure.MulSemiringAction
        (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L)
    let canonicalIdealAction : MulAction Gal(L/K)
        (Ideal (NumberField.RingOfIntegers L)) :=
      (@Ideal.pointwiseDistribMulAction Gal(L/K)
        (NumberField.RingOfIntegers L) _ _ canonicalAction).toMulAction
    let integralIdealAction : MulAction Gal(L/K)
        (Ideal (NumberField.RingOfIntegers L)) :=
      (@Ideal.pointwiseDistribMulAction Gal(L/K)
        (NumberField.RingOfIntegers L) _ _ integralAction).toMulAction
    @MulAction.stabilizer Gal(L/K) (Ideal (NumberField.RingOfIntegers L))
        _ canonicalIdealAction P =
      @MulAction.stabilizer Gal(L/K) (Ideal (NumberField.RingOfIntegers L))
        _ integralIdealAction P := by
  dsimp only
  ext sigma
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro hcanonical
    exact (ring_integers_smul K L sigma P).symm.trans
      hcanonical
  · intro hintegral
    exact (ring_integers_smul K L sigma P).trans
      hintegral

/-- Every nonzero prime of a ring of integers lies over a rational prime. -/
private theorem rational_lies
    (L : Type*) [Field L] [NumberField L]
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime] (hP0 : P ≠ ⊥) :
    ∃ q : ℕ, Nat.Prime q ∧ P.LiesOver (Ideal.rationalPrimeIdeal q) := by
  let p0 : Ideal ℤ := Ideal.under ℤ P
  have hp0prime : p0.IsPrime :=
    Ideal.comap_isPrime (algebraMap ℤ (NumberField.RingOfIntegers L)) P
  have hp0ne : p0 ≠ ⊥ := by
    intro hp0
    apply hP0
    exact Ideal.eq_bot_of_comap_eq_bot
      (R := ℤ) (S := NumberField.RingOfIntegers L) (I := P) hp0
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
  let q : ℕ := Int.natAbs g
  have hqprime : Nat.Prime q :=
    (Int.prime_iff_natAbs_prime).mp hgprime
  refine ⟨q, hqprime, Ideal.LiesOver.mk ?_⟩
  calc
    Ideal.rationalPrimeIdeal q = Ideal.span ({g} : Set ℤ) := by
      exact (Ideal.span_singleton_eq_span_singleton).2
        (Int.associated_natAbs g).symm
    _ = Ideal.comap (algebraMap ℤ (NumberField.RingOfIntegers L)) P := by
      simpa [q, p0, Ideal.under] using hspan

/-- A finite group with at most two elements is solvable. -/
private theorem solvable_card_two
    (G : Type*) [Group G] [Finite G] (hcard : Nat.card G ≤ 2) :
    IsSolvable G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  obtain hcardOne | hcardTwo : Nat.card G = 1 ∨ Nat.card G = 2 := by
    omega
  · letI : Subsingleton G :=
      Finite.card_le_one_iff_subsingleton.mp (by omega)
    exact isSolvable_of_comm fun a b => Subsingleton.elim _ _
  · letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyclic : IsCyclic G := isCyclic_of_prime_card hcardTwo
    letI : IsCyclic G := hcyclic
    exact isSolvable_of_comm mul_comm'

/-- If the global Galois group is nonsolvable, the decomposition group at
every finite rational prime is a proper subgroup. -/
theorem number_decomposition_solvable
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hglobal : ¬ IsSolvable Gal(L/ℚ))
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (𝓞 L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    MulAction.stabilizer Gal(L/ℚ) P ≠ ⊤ := by
  intro htop
  have hD : IsSolvable (MulAction.stabilizer Gal(L/ℚ) P) :=
    decomposition_group_solvable L hq P
  have htopSolvable : IsSolvable (⊤ : Subgroup Gal(L/ℚ)) := by
    exact htop ▸ hD
  letI : IsSolvable (⊤ : Subgroup Gal(L/ℚ)) := htopSolvable
  apply hglobal
  exact solvable_of_surjective
    (f := (Subgroup.topEquiv : (⊤ : Subgroup Gal(L/ℚ)) ≃* Gal(L/ℚ)).toMonoidHom)
    Subgroup.topEquiv.surjective

/-- Equivalently, the decomposition group has more than one left coset in
the global group. -/
theorem decomposition_not_solvable
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hglobal : ¬ IsSolvable Gal(L/ℚ))
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (𝓞 L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    1 < (MulAction.stabilizer Gal(L/ℚ) P).index :=
  Subgroup.one_lt_index_of_ne_top
    (number_decomposition_solvable
      L hglobal hq P)

/-- The stabilizer of every nontrivial nonarchimedean absolute value is
proper when the global Galois group is nonsolvable. -/
theorem absolute_stabilizer_solvable
    (L : Type) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hglobal : ¬ IsSolvable Gal(L/ℚ))
    (w : AbsoluteValue L ℝ) (hw : w.IsNontrivial)
    (hna : IsNonarchimedean w) :
    MulAction.stabilizer Gal(L/ℚ) w ≠ ⊤ := by
  let P := nonarchimedeanHeightSpectrum w hw hna
  obtain ⟨q, hq, hPq⟩ :=
    rational_lies L P.asIdeal P.ne_bot
  letI : P.asIdeal.LiesOver (Ideal.rationalPrimeIdeal q) := hPq
  have hproper :=
    number_decomposition_solvable
      L hglobal hq P.asIdeal
  have hstabilizer :
      MulAction.stabilizer Gal(L/ℚ) P.asIdeal =
        MulAction.stabilizer Gal(L/ℚ) w := by
    calc
      MulAction.stabilizer Gal(L/ℚ) P.asIdeal =
          @MulAction.stabilizer Gal(L/ℚ)
            (Ideal (NumberField.RingOfIntegers L)) _
            (@Ideal.pointwiseDistribMulAction Gal(L/ℚ)
              (NumberField.RingOfIntegers L) _ _
              (IsIntegralClosure.MulSemiringAction
                (NumberField.RingOfIntegers ℚ) ℚ L
                (NumberField.RingOfIntegers L))).toMulAction P.asIdeal :=
        ring_integers_stabilizers ℚ L P.asIdeal
      _ = MulAction.stabilizer Gal(L/ℚ) w := by
        simpa [P] using
          (centered_stabilizer_value
            (K := ℚ) w hw hna)
  rwa [hstabilizer] at hproper

/-- The preceding properness statement for an exact extension of a
nonarchimedean absolute value. -/
theorem number_stabilizer_solvable
    (L : Type) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hglobal : ¬ IsSolvable Gal(L/ℚ))
    (v : AbsoluteValue ℚ ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : CompletionPlacesAbove (L := L) v) :
    MulAction.stabilizer Gal(L/ℚ) w ≠ ⊤ := by
  have hw : w.1.IsNontrivial := absolute_extension_nontrivial v w
  have hwna : IsNonarchimedean w.1 :=
    absolute_extension_nonarchimedean v w
  have hproper :=
    absolute_stabilizer_solvable
      L hglobal w.1 hw hwna
  have hstabilizer :
      MulAction.stabilizer Gal(L/ℚ) w =
        MulAction.stabilizer Gal(L/ℚ) w.1 := by
    ext sigma
    change sigma • w = w ↔ sigma • w.1 = w.1
    exact Subtype.ext_iff
  rwa [hstabilizer]

/-- ANT, Remark 8.40(e), finite-place step: in a nonsolvable Galois number
field, the minimal polynomial of every primitive element becomes reducible
over every nonarchimedean completion of `ℚ`. -/
theorem minpol_irred_nonar
    (L : Type) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hglobal : ¬ IsSolvable Gal(L/ℚ))
    (v : AbsoluteValue ℚ ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (alpha : L) (halpha : Algebra.adjoin ℚ {alpha} = ⊤) :
    ¬ Irreducible ((minpoly ℚ alpha).map (completionEmbedding v)) := by
  let W := CompletionPlacesAbove (L := L) v
  letI : Nonempty W := absolute_value_extension (K := ℚ) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/ℚ) W :=
    above_pretr_nonar v hvna
  let w : W := Classical.choice (inferInstance : Nonempty W)
  have hproper : MulAction.stabilizer Gal(L/ℚ) w ≠ ⊤ :=
    number_stabilizer_solvable
      L hglobal v w
  have hone : 1 < (MulAction.stabilizer Gal(L/ℚ) w).index :=
    Subgroup.one_lt_index_of_ne_top hproper
  have hplaces : 1 < Nat.card W := by
    rwa [MulAction.index_stabilizer_of_transitive Gal(L/ℚ) w] at hone
  exact mapped_minpoly_above
    v alpha halpha hplaces

/-- The finite-place conclusion of Remark 8.40(e) under the source's
standard `S_n`, `n ≥ 5`, realization hypothesis. -/
theorem symmetric_minpoly_nonarchimedean
    (L : Type) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {n : ℕ} (hn : 5 ≤ n)
    (e : Gal(L/ℚ) ≃* Equiv.Perm (Fin n))
    (v : AbsoluteValue ℚ ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (alpha : L) (halpha : Algebra.adjoin ℚ {alpha} = ⊤) :
    ¬ Irreducible ((minpoly ℚ alpha).map (completionEmbedding v)) := by
  apply minpol_irred_nonar
    L _ v hvna alpha halpha
  intro hsolvable
  letI : IsSolvable Gal(L/ℚ) := hsolvable
  have hSn : IsSolvable (Equiv.Perm (Fin n)) :=
    solvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact (Equiv.Perm.not_solvable (Fin n) (by simpa using hn)) hSn

/-- ANT, Remark 8.40(e), infinite-place step: the minimal polynomial of a
primitive element of a nonsolvable Galois number field is reducible over
`ℝ`. -/
theorem minpoly_irreducible_real
    (L : Type) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hglobal : ¬ IsSolvable Gal(L/ℚ))
    (alpha : L) (halpha : Algebra.adjoin ℚ {alpha} = ⊤) :
    ¬ Irreducible ((minpoly ℚ alpha).map (algebraMap ℚ ℝ)) := by
  intro hirreducible
  have hdegree :
      Nat.card Gal(L/ℚ) = (minpoly ℚ alpha).natDegree := by
    calc
      Nat.card Gal(L/ℚ) = Module.finrank ℚ L :=
        IsGalois.card_aut_eq_finrank ℚ L
      _ = (minpoly ℚ alpha).natDegree := by
        simpa using
          (PowerBasis.finrank
            (PowerBasis.ofAdjoinEqTop
              (Algebra.IsIntegral.isIntegral alpha) halpha))
  have hmapDegree :
      ((minpoly ℚ alpha).map (algebraMap ℚ ℝ)).natDegree =
        (minpoly ℚ alpha).natDegree :=
    (minpoly.monic (Algebra.IsIntegral.isIntegral alpha)).natDegree_map
      (algebraMap ℚ ℝ)
  have hcard : Nat.card Gal(L/ℚ) ≤ 2 := by
    rw [hdegree, ← hmapDegree]
    exact hirreducible.natDegree_le_two
  exact hglobal (solvable_card_two Gal(L/ℚ) hcard)

/-- A global identification with `S_n`, for `n ≥ 5`, forces every finite
decomposition group to be proper. -/
theorem symmetric_decomposition_top
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {n : ℕ} (hn : 5 ≤ n)
    (e : Gal(L/ℚ) ≃* Equiv.Perm (Fin n))
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (𝓞 L))
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    MulAction.stabilizer Gal(L/ℚ) P ≠ ⊤ := by
  apply number_decomposition_solvable L _ hq P
  intro hsolvable
  letI : IsSolvable Gal(L/ℚ) := hsolvable
  have hSn : IsSolvable (Equiv.Perm (Fin n)) :=
    solvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact (Equiv.Perm.not_solvable (Fin n) (by simpa using hn)) hSn

end

end Submission.NumberTheory.Milne
