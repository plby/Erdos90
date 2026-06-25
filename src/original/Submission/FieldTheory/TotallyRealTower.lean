
import Submission.FieldTheory.HMRZassenhausOpen


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Submission
namespace TBluepr
namespace STBuild

lemma filtration_open_aux (n : ℕ) :
    IsOpen ((initialZassenhausFiltration n : Set initialGaloisGroup)) := by
  exact Subgroup.isOpen_mono
    (initial_jennings_ker n)
    (initial_jennings_open n)

/- For every `i ≥ 0`, define `L_i := (Q_S^(3))^(G_{k+i})`. -/
theorem filtration_realized_subextension
    (n : ℕ) :
    ∃ L : IntermediateField ℚ initialProExtension,
      FiniteDimensional ℚ L ∧
      L.fixingSubgroup = initialZassenhausFiltration n := by
  -- The only remaining input here is that the `n`th Zassenhaus term is open.
  have hOpen : IsOpen ((initialZassenhausFiltration n : Set initialGaloisGroup)) := by
    exact filtration_open_aux n
  have hClosed : IsClosed ((initialZassenhausFiltration n : Set initialGaloisGroup)) := by
    exact Subgroup.isClosed_of_isOpen _ hOpen
  let H : ClosedSubgroup initialGaloisGroup :=
    ⟨initialZassenhausFiltration n, hClosed⟩
  letI : H.Normal := by
    change (initialZassenhausFiltration n).Normal
    change (zassenhausFiltration initialPrimeParameter initialGaloisGroup n).Normal
    letI : (zassenhausFiltration initialPrimeParameter initialGaloisGroup n).Characteristic := by
      rw [Subgroup.characteristic_iff_map_le]
      intro ϕ
      rw [zassenhausFiltration, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨g, hg, rfl⟩
      rcases hg with ⟨i, j, x, hx, hbound, rfl⟩
      exact ⟨i, j, ϕ x,
        (Subgroup.lowerCentralSeries.map ϕ.toMonoidHom i) (Subgroup.mem_map_of_mem ϕ.toMonoidHom
          hx),
        hbound,
        by simp⟩
    infer_instance
  have hfix : (IntermediateField.fixedField H.1).fixingSubgroup = H.1 := by
    simpa using
      (InfiniteGalois.fixingSubgroup_fixedField
        (k := ℚ) (K := initialProExtension) H)
  refine ⟨IntermediateField.fixedField H.1, ?_, ?_⟩
  · exact
      ((InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
        (k := ℚ) (K := initialProExtension) (IntermediateField.fixedField H.1)).mp <| by
          rw [hfix]
          exact ⟨hOpen, by infer_instance⟩).1
  · simpa [H] using hfix

theorem initial_filtration_open (n : ℕ) :
    IsOpen ((initialZassenhausFiltration n : Set initialGaloisGroup)) := by
  exact filtration_open_aux n

theorem initial_filtration_normal (n : ℕ) :
    (initialZassenhausFiltration n).Normal := by
  change (zassenhausFiltration initialPrimeParameter initialGaloisGroup n).Normal
  letI : (zassenhausFiltration initialPrimeParameter initialGaloisGroup n).Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro ϕ
    rw [zassenhausFiltration, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨g, hg, rfl⟩
    rcases hg with ⟨i, j, x, hx, hbound, rfl⟩
    exact ⟨i, j, ϕ x,
      (Subgroup.lowerCentralSeries.map ϕ.toMonoidHom i) (Subgroup.mem_map_of_mem ϕ.toMonoidHom hx),
      hbound,
      by simp⟩
  infer_instance

def initialOpenNormal (n : ℕ) : OpenNormalSubgroup initialGaloisGroup where
  toOpenSubgroup :=
    { toSubgroup := initialZassenhausFiltration n
      isOpen' := initial_filtration_open n }
  isNormal' := initial_filtration_normal n

def layerSubgroup (i : ℕ) : OpenNormalSubgroup initialGaloisGroup :=
  initialOpenNormal (cuttingLevel + i)

noncomputable def layerField (i : ℕ) : IntermediateField ℚ initialProExtension :=
  IntermediateField.fixedField (layerSubgroup i : Subgroup initialGaloisGroup)

instance instAlgebraRat (i : ℕ) : Algebra ℚ (layerField i) :=
  (layerField i).algebra

instance instRatField (i : ℕ) : Module ℚ (layerField i) := by
  let _ := instAlgebraRat i
  infer_instance

instance instNumberLayer (i : ℕ) : NumberField (layerField i) := by
  have hClosed :
      IsClosed
        (((layerSubgroup i : Subgroup initialGaloisGroup) : Set initialGaloisGroup)) := by
    exact Subgroup.isClosed_of_isOpen
      (layerSubgroup i : Subgroup initialGaloisGroup)
      (show IsOpen
          (((layerSubgroup i : Subgroup initialGaloisGroup) : Set initialGaloisGroup)) from
        (layerSubgroup i).isOpen')
  let H : ClosedSubgroup initialGaloisGroup :=
    ⟨(layerSubgroup i : Subgroup initialGaloisGroup), hClosed⟩
  letI : H.Normal := by
    change (layerSubgroup i : Subgroup initialGaloisGroup).Normal
    infer_instance
  have hfix : (layerField i).fixingSubgroup = H.1 := by
    simpa [layerField] using
      (InfiniteGalois.fixingSubgroup_fixedField
        (k := ℚ) (K := initialProExtension) H)
  let hfg :=
    (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
      (k := ℚ) (K := initialProExtension) (layerField i)).mp <| by
        rw [hfix]
        refine ⟨(layerSubgroup i).isOpen', ?_⟩
        change (layerSubgroup i : Subgroup initialGaloisGroup).Normal
        infer_instance
  letI : FiniteDimensional ℚ (layerField i) := by
    exact hfg.1
  exact NumberField.of_module_finite ℚ (layerField i)

/- The field `L_i` is the fixed field of `G_{k+i}` inside `Q_S^(3)`. -/
theorem layer_field_fixed (i : ℕ) :
    layerField i =
      IntermediateField.fixedField (initialZassenhausFiltration (cuttingLevel + i)) := by
  simp [layerField, layerSubgroup, initialOpenNormal]

theorem layer_fixing_subgroup (i : ℕ) :
    (layerField i).fixingSubgroup =
      initialZassenhausFiltration (cuttingLevel + i) := by
  have hClosed :
      IsClosed
        (((layerSubgroup i : Subgroup initialGaloisGroup) : Set initialGaloisGroup)) := by
    exact Subgroup.isClosed_of_isOpen
      (layerSubgroup i : Subgroup initialGaloisGroup)
      (show IsOpen
          (((layerSubgroup i : Subgroup initialGaloisGroup) : Set initialGaloisGroup)) from
        (layerSubgroup i).isOpen')
  let H : ClosedSubgroup initialGaloisGroup :=
    ⟨(layerSubgroup i : Subgroup initialGaloisGroup), hClosed⟩
  letI : H.Normal := by
    change (layerSubgroup i : Subgroup initialGaloisGroup).Normal
    infer_instance
  have hfix : (layerField i).fixingSubgroup = H.1 := by
    simpa [layerField] using
      (InfiniteGalois.fixingSubgroup_fixedField
        (k := ℚ) (K := initialProExtension) H)
  simpa [H, layerSubgroup, initialOpenNormal] using hfix

/- Because `G / G_{k+i}` is a finite `3`-group, `L_i/ℚ` is a finite Galois `3`-extension. -/
theorem layer_three_group (i : ℕ) :
    GaloisThreeExtension (layerField i) := by
  have hClosed :
      IsClosed
        (((layerSubgroup i : Subgroup initialGaloisGroup) : Set initialGaloisGroup)) := by
    exact Subgroup.isClosed_of_isOpen
      (layerSubgroup i : Subgroup initialGaloisGroup)
      (show IsOpen
          (((layerSubgroup i : Subgroup initialGaloisGroup) : Set initialGaloisGroup)) from
        (layerSubgroup i).isOpen')
  let H : ClosedSubgroup initialGaloisGroup :=
    ⟨(layerSubgroup i : Subgroup initialGaloisGroup), hClosed⟩
  letI : H.Normal := by
    change (layerSubgroup i : Subgroup initialGaloisGroup).Normal
    infer_instance
  constructor
  · change IsGalois ℚ (layerField i)
    refine (InfiniteGalois.normal_iff_isGalois (layerField i)).mp ?_
    have hfix : (layerField i).fixingSubgroup = H.1 := by
      simpa [layerField] using
        (InfiniteGalois.fixingSubgroup_fixedField
          (k := ℚ) (K := initialProExtension) H)
    rw [hfix]
    infer_instance
  · let e : initialGaloisGroup ⧸ H.1 ≃* Gal(layerField i/ℚ) := by
      simpa [layerField] using
        (galoisFixedField
          (F := ℚ) (L := initialProExtension) H)
    have hquot : IsPGroup 3 (initialGaloisGroup ⧸ H.1) := by
      refine IsPGroup.iff_orderOf.mpr ?_
      intro g
      refine Quotient.inductionOn g ?_
      intro a
      change ∃ k, orderOf (QuotientGroup.mk' H.1 a) = 3 ^ k
      let n : ℕ := cuttingLevel + i
      let m : ℕ := n
      have hm : n ≤ 3 ^ m := by
        change n ≤ 3 ^ n
        induction n with
        | zero =>
            simp
        | succ n ih =>
            have hpos : 0 < 3 ^ n := by
              positivity
            calc
              n.succ ≤ 3 ^ n + 3 ^ n := by
                omega
              _ ≤ 3 ^ n + (3 ^ n + 3 ^ n) := by
                omega
              _ = 3 ^ n.succ := by
                rw [pow_succ]
                omega
      have hmem : a ^ (3 ^ m) ∈ H.1 := by
        change a ^ (3 ^ m) ∈ initialZassenhausFiltration (cuttingLevel + i)
        exact Subgroup.subset_closure
          ⟨0, m, a, by simp [Subgroup.lowerCentralSeries_zero], by simpa [n, m] using hm, rfl⟩
      have hpow : (QuotientGroup.mk' H.1 a) ^ (3 ^ m) = 1 := by
        change QuotientGroup.mk' H.1 (a ^ (3 ^ m)) = QuotientGroup.mk' H.1 1
        have hmem' : (a ^ (3 ^ m))⁻¹ * 1 ∈ H.1 := by
          simpa using H.1.inv_mem hmem
        exact QuotientGroup.eq.mpr hmem'
      have hdiv : orderOf (QuotientGroup.mk' H.1 a) ∣ 3 ^ m := by
        exact orderOf_dvd_of_pow_eq_one hpow
      rcases (Nat.dvd_prime_pow Nat.prime_three).mp hdiv with ⟨k, -, hk⟩
      exact ⟨k, hk⟩
    exact IsPGroup.of_equiv hquot e

/-- The layer field viewed as a finite Galois intermediate field of the ambient
initial pro-`3` extension. -/
noncomputable def galoisIntermediateField (i : ℕ) :
    FiniteGaloisIntermediateField ℚ initialProExtension := by
  letI : IsGalois ℚ (layerField i) := (layer_three_group i).1
  exact .mk (layerField i)

/- Since `L_i/ℚ` is a finite Galois `3`-extension, we have `L_i ∩ ℚ(i) = ℚ`. -/
theorem trivial_intersection_gaussian (i : ℕ) :
    TrivialIntersectionGaussian (layerField i) := by
  rcases layer_three_group i with ⟨hGal, hPGroup⟩
  letI : IsGalois ℚ (layerField i) := hGal
  refine ⟨hGal, ?_⟩
  have hcard_odd : Odd (Nat.card (Gal(layerField i/ℚ))) := by
    obtain ⟨n, hn⟩ := hPGroup.exists_card_eq
    rw [hn]
    simpa using (show Odd 3 by decide).pow
  have hcard :
      Nat.card (Gal(layerField i/ℚ)) = Module.finrank ℚ (layerField i) := by
    simpa using
      (IsGaloisGroup.card_eq_finrank
        (G := Gal(layerField i/ℚ)) (K := ℚ) (L := layerField i))
  rw [← hcard]
  exact hcard_odd

/- The degree of `L_i ∩ ℚ(i)` over `ℚ` divides both a power of `3` and `2`. -/
theorem layer_intersection_degree (i : ℕ) :
    IntersectionDividesTwo (layerField i) := by
  refine ⟨1, 0, one_dvd _, ?_, ?_⟩
  · simp
  · simp

/- Therefore the compositum `M_i := L_i ℚ(i)` is finite Galois over `ℚ`. -/
theorem exists_gaussianCompositum (i : ℕ) :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra ℚ M),
      GaussianCompositum (layerField i) M := by
  let eK : layerField i →ₐ[ℚ] AlgebraicClosure ℚ :=
    IsAlgClosed.lift
  let eG : GaussianField →ₐ[ℚ] AlgebraicClosure ℚ :=
    IsAlgClosed.lift
  let K' : IntermediateField ℚ (AlgebraicClosure ℚ) := eK.fieldRange
  let G' : IntermediateField ℚ (AlgebraicClosure ℚ) := eG.fieldRange
  let M' : IntermediateField ℚ (AlgebraicClosure ℚ) := K' ⊔ G'
  let eK' : layerField i ≃ₐ[ℚ] ↥K' := by
    simpa [K', AlgHom.fieldRange_toSubalgebra eK] using (AlgEquiv.ofInjectiveField eK)
  let eG' : GaussianField ≃ₐ[ℚ] ↥G' := by
    simpa [G', AlgHom.fieldRange_toSubalgebra eG] using (AlgEquiv.ofInjectiveField eG)
  haveI : IsGalois ℚ (layerField i) := (layer_three_group i).1
  letI : FiniteDimensional ℚ ↥K' :=
    FiniteDimensional.of_surjective eK'.toLinearEquiv.toLinearMap eK'.surjective
  letI : NumberField ↥K' := NumberField.of_module_finite ℚ ↥K'
  letI : Normal ℚ ↥K' := Normal.of_algEquiv eK'
  letI : IsGalois ℚ ↥K' := IsGalois.of_algEquiv eK'
  haveI : IsCyclotomicExtension {4} ℚ GaussianField := by
    simpa [GaussianField] using (CyclotomicField.isCyclotomicExtension 4 ℚ)
  haveI : IsGalois ℚ GaussianField :=
    IsCyclotomicExtension.isGalois (S := {4}) (K := ℚ) (L := GaussianField)
  letI : FiniteDimensional ℚ ↥G' :=
    FiniteDimensional.of_surjective eG'.toLinearEquiv.toLinearMap eG'.surjective
  letI : NumberField ↥G' := NumberField.of_module_finite ℚ ↥G'
  letI : Normal ℚ ↥G' := Normal.of_algEquiv eG'
  letI : IsGalois ℚ ↥G' := IsGalois.of_algEquiv eG'
  let Kfg : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    @FiniteGaloisIntermediateField.mk ℚ (AlgebraicClosure ℚ) _ _ _ K' inferInstance
      (IsGalois.of_algEquiv eK')
  let Gfg : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    @FiniteGaloisIntermediateField.mk ℚ (AlgebraicClosure ℚ) _ _ _ G' inferInstance
      (IsGalois.of_algEquiv eG')
  let Mfg : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) := Kfg ⊔ Gfg
  letI : FiniteDimensional ℚ ↥M' := IntermediateField.finiteDimensional_sup K' G'
  refine ⟨↥Mfg, inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨(show GaloisExtensionQ ↥Mfg from by
    simpa [GaloisExtensionQ] using Mfg.isGalois), ?_, ?_, ?_⟩
  · refine ⟨(IntermediateField.inclusion
      (show K' ≤ (Mfg : IntermediateField ℚ (AlgebraicClosure ℚ)) from by
        change (Kfg : IntermediateField ℚ (AlgebraicClosure ℚ)) ≤
          (Mfg : IntermediateField ℚ (AlgebraicClosure ℚ))
        exact le_sup_left)).comp eK'.toAlgHom⟩
  · refine ⟨(IntermediateField.inclusion
      (show G' ≤ (Mfg : IntermediateField ℚ (AlgebraicClosure ℚ)) from by
        change (Gfg : IntermediateField ℚ (AlgebraicClosure ℚ)) ≤
          (Mfg : IntermediateField ℚ (AlgebraicClosure ℚ))
        exact le_sup_right)).comp eG'.toAlgHom⟩
  · have hodd : Odd (Module.finrank ℚ (layerField i)) :=
      (trivial_intersection_gaussian i).2
    have hKdeg : Module.finrank ℚ ↥K' = Module.finrank ℚ (layerField i) := by
      simpa using eK'.symm.toLinearEquiv.finrank_eq
    have hGdeg_range : Module.finrank ℚ ↥G' = Module.finrank ℚ GaussianField := by
      simpa using eG'.symm.toLinearEquiv.finrank_eq
    have hGdeg : Module.finrank ℚ ↥G' = 2 := by
      rw [hGdeg_range]
      have hcyclo :
          Module.finrank ℚ GaussianField = Nat.totient 4 := by
        simpa [GaussianField] using
          (IsCyclotomicExtension.finrank (n := 4) (K := ℚ) (L := GaussianField)
            (Polynomial.cyclotomic.irreducible_rat (by decide : 0 < 4)))
      norm_num at hcyclo
      exact hcyclo
    have hld0 : K'.LinearDisjoint ↥G' := by
      apply IntermediateField.LinearDisjoint.of_finrank_coprime
      rw [hKdeg, hGdeg]
      exact hodd.coprime_two_right
    have hld : K'.LinearDisjoint G' := by
      rw [IntermediateField.linearDisjoint_iff] at hld0 ⊢
      simpa [AlgHom.fieldRange_toSubalgebra] using hld0
    calc
      Module.finrank ℚ ↥Mfg = Module.finrank ℚ ↥K' * Module.finrank ℚ ↥G' := by
        change
          Module.finrank ℚ ↥(K' ⊔ G') =
            Module.finrank ℚ ↥K' * Module.finrank ℚ ↥G'
        exact hld.finrank_sup
      _ = Module.finrank ℚ (layerField i) * 2 := by rw [hKdeg, hGdeg]
      _ = 2 * Module.finrank ℚ (layerField i) := Nat.mul_comm _ _

noncomputable def gaussianCompositum (i : ℕ) : Type :=
  Classical.choose (exists_gaussianCompositum i)

noncomputable instance instFieldGaussian (i : ℕ) : Field (gaussianCompositum i) :=
  Classical.choose (Classical.choose_spec (exists_gaussianCompositum i))

noncomputable instance instGaussianCompositum (i : ℕ) :
    NumberField (gaussianCompositum i) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (exists_gaussianCompositum i)))

noncomputable instance instRatGaussian (i : ℕ) :
    Algebra ℚ (gaussianCompositum i) :=
  Classical.choose
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (exists_gaussianCompositum i))))

theorem gaussianCompositum_spec (i : ℕ) :
    GaussianCompositum (layerField i) (gaussianCompositum i) := by
  exact Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (exists_gaussianCompositum i))))

theorem gaussian_compositum_galois (i : ℕ) :
    GaloisExtensionQ (gaussianCompositum i) := by
  exact (gaussianCompositum_spec i).1

/- We now choose rational primes `q_0, q_1, q_2, ...` recursively. -/
theorem chosen_prime_sequence :
    ∃ q : ℕ → ℕ,
      Function.Injective q ∧
        ∀ i,
          Nat.Prime (q i) ∧
            q i ∉ initialRamifiedPrimes ∧
            splitsCompletely (gaussianCompositum i) (q i) := by
  letI : IsGalois ℚ (gaussianCompositum 0) := gaussian_compositum_galois 0
  obtain ⟨q0, -, hq0prime, hq0avoid, hq0split⟩ :=
    SPExist.not_splits_completely
      (M := gaussianCompositum 0) (T := initialRamifiedPrimes) 0
  have hnext :
      ∀ n p : ℕ,
        ∃ r,
          r > p ∧
            Nat.Prime r ∧
            r ∉ initialRamifiedPrimes ∧
            splitsCompletely (gaussianCompositum (n + 1)) r := by
    intro n p
    letI : IsGalois ℚ (gaussianCompositum (n + 1)) :=
      gaussian_compositum_galois (n + 1)
    exact SPExist.not_splits_completely
      (M := gaussianCompositum (n + 1)) (T := initialRamifiedPrimes) p
  let q : ℕ → ℕ :=
    Nat.rec q0 fun n qn => Classical.choose (hnext n qn)
  have hq0 :
      Nat.Prime (q 0) ∧
        q 0 ∉ initialRamifiedPrimes ∧
        splitsCompletely (gaussianCompositum 0) (q 0) := by
    simpa [q] using ⟨hq0prime, hq0avoid, hq0split⟩
  have hsucc :
      ∀ n,
        q (n + 1) > q n ∧
          Nat.Prime (q (n + 1)) ∧
            q (n + 1) ∉ initialRamifiedPrimes ∧
            splitsCompletely (gaussianCompositum (n + 1)) (q (n + 1)) := by
    intro n
    simpa [q] using Classical.choose_spec (hnext n (q n))
  have hstrict : StrictMono q := by
    exact strictMono_nat_of_lt_succ fun n => (hsucc n).1
  refine ⟨q, hstrict.injective, ?_⟩
  intro i
  cases i with
  | zero =>
      exact hq0
  | succ n =>
      exact ⟨(hsucc n).2.1, (hsucc n).2.2.1, (hsucc n).2.2.2⟩

noncomputable def chosenPrime (i : ℕ) : ℕ :=
  Classical.choose chosen_prime_sequence i

/- By Chebotarev, choose a rational prime `q_i` splitting completely in `M_i`. -/
theorem chosenPrime_prime (i : ℕ) :
    Nat.Prime (chosenPrime i) := by
  exact ((Classical.choose_spec chosen_prime_sequence).2 i).1

theorem chosen_avoids_s (i : ℕ) :
    chosenPrime i ∉ initialRamifiedPrimes := by
  exact ((Classical.choose_spec chosen_prime_sequence).2 i).2.1

theorem chosen_avoids_previous (i j : ℕ) (hji : j < i) :
    chosenPrime i ≠ chosenPrime j := by
  exact fun hij => (Nat.ne_of_gt hji) ((Classical.choose_spec chosen_prime_sequence).1 hij)

theorem chosen_gaussian_compositum (i : ℕ) :
    splitsCompletely (gaussianCompositum i) (chosenPrime i) := by
  exact ((Classical.choose_spec chosen_prime_sequence).2 i).2.2

/- Then `q_i` splits completely in `ℚ(i)`. -/
theorem chosen_splits_gaussian (i : ℕ) :
    SplitsCompletelyRationals (chosenPrime i) := by
  let q := chosenPrime i
  have hq : Nat.Prime q := chosenPrime_prime i
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  letI : IsCyclotomicExtension {4} ℚ GaussianField := by
    dsimp [GaussianField]
    exact CyclotomicField.isCyclotomicExtension 4 ℚ
  letI : IsGalois ℚ GaussianField := IsCyclotomicExtension.isGalois {4} ℚ GaussianField
  haveI : IsGalois ℚ (gaussianCompositum i) := gaussian_compositum_galois i
  rcases (gaussianCompositum_spec i).2.2.1 with ⟨e⟩
  have hsplit : splitsCompletely GaussianField q :=
    splits_completely_hom e hq (by simpa [q] using chosen_gaussian_compositum i)
  have hq_ne_two : q ≠ 2 := by
    intro hq2
    letI : IsCyclotomicExtension {2 ^ (1 + 1)} ℚ GaussianField := by
      simpa [GaussianField] using CyclotomicField.isCyclotomicExtension (2 ^ (1 + 1)) ℚ
    letI : (Ideal.rationalPrimeIdeal 2).IsMaximal := rational_ideal_maximal Nat.prime_two
    obtain ⟨⟨P, hPPrime, hPLiesOver⟩⟩ :=
      (Ideal.rationalPrimeIdeal 2).nonempty_primesOver (S := 𝓞 GaussianField)
    letI : P.IsPrime := hPPrime
    letI : P.LiesOver (Ideal.rationalPrimeIdeal 2) := hPLiesOver
    have hPLiesOverSpan : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := by
      simpa [Ideal.rationalPrimeIdeal] using hPLiesOver
    letI : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := hPLiesOverSpan
    have hPmem :
        P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal 2) (𝓞 GaussianField) :=
      ⟨hPPrime, hPLiesOver⟩
    have hPmem' :
        P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q) (𝓞 GaussianField) := by
      simpa [q, hq2] using hPmem
    have hram_split : Ideal.ramificationIdx (Ideal.rationalPrimeIdeal 2) P = 1 := by
      simpa [q, hq2] using (hsplit.2 P hPmem').1
    have hram_cycl :
        Ideal.ramificationIdx (Ideal.rationalPrimeIdeal 2) P = 2 := by
      simpa [Ideal.rationalPrimeIdeal, GaussianField] using
        (IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime_pow
          (p := 2) (k := 1) (K := GaussianField) (P := P))
    omega
  have hq_not_dvd_four : ¬ q ∣ 4 := by
    intro hq_four
    have hq_two : q ∣ 2 := hq.dvd_of_dvd_pow (by simpa using hq_four : q ∣ 2 ^ 2)
    have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq_two
    exact hq_ne_two this
  letI : (Ideal.rationalPrimeIdeal q).IsMaximal := rational_ideal_maximal hq
  obtain ⟨⟨P, hPPrime, hPLiesOver⟩⟩ :=
    (Ideal.rationalPrimeIdeal q).nonempty_primesOver (S := 𝓞 GaussianField)
  letI : P.IsPrime := hPPrime
  letI : P.LiesOver (Ideal.rationalPrimeIdeal q) := hPLiesOver
  have hPLiesOverSpan : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := by
    simpa [Ideal.rationalPrimeIdeal] using hPLiesOver
  letI : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hPLiesOverSpan
  have hPmem :
      P ∈ Ideal.primesOver (Ideal.rationalPrimeIdeal q) (𝓞 GaussianField) :=
    ⟨hPPrime, hPLiesOver⟩
  have hinertia_split : Ideal.inertiaDeg (Ideal.rationalPrimeIdeal q) P = 1 :=
    (hsplit.2 P hPmem).2
  have hinertia_cycl :
      Ideal.inertiaDeg (Ideal.rationalPrimeIdeal q) P = orderOf (q : ZMod 4) := by
    simpa [Ideal.rationalPrimeIdeal, GaussianField] using
      (IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
        (p := q) (m := 4) (K := GaussianField) (P := P) hq_not_dvd_four)
  have hq_mod : (q : ZMod 4) = 1 := by
    apply orderOf_eq_one_iff.mp
    rw [← hinertia_cycl, hinertia_split]
  rw [SplitsCompletelyRationals]
  exact (ZMod.natCast_eq_natCast_iff' q 1 4).mp hq_mod

/- Hence `q_i ≡ 1 mod 4`. -/
theorem chosen_mod_four (i : ℕ) :
    chosenPrime i % 4 = 1 := by
  simpa [SplitsCompletelyRationals] using chosen_splits_gaussian i

/- Also `q_i` splits completely in `L_i`. -/
theorem chosen_splits_layer (i : ℕ) :
    splitsCompletely (layerField i) (chosenPrime i) := by
  letI : IsGalois ℚ (layerField i) := (layer_three_group i).1
  letI : IsGalois ℚ (gaussianCompositum i) := gaussian_compositum_galois i
  rcases (gaussianCompositum_spec i).2.1 with ⟨e⟩
  exact splits_completely_hom e (chosenPrime_prime i) (chosen_gaussian_compositum i)

/-
Choose a prime ideal `Q_i` of `L_i` lying above `q_i`.
-/
theorem chosen_layer_data (i : ℕ) :
    ∃ Q : Ideal.primesOver (Ideal.rationalPrimeIdeal (chosenPrime i))
        (NumberField.RingOfIntegers (layerField i)),
      Algebra.IsUnramifiedAt ℤ Q.1 := by
  let q : ℕ := chosenPrime i
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  have hq : Nat.Prime q := chosenPrime_prime i
  haveI : qI.IsPrime := rational_prime_ideal hq
  obtain ⟨Q⟩ := qI.nonempty_primesOver
    (S := NumberField.RingOfIntegers (layerField i))
  refine ⟨Q, ?_⟩
  letI : Q.1.IsPrime := Q.2.1
  letI : Q.1.LiesOver qI := Q.2.2
  have hQ0 : Q.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (rational_ne_bot hq) Q.1
  have hramQ :
      Ideal.ramificationIdx (Ideal.under ℤ Q.1) Q.1 = 1 := by
    rw [← Ideal.LiesOver.over (P := Q.1) (p := qI)]
    simpa [qI, q] using
      ((chosen_splits_layer i).2 Q.1
        (show Q.1 ∈ Ideal.primesOver qI
            (NumberField.RingOfIntegers (layerField i)) from Q.2)).1
  letI : Algebra.IsUnramifiedAt ℤ Q.1 :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
      (R := ℤ) (S := NumberField.RingOfIntegers (layerField i))
      (p := Q.1) hQ0).2 hramQ
  infer_instance

noncomputable def chosenLayerPrime (i : ℕ) :
    Ideal (NumberField.RingOfIntegers (layerField i)) :=
  (Classical.choose (chosen_layer_data i)).1

instance instChosenPrime (i : ℕ) :
    (chosenLayerPrime i).IsPrime := by
  exact (Classical.choose (chosen_layer_data i)).2.1

instance instChosenLies (i : ℕ) :
    (chosenLayerPrime i).LiesOver (Ideal.rationalPrimeIdeal (chosenPrime i)) := by
  exact (Classical.choose (chosen_layer_data i)).2.2

instance instChosenUnramified (i : ℕ) :
    Algebra.IsUnramifiedAt ℤ (chosenLayerPrime i) := by
  exact Classical.choose_spec (chosen_layer_data i)

instance instLayerGalois (i : ℕ) :
    IsGalois ℚ (layerField i) := by
  exact (layer_three_group i).1

instance instResidueChosen (i : ℕ) :
    Finite (NumberField.RingOfIntegers (layerField i) ⧸ chosenLayerPrime i) := by
  have hQ0 :
      chosenLayerPrime i ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
        (rational_ne_bot (chosenPrime_prime i)) (chosenLayerPrime i)
  exact Ideal.finiteQuotientOfFreeOfNeBot (chosenLayerPrime i) hQ0

set_option maxHeartbeats 800000 in
-- The scalar-tower instance on ring of integers takes extra elaboration through coercions.
set_option synthInstance.maxHeartbeats 100000 in
instance ring_integers_tower (i : ℕ) :
    IsScalarTower ℤ (𝓞 ↥(layerField i)) ↥(layerField i) := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  simp

set_option synthInstance.maxHeartbeats 100000 in
-- The invariance statement introduces several heavy typeclass searches around the layer field.
theorem ring_integers_invariant (i : ℕ) :
    Algebra.IsInvariant ℤ (𝓞 ↥(layerField i))
      (Gal(↥(layerField i)/ℚ)) := by
  letI : IsScalarTower ℤ (𝓞 ↥(layerField i)) ↥(layerField i) :=
    ring_integers_tower i
  refine ⟨?_⟩
  intro x hx
  letI : IsGaloisGroup (Gal(↥(layerField i)/ℚ)) ℚ ↥(layerField i) := by
    infer_instance
  have hx' : ∀ g : Gal(↥(layerField i)/ℚ),
      g • (algebraMap (NumberField.RingOfIntegers (layerField i)) (layerField i) x) =
        algebraMap (NumberField.RingOfIntegers (layerField i)) (layerField i) x := by
    intro g
    calc
      g • (algebraMap (NumberField.RingOfIntegers (layerField i)) (layerField i) x)
        = algebraMap (NumberField.RingOfIntegers (layerField i)) (layerField i) (g • x) := by
            simpa using
              (algebraMap.coe_smul'
                (B := NumberField.RingOfIntegers (layerField i))
                (C := layerField i) g x).symm
      _ = algebraMap (NumberField.RingOfIntegers (layerField i)) (layerField i) x := by
            exact congrArg
              (algebraMap (NumberField.RingOfIntegers (layerField i)) (layerField i)) (hx g)
  obtain ⟨q, hq⟩ :=
    Algebra.IsInvariant.isInvariant (A := ℚ) (B := ↥(layerField i))
      (G := Gal(↥(layerField i)/ℚ))
      (algebraMap (NumberField.RingOfIntegers (layerField i)) (layerField i) x) hx'
  have hx_int :
      IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers (layerField i)) (layerField i) x) :=
    NumberField.RingOfIntegers.isIntegral_coe x
  rw [← hq, isIntegral_algebraMap_iff (algebraMap ℚ (layerField i)).injective] at hx_int
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hx_int
  refine ⟨a, ?_⟩
  apply (FaithfulSMul.algebraMap_injective
    (NumberField.RingOfIntegers (layerField i)) (layerField i))
  calc
    algebraMap (NumberField.RingOfIntegers (layerField i)) (layerField i)
        (algebraMap ℤ (NumberField.RingOfIntegers (layerField i)) a)
      = algebraMap ℤ (layerField i) a := by
          simp
    _ = algebraMap ℚ (layerField i) q := by
          simpa [IsScalarTower.algebraMap_apply] using
            congrArg (algebraMap ℚ (layerField i)) ha
    _ = algebraMap (NumberField.RingOfIntegers (layerField i)) (layerField i) x := hq

/-
Let `x_i` be an arithmetic Frobenius at `Q_i`.
-/
noncomputable def chosenLayerFrobenius (i : ℕ) :
    Gal((layerField i)/ℚ) :=
  let _ := ring_integers_invariant i
  arithFrobAt ℤ (Gal((layerField i)/ℚ)) (chosenLayerPrime i)

theorem chosen_arith_frob (i : ℕ) :
    IsArithFrobAt ℤ (chosenLayerFrobenius i) (chosenLayerPrime i) := by
  let _ := ring_integers_invariant i
  simpa [chosenLayerFrobenius] using
    (IsArithFrobAt.arithFrobAt
      (R := ℤ) (S := NumberField.RingOfIntegers (layerField i))
      (G := Gal((layerField i)/ℚ)) (Q := chosenLayerPrime i))

/- Because `q_i` splits completely in `L_i`, this arithmetic Frobenius is trivial. -/
theorem chosen_layer_frobenius (i : ℕ) :
    chosenLayerFrobenius i = 1 := by
  have hGal : IsGalois ℚ (layerField i) := (layer_three_group i).1
  have hGal' : IsGalois ℚ ↥(layerField i) := by
    simpa using hGal
  have hiff :
      splitsCompletely (layerField i) (chosenPrime i) ↔ chosenLayerFrobenius i = 1 :=
    @completely_arith_frob
      ↥(layerField i) inferInstance inferInstance hGal'
      (chosenPrime i) (chosenPrime_prime i)
      (chosenLayerPrime i) inferInstance inferInstance inferInstance
      (chosenLayerFrobenius i) (chosen_arith_frob i)
  exact hiff.1 (chosen_splits_layer i)

/- Thus the primes `q_i` are distinct. -/
theorem chosenPrime_injective :
    Function.Injective chosenPrime := by
  exact (Classical.choose_spec chosen_prime_sequence).1

/- Thus we have constructed distinct rational primes `q_i ∉ S` with `q_i ≡ 1 mod 4`. -/
theorem chosenPrime_package (i : ℕ) :
    Nat.Prime (chosenPrime i) ∧
    chosenPrime i ∉ initialRamifiedPrimes ∧
    chosenPrime i % 4 = 1 := by
  exact ⟨chosenPrime_prime i, chosen_avoids_s i, chosen_mod_four i⟩

/- Thus we have constructed finite-level Frobenius data above `q_i`, and it is trivial in `L_i`. -/
theorem chosen_frobenius_package (i : ℕ) :
    IsArithFrobAt ℤ (chosenLayerFrobenius i) (chosenLayerPrime i) ∧
    chosenLayerFrobenius i = 1 := by
  exact ⟨chosen_arith_frob i, chosen_layer_frobenius i⟩

/-- Compose a finite-level embedding with an ambient extension embedding. -/
theorem embeds_extension_trans
    {K : Type} [Field K] [NumberField K] [Algebra ℚ K]
    {L M : Type} [Field L] [Algebra ℚ L] [Field M] [Algebra ℚ M]
    (hKL : EmbedsIntoExtension K L)
    (hLM : ExtensionEmbeds L M) :
    EmbedsIntoExtension K M := by
  rcases hKL with ⟨f⟩
  rcases hLM with ⟨g⟩
  exact ⟨g.comp f⟩

/-- The finite Galois building blocks used in the defining `iSup` for `Q_S^(3)`. -/
abbrev ProThreeComponent :=
  {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
    IsPGroup 3 (Gal(E/ℚ)) ∧ UnramifiedOutside E initialRamifiedPrimes}

/-- A finite stage of the defining compositum for `Q_S^(3)`. This is the specialized finite
compositum whose ramification control is the next missing input for the tower argument. -/
noncomputable def initialProCompositum
    (T : Finset ProThreeComponent) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  ⨆ E ∈ T, E.1.toIntermediateField

noncomputable instance instRatCompositum
    (T : Finset ProThreeComponent) :
    Algebra ℚ ↥(initialProCompositum T) :=
  (initialProCompositum T).algebra

instance instModuleCompositum
    (T : Finset ProThreeComponent) :
    Module ℚ ↥(initialProCompositum T) := by
  let _ := instRatCompositum T
  infer_instance

instance instDimensionalCompositum
    (T : Finset ProThreeComponent) :
    FiniteDimensional ℚ ↥(initialProCompositum T) := by
  change FiniteDimensional ℚ ↥(⨆ E ∈ T, E.1.toIntermediateField)
  exact IntermediateField.finiteDimensional_iSup_of_finset'
    (t := fun E : ProThreeComponent => E.1.toIntermediateField)
    (s := T) (fun E _ => inferInstance)

instance instProCompositum
    (T : Finset ProThreeComponent) :
    NumberField ↥(initialProCompositum T) := by
  letI : FiniteDimensional ℚ ↥(initialProCompositum T) :=
    instDimensionalCompositum T
  exact NumberField.of_module_finite ℚ ↥(initialProCompositum T)

instance ring_scalar_tower
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K] :
    IsScalarTower ℤ (𝓞 K) K := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  simp

theorem compositum_i_sup
    (T : Finset ProThreeComponent) :
    let ι := {E // E ∈ T}
    let t : ι → IntermediateField ℚ (AlgebraicClosure ℚ) :=
      fun E => E.1.1.toIntermediateField
    initialProCompositum T = ⨆ E : ι, t E := by
  classical
  unfold initialProCompositum
  apply le_antisymm
  · refine iSup_le fun E => iSup_le fun hE => ?_
    exact le_iSup_of_le ⟨E, hE⟩ le_rfl
  · refine iSup_le fun E => ?_
    exact le_iSup_of_le E.1 <| le_iSup_of_le E.2 le_rfl

theorem finset_compositum_galois
    (T : Finset ProThreeComponent) :
    IsGalois ℚ ↥(initialProCompositum T) := by
  classical
  let ι := {E // E ∈ T}
  let t : ι → IntermediateField ℚ (AlgebraicClosure ℚ) :=
    fun E => E.1.1.toIntermediateField
  have hEq :
      initialProCompositum T = ⨆ E : ι, t E := by
    simpa [ι, t] using compositum_i_sup T
  have hnormal :
      Normal ℚ ↥(⨆ E : ι, t E) := by
    simpa [t] using
      (IntermediateField.normal_iSup
        (F := ℚ) (K := AlgebraicClosure ℚ) (t := t)
        (h := fun E => by
          letI : IsGalois ℚ E.1.1 := E.1.1.isGalois
          simpa using (IsGalois.to_normal (F := ℚ) (E := E.1.1))))
  have hsep :
      Algebra.IsSeparable ℚ ↥(⨆ E : ι, t E) := by
    simpa [t] using
      (IntermediateField.isSeparable_iSup
        (F := ℚ) (E := AlgebraicClosure ℚ) (t := t)
        (h := fun E => by
          letI : IsGalois ℚ E.1.1 := E.1.1.isGalois
          simpa using (IsGalois.to_isSeparable (F := ℚ) (E := E.1.1))))
  letI : Algebra ℚ ↥(⨆ E : ι, t E) := (⨆ E : ι, t E).algebra
  have hgal : IsGalois ℚ ↥(⨆ E : ι, t E) := { to_isSeparable := hsep, to_normal := hnormal }
  letI : IsGalois ℚ ↥(⨆ E : ι, t E) := hgal
  exact IsGalois.of_algEquiv (IntermediateField.equivOfEq hEq.symm)

instance instGaloisCompositum
    (T : Finset ProThreeComponent) :
    IsGalois ℚ ↥(initialProCompositum T) :=
  finset_compositum_galois T

noncomputable def initialProComponent
    (T : Finset ProThreeComponent)
    (i : {E // E ∈ T}) :
    IntermediateField ℚ ↥(initialProCompositum T) :=
  let t : {E // E ∈ T} → IntermediateField ℚ (AlgebraicClosure ℚ) :=
    fun E => E.1.1.toIntermediateField
  (t i).restrict
    (show t i ≤ initialProCompositum T by
      exact le_iSup_of_le i.1 <| le_iSup_of_le i.2 le_rfl)

noncomputable def initial_compositum_component
    (T : Finset ProThreeComponent)
    (i : {E // E ∈ T}) :
    i.1.1 ≃ₐ[ℚ] ↥(initialProComponent T i) := by
  exact IntermediateField.restrict_algEquiv
    (show i.1.1.toIntermediateField ≤ initialProCompositum T by
      exact le_iSup_of_le i.1 <| le_iSup_of_le i.2 le_rfl)

instance instCompositumComponent
    (T : Finset ProThreeComponent)
    (i : {E // E ∈ T}) :
    FiniteDimensional ℚ ↥(initialProComponent T i) := by
  let e :=
    initial_compositum_component T i
  exact FiniteDimensional.of_surjective e.toLinearEquiv.toLinearMap e.surjective

instance finsetCompositumComponent
    (T : Finset ProThreeComponent)
    (i : {E // E ∈ T}) :
    NumberField ↥(initialProComponent T i) := by
  exact NumberField.of_module_finite ℚ ↥(initialProComponent T i)

theorem compositum_component_galois
    (T : Finset ProThreeComponent)
    (i : {E // E ∈ T}) :
    IsGalois ℚ ↥(initialProComponent T i) := by
  letI : IsGalois ℚ i.1.1 := i.1.1.isGalois
  exact IsGalois.of_algEquiv
    (initial_compositum_component T i)

instance proCompositumComponent
    (T : Finset ProThreeComponent)
    (i : {E // E ∈ T}) :
    IsGalois ℚ ↥(initialProComponent T i) :=
  compositum_component_galois T i

theorem pro_component_unramified
    (T : Finset ProThreeComponent)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ initialRamifiedPrimes)
    (i : {E // E ∈ T}) :
    RationalPrimeUnramified
      (S := 𝓞 ↥(initialProComponent T i)) q := by
  exact
    rational_unramified_alg
      (initial_compositum_component T i)
      (i.1.2.2 q hq hqS)

theorem pro_component_integers
    (T : Finset ProThreeComponent)
    (i : {E // E ∈ T}) :
    IsGaloisGroup
      (Gal(↥(initialProComponent T i)/ℚ))
      ℤ
      (𝓞 ↥(initialProComponent T i)) := by
  let E := initialProComponent T i
  let hst : IsScalarTower ℤ (𝓞 ↥E) ↥E :=
    ring_scalar_tower (K := ↥E)
  exact
    @IsGaloisGroup.of_isFractionRing
      (Gal(↥E/ℚ))
      ℤ
      (𝓞 ↥E)
      ℚ
      ↥E
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hst
      _ _ _ _ _

theorem compositum_component_normal
    (T : Finset ProThreeComponent)
    (i : {E // E ∈ T}) :
    Normal ℚ ↥(initialProComponent T i) := by
  letI : IsGalois ℚ ↥(initialProComponent T i) :=
    compositum_component_galois T i
  infer_instance

set_option maxHeartbeats 800000 in
-- Restricting inertia through a compositum component unfolds the dependent prime tower.
set_option synthInstance.maxHeartbeats 200000 in
-- The component and compositum inertia instances require a larger synthesis budget.
theorem pro_component_restrict
    (T : Finset ProThreeComponent)
    {q : ℕ}
    {P : Ideal (𝓞 ↥(initialProCompositum T))}
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : Gal(↥(initialProCompositum T)/ℚ))
    (hσ : σ ∈ P.inertia (Gal(↥(initialProCompositum T)/ℚ)))
    (i : {E // E ∈ T}) :
    AlgEquiv.restrictNormalHom (initialProComponent T i) σ ∈
      (P.under (𝓞 ↥(initialProComponent T i))).inertia
        (Gal(↥(initialProComponent T i)/ℚ)) := by
  let E := initialProComponent T i
  letI : IsGalois ℚ ↥E := compositum_component_galois T i
  letI : Normal ℚ ↥E := IsGalois.to_normal
  letI : Normal ℚ ↥(initialProComponent T i) :=
    compositum_component_normal T i
  letI : IsScalarTower ℤ (𝓞 ↥E) ↥E := ring_scalar_tower (K := ↥E)
  letI : IsGalois ℚ ↥(initialProCompositum T) :=
    finset_compositum_galois T
  let Q : Ideal (𝓞 ↥E) := P.under (𝓞 ↥E)
  intro x
  change
    MulSemiringAction.toAlgHom ℤ (𝓞 ↥E)
      (AlgEquiv.restrictNormalHom E σ) x - x ∈ Q
  rw [Ideal.mem_of_liesOver
    (A := 𝓞 ↥E)
    (B := 𝓞 ↥(initialProCompositum T))
    (p := Q)
    (P := P)]
  rw [map_sub]
  have hmap :
      algebraMap (𝓞 ↥E) (𝓞 ↥(initialProCompositum T))
        (MulSemiringAction.toAlgHom ℤ
          (𝓞 ↥E) (σ.restrictNormalHom E) x) =
      MulSemiringAction.toAlgHom ℤ
        (𝓞 ↥(initialProCompositum T)) σ
          (algebraMap (𝓞 ↥E)
            (𝓞 ↥(initialProCompositum T)) x) := by
    apply Subtype.ext
    change
      algebraMap ↥(initialProComponent T i)
          ↥(initialProCompositum T)
          (((AlgEquiv.restrictNormalHom
              (initialProComponent T i)) σ)
            (algebraMap
              (𝓞 ↥(initialProComponent T i))
              ↥(initialProComponent T i)
              x)) =
        σ
          (algebraMap ↥(initialProComponent T i)
            ↥(initialProCompositum T)
            (algebraMap
              (𝓞 ↥(initialProComponent T i))
              ↥(initialProComponent T i)
              x))
    simpa using
      (@AlgEquiv.restrictNormalHom_apply
        ℚ
        _
        ↥(initialProCompositum T)
        _
        _
        (initialProComponent T i)
        (compositum_component_normal T i)
        σ
        (algebraMap
          (𝓞 ↥(initialProComponent T i))
          ↥(initialProComponent T i)
          x))
  rw [hmap]
  simpa using hσ (algebraMap (𝓞 ↥E) (𝓞 ↥(initialProCompositum T)) x)

theorem initial_pro_component
    (T : Finset ProThreeComponent)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ initialRamifiedPrimes)
    {P : Ideal (𝓞 ↥(initialProCompositum T))}
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (i : {E // E ∈ T}) :
    Nat.card
      ((P.under (𝓞 ↥(initialProComponent T i))).inertia
        (Gal(↥(initialProComponent T i)/ℚ))) = 1 := by
  let E := initialProComponent T i
  letI : IsGalois ℚ ↥E := compositum_component_galois T i
  letI :
      IsGaloisGroup
        (Gal(↥E/ℚ))
        ℤ
        (𝓞 ↥E) :=
    pro_component_integers T i
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsMaximal := rational_ideal_maximal hq
  letI : Field (ℤ ⧸ qI) := Ideal.Quotient.field qI
  let Q : Ideal (𝓞 ↥E) := P.under (𝓞 ↥E)
  have hQmem : Q ∈ Ideal.primesOver qI (𝓞 ↥E) := by
    refine ⟨inferInstance, inferInstance⟩
  have hQram : Ideal.ramificationIdx qI Q = 1 := by
    exact
      pro_component_unramified
        T hq hqS i Q hQmem
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqI0 Q
  letI : Q.IsMaximal := Ideal.IsPrime.isMaximal (show Q.IsPrime by infer_instance) hQ0
  letI : Field ((𝓞 ↥E) ⧸ Q) := Ideal.Quotient.field Q
  letI : Algebra.IsSeparable (ℤ ⧸ qI) ((𝓞 ↥E) ⧸ Q) := by
    letI : IsGalois (ℤ ⧸ qI) ((𝓞 ↥E) ⧸ Q) :=
      { __ := Ideal.Quotient.normal (A := ℤ) (G := Gal(↥E/ℚ)) qI Q }
    infer_instance
  have hramIn : qI.ramificationIdxIn (𝓞 ↥E) = 1 := by
    calc
      qI.ramificationIdxIn (𝓞 ↥E) = Ideal.ramificationIdx qI Q := by
        exact Ideal.ramificationIdxIn_eq_ramificationIdx
          (p := qI) (P := Q) (G := Gal(↥E/ℚ))
      _ = 1 := hQram
  calc
    Nat.card (Q.inertia (Gal(↥E/ℚ))) = qI.ramificationIdxIn (𝓞 ↥E) := by
      exact Ideal.card_inertia_eq_ramificationIdxIn
        (G := Gal(↥E/ℚ)) qI hqI0 Q
    _ = 1 := hramIn

set_option synthInstance.maxHeartbeats 200000 in
-- Identifying restricted inertia with the trivial component action needs deeper synthesis.
theorem compositum_component_restriction
    (T : Finset ProThreeComponent)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ initialRamifiedPrimes)
    {P : Ideal (𝓞 ↥(initialProCompositum T))}
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (σ : Gal(↥(initialProCompositum T)/ℚ))
    (hσ : σ ∈ P.inertia (Gal(↥(initialProCompositum T)/ℚ)))
    (i : {E // E ∈ T}) :
    AlgEquiv.restrictNormalHom (initialProComponent T i) σ = 1 := by
  let E := initialProComponent T i
  letI : IsGalois ℚ ↥E := compositum_component_galois T i
  let σE : Gal(↥E/ℚ) := AlgEquiv.restrictNormalHom E σ
  let Q : Ideal (𝓞 ↥E) := P.under (𝓞 ↥E)
  have hσE :
      σE ∈ Q.inertia (Gal(↥E/ℚ)) := by
    exact
      pro_component_restrict
        (q := q) (P := P) T σ hσ i
  have hcard :
      Nat.card (Q.inertia (Gal(↥E/ℚ))) = 1 := by
    exact
      initial_pro_component
        T hq hqS i
  have hsub :
      Subsingleton ↥(Q.inertia (Gal(↥E/ℚ))) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  letI : Subsingleton ↥(Q.inertia (Gal(↥E/ℚ))) := hsub
  have hσEeq :
      (⟨σE, hσE⟩ : Q.inertia (Gal(↥E/ℚ))) = 1 := by
    exact Subsingleton.elim _ _
  exact congrArg Subtype.val hσEeq

theorem pro_components_top
    (T : Finset ProThreeComponent) :
    let ι := {E // E ∈ T}
    (⨆ i ∈ (Finset.univ : Finset ι), initialProComponent T i) = ⊤ := by
  classical
  let ι := {E // E ∈ T}
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := initialProCompositum T
  let A : IntermediateField ℚ ↥K :=
    ⨆ i ∈ (Finset.univ : Finset ι), initialProComponent T i
  change A = ⊤
  apply (IntermediateField.lift_injective K)
  change IntermediateField.lift A = IntermediateField.lift (⊤ : IntermediateField ℚ ↥K)
  rw [show IntermediateField.lift (⊤ : IntermediateField ℚ ↥K) = K by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩]
  refine le_antisymm (IntermediateField.lift_le A) ?_
  change initialProCompositum T ≤ IntermediateField.lift A
  rw [compositum_i_sup T]
  refine iSup_le fun i => ?_
  have hi : initialProComponent T i ≤ A := by
    exact le_iSup_of_le i <| le_iSup_of_le (by simp) le_rfl
  have hmap :
      IntermediateField.lift (initialProComponent T i) ≤
        IntermediateField.lift A := by
    exact IntermediateField.map_mono (IntermediateField.val K) hi
  simpa [K, initialProComponent] using hmap

set_option maxHeartbeats 800000 in
-- Combining every component restriction through the finite compositum exceeds the default budget.
set_option synthInstance.maxHeartbeats 200000 in
-- The dependent family of component Galois actions is expensive to synthesize.
theorem finset_compositum_trivial
    (T : Finset ProThreeComponent)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ initialRamifiedPrimes)
    {P : Ideal (𝓞 ↥(initialProCompositum T))}
    [P.IsPrime] [P.LiesOver (Ideal.rationalPrimeIdeal q)] :
    ∀ σ : P.inertia (Gal(↥(initialProCompositum T)/ℚ)), σ = 1 := by
  intro σ
  classical
  let ι := {E // E ∈ T}
  have hfix :
      ∀ i : ι,
        (σ : Gal(↥(initialProCompositum T)/ℚ)) ∈
          (initialProComponent T i).fixingSubgroup := by
    intro i
    letI : IsGalois ℚ ↥(initialProComponent T i) :=
      compositum_component_galois T i
    letI : Normal ℚ ↥(initialProComponent T i) :=
      IsGalois.to_normal
    have hrestrict :
        AlgEquiv.restrictNormalHom (initialProComponent T i)
            (σ : Gal(↥(initialProCompositum T)/ℚ)) =
          1 :=
      compositum_component_restriction
        T hq hqS (σ : Gal(↥(initialProCompositum T)/ℚ)) σ.2 i
    rw [IntermediateField.mem_fixingSubgroup_iff
      (K := initialProComponent T i)]
    intro x hx
    have hsub :
        (AlgEquiv.restrictNormalHom (initialProComponent T i)
            (σ : Gal(↥(initialProCompositum T)/ℚ))) ⟨x, hx⟩ =
          ⟨x, hx⟩ := by
      simpa using congrArg (fun τ => τ ⟨x, hx⟩) hrestrict
    calc
      (σ : Gal(↥(initialProCompositum T)/ℚ)) x =
          ↑((AlgEquiv.restrictNormalHom (initialProComponent T i)
            (σ : Gal(↥(initialProCompositum T)/ℚ))) ⟨x, hx⟩) := by
        symm
        change
          ↑(((σ : Gal(↥(initialProCompositum T)/ℚ)).restrictNormal
              ↥(initialProComponent T i)) ⟨x, hx⟩) =
            (σ : Gal(↥(initialProCompositum T)/ℚ)) x
        exact
          AlgEquiv.restrictNormal_commutes
            (χ := (σ : Gal(↥(initialProCompositum T)/ℚ)))
            (E := initialProComponent T i) ⟨x, hx⟩
      _ = x := congrArg Subtype.val hsub
  have hsup :
      (σ : Gal(↥(initialProCompositum T)/ℚ)) ∈
        (⨆ i : ι, initialProComponent T i).fixingSubgroup := by
    have hs :
        ∀ s : Finset ι,
          (σ : Gal(↥(initialProCompositum T)/ℚ)) ∈
            (s.sup fun i => initialProComponent T i).fixingSubgroup := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp
      · intro a s ha hs
        rw [Finset.sup_insert, IntermediateField.fixingSubgroup_sup]
        exact ⟨hfix a, hs⟩
    simpa [Finset.sup_eq_iSup] using hs Finset.univ
  have hsup_eq_top :
      (⨆ i : ι, initialProComponent T i) = ⊤ := by
    simpa [ι, Finset.sup_eq_iSup] using
      (pro_components_top T)
  have htop :
      (σ : Gal(↥(initialProCompositum T)/ℚ)) ∈
        (⊤ : IntermediateField ℚ ↥(initialProCompositum T)).fixingSubgroup := by
    rwa [hsup_eq_top] at hsup
  have hσ : (σ : Gal(↥(initialProCompositum T)/ℚ)) = 1 := by
    rwa [IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at htop
  exact Subtype.ext hσ

set_option maxHeartbeats 800000 in
-- Converting trivial inertia into the ramification-index formula unfolds the integer tower.
theorem finset_compositum_ramification
    (T : Finset ProThreeComponent)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ initialRamifiedPrimes) :
    (Ideal.rationalPrimeIdeal q).ramificationIdxIn
      (𝓞 ↥(initialProCompositum T)) = 1 := by
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsMaximal := rational_ideal_maximal hq
  letI : Field (ℤ ⧸ qI) := Ideal.Quotient.field qI
  let hst : IsScalarTower ℤ (𝓞 ↥(initialProCompositum T))
      ↥(initialProCompositum T) :=
    ring_scalar_tower
      (K := ↥(initialProCompositum T))
  letI : IsGaloisGroup Gal(↥(initialProCompositum T)/ℚ) ℤ
      (𝓞 ↥(initialProCompositum T)) :=
    by
      exact
        @IsGaloisGroup.of_isFractionRing
          (Gal(↥(initialProCompositum T)/ℚ))
          ℤ (𝓞 ↥(initialProCompositum T)) ℚ
          ↥(initialProCompositum T)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ hst _ _ _ _ _
  obtain ⟨P, hP⟩ :
      Set.Nonempty
        (Ideal.primesOver qI (𝓞 ↥(initialProCompositum T))) :=
    Set.nonempty_of_ncard_ne_zero <|
      IsDedekindDomain.primesOver_ncard_ne_zero qI (𝓞 ↥(initialProCompositum T))
  letI : P.IsPrime := hP.1
  letI : P.LiesOver qI := hP.2
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqI0 P
  letI : P.IsMaximal := hP.1.isMaximal hP0
  letI : Field ((𝓞 ↥(initialProCompositum T)) ⧸ P) := Ideal.Quotient.field P
  letI : Algebra.IsSeparable (ℤ ⧸ qI)
      ((𝓞 ↥(initialProCompositum T)) ⧸ P) := by
    letI : IsGalois (ℤ ⧸ qI)
        ((𝓞 ↥(initialProCompositum T)) ⧸ P) :=
      { __ := Ideal.Quotient.normal
          (A := ℤ) (G := Gal(↥(initialProCompositum T)/ℚ)) qI P }
    infer_instance
  have hcard :
      Nat.card
        (P.inertia (Gal(↥(initialProCompositum T)/ℚ))) = 1 := by
    have hsub :
        Subsingleton
          ↥(P.inertia (Gal(↥(initialProCompositum T)/ℚ))) := by
      refine ⟨?_⟩
      intro σ τ
      calc
        σ = 1 := finset_compositum_trivial T hq hqS σ
        _ = τ := by
          symm
          exact finset_compositum_trivial T hq hqS τ
    letI :
        Subsingleton
          ↥(P.inertia (Gal(↥(initialProCompositum T)/ℚ))) := hsub
    letI :
        Fintype
          ↥(P.inertia (Gal(↥(initialProCompositum T)/ℚ))) :=
      Fintype.ofSubsingleton
        (1 : P.inertia (Gal(↥(initialProCompositum T)/ℚ)))
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ofSubsingleton
      (1 : P.inertia (Gal(↥(initialProCompositum T)/ℚ)))
  calc
    qI.ramificationIdxIn (𝓞 ↥(initialProCompositum T)) =
        Nat.card
          (P.inertia (Gal(↥(initialProCompositum T)/ℚ))) := by
      symm
      exact Ideal.card_inertia_eq_ramificationIdxIn
        (G := Gal(↥(initialProCompositum T)/ℚ)) qI hqI0 P
    _ = 1 := hcard

theorem finset_compositum_unramified
    (T : Finset ProThreeComponent)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ initialRamifiedPrimes) :
    RationalPrimeUnramified (S := 𝓞 ↥(initialProCompositum T)) q := by
  simpa [RationalPrimeUnramified, RationalRamificationIdx] using
    fun P hP => by
      rw [rational_idx_primes
        (L := ↥(initialProCompositum T)) (hr := hq) hP]
      exact finset_compositum_ramification T hq hqS

/-- The first missing ramification lemma for the tower: a finite compositum of the defining
finite Galois `3`-extensions is still unramified outside `initialRamifiedPrimes`. -/
theorem finset_compositum_outside
    (T : Finset ProThreeComponent) :
    UnramifiedOutside ↥(initialProCompositum T) initialRamifiedPrimes := by
  intro q hq hqS
  exact finset_compositum_unramified T hq hqS

set_option maxHeartbeats 800000 in
-- Trapping a finite subextension inside a finite stage of the ambient `iSup` needs extra
-- reduction budget for the basis-and-restriction bookkeeping.
set_option synthInstance.maxHeartbeats 100000 in
/-- Once the finite-stage composita are controlled, every finite Galois subextension of
`Q_S^(3)` should inherit the same unramified-outside condition by passing through a finite
stage of the defining `iSup`. -/
theorem initial_subextension_outside
    (E : FiniteGaloisIntermediateField ℚ initialProExtension) :
    UnramifiedOutside E initialRamifiedPrimes := by
  classical
  letI : IsGalois ℚ ↥E := E.isGalois
  let b := Module.finBasis ℚ E
  let supports : Fin (Module.finrank ℚ E) → Finset ProThreeComponent := fun i =>
    Classical.choose <|
      IntermediateField.exists_finset_of_mem_iSup
        (f := fun F : ProThreeComponent => F.1.toIntermediateField)
        (show (((b i : E) : initialProExtension) : AlgebraicClosure ℚ) ∈
            initialProIntermediate from
          (((b i : E) : initialProExtension)).2)
  let T : Finset ProThreeComponent := Finset.univ.biUnion supports
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := initialProCompositum T
  have hbasis_mem_K :
      ∀ i : Fin (Module.finrank ℚ E),
        (((b i : E) : initialProExtension) : AlgebraicClosure ℚ) ∈ K := by
    intro i
    have hi :
        (((b i : E) : initialProExtension) : AlgebraicClosure ℚ) ∈
          ⨆ F ∈ supports i, F.1.toIntermediateField :=
      Classical.choose_spec <|
        IntermediateField.exists_finset_of_mem_iSup
          (f := fun F : ProThreeComponent => F.1.toIntermediateField)
          (show (((b i : E) : initialProExtension) : AlgebraicClosure ℚ) ∈
              initialProIntermediate from
            (((b i : E) : initialProExtension)).2)
    have hle : (⨆ F ∈ supports i, F.1.toIntermediateField) ≤ K := by
      unfold K initialProCompositum
      refine iSup_le fun F => iSup_le fun hF => ?_
      exact
        le_iSup_of_le F <|
          le_iSup_of_le
            (by
              exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hF⟩)
            le_rfl
    exact hle hi
  have hKle : K ≤ initialProIntermediate := by
    unfold K initialProCompositum initialProIntermediate
    refine iSup_le fun F => iSup_le fun hF => ?_
    exact le_iSup_of_le F le_rfl
  let K' : IntermediateField ℚ initialProExtension := K.restrict hKle
  have hbasis_mem_K' :
      ∀ i : Fin (Module.finrank ℚ E), ((b i : E) : initialProExtension) ∈ K' := by
    intro i
    exact
      (IntermediateField.mem_restrict hKle (((b i : E) : initialProExtension))).2
        (hbasis_mem_K i)
  have hE_le_K' : E ≤ K' := by
    intro x hx
    let xE : E := ⟨x, hx⟩
    have hxsumE : ∑ i, (b.repr xE i : ℚ) • (b i : E) = xE := b.sum_repr xE
    have hcoe :
        (((∑ i, (b.repr xE i : ℚ) • (b i : E)) : E) : initialProExtension) =
          ∑ i, (b.repr xE i : ℚ) • (((b i : E) : initialProExtension)) := by
      simpa using
        (IntermediateField.coe_sum (f := fun i =>
          (b.repr xE i : ℚ) • (b i : E)))
    have hxsum :
        ∑ i, (b.repr xE i : ℚ) • (((b i : E) : initialProExtension)) = x := by
      exact hcoe.symm.trans (congrArg Subtype.val hxsumE)
    have hxmem :
        ∑ i, (b.repr xE i : ℚ) • (((b i : E) : initialProExtension)) ∈ K' := by
      simpa using
        K'.sum_mem (t := Finset.univ) (fun i _ => K'.smul_mem (hbasis_mem_K' i))
    exact hxsum.symm ▸ hxmem
  let E' : IntermediateField ℚ K' := E.restrict hE_le_K'
  let eE : E ≃ₐ[ℚ] ↥E' := IntermediateField.restrict_algEquiv hE_le_K'
  let ι := {F // F ∈ T}
  let t : ι → IntermediateField ℚ (AlgebraicClosure ℚ) := fun F => F.1.1.toIntermediateField
  let K0 : IntermediateField ℚ (AlgebraicClosure ℚ) := ⨆ F : ι, t F
  letI : Algebra ℚ ↥K0 := K0.algebra
  have hK_eq : K = K0 := by
    unfold K initialProCompositum
    apply le_antisymm
    · refine iSup_le fun F => iSup_le fun hF => ?_
      exact le_iSup_of_le ⟨F, hF⟩ le_rfl
    · refine iSup_le fun F => ?_
      exact le_iSup_of_le F.1 <| le_iSup_of_le F.2 le_rfl
  have hK_normal : Normal ℚ ↥K0 := by
    change Normal ℚ ↥(⨆ F : ι, t F)
    simpa [K0, t] using
      (IntermediateField.normal_iSup
        (F := ℚ) (K := AlgebraicClosure ℚ) (t := t)
        (h := fun F => by
          letI : IsGalois ℚ ↥(F.1.1) := F.1.1.isGalois
          simpa using (IsGalois.to_normal (F := ℚ) (E := ↥(F.1.1)))))
  have hK_sep : Algebra.IsSeparable ℚ ↥K0 := by
    change Algebra.IsSeparable ℚ ↥(⨆ F : ι, t F)
    simpa [K0, t] using
      (IntermediateField.isSeparable_iSup
        (F := ℚ) (E := AlgebraicClosure ℚ) (t := t)
        (h := fun F => by
          letI : IsGalois ℚ ↥(F.1.1) := F.1.1.isGalois
          simpa using (IsGalois.to_isSeparable (F := ℚ) (E := ↥(F.1.1)))))
  have hK_galois_aux : IsGalois ℚ ↥K0 := by
    exact { to_normal := hK_normal, to_isSeparable := hK_sep }
  letI : IsGalois ℚ ↥K0 := hK_galois_aux
  letI : IsGalois ℚ ↥K := IsGalois.of_algEquiv (IntermediateField.equivOfEq hK_eq).symm
  let eK : ↥K ≃ₐ[ℚ] ↥K' := IntermediateField.restrict_algEquiv hKle
  letI : FiniteDimensional ℚ ↥K' :=
    FiniteDimensional.of_surjective eK.toLinearEquiv.toLinearMap eK.surjective
  letI : NumberField ↥K' := NumberField.of_module_finite ℚ ↥K'
  letI : IsGalois ℚ ↥K' := IsGalois.of_algEquiv eK
  letI : FiniteDimensional ℚ ↥E' :=
    FiniteDimensional.of_surjective eE.toLinearEquiv.toLinearMap eE.surjective
  letI : NumberField ↥E' := NumberField.of_module_finite ℚ ↥E'
  letI : IsGalois ℚ ↥E' := IsGalois.of_algEquiv eE
  have hK'_unram : UnramifiedOutside ↥K' initialRamifiedPrimes := by
    intro q hq hqS
    exact
      rational_unramified_alg eK
        (finset_compositum_outside T q hq hqS)
  have hE'_unram : UnramifiedOutside ↥E' initialRamifiedPrimes := by
    intro q hq hqS
    exact
      rational_unramified_intermediate
        (K := ↥K') E' hq (hK'_unram q hq hqS)
  intro q hq hqS
  exact rational_unramified_alg eE.symm (hE'_unram q hq hqS)

/-- A finite Galois number field embedding into `Q_S^(3)` should therefore already be
unramified outside `initialRamifiedPrimes`. This is the wrapper `tower_unramified_outside`
will use after moving to the field range of the embedding. -/
theorem unramified_outside_embeds
    {K : Type} [Field K] [NumberField K] [Algebra ℚ K] [IsGalois ℚ K]
    (hK : EmbedsIntoExtension K initialProExtension) :
    UnramifiedOutside K initialRamifiedPrimes := by
  rw [UnramifiedOutside, RamifiedOnlyAt]
  intro q hq hqS
  rcases hK with ⟨f⟩
  let E : IntermediateField ℚ initialProExtension := f.fieldRange
  let e : K ≃ₐ[ℚ] ↥E := by
    simpa [E, AlgHom.fieldRange_toSubalgebra f] using (AlgEquiv.ofInjectiveField f)
  letI : FiniteDimensional ℚ ↥E :=
    FiniteDimensional.of_surjective e.toLinearEquiv.toLinearMap e.surjective
  letI : NumberField ↥E := NumberField.of_module_finite ℚ ↥E
  have hE_gal : IsGalois ℚ ↥E := IsGalois.of_algEquiv e
  let Efg : FiniteGaloisIntermediateField ℚ initialProExtension :=
    @FiniteGaloisIntermediateField.mk ℚ initialProExtension _ _ _ E inferInstance hE_gal
  have hE_unram : RationalPrimeUnramified (S := 𝓞 ↥E) q := by
    simpa [UnramifiedOutside, RamifiedOnlyAt, Efg] using
      (initial_subextension_outside Efg) q hq hqS
  exact rational_unramified_alg e.symm hE_unram

theorem abs_rational_ideal (q : ℕ) :
    Ideal.absNorm (Ideal.rationalPrimeIdeal q) = q := by
  rw [Ideal.rationalPrimeIdeal, Ideal.absNorm_apply]
  simpa [Submodule.cardQuot_apply] using Int.card_ideal_quot q

noncomputable def chosenPrimePlace (i : ℕ) : FinitePlace ℚ := by
  let pI : Ideal (𝓞 ℚ) := (chosenLayerPrime i).under (𝓞 ℚ)
  have hpI0 : pI ≠ ⊥ := by
    exact Ideal.ne_bot_of_liesOver_of_ne_bot
      (rational_ne_bot (chosenPrime_prime i)) pI
  exact FinitePlace.mk <|
    IsDedekindDomain.HeightOneSpectrum.ofPrime
      (Ideal.prime_of_isPrime hpI0 inferInstance)

theorem chosen_prime_place (i : ℕ) :
    (chosenPrimePlace i).maximalIdeal.asIdeal =
      (chosenLayerPrime i).under (𝓞 ℚ) := by
  simp [chosenPrimePlace, FinitePlace.maximalIdeal_mk]

theorem chosen_ring_integers (i : ℕ) :
    (chosenPrimePlace i).maximalIdeal.asIdeal.map Rat.ringOfIntegersEquiv =
      Ideal.rationalPrimeIdeal (chosenPrime i) := by
  let pI : Ideal (𝓞 ℚ) := (chosenLayerPrime i).under (𝓞 ℚ)
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal (chosenPrime i)
  let e0 : 𝓞 ℚ ≃ₐ[ℤ] ℤ :=
    AlgEquiv.ofRingEquiv (R := ℤ) (f := Rat.ringOfIntegersEquiv) <| by
      intro x
      norm_num [Rat.ringOfIntegersEquiv_apply_coe]
  have halg : (algebraMap ℤ (𝓞 ℚ)) = e0.symm.toRingHom :=
    Subsingleton.elim _ _
  have hpIover : pI.LiesOver qI := by
    dsimp [pI, qI]
    infer_instance
  have hpIunder0 : qI = Ideal.under ℤ pI := by
    simpa [Ideal.liesOver_iff] using (show pI.LiesOver qI from hpIover)
  have hpIunder : Ideal.under ℤ pI = qI := by
    exact hpIunder0.symm
  have hpImap : pI.map e0 = qI := by
    calc
      pI.map e0.toRingHom = pI.comap e0.symm.toRingHom := by
        exact Ideal.map_comap_of_equiv (I := pI) e0.toRingEquiv
      _ = qI := by
        simpa [Ideal.under, halg] using hpIunder
  rw [chosen_prime_place i]
  simpa [pI] using hpImap

theorem chosen_place_norm (i : ℕ) :
    finitePlaceNorm (chosenPrimePlace i) = chosenPrime i := by
  have hEq :
      Ideal.rationalPrimeIdeal (finitePlaceNorm (chosenPrimePlace i)) =
        Ideal.rationalPrimeIdeal (chosenPrime i) := by
    calc
      Ideal.rationalPrimeIdeal (finitePlaceNorm (chosenPrimePlace i))
        = (chosenPrimePlace i).maximalIdeal.asIdeal.map Rat.ringOfIntegersEquiv := by
            symm
            exact initial_hmr_integers (chosenPrimePlace i)
      _ = Ideal.rationalPrimeIdeal (chosenPrime i) := by
            exact chosen_ring_integers i
  have hAbs := congrArg Ideal.absNorm hEq
  simpa [abs_rational_ideal] using hAbs

theorem arith_frob_rat
    {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
    [IsGaloisGroup Gal(E/ℚ) (𝓞 ℚ) (𝓞 E)]
    [IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E)]
    {Q : Ideal (𝓞 E)} {σ : Gal(E/ℚ)} :
    IsArithFrobAt (𝓞 ℚ) σ Q ↔ IsArithFrobAt ℤ σ Q := by
  let e0 : 𝓞 ℚ ≃ₐ[ℤ] ℤ :=
    AlgEquiv.ofRingEquiv (R := ℤ) (f := Rat.ringOfIntegersEquiv) <| by
      intro x
      norm_num [Rat.ringOfIntegersEquiv_apply_coe]
  have halg : (algebraMap ℤ (𝓞 ℚ)) = e0.symm.toRingHom :=
    Subsingleton.elim _ _
  have hmap :
      Q.under ℤ = (Q.under (𝓞 ℚ)).map e0 := by
    have hcomp :
        (algebraMap ℤ (𝓞 E)) =
          (algebraMap (𝓞 ℚ) (𝓞 E)).comp e0.symm.toRingHom :=
      Subsingleton.elim _ _
    calc
      Q.under ℤ = (Q.under (𝓞 ℚ)).comap e0.symm.toRingHom := by
        rw [Ideal.under, hcomp, Ideal.under, Ideal.comap_comap]
      _ = (Q.under (𝓞 ℚ)).map e0.toRingHom := by
        symm
        exact Ideal.map_comap_of_equiv (I := Q.under (𝓞 ℚ)) e0.toRingEquiv
  have hcard :
      Nat.card ((𝓞 ℚ) ⧸ Q.under (𝓞 ℚ)) =
        Nat.card (ℤ ⧸ Q.under ℤ) := by
    let e :
        (𝓞 ℚ) ⧸ Q.under (𝓞 ℚ) ≃+*
          ℤ ⧸ Q.under ℤ :=
      Ideal.quotientEquiv (Q.under (𝓞 ℚ)) (Q.under ℤ) Rat.ringOfIntegersEquiv hmap
    exact Nat.card_congr e.toEquiv
  constructor <;> intro hσ <;>
    simpa [IsArithFrobAt, AlgHom.IsArithFrobAt, hcard] using hσ

theorem arith_rat_restrict
    {E L : Type*} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    [Algebra E L] [IsScalarTower ℚ E L]
    [IsGaloisGroup Gal(E/ℚ) (𝓞 ℚ) (𝓞 E)]
    [IsGaloisGroup Gal(L/ℚ) (𝓞 ℚ) (𝓞 L)]
    {P : Ideal (𝓞 L)} [P.IsPrime]
    {σ : Gal(L/ℚ)}
    (hσ : IsArithFrobAt (𝓞 ℚ) σ P) :
    IsArithFrobAt (𝓞 ℚ) (σ.restrictNormalHom E)
      (P.under (𝓞 E)) := by
  intro x
  rw [Ideal.mem_of_liesOver
    (A := 𝓞 E) (B := 𝓞 L) (p := P.under (𝓞 E)) (P := P)]
  have hmap :
      algebraMap (𝓞 E) (𝓞 L)
        (MulSemiringAction.toAlgHom (𝓞 ℚ)
          (𝓞 E) (σ.restrictNormalHom E) x) =
      MulSemiringAction.toAlgHom (𝓞 ℚ)
        (𝓞 L) σ (algebraMap (𝓞 E) (𝓞 L) x) := by
    apply Subtype.ext
    calc
      algebraMap (𝓞 L) L
          (algebraMap (𝓞 E) (𝓞 L)
            (MulSemiringAction.toAlgHom (𝓞 ℚ)
              (𝓞 E) (σ.restrictNormalHom E) x))
        =
          algebraMap E L
            (algebraMap (𝓞 E) E
              (MulSemiringAction.toAlgHom (𝓞 ℚ)
                (𝓞 E) (σ.restrictNormalHom E) x)) := by
            rfl
      _ =
          algebraMap E L
            ((σ.restrictNormalHom E)
              (algebraMap (𝓞 E) E x)) := by
            rw [alg_gal_restrict
              (K := ℚ) (E := E) (σ := σ.restrictNormalHom E) x]
            exact congrArg (algebraMap E L)
              (algebraMap_galRestrict_apply
                (A := 𝓞 ℚ) (K := ℚ) (L := E)
                (B := 𝓞 E) (σ := σ.restrictNormalHom E) x)
      _ = σ (algebraMap E L (algebraMap (𝓞 E) E x)) := by
            exact AlgEquiv.restrictNormal_commutes σ E (algebraMap (𝓞 E) E x)
      _ = σ
          (algebraMap (𝓞 L) L
            (algebraMap (𝓞 E) (𝓞 L) x)) := by
            rfl
      _ =
          algebraMap (𝓞 L) L
            (MulSemiringAction.toAlgHom (𝓞 ℚ)
              (𝓞 L) σ (algebraMap (𝓞 E) (𝓞 L) x)) := by
            rw [alg_gal_restrict
              (K := ℚ) (E := L) (σ := σ)
              (x := algebraMap (𝓞 E) (𝓞 L) x)]
            exact
              (algebraMap_galRestrict_apply
                (A := 𝓞 ℚ) (K := ℚ) (L := L)
                (B := 𝓞 L) σ
                (algebraMap (𝓞 E) (𝓞 L) x)).symm
  have hσx :
      MulSemiringAction.toAlgHom (𝓞 ℚ)
          (𝓞 L) σ
          (algebraMap (𝓞 E) (𝓞 L) x) -
        (algebraMap (𝓞 E)
          (𝓞 L) x) ^
          Nat.card ((𝓞 ℚ) ⧸ P.under (𝓞 ℚ)) ∈
        P := by
    exact hσ (algebraMap (𝓞 E) (𝓞 L) x)
  rw [← hmap] at hσx
  simpa [AlgHom.IsArithFrobAt, Ideal.under_under, map_sub, map_pow] using hσx

theorem arith_frob_int
    {E L : Type*} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    [Algebra E L] [IsScalarTower ℚ E L]
    [IsGaloisGroup Gal(E/ℚ) (𝓞 ℚ) (𝓞 E)]
    [IsGaloisGroup Gal(L/ℚ) (𝓞 ℚ) (𝓞 L)]
    [IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E)]
    [IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L)]
    {P : Ideal (𝓞 L)} [P.IsPrime]
    {σ : Gal(L/ℚ)}
    (hσ : IsArithFrobAt ℤ σ P) :
    IsArithFrobAt ℤ (σ.restrictNormalHom E)
      (P.under (𝓞 E)) := by
  have hσ' : IsArithFrobAt (𝓞 ℚ) σ P :=
    (arith_frob_rat (E := L)).2 hσ
  have h' :
      IsArithFrobAt (𝓞 ℚ) (σ.restrictNormalHom E)
        (P.under (𝓞 E)) :=
    arith_rat_restrict (E := E) (L := L) hσ'
  exact (arith_frob_rat (E := E)).1 h'

theorem frobenius_restrict_hom
    {E L : Type*} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    [Algebra E L] [IsScalarTower ℚ E L]
    [IsGaloisGroup Gal(E/ℚ) (𝓞 ℚ) (𝓞 E)]
    [IsGaloisGroup Gal(L/ℚ) (𝓞 ℚ) (𝓞 L)]
    {v : FinitePlace ℚ} {σ : Gal(L/ℚ)}
    (hσ : FrobeniusPlaceField (K := ℚ) (E := L) v σ) :
    FrobeniusPlaceField (K := ℚ) (E := E) v (σ.restrictNormalHom E) := by
  rcases hσ with ⟨Q, hQFrob⟩
  refine ⟨⟨Q.1.under (𝓞 E), inferInstance, inferInstance⟩, ?_⟩
  exact arith_rat_restrict (E := E) (L := L) hQFrob

/- A compatible family of finite-level Frobenius elements above the chosen prime `q_i`,
together with its distinguished value on the layer field. This is the finite-level input that
must be lifted to the ambient Galois group of `initialProExtension/ℚ`. -/
set_option maxHeartbeats 4000000 in
-- Constructing the compatible Frobenius family traverses all finite Galois layers at once.
set_option synthInstance.maxHeartbeats 200000 in
-- Compatibility across the finite-layer family requires additional instance search.
theorem restriction_compatible_chosen (i : ℕ) :
    ∃ (𝔮 : FinitePlace ℚ)
      (σs :
        FiniteGaloisFamily (K := ℚ) (KS := initialProExtension)),
      finitePlaceNorm 𝔮 = chosenPrime i ∧
        UnramifiedInAmbient (K := ℚ) (KS := initialProExtension) 𝔮 ∧
        FrobeniusFamilyPlace (K := ℚ) (KS := initialProExtension) 𝔮 σs ∧
        RestrictionCompatibleFamily
          (K := ℚ) (KS := initialProExtension) σs ∧
        σs (galoisIntermediateField i) = chosenLayerFrobenius i := by
  classical
  let E0 : FiniteGaloisIntermediateField ℚ initialProExtension :=
    galoisIntermediateField i
  letI : IsGalois ℚ ↥E0 := E0.isGalois
  let frob0 : Gal(↥E0/ℚ) := by
    simpa [E0] using chosenLayerFrobenius i
  let A : Set initialGaloisGroup :=
    {σ | σ.restrictNormalHom E0 = frob0}
  let T :
      FiniteGaloisIntermediateField ℚ initialProExtension →
        Set initialGaloisGroup :=
    fun E =>
      letI : IsGalois ℚ ↥E := E.isGalois
      {σ | FrobeniusPlaceField
        (K := ℚ) (E := ↥E) (chosenPrimePlace i) (σ.restrictNormalHom E)}
  let U :
      FiniteGaloisIntermediateField ℚ initialProExtension →
        Set initialGaloisGroup :=
    fun E => A ∩ T E
  have hAclosed : IsClosed A := by
    change IsClosed
      ((AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := initialProExtension) E0) ⁻¹'
        {chosenLayerFrobenius i})
    exact (isClosed_discrete _).preimage <|
      InfiniteGalois.restrictNormalHom_continuous
        (k := ℚ) (K := initialProExtension) (L := E0)
  have hTclosed :
      ∀ E : FiniteGaloisIntermediateField ℚ initialProExtension,
        IsClosed (T E) := by
    intro E
    letI : IsGalois ℚ ↥E := E.isGalois
    have hclosed :
        IsClosed
          ((AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := initialProExtension) E) ⁻¹'
            {τ | FrobeniusPlaceField
              (K := ℚ) (E := ↥E) (chosenPrimePlace i) τ}) := by
      exact (isClosed_discrete _).preimage <|
        InfiniteGalois.restrictNormalHom_continuous
          (k := ℚ) (K := initialProExtension) (L := E)
    simpa [T] using hclosed
  have hUclosed :
      ∀ E : FiniteGaloisIntermediateField ℚ initialProExtension,
        IsClosed (U E) := by
    intro E
    exact hAclosed.inter (hTclosed E)
  have hUfinite :
      ∀ B : Finset (FiniteGaloisIntermediateField ℚ initialProExtension),
        (⋂ E ∈ B, U E).Nonempty := by
    intro B
    let B0 : Finset (FiniteGaloisIntermediateField ℚ initialProExtension) := insert E0 B
    let ι := {E // E ∈ B0}
    let t : ι → IntermediateField ℚ initialProExtension :=
      fun E => E.1.toIntermediateField
    let M : IntermediateField ℚ initialProExtension := ⨆ E : ι, t E
    letI : FiniteDimensional ℚ ↥M := by
      change FiniteDimensional ℚ ↥(⨆ E : ι, t E)
      infer_instance
    letI : NumberField ↥M := NumberField.of_module_finite ℚ ↥M
    have hMnormal : Normal ℚ ↥M := by
      change Normal ℚ ↥(⨆ E : ι, t E)
      simpa [M, t] using
        (IntermediateField.normal_iSup
          (F := ℚ) (K := initialProExtension) (t := t)
          (h := fun E => by
            letI : IsGalois ℚ E.1 := E.1.isGalois
            simpa using (IsGalois.to_normal (F := ℚ) (E := E.1))))
    have hMsep : Algebra.IsSeparable ℚ ↥M := by
      change Algebra.IsSeparable ℚ ↥(⨆ E : ι, t E)
      simpa [M, t] using
        (IntermediateField.isSeparable_iSup
          (F := ℚ) (E := initialProExtension) (t := t)
          (h := fun E => by
            letI : IsGalois ℚ E.1 := E.1.isGalois
            simpa using (IsGalois.to_isSeparable (F := ℚ) (E := E.1))))
    have hM_gal : IsGalois ℚ ↥M := { to_normal := hMnormal, to_isSeparable := hMsep }
    letI : IsGalois ℚ ↥M := hM_gal
    have hE_le_M :
        ∀ E : FiniteGaloisIntermediateField ℚ initialProExtension,
          E ∈ B0 → (E : IntermediateField ℚ initialProExtension) ≤ M := by
      intro E hE
      exact le_iSup_of_le ⟨E, hE⟩ le_rfl
    have hE0_le_M :
        (E0 : IntermediateField ℚ initialProExtension) ≤ M :=
      hE_le_M E0 (by simp [B0])
    letI : Algebra E0 ↥M := RingHom.toAlgebra (IntermediateField.inclusion hE0_le_M)
    haveI : IsScalarTower ℚ E0 ↥M := IsScalarTower.of_algebraMap_eq (congrFun rfl)
    let PI : Ideal (𝓞 E0) := by
      simpa [E0] using chosenLayerPrime i
    have hPI0 : PI ≠ ⊥ := by
      simpa [PI, E0] using
        (Ideal.ne_bot_of_liesOver_of_ne_bot
          (rational_ne_bot (chosenPrime_prime i)) (chosenLayerPrime i))
    letI : PI.IsPrime := by
      simpa [PI, E0] using (inferInstance : (chosenLayerPrime i).IsPrime)
    letI : PI.LiesOver (Ideal.rationalPrimeIdeal (chosenPrime i)) := by
      simpa [PI, E0] using
        (inferInstance : (chosenLayerPrime i).LiesOver
          (Ideal.rationalPrimeIdeal (chosenPrime i)))
    letI : PI.IsMaximal := (show PI.IsPrime by infer_instance).isMaximal hPI0
    letI : Algebra.IsUnramifiedAt ℤ PI := by
      simpa [PI, E0] using (inferInstance : Algebra.IsUnramifiedAt ℤ (chosenLayerPrime i))
    obtain ⟨⟨P, hPprime, hPover⟩⟩ := PI.nonempty_primesOver (S := 𝓞 ↥M)
    letI : P.IsPrime := hPprime
    letI : P.LiesOver PI := hPover
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hPI0 P
    letI : P.IsMaximal := hPprime.isMaximal hP0
    letI : Finite ((𝓞 ↥M) ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
    let τ : Gal(↥M/ℚ) := arithFrobAt ℤ (Gal(↥M/ℚ)) P
    have hτarith_int : IsArithFrobAt ℤ τ P := by
      simpa [τ] using
        (IsArithFrobAt.arithFrobAt
          (R := ℤ) (S := 𝓞 ↥M) (G := Gal(↥M/ℚ)) (Q := P))
    have hPunderE00 : PI = P.under (𝓞 E0) := by
      simpa [Ideal.liesOver_iff] using (show P.LiesOver PI from hPover)
    have hPunderE0 : P.under (𝓞 E0) = PI := hPunderE00.symm
    have hPunderQ :
        P.under (𝓞 ℚ) = (chosenPrimePlace i).maximalIdeal.asIdeal := by
      calc
        P.under (𝓞 ℚ) = (P.under (𝓞 E0)).under (𝓞 ℚ) := by
          rw [Ideal.under_under (A := 𝓞 ℚ) (B := 𝓞 E0) (C := 𝓞 ↥M)]
        _ = (chosenLayerPrime i).under (𝓞 ℚ) := by
          simpa [PI, E0] using congrArg (Ideal.under (𝓞 ℚ)) hPunderE0
        _ = (chosenPrimePlace i).maximalIdeal.asIdeal := by
          rw [chosen_prime_place]
    have hPoverQ : P.LiesOver ((chosenPrimePlace i).maximalIdeal.asIdeal) := by
      rw [Ideal.liesOver_iff]
      exact hPunderQ.symm
    have hτarith_rat : IsArithFrobAt (𝓞 ℚ) τ P := by
      exact (arith_frob_rat (E := ↥M)).2 hτarith_int
    have hτFrobM :
        FrobeniusPlaceField
          (K := ℚ) (E := ↥M) (chosenPrimePlace i) τ := by
      refine ⟨⟨P, hPprime, hPoverQ⟩, hτarith_rat⟩
    obtain ⟨σB, hσBM⟩ :=
      (AlgEquiv.restrictNormalHom_surjective
        (F := ℚ) (K₁ := ↥M) (E := initialProExtension) τ)
    haveI : IsScalarTower ↥E0 ↥M initialProExtension := IsScalarTower.of_algebraMap_eq' rfl
    have hσB_layer :
        σB.restrictNormalHom E0 = τ.restrictNormalHom E0 := by
      rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply
        (F := ℚ) (K₁ := ↥E0) (K₂ := ↥M) (K₃ := initialProExtension) σB]
      rw [hσBM]
    have hτLayer_int :
        IsArithFrobAt ℤ (τ.restrictNormalHom E0) PI := by
      have h' :
          IsArithFrobAt ℤ (τ.restrictNormalHom E0) (P.under (𝓞 E0)) :=
        arith_frob_int (E := ↥E0) (L := ↥M) hτarith_int
      simpa [hPunderE0] using h'
    have hτLayer_eq :
        τ.restrictNormalHom E0 = frob0 := by
      have hsplit : splitsCompletely ↥E0 (chosenPrime i) := by
        simpa [E0] using chosen_splits_layer i
      have hτeq1 :
          τ.restrictNormalHom E0 = 1 := by
        exact
          (completely_arith_frob
            ↥E0 (chosenPrime_prime i) PI (τ.restrictNormalHom E0) hτLayer_int).1 hsplit
      have hfrob0eq1 : frob0 = 1 := by
        simpa [frob0, E0] using chosen_layer_frobenius i
      calc
        τ.restrictNormalHom E0 = 1 := hτeq1
        _ = frob0 := hfrob0eq1.symm
    have hσB_in_A : σB ∈ A := by
      dsimp [A]
      exact hσB_layer.trans hτLayer_eq
    have hσB_in_T :
        ∀ E : FiniteGaloisIntermediateField ℚ initialProExtension,
          E ∈ B → σB ∈ T E := by
      intro E hE
      letI : IsGalois ℚ ↥E := E.isGalois
      have hE_le_M :
          (E : IntermediateField ℚ initialProExtension) ≤ M :=
        hE_le_M E (by simp [B0, hE])
      letI : Algebra E ↥M := RingHom.toAlgebra (IntermediateField.inclusion hE_le_M)
      haveI : IsScalarTower ℚ E ↥M := IsScalarTower.of_algebraMap_eq (congrFun rfl)
      haveI : IsScalarTower ↥E ↥M initialProExtension :=
        IsScalarTower.of_algebraMap_eq' rfl
      have hσB_E :
          σB.restrictNormalHom E = τ.restrictNormalHom E := by
        rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply
          (F := ℚ) (K₁ := ↥E) (K₂ := ↥M) (K₃ := initialProExtension) σB]
        rw [hσBM]
      have hτFrobE :
          FrobeniusPlaceField
            (K := ℚ) (E := ↥E) (chosenPrimePlace i) (τ.restrictNormalHom E) :=
        frobenius_restrict_hom
          (E := ↥E) (L := ↥M) hτFrobM
      simpa [T, hσB_E] using hτFrobE
    refine ⟨σB, ?_⟩
    simp only [Set.mem_iInter, U, Set.mem_inter_iff]
    intro E hE
    exact ⟨hσB_in_A, hσB_in_T E hE⟩
  obtain ⟨σ, hσ⟩ := CompactSpace.iInter_nonempty hUclosed hUfinite
  let σs :
      FiniteGaloisFamily (K := ℚ) (KS := initialProExtension) :=
    fun E => by
      letI : IsGalois ℚ ↥E := E.isGalois
      exact σ.restrictNormalHom E
  have hσA : σ ∈ A := by
    exact (Set.mem_iInter.mp hσ E0).1
  have hσT :
      ∀ E : FiniteGaloisIntermediateField ℚ initialProExtension, σ ∈ T E := by
    intro E
    exact (Set.mem_iInter.mp hσ E).2
  have hunr :
      UnramifiedInAmbient
        (K := ℚ) (KS := initialProExtension) (chosenPrimePlace i) := by
    intro E
    have hRatUnr :
        RationalPrimeUnramified (S := 𝓞 E) (chosenPrime i) := by
      exact
        (initial_subextension_outside E)
          (chosenPrime i) (chosenPrime_prime i) (chosen_avoids_s i)
    have hRatUnr' :
        RationalPrimeUnramified
          (S := 𝓞 E) (finitePlaceNorm (chosenPrimePlace i)) := by
      simpa [chosen_place_norm i] using hRatUnr
    exact
      initial_hmr_unramified
        (v := chosenPrimePlace i) hRatUnr'
  have hFrob :
      FrobeniusFamilyPlace
        (K := ℚ) (KS := initialProExtension) (chosenPrimePlace i) σs := by
    intro E
    simpa [T, σs] using hσT E
  have hCompat :
      RestrictionCompatibleFamily
        (K := ℚ) (KS := initialProExtension) σs := by
    refine ⟨σ, ?_⟩
    intro E
    letI : IsGalois ℚ ↥E := E.isGalois
    change (AlgEquiv.restrictNormalHom ↥E.toIntermediateField) σ =
      (AlgEquiv.restrictNormalHom ↥E.toIntermediateField) σ
    exact rfl
  refine ⟨chosenPrimePlace i, σs, chosen_place_norm i,
    hunr, hFrob, hCompat, ?_⟩
  simpa [A, σs, frob0, E0] using hσA

/- The admi_tted finite-level family can be lifted to an ambient Frobenius element, and the
triviality of its restriction to `L_i` forces it into the Zassenhaus term cutting out `L_i`. -/
set_option maxHeartbeats 800000 in
-- Lifting the finite Frobenius family to the ambient Galois group needs extra elaboration budget.
set_option synthInstance.maxHeartbeats 100000 in
theorem ambient_frobenius_chosen (i : ℕ) :
    ∃ (𝔮 : FinitePlace ℚ) (σ : initialGaloisGroup),
      finitePlaceNorm 𝔮 = chosenPrime i ∧
        UnramifiedInAmbient (K := ℚ) (KS := initialProExtension) 𝔮 ∧
        FrobeniusPlace (K := ℚ) (KS := initialProExtension) 𝔮 σ ∧
        σ ∈ initialZassenhausFiltration (cuttingLevel + i) := by
  letI : IsGalois ℚ (layerField i) := (layer_three_group i).1
  rcases restriction_compatible_chosen i with
    ⟨𝔮, σs, hnorm, hunr, hFrob, hCompat, hlayer⟩
  rcases ambient_frobenius_family
      (K := ℚ) (KS := initialProExtension) hFrob hCompat with
    ⟨σ, hσrestrict, hσfrob⟩
  refine ⟨𝔮, σ, hnorm, hunr, hσfrob, ?_⟩
  let E : FiniteGaloisIntermediateField ℚ initialProExtension :=
    galoisIntermediateField i
  letI : IsGalois ℚ E := E.isGalois
  have hσsLayer1 : σs E = 1 := by
    simpa [E, chosen_layer_frobenius i] using hlayer
  have hσlayer1 :
      σ.restrictNormalHom E = 1 := by
    exact (hσrestrict E).trans hσsLayer1
  have hfix : σ ∈ (layerField i).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff (K := layerField i)]
    intro x hx
    have hsub :
        (σ.restrictNormalHom E) ⟨x, hx⟩ = ⟨x, hx⟩ := by
      simpa using congrArg (fun τ => τ ⟨x, hx⟩) hσlayer1
    calc
      σ x = ↑((σ.restrictNormalHom E) ⟨x, hx⟩) := by
        symm
        simpa using AlgEquiv.restrictNormalHom_apply E σ ⟨x, hx⟩
      _ = x := congrArg Subtype.val hsub
  rw [layer_fixing_subgroup i] at hfix
  exact hfix

/- The cut extension. -/
theorem exists_cuttingData :
    ∃ (𝔮 : ℕ → FinitePlace ℚ) (x : ℕ → initialGaloisGroup),
      (∀ i, finitePlaceNorm (𝔮 i) = chosenPrime i) ∧
        (∀ i, UnramifiedInAmbient (K := ℚ) (KS := initialProExtension) (𝔮 i)) ∧
        (∀ i, FrobeniusPlace (K := ℚ) (KS := initialProExtension) (𝔮 i) (x i)) ∧
        (∀ i, x i ∈ initialZassenhausFiltration (cuttingLevel + i)) := by
  classical
  let 𝔮 : ℕ → FinitePlace ℚ :=
    fun i => Classical.choose (ambient_frobenius_chosen i)
  let x : ℕ → initialGaloisGroup :=
    fun i => Classical.choose (Classical.choose_spec (ambient_frobenius_chosen i))
  refine ⟨𝔮, x, ?_, ?_, ?_, ?_⟩
  · intro i
    exact
      (Classical.choose_spec
        (Classical.choose_spec (ambient_frobenius_chosen i))).1
  · intro i
    exact
      (Classical.choose_spec
        (Classical.choose_spec (ambient_frobenius_chosen i))).2.1
  · intro i
    exact
      (Classical.choose_spec
        (Classical.choose_spec (ambient_frobenius_chosen i))).2.2.1
  · intro i
    exact
      (Classical.choose_spec
        (Classical.choose_spec (ambient_frobenius_chosen i))).2.2.2

noncomputable def chosenAmbientPlace : ℕ → FinitePlace ℚ :=
  Classical.choose exists_cuttingData

noncomputable def chosenAmbientFrobenius : ℕ → initialGaloisGroup :=
  Classical.choose (Classical.choose_spec exists_cuttingData)

theorem chosen_ambient_norm (i : ℕ) :
    finitePlaceNorm (chosenAmbientPlace i) = chosenPrime i := by
  exact (Classical.choose_spec (Classical.choose_spec exists_cuttingData)).1 i

theorem chosen_ambient_unramified (i : ℕ) :
    UnramifiedInAmbient (K := ℚ) (KS := initialProExtension) (chosenAmbientPlace i) := by
  exact (Classical.choose_spec (Classical.choose_spec exists_cuttingData)).2.1 i

theorem chosen_ambient (i : ℕ) :
    FrobeniusPlace (K := ℚ) (KS := initialProExtension)
      (chosenAmbientPlace i) (chosenAmbientFrobenius i) := by
  exact (Classical.choose_spec (Classical.choose_spec exists_cuttingData)).2.2.1 i

theorem chosen_ambient_frobenius (i : ℕ) :
    chosenAmbientFrobenius i ∈ initialZassenhausFiltration (cuttingLevel + i) := by
  exact (Classical.choose_spec (Classical.choose_spec exists_cuttingData)).2.2.2 i

noncomputable def cutSubgroup : Subgroup initialGaloisGroup :=
  hmrCutSubgroup (K := ℚ) (KS := initialProExtension) chosenAmbientFrobenius

instance instCutSubgroup : cutSubgroup.Normal := by
  change
    (hmrCutSubgroup (K := ℚ) (KS := initialProExtension) chosenAmbientFrobenius).Normal
  infer_instance

theorem cutSubgroup_normal :
    cutSubgroup.Normal := by
  infer_instance

noncomputable def cutClosedSubgroup : ClosedSubgroup initialGaloisGroup :=
  hmrCutClosed (K := ℚ) (KS := initialProExtension) chosenAmbientFrobenius

instance instCutClosed : cutClosedSubgroup.Normal := by
  change
    (hmrCutClosed (K := ℚ) (KS := initialProExtension)
      chosenAmbientFrobenius).Normal
  infer_instance

/- Let `𝓕 := (Q_S^(3))^N` be the corresponding fixed field. -/
noncomputable def cutField : IntermediateField ℚ initialProExtension :=
  IntermediateField.fixedField cutClosedSubgroup.1

instance instRatCut : Algebra ℚ cutField :=
  cutField.algebra

instance instModuleCut : Module ℚ cutField := by
  let _ := instRatCut
  infer_instance

instance instGaloisCut : IsGalois ℚ cutField := by
  change IsGalois ℚ (IntermediateField.fixedField cutClosedSubgroup.1)
  refine
    (InfiniteGalois.normal_iff_isGalois
      (IntermediateField.fixedField cutClosedSubgroup.1)).mp ?_
  have hfix :
      (IntermediateField.fixedField cutClosedSubgroup.1).fixingSubgroup =
        cutClosedSubgroup.1 := by
    simpa using
      (InfiniteGalois.fixingSubgroup_fixedField
        (k := ℚ) (K := initialProExtension) cutClosedSubgroup)
  rw [hfix]
  infer_instance

/- Define `Γ := G / N`. -/
abbrev cutQuotientGroup := Gal(cutField/ℚ)

noncomputable def cutQuotientEquiv :
    initialGaloisGroup ⧸ cutClosedSubgroup.1 ≃* cutQuotientGroup := by
  simpa [initialGaloisGroup, cutQuotientGroup, cutField, cutClosedSubgroup] using
    (galoisFixedField (L := initialProExtension) cutClosedSubgroup)

noncomputable def cutQuotientMap : initialGaloisGroup →* cutQuotientGroup :=
  cutQuotientEquiv.toMonoidHom.comp (QuotientGroup.mk' cutClosedSubgroup.1)

theorem cut_group_spec :
    Nonempty (initialGaloisGroup ⧸ cutClosedSubgroup.1 ≃* cutQuotientGroup) := by
  exact ⟨cutQuotientEquiv⟩

theorem cut_fixed_spec :
    cutField = IntermediateField.fixedField cutClosedSubgroup.1 := by
  rfl

theorem cut_realizes_galois :
    Nonempty (cutQuotientGroup ≃* Gal(cutField/ℚ)) := by
  exact ⟨MulEquiv.refl _⟩

/- By the HMR Frobenius-cutting theorem, `Γ` is infinite. -/
theorem cut_group_infinite :
    Infinite cutQuotientGroup := by
  have hS :
      ∀ i, finitePlaceNorm (chosenAmbientPlace i) ∉ initialRamifiedPrimes := by
    intro i
    rw [chosen_ambient_norm i]
    exact chosen_avoids_s i
  have hcut :=
    (cutting_level_output chosenAmbientPlace chosenAmbientFrobenius
      hS
      chosen_ambient_unramified
      chosen_ambient
      chosen_ambient_frobenius).1
  simpa [cutQuotientGroup, cutField, cutClosedSubgroup, hmrCutQuotient, hmrFixedField] using hcut

set_option maxHeartbeats 2000000 in
-- Transporting the finite subextension through both lifted fixed fields is reduction-intensive.
set_option synthInstance.maxHeartbeats 200000 in
-- The two transported Galois structures need a larger synthesis budget.
theorem cut_subextension_p
    (E : IntermediateField ℚ cutField) [FiniteDimensional ℚ E] [IsGalois ℚ E] :
    IsPGroup 3 (Gal(E/ℚ)) := by
  classical
  let E₁ : IntermediateField ℚ initialProExtension :=
    IntermediateField.lift (F := cutField) E
  let e₁ : E ≃ₐ[ℚ] E₁ := IntermediateField.liftAlgEquiv (E := cutField) E
  letI : FiniteDimensional ℚ E₁ := e₁.toLinearEquiv.finiteDimensional
  letI : IsGalois ℚ E₁ := (AlgEquiv.transfer_galois e₁).mp inferInstance
  let E₂ : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.lift (F := initialProIntermediate) E₁
  let e₂ : E₁ ≃ₐ[ℚ] E₂ :=
    IntermediateField.liftAlgEquiv (E := initialProIntermediate) E₁
  letI : FiniteDimensional ℚ E₂ := e₂.toLinearEquiv.finiteDimensional
  letI : IsGalois ℚ E₂ := (AlgEquiv.transfer_galois e₂).mp inferInstance
  let eE : E ≃ₐ[ℚ] E₂ := e₁.trans e₂
  have hsup_pgroup :
      ∀ {K L : IntermediateField ℚ (AlgebraicClosure ℚ)}
        [FiniteDimensional ℚ K] [IsGalois ℚ K]
        [FiniteDimensional ℚ L] [IsGalois ℚ L],
        IsPGroup 3 (Gal(K/ℚ)) →
        IsPGroup 3 (Gal(L/ℚ)) →
        IsPGroup 3 (Gal(↥(K ⊔ L)/ℚ)) := by
    intro K L _ _ _ _ hK hL
    let M : IntermediateField ℚ (AlgebraicClosure ℚ) := K ⊔ L
    let Ksub : IntermediateField ℚ M :=
      IntermediateField.restrict (show K ≤ M by exact le_sup_left)
    let Lsub : IntermediateField ℚ M :=
      IntermediateField.restrict (show L ≤ M by exact le_sup_right)
    have hKsub : IsPGroup 3 (Gal(Ksub/ℚ)) := by
      let eK : K ≃ₐ[ℚ] Ksub :=
        IntermediateField.restrict_algEquiv (show K ≤ M by exact le_sup_left)
      exact IsPGroup.of_equiv hK (AlgEquiv.autCongr eK)
    have hLsub : IsPGroup 3 (Gal(Lsub/ℚ)) := by
      let eL : L ≃ₐ[ℚ] Lsub :=
        IntermediateField.restrict_algEquiv (show L ≤ M by exact le_sup_right)
      exact IsPGroup.of_equiv hL (AlgEquiv.autCongr eL)
    let eK : K ≃ₐ[ℚ] Ksub :=
      IntermediateField.restrict_algEquiv (show K ≤ M by exact le_sup_left)
    let eL : L ≃ₐ[ℚ] Lsub :=
      IntermediateField.restrict_algEquiv (show L ≤ M by exact le_sup_right)
    letI : IsGalois ℚ ↥Ksub := (AlgEquiv.transfer_galois eK).mp inferInstance
    letI : IsGalois ℚ ↥Lsub := (AlgEquiv.transfer_galois eL).mp inferInstance
    letI : Normal ℚ ↥Ksub := IsGalois.to_normal (F := ℚ) (E := ↥Ksub)
    letI : Normal ℚ ↥Lsub := IsGalois.to_normal (F := ℚ) (E := ↥Lsub)
    letI : IsScalarTower ℚ ↥Ksub ↥M :=
      IntermediateField.isScalarTower_mid' (K := ℚ) (S := Ksub) (L := ↥M)
    letI : IsScalarTower ℚ ↥Lsub ↥M :=
      IntermediateField.isScalarTower_mid' (K := ℚ) (S := Lsub) (L := ↥M)
    haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hprod : IsPGroup 3 (Gal(Ksub/ℚ) × Gal(Lsub/ℚ)) := by
      obtain ⟨nK, hnK⟩ := (IsPGroup.iff_card (p := 3) (G := Gal(Ksub/ℚ))).mp hKsub
      obtain ⟨nL, hnL⟩ := (IsPGroup.iff_card (p := 3) (G := Gal(Lsub/ℚ))).mp hLsub
      apply IsPGroup.of_card (p := 3) (n := nK + nL)
      rw [Nat.card_prod, hnK, hnL, pow_add]
    let φ : Gal(M/ℚ) →* (Gal(Ksub/ℚ) × Gal(Lsub/ℚ)) :=
      { toFun := fun σ => (AlgEquiv.restrictNormalHom Ksub σ, AlgEquiv.restrictNormalHom Lsub σ)
        map_one' := by
          apply Prod.ext
          · exact (AlgEquiv.restrictNormalHom Ksub).map_one
          · exact (AlgEquiv.restrictNormalHom Lsub).map_one
        map_mul' := by
          intro σ τ
          apply Prod.ext
          · exact (AlgEquiv.restrictNormalHom Ksub).map_mul σ τ
          · exact (AlgEquiv.restrictNormalHom Lsub).map_mul σ τ }
    have hφinj : Function.Injective φ := by
      intro σ τ hστ
      have htop : Ksub ⊔ Lsub = ⊤ := by
        apply top_unique
        intro x hx
        have hlift : IntermediateField.lift (F := M) (Ksub ⊔ Lsub) = M := by
          simp [Ksub, Lsub, M, IntermediateField.lift_sup]
        have hx' : x.1 ∈ IntermediateField.lift (F := M) (Ksub ⊔ Lsub) := by
          simp [hlift]
        exact (IntermediateField.mem_lift (E := Ksub ⊔ Lsub) x).mp hx'
      apply AlgEquiv.ext
      intro x
      have hx :
          x ∈ IntermediateField.adjoin ℚ ((Ksub : Set M) ∪ (Lsub : Set M)) := by
        simp [htop, IntermediateField.adjoin_union]
      exact
        IntermediateField.adjoin_induction
          (s := ((Ksub : Set M) ∪ (Lsub : Set M)))
          (p := fun y _ => σ y = τ y)
          (mem := fun y hy => by
            rw [Set.mem_union] at hy
            rcases hy with hy | hy
            · have hfst := congrArg Prod.fst hστ
              have hfst_eval :
                  (((φ σ).1) ⟨y, hy⟩ : M) = ((((φ τ).1) ⟨y, hy⟩ : Ksub) : M) := by
                exact congrArg (fun z : Ksub => (z : M)) (congrArg (fun f => f ⟨y, hy⟩) hfst)
              have hfst' :
                  (((AlgEquiv.restrictNormalHom Ksub) σ) ⟨y, hy⟩ : M) =
                    (((AlgEquiv.restrictNormalHom Ksub) τ) ⟨y, hy⟩ : M) := by
                simpa [φ] using hfst_eval
              exact
                restrict_normal_implies (M := ↥M) (S := Ksub) hy hfst'
            · have hsnd := congrArg Prod.snd hστ
              have hsnd_eval :
                  (((φ σ).2) ⟨y, hy⟩ : M) = ((((φ τ).2) ⟨y, hy⟩ : Lsub) : M) := by
                exact congrArg (fun z : Lsub => (z : M)) (congrArg (fun f => f ⟨y, hy⟩) hsnd)
              have hsnd' :
                  (((AlgEquiv.restrictNormalHom Lsub) σ) ⟨y, hy⟩ : M) =
                    (((AlgEquiv.restrictNormalHom Lsub) τ) ⟨y, hy⟩ : M) := by
                simpa [φ] using hsnd_eval
              exact
                restrict_normal_implies (M := ↥M) (S := Lsub) hy hsnd')
          (algebraMap := fun q => by simp)
          (add := fun y z _ _ hσy hσz => by simpa using congrArg₂ (· + ·) hσy hσz)
          (inv := fun y _ hσy => by simpa using congrArg Inv.inv hσy)
          (mul := fun y z _ _ hσy hσz => by simpa using congrArg₂ (· * ·) hσy hσz)
          (h := hx)
    exact hprod.of_injective φ hφinj
  have hcompositum_galois :
      ∀ T : Finset ProThreeComponent,
        IsGalois ℚ ↥(initialProCompositum T) := by
    intro T
    let ι := {F // F ∈ T}
    let t : ι → IntermediateField ℚ (AlgebraicClosure ℚ) :=
      fun F => F.1.1.toIntermediateField
    let K0 : IntermediateField ℚ (AlgebraicClosure ℚ) := ⨆ F : ι, t F
    letI : Algebra ℚ ↥K0 := K0.algebra
    have hEq :
        initialProCompositum T = K0 := by
      unfold initialProCompositum
      apply le_antisymm
      · refine iSup_le fun F => iSup_le fun hF => ?_
        exact le_iSup_of_le ⟨F, hF⟩ le_rfl
      · refine iSup_le fun F => ?_
        exact le_iSup_of_le F.1 <| le_iSup_of_le F.2 le_rfl
    have hnormal :
        Normal ℚ ↥K0 := by
      change Normal ℚ ↥(⨆ F : ι, t F)
      simpa [K0, t] using
        (IntermediateField.normal_iSup
          (F := ℚ) (K := AlgebraicClosure ℚ) (t := t)
          (h := fun F => by
            letI : IsGalois ℚ ↥(F.1.1) := F.1.1.isGalois
            simpa using (IsGalois.to_normal (F := ℚ) (E := ↥(F.1.1)))))
    have hsep :
        Algebra.IsSeparable ℚ ↥K0 := by
      change Algebra.IsSeparable ℚ ↥(⨆ F : ι, t F)
      simpa [K0, t] using
        (IntermediateField.isSeparable_iSup
          (F := ℚ) (E := AlgebraicClosure ℚ) (t := t)
          (h := fun F => by
            letI : IsGalois ℚ ↥(F.1.1) := F.1.1.isGalois
            simpa using (IsGalois.to_isSeparable (F := ℚ) (E := ↥(F.1.1)))))
    have hgal : IsGalois ℚ ↥K0 := by
      exact { to_normal := hnormal, to_isSeparable := hsep }
    let eK0 : initialProCompositum T ≃ₐ[ℚ] K0 := IntermediateField.equivOfEq hEq
    exact (AlgEquiv.transfer_galois eK0).mpr hgal
  have hfinset_mono :
      ∀ {T₁ T₂ : Finset ProThreeComponent},
        T₁ ⊆ T₂ →
        initialProCompositum T₁ ≤ initialProCompositum T₂ := by
    intro T₁ T₂ hT
    simpa [initialProCompositum] using
      (show
        (⨆ C ∈ T₁, C.1.toIntermediateField) ≤
          (⨆ C ∈ T₂, C.1.toIntermediateField) from
        iSup₂_le fun C hC => le_iSup_of_le C (le_iSup_of_le (hT hC) le_rfl))
  have hstage :
      ∀ T : Finset ProThreeComponent,
        IsGalois ℚ ↥(initialProCompositum T) ∧
          IsPGroup 3 (Gal(↥(initialProCompositum T)/ℚ)) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · constructor
      · exact hcompositum_galois ∅
      · have hRat : IsPGroup 3 (Gal(ℚ/ℚ)) := by
          intro σ
          refine ⟨0, ?_⟩
          ext q
          exact σ.commutes q
        let eEmpty :
            initialProCompositum ∅ ≃ₐ[ℚ]
              (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
          IntermediateField.equivOfEq (by simp [initialProCompositum])
        have hBot :
            IsPGroup 3 (Gal(↥(⊥ : IntermediateField ℚ (AlgebraicClosure ℚ))/ℚ)) :=
          IsPGroup.of_equiv hRat
            ((AlgEquiv.autCongr (IntermediateField.botEquiv ℚ (AlgebraicClosure ℚ))).symm)
        exact IsPGroup.of_equiv hBot ((AlgEquiv.autCongr eEmpty).symm)
    · intro a T ha hT
      rcases hT with ⟨_, hPT⟩
      letI : IsGalois ℚ ↥(a.1.toIntermediateField) := a.1.isGalois
      letI : IsGalois ℚ ↥(initialProCompositum T) := hcompositum_galois T
      let Ksup : IntermediateField ℚ (AlgebraicClosure ℚ) :=
        a.1.toIntermediateField ⊔ initialProCompositum T
      have hInsert :
          initialProCompositum (insert a T) =
            Ksup := by
        unfold initialProCompositum
        apply le_antisymm
        · refine iSup_le fun C => iSup_le fun hC => ?_
          rcases Finset.mem_insert.mp hC with rfl | hC
          · exact le_sup_left
          · have hCT : C.1.toIntermediateField ≤ initialProCompositum T := by
              exact le_iSup_of_le C <| le_iSup_of_le hC le_rfl
            exact hCT.trans le_sup_right
        · refine sup_le ?_ ?_
          · exact le_iSup_of_le a <| le_iSup_of_le (Finset.mem_insert_self a T) le_rfl
          · refine iSup_le fun C => iSup_le fun hC => ?_
            have hCinsert : C.1.toIntermediateField ≤
                initialProCompositum (insert a T) := by
              exact le_iSup_of_le C <| le_iSup_of_le (Finset.mem_insert_of_mem hC) le_rfl
            exact hCinsert
      constructor
      · simpa [initialProCompositum, ha, sup_assoc, sup_comm, sup_left_comm] using
          hcompositum_galois (insert a T)
      · let eInsert :
            initialProCompositum (insert a T) ≃ₐ[ℚ] Ksup :=
          IntermediateField.equivOfEq hInsert
        have hGalSup : IsGalois ℚ ↥Ksup :=
          (AlgEquiv.transfer_galois eInsert).mp (hcompositum_galois (insert a T))
        letI : IsGalois ℚ ↥Ksup := hGalSup
        have hSup : IsPGroup 3 (Gal(Ksup/ℚ)) := by
          let Lstage : IntermediateField ℚ (AlgebraicClosure ℚ) :=
            initialProCompositum T
          have hLstageGal : IsGalois ℚ ↥Lstage := by
            simpa [Lstage] using hcompositum_galois T
          letI : IsGalois ℚ ↥Lstage := hLstageGal
          have hPT' : IsPGroup 3 (Gal(Lstage/ℚ)) := by
            simpa [Lstage] using hPT
          have hSupStage : IsPGroup 3 (Gal(↥(a.1.toIntermediateField ⊔ Lstage)/ℚ)) :=
            @hsup_pgroup (K := a.1.toIntermediateField) (L := Lstage)
              inferInstance inferInstance inferInstance hLstageGal
              a.2.1 hPT'
          simpa [Ksup, Lstage] using
            hSupStage
        exact IsPGroup.of_equiv hSup ((AlgEquiv.autCongr eInsert).symm)
  have hE₂le : E₂ ≤ initialProIntermediate :=
    IntermediateField.lift_le (F := initialProIntermediate) E₁
  let b := Module.finBasis ℚ E₂
  have hbasis_mem :
      ∀ i, ∃ T : Finset ProThreeComponent,
        ((b i : E₂) : AlgebraicClosure ℚ) ∈ initialProCompositum T := by
    intro i
    have hbi :
        ((b i : E₂) : AlgebraicClosure ℚ) ∈ initialProIntermediate :=
      hE₂le (b i).2
    have hbi' :
        ((b i : E₂) : AlgebraicClosure ℚ) ∈
          ⨆ C : ProThreeComponent, C.1.toIntermediateField := by
      simpa [initialProIntermediate] using hbi
    simpa [initialProCompositum] using
      (IntermediateField.exists_finset_of_mem_iSup
        (f := fun C : ProThreeComponent => C.1.toIntermediateField) hbi')
  choose Tmem hbmem using hbasis_mem
  let T : Finset ProThreeComponent := Finset.univ.biUnion Tmem
  have hbT :
      ∀ i, ((b i : E₂) : AlgebraicClosure ℚ) ∈ initialProCompositum T := by
    intro i
    exact
      hfinset_mono
        (fun C hC => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hC⟩)
        (hbmem i)
  have hE₂T : E₂ ≤ initialProCompositum T := by
    intro x hx
    let xE : E₂ := ⟨x, hx⟩
    have hx_repr :
        x = ∑ i, algebraMap ℚ (AlgebraicClosure ℚ) (b.repr xE i) * ((b i : E₂) :
          AlgebraicClosure ℚ) := by
      simpa [xE, Algebra.smul_def] using (congrArg Subtype.val (b.sum_repr xE)).symm
    rw [hx_repr]
    exact (initialProCompositum T).sum_mem fun i _ =>
      (initialProCompositum T).mul_mem
        ((initialProCompositum T).algebraMap_mem (b.repr xE i))
        (hbT i)
  let Esub : IntermediateField ℚ (initialProCompositum T) :=
    IntermediateField.restrict hE₂T
  let eSub : E₂ ≃ₐ[ℚ] Esub := IntermediateField.restrict_algEquiv hE₂T
  have hPEsub : IsPGroup 3 (Gal(Esub/ℚ)) := by
    letI : IsGalois ℚ ↥(initialProCompositum T) := hcompositum_galois T
    letI : IsGalois ℚ ↥Esub := (AlgEquiv.transfer_galois eSub).mp inferInstance
    let ψ : Gal(↥(initialProCompositum T)/ℚ) →* Gal(Esub/ℚ) :=
      AlgEquiv.restrictNormalHom Esub
    have hψsurj : Function.Surjective ψ := by
      simpa [ψ] using
        (AlgEquiv.restrictNormalHom_surjective
          (F := ℚ) (K₁ := ↥Esub) (E := ↥(initialProCompositum T)))
    exact
      ((hstage T).2).of_surjective ψ hψsurj
  have hPE₂ : IsPGroup 3 (Gal(E₂/ℚ)) := by
    exact IsPGroup.of_equiv hPEsub ((AlgEquiv.autCongr eSub).symm)
  exact IsPGroup.of_equiv hPE₂ ((AlgEquiv.autCongr eE).symm)

/- The group `Γ` is an infinite pro-`3` group. -/
set_option maxHeartbeats 800000 in
-- The fixed-field / quotient equivalence proof below triggers heavy typeclass search.
set_option synthInstance.maxHeartbeats 100000 in
theorem cut_group_prothree :
    InfiniteProGroup cutQuotientGroup := by
  classical
  constructor
  · exact cut_group_infinite
  · intro N
    let Nclosed : ClosedSubgroup cutQuotientGroup :=
      { toSubgroup := N
        isClosed' := OpenSubgroup.isClosed N.toOpenSubgroup }
    let E0 : IntermediateField ℚ cutField := IntermediateField.fixedField Nclosed.1
    have hE0fix : E0.fixingSubgroup = Nclosed.1 := by
      simpa [E0] using
        (InfiniteGalois.fixingSubgroup_fixedField
          (k := ℚ) (K := cutField) Nclosed)
    have hE0fg :
        FiniteDimensional ℚ E0 ∧ IsGalois ℚ E0 :=
      (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
        (k := ℚ) (K := cutField) E0).mp <| by
          rw [hE0fix]
          refine ⟨N.isOpen', ?_⟩
          change (N : Subgroup cutQuotientGroup).Normal
          infer_instance
    letI : FiniteDimensional ℚ E0 := hE0fg.1
    letI : IsGalois ℚ E0 := hE0fg.2
    have hQuot :
        Nonempty (cutQuotientGroup ⧸ (N : Subgroup cutQuotientGroup) ≃* Gal(E0/ℚ)) := by
      exact ⟨by
        simpa [E0, Nclosed] using
          (galoisFixedField (L := cutField) Nclosed)⟩
    have hPE0 : IsPGroup 3 (Gal(E0/ℚ)) :=
      cut_subextension_p E0
    rcases hQuot with ⟨eQuot⟩
    exact IsPGroup.of_equiv hPE0 eQuot.symm

theorem place_nat_norm (v : FinitePlace ℚ) :
    Rat.HeightOneSpectrum.natGenerator v.maximalIdeal = finitePlaceNorm v := by
  let I : Ideal (𝓞 ℚ) := v.maximalIdeal.asIdeal
  let J : Ideal ℤ := I.map Rat.ringOfIntegersEquiv
  have hint : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) = Rat.ringOfIntegersEquiv := by
    ext x
    exact Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x
  have hcard :
      Ideal.absNorm J = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply]
    let e : (𝓞 ℚ) ⧸ I ≃+* ℤ ⧸ J :=
      Ideal.quotientEquiv I J Rat.ringOfIntegersEquiv rfl
    exact Nat.card_congr e.toEquiv.symm
  have hspan :
      J = Ideal.span ({(Rat.HeightOneSpectrum.natGenerator v.maximalIdeal : ℤ)} : Set ℤ) := by
    simpa [I, J, hint] using
      (Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v.maximalIdeal).symm
  calc
    Rat.HeightOneSpectrum.natGenerator v.maximalIdeal = Ideal.absNorm J := by
      rw [hspan, Ideal.absNorm_apply]
      simpa [Submodule.cardQuot_apply] using
        (Int.card_ideal_quot (Rat.HeightOneSpectrum.natGenerator v.maximalIdeal)).symm
    _ = Ideal.absNorm I := hcard
    _ = finitePlaceNorm v := by
      rfl

theorem place_ring_integers (v : FinitePlace ℚ) :
    v.maximalIdeal.asIdeal.map Rat.ringOfIntegersEquiv =
      Ideal.rationalPrimeIdeal (finitePlaceNorm v) := by
  have hint : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) = Rat.ringOfIntegersEquiv := by
    ext x
    exact Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x
  calc
    v.maximalIdeal.asIdeal.map Rat.ringOfIntegersEquiv
      = Ideal.span ({(Rat.HeightOneSpectrum.natGenerator v.maximalIdeal : ℤ)} : Set ℤ) := by
          simpa [hint] using
            (Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v.maximalIdeal).symm
    _ = Ideal.rationalPrimeIdeal (finitePlaceNorm v) := by
          rw [place_nat_norm v]
          rfl

theorem splits_completely_split
    {E : Type*} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    (v : FinitePlace ℚ)
    (hq : Nat.Prime (finitePlaceNorm v))
    (hsplit : SplitsCompletelyField (K := ℚ) (E := E) v) :
    splitsCompletely E (finitePlaceNorm v) := by
  letI : IsScalarTower ℤ ℚ E := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    simp
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ E (𝓞 E)
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ ℚ (𝓞 ℚ)
  letI := IsIntegralClosure.MulSemiringAction (𝓞 ℚ) ℚ E (𝓞 E)
  letI : IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(E/ℚ)) (A := ℤ)
      (B := 𝓞 E) (K := ℚ) (L := E)
  letI : IsGaloisGroup Gal(ℚ/ℚ) ℤ (𝓞 ℚ) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(ℚ/ℚ)) (A := ℤ)
      (B := 𝓞 ℚ) (K := ℚ) (L := ℚ)
  letI : IsGaloisGroup Gal(E/ℚ) (𝓞 ℚ) (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(E/ℚ)) (A := 𝓞 ℚ)
      (B := 𝓞 E) (K := ℚ) (L := E)
  let pI : Ideal (𝓞 ℚ) := v.maximalIdeal.asIdeal
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal (finitePlaceNorm v)
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsPrime := rational_prime_ideal hq
  letI : qI.IsMaximal := rational_ideal_maximal hq
  let e0 : 𝓞 ℚ ≃ₐ[ℤ] ℤ :=
    AlgEquiv.ofRingEquiv (R := ℤ) (f := Rat.ringOfIntegersEquiv) <| by
      intro x
      norm_num [Rat.ringOfIntegersEquiv_apply_coe]
  have hpmap : pI.map e0 = qI := by
    simpa [pI, qI] using place_ring_integers v
  have hqover : qI.LiesOver qI := by
    rw [Ideal.liesOver_iff]
    rfl
  letI : qI.LiesOver qI := hqover
  have hpover : pI.LiesOver qI := by
    have halg : (algebraMap ℤ (𝓞 ℚ)) = e0.symm.toRingHom :=
      Subsingleton.elim _ _
    rw [Ideal.liesOver_iff]
    change qI = pI.comap (algebraMap ℤ (𝓞 ℚ))
    rw [halg]
    calc
      qI = pI.map e0.toRingHom := by
        simpa using hpmap.symm
      _ = pI.comap e0.symm.toRingHom := by
        exact (Ideal.comap_symm (I := pI) e0.toRingEquiv).symm
  letI : pI.LiesOver qI := hpover
  letI : pI.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := qI) (P := pI)
  obtain ⟨⟨P, hPprime, hPover⟩⟩ := pI.nonempty_primesOver (S := 𝓞 E)
  letI : P.IsPrime := hPprime
  letI : P.LiesOver pI := hPover
  letI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := pI) (P := P)
  have hPmem : P ∈ Ideal.primesOver pI (𝓞 E) := ⟨hPprime, hPover⟩
  have hPoverq : P.LiesOver qI := Ideal.LiesOver.trans P pI qI
  letI : P.LiesOver qI := hPoverq
  have hramP : Ideal.ramificationIdx pI P = 1 := (hsplit.2 P hPmem).1
  have hinP : Ideal.inertiaDeg pI P = 1 := (hsplit.2 P hPmem).2
  have hramPIn : pI.ramificationIdxIn (𝓞 E) = 1 := by
    calc
      pI.ramificationIdxIn (𝓞 E)
        = Ideal.ramificationIdx pI P := by
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := pI) (P := P) (G := Gal(E/ℚ))
      _ = 1 := hramP
  have hinPIn : pI.inertiaDegIn (𝓞 E) = 1 := by
    calc
      pI.inertiaDegIn (𝓞 E)
        = Ideal.inertiaDeg pI P := by
            exact Ideal.inertiaDegIn_eq_inertiaDeg
              (p := pI) (P := P) (G := Gal(E/ℚ))
      _ = 1 := hinP
  have hramSelf : Ideal.ramificationIdx qI qI = 1 := by
    have hqItop' : qI ≠ ⊤ := Ideal.IsPrime.ne_top (show qI.IsPrime by infer_instance)
    have hqItop : Ideal.map (algebraMap ℤ ℤ) qI ≠ ⊤ := by
      simpa using hqItop'
    have hqI0' : Ideal.map (algebraMap ℤ ℤ) qI ≠ ⊥ := by
      simpa using hqI0
    simpa using
      (Ideal.ramificationIdx_map_self_eq_one (R := ℤ) (S := ℤ)
        (p := qI) hqItop hqI0')
  have hinSelf : Ideal.inertiaDeg qI qI = 1 := by
    rw [Ideal.inertiaDeg_algebraMap (p := qI) (P := qI)]
    exact Module.finrank_self (ℤ ⧸ qI)
  have hramBaseIn : qI.ramificationIdxIn (𝓞 ℚ) = 1 := by
    calc
      qI.ramificationIdxIn (𝓞 ℚ)
        = Ideal.ramificationIdx qI pI := by
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := qI) (P := pI) (G := Gal(ℚ/ℚ))
      _ = Ideal.ramificationIdx qI (pI.map e0) := by
            symm
            exact Ideal.ramificationIdx_map_eq (p := qI) (P := pI) e0
      _ = Ideal.ramificationIdx qI qI := by
            rw [hpmap]
      _ = 1 := hramSelf
  have hinBaseIn : qI.inertiaDegIn (𝓞 ℚ) = 1 := by
    calc
      qI.inertiaDegIn (𝓞 ℚ)
        = Ideal.inertiaDeg qI pI := by
            exact Ideal.inertiaDegIn_eq_inertiaDeg
              (p := qI) (P := pI) (G := Gal(ℚ/ℚ))
      _ = Ideal.inertiaDeg qI (pI.map e0) := by
            symm
            exact Ideal.inertiaDeg_map_eq (p := qI) (P := pI) e0
      _ = Ideal.inertiaDeg qI qI := by
            rw [hpmap]
      _ = 1 := hinSelf
  have hramEIn : qI.ramificationIdxIn (𝓞 E) = 1 := by
    calc
      qI.ramificationIdxIn (𝓞 E)
        = qI.ramificationIdxIn (𝓞 ℚ) * pI.ramificationIdxIn (𝓞 E) := by
            symm
            exact Ideal.ramificationIdxIn_mul_ramificationIdxIn'
              (p := qI) pI (Gal(ℚ/ℚ)) (𝓞 E) (Gal(E/ℚ)) (Gal(E/ℚ))
      _ = 1 := by rw [hramBaseIn, hramPIn]
  have hinEIn : qI.inertiaDegIn (𝓞 E) = 1 := by
    calc
      qI.inertiaDegIn (𝓞 E)
        = qI.inertiaDegIn (𝓞 ℚ) * pI.inertiaDegIn (𝓞 E) := by
            symm
            exact Ideal.inertiaDegIn_mul_inertiaDegIn
              (p := qI) pI (Gal(ℚ/ℚ)) (𝓞 E) (Gal(E/ℚ)) (Gal(E/ℚ))
      _ = 1 := by rw [hinBaseIn, hinPIn]
  have hPe : Ideal.ramificationIdx qI P = 1 := by
    calc
      Ideal.ramificationIdx qI P
        = qI.ramificationIdxIn (𝓞 E) := by
            symm
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := qI) (P := P) (G := Gal(E/ℚ))
      _ = 1 := hramEIn
  have hPf : Ideal.inertiaDeg qI P = 1 := by
    calc
      Ideal.inertiaDeg qI P
        = qI.inertiaDegIn (𝓞 E) := by
            symm
            exact Ideal.inertiaDegIn_eq_inertiaDeg
              (p := qI) (P := P) (G := Gal(E/ℚ))
      _ = 1 := hinEIn
  have h_algE : (DivisionRing.toRatAlgebra : Algebra ℚ E) = ‹Algebra ℚ E› :=
    Subsingleton.elim _ _
  cases h_algE
  exact splits_completely_conditions E hq P hPe hPf

/- Hence `q_i` splits completely in `𝓕/ℚ`. -/
theorem chosen_splits_cut (i : ℕ) :
    SplitsCompletelyExtension (chosenPrime i) cutField := by
  intro K _ _ hEmbed hK
  haveI : IsGalois ℚ K := hK
  rcases hEmbed with ⟨f⟩
  let E : IntermediateField ℚ cutField := f.fieldRange
  let e : K ≃ₐ[ℚ] ↥E := by
    simpa [E, AlgHom.fieldRange_toSubalgebra f] using (AlgEquiv.ofInjectiveField f)
  letI : FiniteDimensional ℚ ↥E :=
    FiniteDimensional.of_surjective e.toLinearEquiv.toLinearMap e.surjective
  letI : NumberField ↥E := NumberField.of_module_finite ℚ ↥E
  letI : IsGalois ℚ ↥E := IsGalois.of_algEquiv e
  have hE_gal : IsGalois ℚ ↥E := IsGalois.of_algEquiv e
  let Efg : FiniteGaloisIntermediateField ℚ cutField :=
    @FiniteGaloisIntermediateField.mk ℚ cutField _ _ _ E inferInstance hE_gal
  have hcut :
      ∀ j,
        SplitsCompletelyPlace (K := ℚ) (KS := initialProExtension)
          (chosenAmbientPlace j) cutField := by
    simpa [cutField, cutClosedSubgroup, hmrFixedField] using
      (cutting_level_output chosenAmbientPlace chosenAmbientFrobenius
        (fun j => by
          rw [chosen_ambient_norm j]
          exact chosen_avoids_s j)
        chosen_ambient_unramified
        chosen_ambient
        chosen_ambient_frobenius).2
  have hsplitAt :
      SplitsCompletelyField (K := ℚ) (E := ↥E) (chosenAmbientPlace i) := by
    simpa [Efg] using hcut i Efg
  have hsplitE :
      splitsCompletely ↥E (chosenPrime i) := by
    have hsplitNorm :
        splitsCompletely ↥E (finitePlaceNorm (chosenAmbientPlace i)) := by
      exact splits_completely_split (chosenAmbientPlace i)
        (by simpa [chosen_ambient_norm i] using chosenPrime_prime i) hsplitAt
    simpa [chosen_ambient_norm i] using hsplitNorm
  simpa using splits_completely_alg e.symm (chosenPrime_prime i) hsplitE

/-
Also, for each `i`, every finite-level arithmetic Frobenius above `q_i`
becomes trivial in the cut extension.
-/
theorem chosen_trivial_cut (i : ℕ) :
    FrobeniusTrivialExtension (chosenPrime i) cutField := by
  intro K _ _ hEmb hGal Q _ _ _ σ hσ
  haveI : IsGalois ℚ K := hGal
  have hsplitK : splitsCompletely K (chosenPrime i) :=
    chosen_splits_cut i K hEmb hGal
  exact
    (completely_arith_frob
      K (chosenPrime_prime i) Q σ hσ).1 hsplitK

/- Define `P_∞ := {q_0, q_1, q_2, ...}`. -/
def splitPrimeSet : Set ℕ :=
  Set.range chosenPrime

/- The set `P_∞` is infinite. -/
theorem split_set_infinite :
    splitPrimeSet.Infinite := by
  simpa [splitPrimeSet] using
    Set.infinite_range_of_injective (f := chosenPrime)
      (Classical.choose_spec chosen_prime_sequence).1

/- Every element of `P_∞` is `1 mod 4`. -/
theorem split_set_four {q : ℕ} (hq : q ∈ splitPrimeSet) :
    q % 4 = 1 := by
  rcases hq with ⟨i, rfl⟩
  exact chosen_mod_four i

/- Every element of `P_∞` splits completely in `𝓕`. -/
theorem split_splits_cut {q : ℕ} (hq : q ∈ splitPrimeSet) :
    SplitsCompletelyExtension q cutField := by
  rcases hq with ⟨i, rfl⟩
  exact chosen_splits_cut i

/- Extracting an ordinary tower of number fields. -/
theorem quotient_tower_data :
    ∃ Γs : ℕ → OpenNormalSubgroup cutQuotientGroup,
      Γs 0 = topOpenSubgroup cutQuotientGroup ∧
      (∀ j, Γs (j + 1) ≤ Γs j) ∧
      Tendsto (fun j => (Γs j : Subgroup cutQuotientGroup).index) atTop atTop := by
  let _ : Infinite cutQuotientGroup := cut_group_infinite
  exact descending_subgroups_tendsto (Γ := cutQuotientGroup)

noncomputable def quotientTower (j : ℕ) : OpenNormalSubgroup cutQuotientGroup :=
  Classical.choose quotient_tower_data j

theorem quotientTower_zero :
    quotientTower 0 = topOpenSubgroup cutQuotientGroup := by
  exact (Classical.choose_spec quotient_tower_data).1

theorem quotientTower_desc (j : ℕ) :
    quotientTower (j + 1) ≤ quotientTower j := by
  exact (Classical.choose_spec quotient_tower_data).2.1 j

theorem tower_index_tendsto :
    Tendsto (fun j => (quotientTower j : Subgroup cutQuotientGroup).index) atTop atTop := by
  exact (Classical.choose_spec quotient_tower_data).2.2

/- Define `F_j := 𝓕^{Γ_j}`. -/
noncomputable def towerField (j : ℕ) : IntermediateField ℚ cutField :=
  IntermediateField.fixedField (quotientTower j : Subgroup cutQuotientGroup)

instance instRatTower (j : ℕ) : Algebra ℚ (towerField j) :=
  (towerField j).algebra

instance instModuleTower (j : ℕ) : Module ℚ (towerField j) := by
  let _ := instRatTower j
  infer_instance

instance instNumberTower (j : ℕ) : NumberField (towerField j) := by
  let H : ClosedSubgroup cutQuotientGroup :=
    { toSubgroup := quotientTower j
      isClosed' := OpenSubgroup.isClosed (quotientTower j).toOpenSubgroup }
  letI : H.Normal := by
    change (quotientTower j : Subgroup cutQuotientGroup).Normal
    infer_instance
  have hfix : (towerField j).fixingSubgroup = H.1 := by
    simpa [towerField] using
      (InfiniteGalois.fixingSubgroup_fixedField
        (k := ℚ) (K := cutField) H)
  let hfg :=
    (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
      (k := ℚ) (K := cutField) (towerField j)).mp <| by
      rw [hfix]
      refine ⟨(quotientTower j).isOpen', ?_⟩
      change (quotientTower j : Subgroup cutQuotientGroup).Normal
      infer_instance
  letI : FiniteDimensional ℚ (towerField j) := by
    exact hfg.1
  exact NumberField.of_module_finite ℚ (towerField j)

def quotientTowerClosed (j : ℕ) : ClosedSubgroup cutQuotientGroup where
  toSubgroup := quotientTower j
  isClosed' := OpenSubgroup.isClosed (quotientTower j).toOpenSubgroup

instance instTowerClosed (j : ℕ) : (quotientTowerClosed j).Normal := by
  change (quotientTower j : Subgroup cutQuotientGroup).Normal
  infer_instance

theorem towerField_fixed (j : ℕ) :
    towerField j = IntermediateField.fixedField (quotientTower j : Subgroup cutQuotientGroup) := by
  rfl

theorem towerField_nested (j : ℕ) :
    EmbedsIntoField (towerField j) (towerField (j + 1)) := by
  refine ⟨IntermediateField.inclusion ?_⟩
  change
    IntermediateField.fixedField (quotientTower j : Subgroup cutQuotientGroup) ≤
      IntermediateField.fixedField (quotientTower (j + 1) : Subgroup cutQuotientGroup)
  exact IntermediateField.fixedField_antitone (quotientTower_desc j)

theorem tower_degree_index (j : ℕ) :
    Module.finrank ℚ (towerField j) =
      (quotientTower j : Subgroup cutQuotientGroup).index := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := towerField j)]
  exact congrArg Subgroup.index <| by
    simpa [towerField, quotientTowerClosed] using
      (InfiniteGalois.fixingSubgroup_fixedField
        (k := ℚ) (K := cutField) (quotientTowerClosed j))

theorem tower_degree_tendsto :
    Tendsto (fun j => Module.finrank ℚ (towerField j)) atTop atTop := by
  simpa [tower_degree_index] using tower_index_tendsto

theorem tower_galois_quotient (j : ℕ) :
    Nonempty
      (cutQuotientGroup ⧸ (quotientTower j : Subgroup cutQuotientGroup) ≃*
        Gal(towerField j/ℚ)) := by
  exact ⟨by
    simpa [towerField, cutQuotientGroup] using
      (galoisFixedField (L := cutField) (quotientTowerClosed j))⟩

theorem tower_three_group (j : ℕ) :
    GaloisThreeExtension (towerField j) := by
  constructor
  · have hfix :
        (towerField j).fixingSubgroup =
          (quotientTowerClosed j : ClosedSubgroup cutQuotientGroup).1 := by
      simpa [towerField, quotientTowerClosed] using
        (InfiniteGalois.fixingSubgroup_fixedField
          (k := ℚ) (K := cutField) (quotientTowerClosed j))
    have hfg :
        FiniteDimensional ℚ (towerField j) ∧ IsGalois ℚ (towerField j) :=
      (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
        (k := ℚ) (K := cutField) (towerField j)).mp <| by
          rw [hfix]
          refine ⟨(quotientTower j).isOpen', ?_⟩
          change (quotientTower j : Subgroup cutQuotientGroup).Normal
          infer_instance
    exact hfg.2
  · have hquot :
        IsPGroup 3
          (cutQuotientGroup ⧸ (quotientTower j : Subgroup cutQuotientGroup)) :=
      cut_group_prothree.2 (quotientTower j)
    rcases tower_galois_quotient j with ⟨e⟩
    exact IsPGroup.of_equiv hquot e

theorem tower_totally_real (j : ℕ) :
    NumberField.IsTotallyReal (towerField j) := by
  rcases tower_three_group j with ⟨hGal, hPGroup⟩
  letI : IsGalois ℚ (towerField j) := hGal
  exact
    totally_gal_rat
      Nat.prime_three
      (by decide : 3 ≠ 2)
      (towerField j)
      hPGroup

theorem tower_embeds_cut (j : ℕ) :
    EmbedsIntoExtension (towerField j) cutField := by
  refine ⟨{ toRingHom := (towerField j).subtype, commutes' := ?_ }⟩
  intro q
  rfl

theorem cut_embeds_pro :
    ExtensionEmbeds cutField initialProExtension := by
  refine ⟨{ toRingHom := cutField.subtype, commutes' := ?_ }⟩
  intro q
  rfl

/-- Each tower field embeds into the ambient initial pro-`3` extension. -/
theorem tower_embeds_pro (j : ℕ) :
    EmbedsIntoExtension (towerField j) initialProExtension := by
  exact embeds_extension_trans
    (tower_embeds_cut j)
    cut_embeds_pro

theorem tower_unramified_outside (j : ℕ) :
    UnramifiedOutside (towerField j) initialRamifiedPrimes := by
  letI : IsGalois ℚ (towerField j) := (tower_three_group j).1
  exact
    unramified_outside_embeds
      (tower_embeds_pro j)

theorem tower_tame_s (j : ℕ) :
    TameAllPrimes (towerField j) initialRamifiedPrimes := by
  letI : IsGalois ℚ (towerField j) := (tower_three_group j).1
  have hPGroup : IsPGroup 3 (Gal(towerField j/ℚ)) := (tower_three_group j).2
  refine
    tame_hypothesis_away
      3
      (by decide)
      (towerField j)
      hPGroup
      initialRamifiedPrimes
      ramified_primes_prime
      ?_
  simp [ramified_primes]

theorem tower_discriminant_product (j : ℕ) :
    rootDiscriminant (towerField j) ≤
      Finset.prod initialRamifiedPrimes (fun r => (r : ℝ)) := by
  rcases tower_three_group j with ⟨hGal, hPGroup⟩
  letI : IsGalois ℚ (towerField j) := hGal
  exact
    discriminant_ramified_ell
      (ℓ := 3) Nat.prime_three
      (L := towerField j) hPGroup
      initialRamifiedPrimes ramified_primes_prime
      (by simp [ramified_primes])
      (by simpa [UnramifiedOutside] using tower_unramified_outside j)

theorem tower_discriminant_numeric (j : ℕ) :
    rootDiscriminant (towerField j) ≤ 1983163 := by
  calc
    rootDiscriminant (towerField j) ≤
        Finset.prod initialRamifiedPrimes (fun r => (r : ℝ)) :=
      tower_discriminant_product j
    _ = 1983163 := by
      norm_num [ramified_primes]

/- In particular, `sup_j rd(F_j) < ∞`. -/
theorem tower_discriminant_bounded :
    ∃ ρ : ℝ, ∀ j : ℕ, rootDiscriminant (towerField j) ≤ ρ := by
  exact ⟨1983163, tower_discriminant_numeric⟩

/- Finally, every `q_i ∈ P_∞` splits completely in every finite subfield `F_j ⊆ 𝓕`. -/
theorem splits_every_tower
    {q : ℕ} (hq : q ∈ splitPrimeSet) (j : ℕ) :
    splitsCompletely (towerField j) q := by
  exact
    split_splits_cut hq
      (towerField j)
      (tower_embeds_cut j)
      (tower_three_group j).1

end STBuild
end TBluepr
end Submission
