import Towers.Group.NilpotentProducts.CommutatorIdentities
import Towers.Group.NilpotentProducts.TripleCommutators
import Towers.Group.Edmonton.HallEmbeddings

open scoped IsMulCommutative

/-!
# Hall-Petresco preliminaries in Struik's 1960 paper

This file records the exact group identities behind Theorems H2 and H3 and
Lemma H1.  The correction is defined without choosing a particular Hall
collection; its membership in the commutator subgroup is independent of that
choice.  `HallEmbeddingTheorems` supplies the finer Petresco decomposition
and polynomial-coordinate results.
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton
open Towers.TCTex

universe u

variable {G : Type u} [Group G]

/-- The correction left after separating the simultaneous powers of the
factors from the power of their ordered product. -/
def hallPowerCorrection (x : List G) (m : ℕ) : G :=
  ((x.map fun g => g ^ m).prod)⁻¹ * x.prod ^ m

/-- Exact form of Struik's equation (2), before choosing and collecting a
sequence of commutator factors. -/
theorem pointwise_powers_correction (x : List G) (m : ℕ) :
    x.prod ^ m =
      (x.map fun g => g ^ m).prod * hallPowerCorrection x m := by
  simp [hallPowerCorrection]

/-- Hall's canonical Petresco terms give the binomial-product side of
Theorem H2.  The exponent of the `w`th term is exactly `choose m w`. -/
theorem petresco (x : List G) (m : ℕ) :
    (x.map fun g => g ^ m).prod =
      petrescoBinomialProduct (petrescoTerm x) m :=
  petresco_term_family x m

/-- The `w`th canonical Petresco term has commutator weight at least `w`,
which is the depth assertion accompanying equations (2)-(3). -/
theorem petrescoTerm_mem
    (x : List G) (w : ℕ) :
    petrescoTerm x w ∈ Subgroup.lowerCentralSeries G (w - 1) :=
  petresco_lower_series x w

/-- The positive-weight Petresco factors after the first term.  This is the
finite part of Hall's fixed commutator sequence that can occur at exponent
`m`. -/
def hallPetrescoTail (x : List G) (m : ℕ) : G :=
  ((List.range (m - 1)).map fun j =>
    petrescoTerm x (j + 2) ^ Nat.choose m (j + 2)).prod

/-- Splitting the first Petresco term from Hall's binomial product. -/
theorem petresco_binomial_tail
    (x : List G) (m : ℕ) :
    petrescoBinomialProduct (petrescoTerm x) m =
      x.prod ^ m * hallPetrescoTail x m := by
  cases m with
  | zero =>
      simp [petrescoBinomialProduct, hallPetrescoTail]
  | succ m =>
      unfold petrescoBinomialProduct hallPetrescoTail
      rw [List.finRange_succ]
      simp only [List.map_cons, List.prod_cons, Fin.val_zero,
        zero_add, Nat.choose_one_right, petrescoTerm_one]
      congr 1
      rw [Nat.succ_sub_one]
      rw [← List.map_coe_finRange_eq_range]
      simp only [List.map_map]
      apply congrArg List.prod
      apply List.map_congr_left
      intro j _
      simp

/-- **Struik's Theorem H2, collected form.**  The correction to
`(R*S)^m = R^m*S^m` is the inverse of the explicit finite product of Hall's
fixed Petresco terms.  The exponent on the term of weight at least `w` is
exactly `choose m w`. -/
theorem powers_petresco_tail (R S : G) (m : ℕ) :
    (R * S) ^ m =
      R ^ m * S ^ m * (hallPetrescoTail [R, S] m)⁻¹ := by
  have hpetresco := petresco [R, S] m
  rw [petresco_binomial_tail] at hpetresco
  have hpetresco' :
      R ^ m * S ^ m =
        (R * S) ^ m * hallPetrescoTail [R, S] m := by
    simpa using hpetresco
  rw [hpetresco']
  group

/-- The two-factor specialization of equation (2). -/
theorem mul_powers_correction (R S : G) (m : ℕ) :
    (R * S) ^ m =
      R ^ m * S ^ m * hallPowerCorrection [R, S] m := by
  simpa [mul_assoc] using pointwise_powers_correction [R, S] m

/-- The previously abstract two-factor correction is exactly the inverse
Petresco tail. -/
theorem pair_petresco_inv
    (R S : G) (m : ℕ) :
    hallPowerCorrection [R, S] m =
      (hallPetrescoTail [R, S] m)⁻¹ := by
  apply mul_left_cancel
    (a := R ^ m * S ^ m)
  rw [← mul_powers_correction, powers_petresco_tail]

/-- In a commutative group, simultaneous powering commutes with taking the
ordered product. -/
private theorem pow_prod
    {A : Type*} [CommGroup A] (x : List G) (f : G →* A) (m : ℕ) :
    ((x.map fun g => f g ^ m).prod) = f x.prod ^ m := by
  induction x with
  | nil => simp
  | cons g x ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, mul_pow, ih]

/-- Every Hall power correction is a product of commutators: it belongs to
the second one-based lower-central term. -/
theorem correction_lower_series
    (x : List G) (m : ℕ) :
    hallPowerCorrection x m ∈ Subgroup.lowerCentralSeries G 1 := by
  let q : G →* G ⧸ Subgroup.lowerCentralSeries G 1 :=
    QuotientGroup.mk' (Subgroup.lowerCentralSeries G 1)
  apply (QuotientGroup.eq_one_iff (hallPowerCorrection x m)).mp
  change q (hallPowerCorrection x m) = 1
  rw [hallPowerCorrection, map_mul, map_inv, map_pow, map_list_prod]
  simp only [List.map_map]
  change
    ((x.map fun g => q (g ^ m)).prod)⁻¹ * q x.prod ^ m = 1
  simp_rw [map_pow]
  letI : IsMulCommutative (G ⧸ Subgroup.lowerCentralSeries G 1) := by
    apply (Subgroup.Normal.quotient_commutative_iff_commutator_le).2
    rfl
  rw [pow_prod x q m]
  exact inv_mul_cancel _

/-- Theorem H2 recollected into Struik's single nondecreasing standard Hall
sequence in the universal free nilpotent truncation.  Every weight-one
coordinate of the correction is zero. -/
theorem correction_standard_recollection
    (d n : ℕ)
    (hn : 2 ≤ n)
    (R S :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (m : ℕ) :
    ∃ e : StandardExponentFamily.{u} d,
      (∀ s : ℕ,
        1 ≤ s →
          s < 2 →
            s < n →
              e s = 0) ∧
        (R * S) ^ m =
          R ^ m * S ^ m * standardHallProduct d n e := by
  let correction := hallPowerCorrection [R, S] m
  have hcorrection :
      correction ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    exact correction_lower_series [R, S] m
  obtain ⟨e, heProduct, heZero⟩ :=
    standard_recollection_series
      d n 2 hn correction (by simpa using hcorrection)
  refine ⟨e, heZero, ?_⟩
  rw [heProduct]
  simpa [correction, mul_assoc] using mul_powers_correction R S m

/-- A list all of whose entries are actual Hall commutators. -/
def HallCommutatorList (c : List G) : Prop :=
  ∀ z ∈ c, ∃ a b : G, z = hallCommutator a b

/-- Reordering a finite product changes it by a finite product of actual
Hall commutators.  The proof follows the supplied permutation: an adjacent
swap contributes one conjugated commutator. -/
theorem perm_prod_commutators
    {x reordered : List G} (hperm : x.Perm reordered) :
    ∃ c : List G,
      HallCommutatorList c ∧
        x.prod = reordered.prod * c.prod := by
  induction hperm with
  | nil =>
      exact ⟨[], by simp [HallCommutatorList]⟩
  | cons g hperm ih =>
      obtain ⟨c, hc, hprod⟩ := ih
      refine ⟨c, hc, ?_⟩
      simp only [List.prod_cons]
      rw [hprod]
      group
  | swap a b l =>
      let t := l.prod
      let c :=
        hallCommutator (t⁻¹ * b * t) (t⁻¹ * a * t)
      refine ⟨[c], ?_, ?_⟩
      · simp only [HallCommutatorList, List.mem_cons,
          List.not_mem_nil, or_false]
        intro z hz
        subst z
        exact ⟨t⁻¹ * b * t, t⁻¹ * a * t, rfl⟩
      · simp only [List.prod_cons, List.prod_nil, mul_one]
        simp [c, t, hallCommutator]
        group
  | trans hxy hyz ihxy ihyz =>
      obtain ⟨cxy, hcxy, hxyprod⟩ := ihxy
      obtain ⟨cyz, hcyz, hyzprod⟩ := ihyz
      refine ⟨cyz ++ cxy, ?_, ?_⟩
      · intro z hz
        rw [List.mem_append] at hz
        exact hz.elim (hcyz z) (hcxy z)
      · rw [hxyprod, hyzprod, List.prod_append]
        group

/-- The correction for collecting the power factors in an arbitrary
permuted order, as in Theorem H3. -/
def hallReorderedCorrection
    (x reordered : List G) (m : ℕ) : G :=
  ((reordered.map fun g => g ^ m).prod)⁻¹ * x.prod ^ m

/-- Exact form of Struik's equation (4) for any chosen ordering of the
power factors. -/
theorem reordered_powers_correction
    (x reordered : List G) (m : ℕ) :
    x.prod ^ m =
      (reordered.map fun g => g ^ m).prod *
        hallReorderedCorrection x reordered m := by
  simp [hallReorderedCorrection]

/-- If `reordered` is a permutation of the original factors, the correction
in Theorem H3 belongs to the commutator subgroup. -/
theorem reordered_lower_series
    {x reordered : List G} (hperm : x.Perm reordered) (m : ℕ) :
    hallReorderedCorrection x reordered m ∈
      Subgroup.lowerCentralSeries G 1 := by
  let q : G →* G ⧸ Subgroup.lowerCentralSeries G 1 :=
    QuotientGroup.mk' (Subgroup.lowerCentralSeries G 1)
  apply
    (QuotientGroup.eq_one_iff
      (hallReorderedCorrection x reordered m)).mp
  change q (hallReorderedCorrection x reordered m) = 1
  rw [hallReorderedCorrection, map_mul, map_inv, map_pow,
    map_list_prod]
  simp only [List.map_map]
  change
    ((reordered.map fun g => q (g ^ m)).prod)⁻¹ *
      q x.prod ^ m = 1
  simp_rw [map_pow]
  letI : IsMulCommutative (G ⧸ Subgroup.lowerCentralSeries G 1) := by
    apply (Subgroup.Normal.quotient_commutative_iff_commutator_le).2
    rfl
  have hpowPerm :
      (x.map fun g => q g ^ m).Perm
        (reordered.map fun g => q g ^ m) :=
    hperm.map _
  rw [← hpowPerm.prod_eq]
  rw [pow_prod x q m]
  exact inv_mul_cancel _

/-- **Struik's Theorem H3, explicit finite collection.**  A chosen
permutation of the powered factors contributes a finite product of actual
Hall commutators, while powering the original ordered product contributes
the fixed Petresco tail with exact binomial exponents. -/
theorem reordered_powers_petresco
    {x reordered : List G} (hperm : x.Perm reordered) (m : ℕ) :
    ∃ c : List G,
      HallCommutatorList c ∧
        x.prod ^ m =
          (reordered.map fun g => g ^ m).prod *
            c.prod * (hallPetrescoTail x m)⁻¹ := by
  obtain ⟨c, hc, hprod⟩ :=
    perm_prod_commutators
      (hperm.map fun g => g ^ m)
  refine ⟨c, hc, ?_⟩
  have hpetresco := petresco x m
  rw [petresco_binomial_tail] at hpetresco
  have hpower :
      (x.map fun g => g ^ m).prod =
        x.prod ^ m * hallPetrescoTail x m := by
    simpa using hpetresco
  rw [hprod] at hpower
  apply mul_right_cancel
    (b := hallPetrescoTail x m)
  rw [hpower]
  group

/-- The earlier opaque H3 correction is exactly the explicit permutation
commutator product followed by the inverse Petresco tail. -/
theorem reordered_correction_collected
    {x reordered : List G} (hperm : x.Perm reordered) (m : ℕ) :
    ∃ c : List G,
      HallCommutatorList c ∧
        hallReorderedCorrection x reordered m =
          c.prod * (hallPetrescoTail x m)⁻¹ := by
  obtain ⟨c, hc, hcollected⟩ := reordered_powers_petresco hperm m
  refine ⟨c, hc, ?_⟩
  apply mul_left_cancel
    (a := (reordered.map fun g => g ^ m).prod)
  rw [← reordered_powers_correction, hcollected]
  group

/-- Theorem H3 recollected into one nondecreasing standard Hall sequence in
the universal free nilpotent truncation.  The supplied permutation affects
the displayed powered factors, while the correction has no weight-one
coordinates. -/
theorem reordered_standard_recollection
    (d n : ℕ)
    (hn : 2 ≤ n)
    {x reordered :
      List
        (LowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} d)) n)}
    (hperm : x.Perm reordered)
    (m : ℕ) :
    ∃ e : StandardExponentFamily.{u} d,
      (∀ s : ℕ,
        1 ≤ s →
          s < 2 →
            s < n →
              e s = 0) ∧
        x.prod ^ m =
          (reordered.map fun g => g ^ m).prod *
            standardHallProduct d n e := by
  let correction := hallReorderedCorrection x reordered m
  have hcorrection :
      correction ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    exact reordered_lower_series hperm m
  obtain ⟨e, heProduct, heZero⟩ :=
    standard_recollection_series
      d n 2 hn correction (by simpa using hcorrection)
  refine ⟨e, heZero, ?_⟩
  rw [heProduct]
  simpa [correction] using reordered_powers_correction x reordered m

/-- The correction occurring in Lemma H1, obtained by applying Theorem H2
to `X` and `(X,Y)`. -/
def hallCommutatorCorrection
    (X Y : G) (m : ℕ) : G :=
  hallPowerCorrection [X, hallCommutator X Y] m

/-- Exact uncollected form of Struik's equation (5). -/
theorem commutator_pow_correction (X Y : G) (m : ℕ) :
    hallCommutator (X ^ m) Y =
      hallCommutator X Y ^ m *
        hallCommutatorCorrection X Y m := by
  let C := hallCommutator X Y
  have hconjugate : Y⁻¹ * X * Y = X * C := by
    simp [C, hallCommutator, mul_assoc]
  have hpower := mul_powers_correction X C m
  have hconjugatePow :
      (Y⁻¹ * X * Y) ^ m = Y⁻¹ * X ^ m * Y := by
    simpa using (conj_pow (a := Y⁻¹) (b := X) (i := m))
  unfold hallCommutator hallCommutatorCorrection
  change
    (X ^ m)⁻¹ * Y⁻¹ * X ^ m * Y =
      C ^ m * hallPowerCorrection [X, C] m
  rw [← inv_pow]
  calc
    X⁻¹ ^ m * Y⁻¹ * X ^ m * Y =
        X⁻¹ ^ m * (Y⁻¹ * X ^ m * Y) := by group
    _ = X⁻¹ ^ m * (Y⁻¹ * X * Y) ^ m := by rw [hconjugatePow]
    _ = X⁻¹ ^ m * (X * C) ^ m := by rw [hconjugate]
    _ = X⁻¹ ^ m *
        (X ^ m * C ^ m * hallPowerCorrection [X, C] m) := by
      rw [hpower]
    _ = C ^ m * hallPowerCorrection [X, C] m := by
      simp [mul_assoc]

/-- **Struik's Lemma H1, collected form.**  The correction factors are the
fixed Petresco terms in `X` and `(X,Y)`, with the same binomial exponents as
in Theorem H2. -/
theorem commutator_petresco_tail (X Y : G) (m : ℕ) :
    hallCommutator (X ^ m) Y =
      hallCommutator X Y ^ m *
        (hallPetrescoTail
          [X, hallCommutator X Y] m)⁻¹ := by
  let C := hallCommutator X Y
  have hconjugate : Y⁻¹ * X * Y = X * C := by
    simp [C, hallCommutator, mul_assoc]
  have hpower := powers_petresco_tail X C m
  have hconjugatePow :
      (Y⁻¹ * X * Y) ^ m = Y⁻¹ * X ^ m * Y := by
    simpa using (conj_pow (a := Y⁻¹) (b := X) (i := m))
  unfold hallCommutator
  change
    (X ^ m)⁻¹ * Y⁻¹ * X ^ m * Y =
      C ^ m * (hallPetrescoTail [X, C] m)⁻¹
  rw [← inv_pow]
  calc
    X⁻¹ ^ m * Y⁻¹ * X ^ m * Y =
        X⁻¹ ^ m * (Y⁻¹ * X ^ m * Y) := by group
    _ = X⁻¹ ^ m * (Y⁻¹ * X * Y) ^ m := by rw [hconjugatePow]
    _ = X⁻¹ ^ m * (X * C) ^ m := by rw [hconjugate]
    _ = X⁻¹ ^ m *
        (X ^ m * C ^ m *
          (hallPetrescoTail [X, C] m)⁻¹) := by
      rw [hpower]
    _ = C ^ m *
        (hallPetrescoTail [X, C] m)⁻¹ := by
      simp [mul_assoc]

/-- The correction used by the original
`commutator_pow_correction` declaration is the explicit
inverse Petresco tail in `X` and `(X,Y)`. -/
theorem petresco_tail_inv
    (X Y : G) (m : ℕ) :
    hallCommutatorCorrection X Y m =
      (hallPetrescoTail
        [X, hallCommutator X Y] m)⁻¹ := by
  unfold hallCommutatorCorrection
  exact
    pair_petresco_inv
      X (hallCommutator X Y) m

/-- The correction in Lemma H1 starts in the third one-based
lower-central term, since `(X,Y)` already belongs to the commutator
subgroup. -/
theorem lower_series_two
    (X Y : G) (m : ℕ) :
    hallCommutatorCorrection X Y m ∈
      Subgroup.lowerCentralSeries G 2 := by
  let C := hallCommutator X Y
  have hC : C ∈ Subgroup.lowerCentralSeries G 1 := by
    simpa [C] using
      commutator_lower_series
        (i := 0) (j := 0)
        (Subgroup.mem_top X) (Subgroup.mem_top Y)
  have hXC : hallCommutator X C ∈ Subgroup.lowerCentralSeries G 2 := by
    simpa using
      commutator_lower_series
        (i := 0) (j := 1)
        (Subgroup.mem_top X) hC
  let q : G →* G ⧸ Subgroup.lowerCentralSeries G 2 :=
    QuotientGroup.mk' (Subgroup.lowerCentralSeries G 2)
  have hcommute : Commute (q X) (q C) := by
    rw [← commute_paper_1960]
    have hmap :
        hallCommutator (q X) (q C) =
          q (hallCommutator X C) := by
      simp [hallCommutator, mul_assoc]
    rw [hmap]
    exact (QuotientGroup.eq_one_iff (hallCommutator X C)).2 hXC
  apply
    (QuotientGroup.eq_one_iff
      (hallCommutatorCorrection X Y m)).mp
  change q (hallCommutatorCorrection X Y m) = 1
  unfold hallCommutatorCorrection
  change q (hallPowerCorrection [X, C] m) = 1
  rw [hallPowerCorrection, map_mul, map_inv, map_pow, map_list_prod]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  change
    (q (X ^ m) * q (C ^ m))⁻¹ * (q X * q C) ^ m = 1
  simp_rw [map_pow]
  rw [hcommute.mul_pow]
  exact inv_mul_cancel _

/-- Lemma H1 recollected into one nondecreasing standard Hall sequence in
the universal free nilpotent truncation.  Its correction has no coordinates
of weights one or two. -/
theorem commutator_standard_recollection
    (d n : ℕ)
    (hn : 2 ≤ n)
    (X Y :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (m : ℕ) :
    ∃ e : StandardExponentFamily.{u} d,
      (∀ s : ℕ,
        1 ≤ s →
          s < 3 →
            s < n →
              e s = 0) ∧
        hallCommutator (X ^ m) Y =
          hallCommutator X Y ^ m *
            standardHallProduct d n e := by
  let correction := hallCommutatorCorrection X Y m
  have hcorrection :
      correction ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    exact lower_series_two X Y m
  obtain ⟨e, heProduct, heZero⟩ :=
    standard_recollection_series
      d n 3 hn correction (by simpa using hcorrection)
  refine ⟨e, heZero, ?_⟩
  rw [heProduct]
  simpa [correction] using commutator_pow_correction X Y m

end P1960
end Struik
