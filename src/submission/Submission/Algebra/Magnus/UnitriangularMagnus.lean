import Submission.Algebra.Magnus.MagnusEmbedding
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.GroupTheory.QuotientGroup.Basic


/-!
# Unitriangular representations from Magnus coefficients

This file constructs the upper-unitriangular representation attached to a
word in Section 5 of Efrat--Chapman.  Incidence algebras on finite chains are
used as the upper-triangular matrix algebra, so multiplication is exactly
convolution over intermediate positions.
-/

noncomputable section

namespace EChapma
namespace MSeries

open Finset

variable {R X : Type*} [CommRing R]

/-- The Cauchy product coefficient of a word, written as the sum over all
prefix/suffix decompositions. -/
theorem convolution_sum_range
    (f g : MSeries R X) (xs : List X) :
    convolutionList f g xs =
      ∑ k ∈ Finset.range (xs.length + 1),
        f (FreeMonoid.ofList (xs.take k)) *
          g (FreeMonoid.ofList (xs.drop k)) := by
  induction xs generalizing f with
  | nil => simp [convolutionList]
  | cons x xs ih =>
      rw [convolutionList, Finset.sum_range_succ']
      simp only [List.length_cons, List.take_zero,
        FreeMonoid.ofList_nil, List.drop_zero, List.take_succ_cons,
        List.drop_succ_cons, FreeMonoid.ofList_cons]
      rw [ih (f := shift x f)]
      rw [add_comm]
      congr 1

/-- The contiguous subword between two positions. -/
def wordSegment
    (xs : List X) (i j : Fin (xs.length + 1)) :
    FreeMonoid X :=
  FreeMonoid.ofList ((xs.drop i.1).take (j.1 - i.1))

/-- Contiguous subwords compose when an intermediate position lies in the
closed interval. -/
theorem wordSegment_mul
    (xs : List X) (i k j : Fin (xs.length + 1))
    (hik : i ≤ k) (hkj : k ≤ j) :
    wordSegment xs i k * wordSegment xs k j =
      wordSegment xs i j := by
  simp only [wordSegment, ← FreeMonoid.ofList_append]
  apply congrArg FreeMonoid.ofList
  have hdrop :
      xs.drop k.1 =
        (xs.drop i.1).drop (k.1 - i.1) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [hdrop, ← List.take_add]
  congr 2 ; omega

/-- The word segment from `i` to `j` has the expected length. -/
theorem wordSegment_length
    (xs : List X) (i j : Fin (xs.length + 1))
    (hij : i ≤ j) :
    (wordSegment xs i j).length = j.1 - i.1 := by
  change
    ((xs.drop i.1).take (j.1 - i.1)).length =
      j.1 - i.1
  simp only [List.length_take, List.length_drop]
  omega

/-- Reindex a sum over the natural offsets from `i` to `j` as a sum over
the corresponding closed interval in `Fin`. -/
theorem range_sub_icc
    {N : ℕ} (i j : Fin N) (hij : i ≤ j) (F : ℕ → R) :
    ∑ t ∈ Finset.range (j.1 - i.1 + 1), F t =
      ∑ k ∈ Finset.Icc i j, F (k.1 - i.1) := by
  have hij' : i.1 ≤ j.1 := hij
  apply Finset.sum_bij
      (fun t ht =>
        (⟨i.1 + t, by
          have ht' := Finset.mem_range.mp ht
          omega⟩ : Fin N))
  · intro t ht
    simp only [Finset.mem_Icc]
    have ht' := Finset.mem_range.mp ht
    constructor
    · change i.1 ≤ i.1 + t
      omega
    · change i.1 + t ≤ j.1
      omega
  · intro a ha b hb hab
    have hab' : i.1 + a = i.1 + b := congrArg Fin.val hab
    exact Nat.add_left_cancel hab'
  · intro k hk
    refine ⟨k.1 - i.1, Finset.mem_range.mpr ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hk
      omega
    · apply Fin.ext
      simp only
      simp only [Finset.mem_Icc] at hk
      omega
  · intro t ht
    rw [Nat.add_sub_cancel_left]

/-- A prefix of the segment from `i` to `j` is the segment ending at the
corresponding intermediate position. -/
theorem wordSegment_take
    (xs : List X) (i k j : Fin (xs.length + 1))
    (hik : i ≤ k) (hkj : k ≤ j) :
    FreeMonoid.ofList
        ((wordSegment xs i j).toList.take (k.1 - i.1)) =
      wordSegment xs i k := by
  have hik' : i.1 ≤ k.1 := hik
  have hkj' : k.1 ≤ j.1 := hkj
  simp only [wordSegment, FreeMonoid.toList_ofList, List.take_take]
  congr 2
  omega

/-- Dropping a prefix of the segment from `i` to `j` leaves the segment
starting at the corresponding intermediate position. -/
theorem wordSegment_drop
    (xs : List X) (i k j : Fin (xs.length + 1))
    (hik : i ≤ k) (hkj : k ≤ j) :
    FreeMonoid.ofList
        ((wordSegment xs i j).toList.drop (k.1 - i.1)) =
      wordSegment xs k j := by
  have hik' : i.1 ≤ k.1 := hik
  have hkj' : k.1 ≤ j.1 := hkj
  simp only [wordSegment, FreeMonoid.toList_ofList, List.drop_take]
  have hdrop :
      (xs.drop i.1).drop (k.1 - i.1) =
        xs.drop k.1 := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [hdrop]
  congr 2
  omega

/-- A power series evaluated on every interval of the finite chain of word
positions. -/
def wordIncidence
    (xs : List X) (f : MSeries R X) :
    IncidenceAlgebra R (Fin (xs.length + 1)) where
  toFun i j := if i ≤ j then f (wordSegment xs i j) else 0
  eq_zero_of_not_le' _i _j hij := if_neg hij

@[simp]
theorem word_incidence
    (xs : List X) (f : MSeries R X)
    (i j : Fin (xs.length + 1)) (hij : i ≤ j) :
    wordIncidence xs f i j = f (wordSegment xs i j) :=
  if_pos hij

/-- Cauchy multiplication on a contiguous word segment is incidence
convolution over the intermediate positions. -/
theorem mul_word_segment
    (xs : List X) (f g : MSeries R X)
    (i j : Fin (xs.length + 1)) (hij : i ≤ j) :
    (f * g) (wordSegment xs i j) =
      ∑ k ∈ Finset.Icc i j,
        f (wordSegment xs i k) * g (wordSegment xs k j) := by
  change
    convolutionList f g (wordSegment xs i j).toList = _
  rw [convolution_sum_range]
  have hlen :
      (wordSegment xs i j).toList.length =
        j.1 - i.1 :=
    wordSegment_length xs i j hij
  rw [hlen]
  rw [range_sub_icc i j hij
    (fun t =>
      f (FreeMonoid.ofList
          ((wordSegment xs i j).toList.take t)) *
        g (FreeMonoid.ofList
          ((wordSegment xs i j).toList.drop t)))]
  apply Finset.sum_congr rfl
  intro k hk
  have hik : i ≤ k := (Finset.mem_Icc.mp hk).1
  have hkj : k ≤ j := (Finset.mem_Icc.mp hk).2
  rw [wordSegment_take xs i k j hik hkj,
    wordSegment_drop xs i k j hik hkj]

/-- Evaluation on all contiguous subwords is a ring homomorphism into the
incidence algebra of word positions. -/
def incidenceRingHom
    (xs : List X) :
    MSeries R X →+*
      IncidenceAlgebra R (Fin (xs.length + 1)) where
  toFun := wordIncidence xs
  map_zero' := by
    apply IncidenceAlgebra.ext
    intro i j hij
    simp [wordIncidence]
  map_one' := by
    apply IncidenceAlgebra.ext
    intro i j hij
    rw [word_incidence xs 1 i j hij,
      IncidenceAlgebra.one_apply, one_apply,
      wordSegment_length xs i j hij]
    by_cases h : i = j
    · subst j
      simp
    · have hval : i.1 < j.1 := by
        have hij' : i.1 ≤ j.1 := hij
        omega
      have hsub : j.1 - i.1 ≠ 0 := by omega
      simp [h, hsub]
  map_add' f g := by
    apply IncidenceAlgebra.ext
    intro i j hij
    simp [word_incidence, hij]
  map_mul' f g := by
    apply IncidenceAlgebra.ext
    intro i j hij
    rw [word_incidence xs (f * g) i j hij,
      IncidenceAlgebra.mul_apply,
      mul_word_segment xs f g i j hij]
    apply Finset.sum_congr rfl
    intro k hk
    have hik : i ≤ k := (Finset.mem_Icc.mp hk).1
    have hkj : k ≤ j := (Finset.mem_Icc.mp hk).2
    rw [word_incidence xs f i k hik,
      word_incidence xs g k j hkj]

/-- The diagonal-one units of a finite-chain incidence algebra.  These are
the upper-unitriangular matrices in incidence-algebra form. -/
def unitriangularIncidenceSubgroup
    (R : Type*) [CommRing R] (N : ℕ) :
    Subgroup (IncidenceAlgebra R (Fin N))ˣ where
  carrier := {u | ∀ i, (u.1 : IncidenceAlgebra R (Fin N)) i i = 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv i
    change ((u.1 * v.1 : IncidenceAlgebra R (Fin N)) i i) = 1
    simp [IncidenceAlgebra.mul_apply, hu i, hv i]
  inv_mem' := by
    intro u hu i
    have h :=
      congrArg
        (fun a : IncidenceAlgebra R (Fin N) => a i i)
        u.val_inv
    change
      (∑ k ∈ Finset.Icc i i,
          (u.1 : IncidenceAlgebra R (Fin N)) i k *
            ((u⁻¹).1 : IncidenceAlgebra R (Fin N)) k i) =
        (1 : IncidenceAlgebra R (Fin N)) i i at h
    simp only [Finset.Icc_self, Finset.sum_singleton, hu i,
      IncidenceAlgebra.one_apply, if_pos] at h
    calc
      ((u⁻¹).1 : IncidenceAlgebra R (Fin N)) i i =
          1 * ((u⁻¹).1 : IncidenceAlgebra R (Fin N)) i i := by
            rw [_root_.one_mul]
      _ = 1 := h

/-- An off-diagonal entry of a product of upper-unitriangular matrices is
the sum of the two corresponding entries and the products through strictly
intermediate indices. -/
theorem unitriangular_mul
    {N : ℕ}
    (u v : unitriangularIncidenceSubgroup R N)
    (i j : Fin N) (hij : i < j) :
    ((((u * v).1.1 : IncidenceAlgebra R (Fin N)) i j)) =
      ((u.1.1 : IncidenceAlgebra R (Fin N)) i j) +
        ((v.1.1 : IncidenceAlgebra R (Fin N)) i j) +
          ∑ k ∈ Finset.Ioo i j,
            ((u.1.1 : IncidenceAlgebra R (Fin N)) i k) *
              ((v.1.1 : IncidenceAlgebra R (Fin N)) k j) := by
  change
    (∑ k ∈ Finset.Icc i j,
        ((u.1.1 : IncidenceAlgebra R (Fin N)) i k) *
          ((v.1.1 : IncidenceAlgebra R (Fin N)) k j)) = _
  have hinterval :
      Finset.Icc i j =
        insert i (insert j (Finset.Ioo i j)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hinterval]
  rw [Finset.sum_insert (by simp [hij.ne]),
    Finset.sum_insert (by simp)]
  simp only [u.2 i, v.2 j]
  ac_rfl

/-- Restriction of an incidence-algebra element to its leading principal
submatrix. -/
def leadingPrincipalIncidence
    (n : ℕ) (f : IncidenceAlgebra R (Fin (n + 1))) :
    IncidenceAlgebra R (Fin n) where
  toFun i j := f i.castSucc j.castSucc
  eq_zero_of_not_le' i j hij := by
    apply IncidenceAlgebra.apply_eq_zero_of_not_le
    simpa using hij

@[simp]
theorem leading_principal_incidence
    (n : ℕ) (f : IncidenceAlgebra R (Fin (n + 1)))
    (i j : Fin n) :
    leadingPrincipalIncidence n f i j =
      f i.castSucc j.castSucc :=
  rfl

/-- Restriction to the leading principal submatrix is a ring homomorphism. -/
def leadingIncidenceHom
    (n : ℕ) :
    IncidenceAlgebra R (Fin (n + 1)) →+*
      IncidenceAlgebra R (Fin n) where
  toFun := leadingPrincipalIncidence n
  map_zero' := by
    apply IncidenceAlgebra.ext
    intro i j hij
    rfl
  map_one' := by
    apply IncidenceAlgebra.ext
    intro i j hij
    simp [IncidenceAlgebra.one_apply]
  map_add' f g := by
    apply IncidenceAlgebra.ext
    intro i j hij
    rfl
  map_mul' f g := by
    apply IncidenceAlgebra.ext
    intro i j hij
    change
      (∑ k ∈ Finset.Icc i.castSucc j.castSucc,
          f i.castSucc k * g k j.castSucc) =
        ∑ k ∈ Finset.Icc i j,
          f i.castSucc k.castSucc *
            g k.castSucc j.castSucc
    rw [Fin.sum_Icc_castSucc]

/-- Restriction of an incidence-algebra element to its trailing principal
submatrix. -/
def trailingPrincipalIncidence
    (n : ℕ) (f : IncidenceAlgebra R (Fin (n + 1))) :
    IncidenceAlgebra R (Fin n) where
  toFun i j := f i.succ j.succ
  eq_zero_of_not_le' i j hij := by
    apply IncidenceAlgebra.apply_eq_zero_of_not_le
    simpa using hij

@[simp]
theorem trailing_principal_incidence
    (n : ℕ) (f : IncidenceAlgebra R (Fin (n + 1)))
    (i j : Fin n) :
    trailingPrincipalIncidence n f i j =
      f i.succ j.succ :=
  rfl

/-- Restriction to the trailing principal submatrix is a ring homomorphism. -/
def trailingIncidenceHom
    (n : ℕ) :
    IncidenceAlgebra R (Fin (n + 1)) →+*
      IncidenceAlgebra R (Fin n) where
  toFun := trailingPrincipalIncidence n
  map_zero' := by
    apply IncidenceAlgebra.ext
    intro i j hij
    rfl
  map_one' := by
    apply IncidenceAlgebra.ext
    intro i j hij
    simp [IncidenceAlgebra.one_apply]
  map_add' f g := by
    apply IncidenceAlgebra.ext
    intro i j hij
    rfl
  map_mul' f g := by
    apply IncidenceAlgebra.ext
    intro i j hij
    change
      (∑ k ∈ Finset.Icc i.succ j.succ,
          f i.succ k * g k j.succ) =
        ∑ k ∈ Finset.Icc i j,
          f i.succ k.succ * g k.succ j.succ
    rw [Fin.sum_Icc_succ]

/-- Leading-principal restriction on upper-unitriangular incidence units. -/
def leadingPrincipalUnitriangular
    (n : ℕ) :
    unitriangularIncidenceSubgroup R (n + 1) →*
      unitriangularIncidenceSubgroup R n where
  toFun u :=
    ⟨Units.map (leadingIncidenceHom (R := R) n) u.1,
      fun i => by
        change
          ((u.1.1 : IncidenceAlgebra R (Fin (n + 1)))
            i.castSucc i.castSucc) = 1
        exact u.2 i.castSucc⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp

/-- Trailing-principal restriction on upper-unitriangular incidence units. -/
def trailingPrincipalUnitriangular
    (n : ℕ) :
    unitriangularIncidenceSubgroup R (n + 1) →*
      unitriangularIncidenceSubgroup R n where
  toFun u :=
    ⟨Units.map (trailingIncidenceHom (R := R) n) u.1,
      fun i => by
        change
          ((u.1.1 : IncidenceAlgebra R (Fin (n + 1)))
            i.succ i.succ) = 1
        exact u.2 i.succ⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp

/-- Forgetting the top-right entry amounts to retaining the leading and
trailing principal submatrices. -/
def principalUnitriangularRestriction
    (n : ℕ) :
    unitriangularIncidenceSubgroup R (n + 1) →*
      unitriangularIncidenceSubgroup R n ×
        unitriangularIncidenceSubgroup R n :=
  (leadingPrincipalUnitriangular (R := R) n).prod
    (trailingPrincipalUnitriangular (R := R) n)

/-- The top-right subgroup `Z_(n+1)(R)`, defined as the kernel of forgetting
the top-right entry.  As a kernel, it is automa normal. -/
def topUnitriangularSubgroup
    (n : ℕ) :
    Subgroup (unitriangularIncidenceSubgroup R (n + 1)) :=
  MonoidHom.ker (principalUnitriangularRestriction (R := R) n)

instance top_unitriangular_normal
    (n : ℕ) :
    (topUnitriangularSubgroup (R := R) n).Normal := by
  dsimp [topUnitriangularSubgroup]
  infer_instance

/-- The barred unitriangular group `U_(n+1)(R) / Z_(n+1)(R)`. -/
abbrev barredUnitriangularIncidence
    (R : Type*) [CommRing R] (n : ℕ) :=
  unitriangularIncidenceSubgroup R (n + 1) ⧸
    topUnitriangularSubgroup (R := R) n

/-- The constant coefficient of every Magnus expansion is one. -/
theorem magnus_series_one (g : FreeGroup X) :
    magnusSeries (R := R) g 1 = 1 := by
  have h :=
    magnus_difference_ideal
      (R := R) (X := X) g
  change (magnusSeries (R := R) g - 1) 1 = 0 at h
  exact sub_eq_zero.mp h

/-- The unit-valued incidence representation attached to a word. -/
def wordIncidenceHom
    (xs : List X) :
    (MSeries R X)ˣ →*
      (IncidenceAlgebra R (Fin (xs.length + 1)))ˣ :=
  Units.map (incidenceRingHom (R := R) xs)

/-- Efrat--Chapman, Lemma 5.1: the representation attached to a word,
bundled with codomain the upper-unitriangular incidence group. -/
def wordCoefficientRepresentation
    (xs : List X) :
    FreeGroup X →*
      unitriangularIncidenceSubgroup R (xs.length + 1) :=
  (wordIncidenceHom (R := R) xs).comp
      (magnusUnitHom (R := R) (X := X)) |>.codRestrict
    (unitriangularIncidenceSubgroup R (xs.length + 1))
    (fun g i => by
      change wordIncidence xs (magnusSeries (R := R) g) i i = 1
      rw [word_incidence xs _ i i le_rfl]
      simpa [wordSegment] using
        magnus_series_one (R := R) (X := X) g)

/-- Every entry of the word representation is the Magnus coefficient of the
corresponding contiguous subword. -/
theorem word_coefficient_representation
    (xs : List X) (g : FreeGroup X)
    (i j : Fin (xs.length + 1)) (hij : i ≤ j) :
    (((wordCoefficientRepresentation (R := R) xs g).1.1 :
        IncidenceAlgebra R (Fin (xs.length + 1))) i j) =
      magnusSeries (R := R) g (wordSegment xs i j) := by
  exact word_incidence xs _ i j hij

/-- The canonical word representation into the actual quotient
`U_(|xs|+1)(R) / Z_(|xs|+1)(R)`. -/
def barredCoefficientRepresentation
    (xs : List X) :
    FreeGroup X →*
      barredUnitriangularIncidence R xs.length :=
  (QuotientGroup.mk'
      (topUnitriangularSubgroup (R := R) xs.length)).comp
    (wordCoefficientRepresentation (R := R) xs)

/-- Kernel membership for the barred word representation is equivalent to
the leading and trailing principal restrictions being trivial. -/
theorem ker_barred_representation
    (xs : List X) (g : FreeGroup X) :
    g ∈ MonoidHom.ker
        (barredCoefficientRepresentation (R := R) xs) ↔
      principalUnitriangularRestriction (R := R) xs.length
          (wordCoefficientRepresentation (R := R) xs g) =
        1 := by
  rw [MonoidHom.mem_ker]
  change
    QuotientGroup.mk'
        (topUnitriangularSubgroup (R := R) xs.length)
        (wordCoefficientRepresentation (R := R) xs g) =
      1 ↔ _
  constructor
  · intro h
    exact MonoidHom.mem_ker.mp
      ((QuotientGroup.eq_one_iff _).mp h)
  · intro h
    exact (QuotientGroup.eq_one_iff _).mpr
      (MonoidHom.mem_ker.mpr h)

/-- The intersection of the kernels of the canonical word representations
whose words have length `n - 1`. -/
def wordCoefficientIntersection
    (n : ℕ) : Subgroup (FreeGroup X) :=
  ⨅ xs : {xs : List X // xs.length = n - 1},
    MonoidHom.ker (wordCoefficientRepresentation (R := R) xs.1)

/-- The canonical word representations detect exactly the coefficients below
degree `n`.  This is the second equality in Efrat--Chapman, Proposition 5.2. -/
theorem magnus_coefficient_intersection
    (n : ℕ) (hn : 1 ≤ n) :
    magnusOrderSubgroup (R := R) (X := X) n =
      wordCoefficientIntersection (R := R) (X := X) n := by
  apply le_antisymm
  · intro g hg
    change
      g ∈ ⨅ xs : {xs : List X // xs.length = n - 1},
        MonoidHom.ker (wordCoefficientRepresentation (R := R) xs.1)
    rw [Subgroup.mem_iInf]
    intro xs
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply Units.ext
    apply IncidenceAlgebra.ext
    intro i j hij
    rw [word_coefficient_representation xs.1 g i j hij]
    have hlen :
        (wordSegment xs.1 i j).length < n := by
      rw [wordSegment_length xs.1 i j hij]
      have hi : i.1 ≤ xs.1.length := by omega
      have hj : j.1 ≤ xs.1.length := by omega
      have hxs := xs.2
      omega
    have hcoeff :
        magnusSeries (R := R) g (wordSegment xs.1 i j) =
          (1 : MSeries R X) (wordSegment xs.1 i j) := by
      have hdifference := hg (wordSegment xs.1 i j) hlen
      exact sub_eq_zero.mp hdifference
    have hone :=
      congrArg
        (fun a : IncidenceAlgebra R (Fin (xs.1.length + 1)) =>
          a i j)
        (incidenceRingHom (R := R) xs.1).map_one
    change
      wordIncidence xs.1 (1 : MSeries R X) i j =
        (1 : IncidenceAlgebra R (Fin (xs.1.length + 1))) i j at hone
    rw [word_incidence xs.1 1 i j hij] at hone
    exact hcoeff.trans hone
  · intro g hg
    change VanishesBelow (magnusDifference (R := R) g) n
    intro u hu
    classical
    by_cases hX : Nonempty X
    · let x : X := Classical.choice hX
      let xs : List X :=
        u.toList ++ List.replicate (n - 1 - u.length) x
      have hxs : xs.length = n - 1 := by
        dsimp [xs]
        rw [List.length_append, List.length_replicate]
        change
          u.length + (n - 1 - u.length) =
            n - 1
        omega
      let indexedWord : {ys : List X // ys.length = n - 1} :=
        ⟨xs, hxs⟩
      have hker :=
        (Subgroup.mem_iInf.mp hg) indexedWord
      rw [MonoidHom.mem_ker] at hker
      let i : Fin (xs.length + 1) := ⟨0, by omega⟩
      let j : Fin (xs.length + 1) := ⟨u.length, by
        rw [hxs]
        omega⟩
      have hij : i ≤ j := by
        change 0 ≤ u.length
        omega
      have hsegment : wordSegment xs i j = u := by
        apply FreeMonoid.toList.injective
        simp only [wordSegment, FreeMonoid.toList_ofList, i, j,
          List.drop_zero, xs]
        rw [List.take_append_of_le_length]
        · simp [FreeMonoid.length]
        · rfl
      have hentry :=
        congrArg
          (fun a :
              unitriangularIncidenceSubgroup R (xs.length + 1) =>
            ((a.1.1 : IncidenceAlgebra R (Fin (xs.length + 1))) i j))
          hker
      change
        magnusSeries (R := R) g (wordSegment xs i j) =
          (1 : IncidenceAlgebra R (Fin (xs.length + 1))) i j at hentry
      rw [hsegment] at hentry
      have hone :=
        congrArg
          (fun a : IncidenceAlgebra R (Fin (xs.length + 1)) =>
            a i j)
          (incidenceRingHom (R := R) xs).map_one
      change
        wordIncidence xs (1 : MSeries R X) i j =
          (1 : IncidenceAlgebra R (Fin (xs.length + 1))) i j at hone
      rw [word_incidence xs 1 i j hij, hsegment] at hone
      exact sub_eq_zero.mpr (hentry.trans hone.symm)
    · letI : IsEmpty X := ⟨fun x => hX ⟨x⟩⟩
      have hg1 : g = 1 := Subsingleton.elim _ _
      subst g
      simp [magnusDifference]

/-- The canonical model of the representation into
`U_(|xs|+1)(R) / Z_(|xs|+1)(R)`: retain the leading and trailing principal
submatrices, thereby forgetting only the top-right entry. -/
def barCoefficientRepresentation
    (xs : List X) :
    FreeGroup X →*
      unitriangularIncidenceSubgroup R (xs.dropLast.length + 1) ×
        unitriangularIncidenceSubgroup R (xs.tail.length + 1) :=
  (wordCoefficientRepresentation (R := R) xs.dropLast).prod
    (wordCoefficientRepresentation (R := R) xs.tail)

/-- The intersection of the kernels of the canonical representations into
the upper-unitriangular group modulo its top-right central subgroup. -/
def barCoefficientIntersection
    (n : ℕ) : Subgroup (FreeGroup X) :=
  ⨅ xs : {xs : List X // xs.length = n},
    MonoidHom.ker (barCoefficientRepresentation (R := R) xs.1)

/-- The intersection of the kernels of the actual quotient-valued barred
word representations of length `n`. -/
def barredCoefficientIntersection
    (n : ℕ) : Subgroup (FreeGroup X) :=
  ⨅ xs : {xs : List X // xs.length = n},
    MonoidHom.ker
      (barredCoefficientRepresentation (R := R) xs.1)

/-- The kernel of a canonical barred word representation is the intersection
of the kernels attached to its length-one prefix and suffix. -/
theorem ker_bar_representation
    (xs : List X) (g : FreeGroup X) :
    g ∈ MonoidHom.ker (barCoefficientRepresentation (R := R) xs) ↔
      g ∈ MonoidHom.ker
          (wordCoefficientRepresentation (R := R) xs.dropLast) ∧
        g ∈ MonoidHom.ker
          (wordCoefficientRepresentation (R := R) xs.tail) := by
  simp [barCoefficientRepresentation, MonoidHom.mem_ker]

/-- Efrat--Chapman, Proposition 5.4: Magnus order `n` is the intersection of
the kernels of the canonical length-`n` representations after quotienting
the upper-unitriangular target by its top-right central subgroup. -/
theorem magnus_bar_intersection
    (n : ℕ) (hn : 1 ≤ n) :
    magnusOrderSubgroup (R := R) (X := X) n =
      barCoefficientIntersection (R := R) (X := X) n := by
  rw [magnus_coefficient_intersection
    (R := R) (X := X) n hn]
  apply le_antisymm
  · intro g hg
    change
      g ∈ ⨅ xs : {xs : List X // xs.length = n},
        MonoidHom.ker
          (barCoefficientRepresentation (R := R) xs.1)
    rw [Subgroup.mem_iInf]
    intro xs
    rw [ker_bar_representation]
    constructor
    · have hlength : xs.1.dropLast.length = n - 1 := by
        rw [List.length_dropLast, xs.2]
      exact
        (Subgroup.mem_iInf.mp hg)
          ⟨xs.1.dropLast, hlength⟩
    · have hlength : xs.1.tail.length = n - 1 := by
        rw [List.length_tail, xs.2]
      exact
        (Subgroup.mem_iInf.mp hg)
          ⟨xs.1.tail, hlength⟩
  · intro g hg
    change
      g ∈ ⨅ ys : {ys : List X // ys.length = n - 1},
        MonoidHom.ker
          (wordCoefficientRepresentation (R := R) ys.1)
    rw [Subgroup.mem_iInf]
    intro ys
    classical
    by_cases hX : Nonempty X
    · let x : X := Classical.choice hX
      let xs : List X := ys.1.concat x
      have hxs : xs.length = n := by
        dsimp [xs]
        rw [List.length_concat, ys.2]
        omega
      have hbar :=
        (Subgroup.mem_iInf.mp hg)
          (⟨xs, hxs⟩ :
            {zs : List X // zs.length = n})
      rw [ker_bar_representation] at hbar
      have hdrop : xs.dropLast = ys.1 := by
        dsimp [xs]
        rw [List.concat_eq_append, List.dropLast_concat]
      rw [hdrop] at hbar
      exact hbar.1
    · letI : IsEmpty X := ⟨fun x => hX ⟨x⟩⟩
      have hg1 : g = 1 := Subsingleton.elim _ _
      subst g
      exact Subgroup.one_mem _

/-- Efrat--Chapman, Proposition 5.4 in its literal quotient-group form:
Magnus order `n` is the intersection of the kernels of all canonical
length-`n` representations into `U_(n+1)(R) / Z_(n+1)(R)`. -/
theorem magnus_barred_intersection
    (n : ℕ) (hn : 1 ≤ n) :
    magnusOrderSubgroup (R := R) (X := X) n =
      barredCoefficientIntersection
        (R := R) (X := X) n := by
  apply le_antisymm
  · intro g hg
    change
      g ∈ ⨅ xs : {xs : List X // xs.length = n},
        MonoidHom.ker
          (barredCoefficientRepresentation (R := R) xs.1)
    rw [Subgroup.mem_iInf]
    intro xs
    rw [ker_barred_representation]
    apply Prod.ext
    · apply Subtype.ext
      apply Units.ext
      apply IncidenceAlgebra.ext
      intro i j hij
      change
        (((wordCoefficientRepresentation (R := R) xs.1 g).1.1 :
            IncidenceAlgebra R (Fin (xs.1.length + 1)))
          i.castSucc j.castSucc) =
          (1 : IncidenceAlgebra R (Fin xs.1.length)) i j
      have hsource :
          i.castSucc ≤ (j.castSucc : Fin (xs.1.length + 1)) := by
        simpa using hij
      rw [word_coefficient_representation
        xs.1 g i.castSucc j.castSucc hsource]
      have hlength :
          (wordSegment xs.1 i.castSucc j.castSucc).length < n := by
        rw [wordSegment_length xs.1 i.castSucc j.castSucc hsource]
        change j.1 - i.1 < n
        omega
      have hcoeff :=
        sub_eq_zero.mp (hg _ hlength)
      have hone :=
        congrArg
          (fun a :
              IncidenceAlgebra R (Fin (xs.1.length + 1)) =>
            a i.castSucc j.castSucc)
          (incidenceRingHom (R := R) xs.1).map_one
      change
        wordIncidence xs.1 (1 : MSeries R X)
            i.castSucc j.castSucc =
          (1 : IncidenceAlgebra R (Fin (xs.1.length + 1)))
            i.castSucc j.castSucc at hone
      rw [word_incidence
        xs.1 1 i.castSucc j.castSucc hsource] at hone
      have hone' :
          (1 : IncidenceAlgebra R (Fin (xs.1.length + 1)))
              i.castSucc j.castSucc =
            (1 : IncidenceAlgebra R (Fin xs.1.length)) i j := by
        simp [IncidenceAlgebra.one_apply]
      exact hcoeff.trans (hone.trans hone')
    · apply Subtype.ext
      apply Units.ext
      apply IncidenceAlgebra.ext
      intro i j hij
      change
        (((wordCoefficientRepresentation (R := R) xs.1 g).1.1 :
            IncidenceAlgebra R (Fin (xs.1.length + 1)))
          i.succ j.succ) =
          (1 : IncidenceAlgebra R (Fin xs.1.length)) i j
      have hsource :
          i.succ ≤ (j.succ : Fin (xs.1.length + 1)) := by
        simpa using hij
      rw [word_coefficient_representation
        xs.1 g i.succ j.succ hsource]
      have hlength :
          (wordSegment xs.1 i.succ j.succ).length < n := by
        rw [wordSegment_length xs.1 i.succ j.succ hsource]
        change j.1 + 1 - (i.1 + 1) < n
        omega
      have hcoeff :=
        sub_eq_zero.mp (hg _ hlength)
      have hone :=
        congrArg
          (fun a :
              IncidenceAlgebra R (Fin (xs.1.length + 1)) =>
            a i.succ j.succ)
          (incidenceRingHom (R := R) xs.1).map_one
      change
        wordIncidence xs.1 (1 : MSeries R X)
            i.succ j.succ =
          (1 : IncidenceAlgebra R (Fin (xs.1.length + 1)))
            i.succ j.succ at hone
      rw [word_incidence
        xs.1 1 i.succ j.succ hsource] at hone
      have hone' :
          (1 : IncidenceAlgebra R (Fin (xs.1.length + 1)))
              i.succ j.succ =
            (1 : IncidenceAlgebra R (Fin xs.1.length)) i j := by
        simp [IncidenceAlgebra.one_apply]
      exact hcoeff.trans (hone.trans hone')
  · intro g hg
    change VanishesBelow (magnusDifference (R := R) g) n
    intro u hu
    classical
    by_cases hX : Nonempty X
    · let x : X := Classical.choice hX
      let xs : List X :=
        u.toList ++ List.replicate (n - u.length) x
      have hxs : xs.length = n := by
        dsimp [xs]
        rw [List.length_append, List.length_replicate]
        change u.length + (n - u.length) = n
        omega
      have hbar :=
        (Subgroup.mem_iInf.mp hg)
          (⟨xs, hxs⟩ :
            {zs : List X // zs.length = n})
      rw [ker_barred_representation] at hbar
      let i : Fin xs.length := ⟨0, by
        rw [hxs]
        omega⟩
      let j : Fin xs.length := ⟨u.length, by
        rw [hxs]
        exact hu⟩
      have hij : i ≤ j := by
        change 0 ≤ u.length
        omega
      have hentry :=
        congrArg
          (fun a :
              unitriangularIncidenceSubgroup R xs.length ×
                unitriangularIncidenceSubgroup R xs.length =>
            ((a.1.1.1 :
                IncidenceAlgebra R (Fin xs.length)) i j))
          hbar
      change
        (((wordCoefficientRepresentation (R := R) xs g).1.1 :
            IncidenceAlgebra R (Fin (xs.length + 1)))
          i.castSucc j.castSucc) =
          (1 : IncidenceAlgebra R (Fin xs.length)) i j at hentry
      have hsource :
          i.castSucc ≤ (j.castSucc : Fin (xs.length + 1)) := by
        simpa using hij
      rw [word_coefficient_representation
        xs g i.castSucc j.castSucc hsource] at hentry
      have hsegment :
          wordSegment xs i.castSucc j.castSucc = u := by
        apply FreeMonoid.toList.injective
        simp only [wordSegment, FreeMonoid.toList_ofList, i, j,
          Fin.val_castSucc, List.drop_zero, xs]
        rw [List.take_append_of_le_length]
        · simp [FreeMonoid.length]
        · rfl
      rw [hsegment] at hentry
      have hone :=
        congrArg
          (fun a : IncidenceAlgebra R (Fin (xs.length + 1)) =>
            a i.castSucc j.castSucc)
          (incidenceRingHom (R := R) xs).map_one
      change
        wordIncidence xs (1 : MSeries R X)
            i.castSucc j.castSucc =
          (1 : IncidenceAlgebra R (Fin (xs.length + 1)))
            i.castSucc j.castSucc at hone
      rw [word_incidence
        xs 1 i.castSucc j.castSucc hsource] at hone
      rw [hsegment] at hone
      have hone' :
          (1 : IncidenceAlgebra R (Fin (xs.length + 1)))
              i.castSucc j.castSucc =
            (1 : IncidenceAlgebra R (Fin xs.length)) i j := by
        simp [IncidenceAlgebra.one_apply]
      exact
        sub_eq_zero.mpr
          (hentry.trans (hone.trans hone').symm)
    · letI : IsEmpty X := ⟨fun x => hX ⟨x⟩⟩
      have hg1 : g = 1 := Subsingleton.elim _ _
      subst g
      simp [magnusDifference]

/-- On the degree-`n` Magnus subgroup, a coefficient of length `n` is
additive under multiplication.  This is Efrat--Chapman, Corollary 5.5. -/
def restrictedCoefficientHom
    (xs : List X) (hxs : 0 < xs.length) :
    magnusOrderSubgroup (R := R) (X := X) xs.length →*
      Multiplicative R where
  toFun g :=
    Multiplicative.ofAdd
      (magnusSeries (R := R) g.1 (FreeMonoid.ofList xs))
  map_one' := by
    apply Multiplicative.toAdd.injective
    change
      magnusSeries (R := R) (1 : FreeGroup X)
          (FreeMonoid.ofList xs) =
        0
    rw [magnusSeries_one, one_apply]
    simp [FreeMonoid.length, hxs.ne']
  map_mul' := by
    intro g h
    apply Multiplicative.toAdd.injective
    change
      magnusSeries (R := R) (g.1 * h.1)
          (FreeMonoid.ofList xs) =
        magnusSeries (R := R) g.1 (FreeMonoid.ofList xs) +
          magnusSeries (R := R) h.1 (FreeMonoid.ofList xs)
    rw [magnusSeries_mul]
    change
      convolutionList
          (magnusSeries (R := R) g.1)
          (magnusSeries (R := R) h.1) xs = _
    rw [convolution_sum_range]
    let term : ℕ → R := fun k =>
      magnusSeries (R := R) g.1
          (FreeMonoid.ofList (xs.take k)) *
        magnusSeries (R := R) h.1
          (FreeMonoid.ofList (xs.drop k))
    have hpair :
        ({0, xs.length} : Finset ℕ) ⊆
          Finset.range (xs.length + 1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp
    have hsum :
        ∑ k ∈ ({0, xs.length} : Finset ℕ), term k =
          ∑ k ∈ Finset.range (xs.length + 1), term k := by
      apply Finset.sum_subset hpair
      intro k hk hnot
      have hklt : k < xs.length + 1 :=
        Finset.mem_range.mp hk
      have hk0 : k ≠ 0 := by
        intro hkzero
        subst k
        exact hnot (by simp)
      have hklen : k ≠ xs.length := by
        intro hkeq
        subst k
        exact hnot (by simp)
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hkle : k ≤ xs.length := by omega
      have hkstrict : k < xs.length := by omega
      have hprefixLength :
          (FreeMonoid.ofList (xs.take k)).length = k := by
        change (xs.take k).length = k
        simp [List.length_take, hkle]
      have hgdifference :=
        g.2 (FreeMonoid.ofList (xs.take k)) (by
          rw [hprefixLength]
          exact hkstrict)
      have hgcoeff :
          magnusSeries (R := R) g.1
              (FreeMonoid.ofList (xs.take k)) =
            (1 : MSeries R X)
              (FreeMonoid.ofList (xs.take k)) :=
        sub_eq_zero.mp hgdifference
      dsimp only [term]
      rw [hgcoeff, one_apply, hprefixLength]
      simp [hk0]
    rw [← hsum]
    simp only [term]
    rw [Finset.sum_pair (by omega : (0 : ℕ) ≠ xs.length)]
    simp [magnus_series_one, add_comm]

end MSeries
end EChapma
