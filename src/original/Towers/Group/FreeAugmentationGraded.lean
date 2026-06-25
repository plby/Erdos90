import Towers.Group.PresentedFox


open scoped BigOperators

noncomputable section

namespace Towers
namespace TBluepr

/--
The augmentation monomial attached to a word in the free generators.

The list is stored from the right boundary inward: the head contributes the
rightmost factor.  This convention makes iterated Fox differentiation recurse
directly on lists.
-/
def freeAugmentationWord
    (R ι : Type*) [CommRing R] :
    List ι → MonoidAlgebra R (FreeGroup ι)
  | [] => 1
  | i :: w =>
      freeAugmentationWord R ι w *
        augmentationDifference R (FreeGroup ι) (FreeGroup.of i)

@[simp]
theorem free_augmentation_nil
    (R ι : Type*) [CommRing R] :
    freeAugmentationWord R ι [] = 1 :=
  rfl

@[simp]
theorem free_augmentation_cons
    (R ι : Type*) [CommRing R]
    (i : ι) (w : List ι) :
    freeAugmentationWord R ι (i :: w) =
      freeAugmentationWord R ι w *
        augmentationDifference R (FreeGroup ι) (FreeGroup.of i) :=
  rfl

/-- An augmentation word of length `n` belongs to the `n`th augmentation power. -/
theorem free_ideal_pow
    (R ι : Type*) [CommRing R]
    (w : List ι) :
    freeAugmentationWord R ι w ∈
      (GShafar.augmentationIdeal R (FreeGroup ι)) ^ w.length := by
  let I : Ideal (MonoidAlgebra R (FreeGroup ι)) :=
    GShafar.augmentationIdeal R (FreeGroup ι)
  letI : I.IsTwoSided := by
    dsimp [I, GShafar.augmentationIdeal]
    infer_instance
  induction w with
  | nil =>
      simp [freeAugmentationWord, Submodule.pow_zero, Ideal.one_eq_top]
  | cons i w ih =>
      have hdiff :
          augmentationDifference R (FreeGroup ι) (FreeGroup.of i) ∈ I ^ 1 := by
        simpa [Submodule.pow_one, I] using
          augmentation_difference_ideal
            R (FreeGroup ι) (FreeGroup.of i)
      have hmul :
          freeAugmentationWord R ι w *
              augmentationDifference R (FreeGroup ι) (FreeGroup.of i) ∈
            I ^ w.length * I ^ 1 :=
        Ideal.mul_mem_mul (by simpa [I] using ih) hdiff
      rw [← Ideal.IsTwoSided.pow_add (I := I) (m := w.length) (n := 1)] at hmul
      simpa [freeAugmentationWord, I] using hmul

/--
One Fox derivative removes the rightmost augmentation letter and vanishes on
the words with a different rightmost letter.
-/
@[simp]
theorem fox_derivative_cons
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]
    (j i : ι) (w : List ι) :
    freeFoxDerivative R ι j
        (freeAugmentationWord R ι (i :: w)) =
      if i = j then freeAugmentationWord R ι w else 0 := by
  rw [free_augmentation_cons, algebra_fox_derivative]
  simp [augmentationDifference, GShafar.augmentationHom,
    GShafar.augmentationCharacter]

/-- Apply the Fox derivatives listed from the right boundary inward. -/
noncomputable def iteratedFoxDerivative
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :
    List ι → MonoidAlgebra R (FreeGroup ι) →ₗ[R]
      MonoidAlgebra R (FreeGroup ι)
  | [] => LinearMap.id
  | i :: w =>
      (iteratedFoxDerivative R ι w).comp
        (freeFoxDerivative R ι i)

@[simp]
theorem iterated_derivative_nil
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]
    (x : MonoidAlgebra R (FreeGroup ι)) :
    iteratedFoxDerivative R ι [] x = x :=
  rfl

@[simp]
theorem iterated_derivative_cons
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]
    (i : ι) (w : List ι)
    (x : MonoidAlgebra R (FreeGroup ι)) :
    iteratedFoxDerivative R ι (i :: w) x =
      iteratedFoxDerivative R ι w
        (freeFoxDerivative R ι i x) :=
  rfl

/--
Iterated Fox differentiation reads back an augmentation word of the same
length exactly.
-/
@[simp]
theorem iterated_fox_derivative
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :
    ∀ (v w : List ι),
      v.length = w.length →
      iteratedFoxDerivative R ι v
          (freeAugmentationWord R ι w) =
        if v = w then 1 else 0
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | i :: v, j :: w, h => by
      simp only [List.length_cons, Nat.succ.injEq] at h
      rw [iterated_derivative_cons,
        fox_derivative_cons]
      by_cases hij : j = i
      · subst j
        simp [h, iterated_fox_derivative
          R ι v w]
      · have hij' : i ≠ j := Ne.symm hij
        simp [hij, hij']

/-- Fixed-length packaging of the free augmentation monomials. -/
def freeVectorWord
    (R ι : Type*) [CommRing R]
    {n : ℕ}
    (w : List.Vector ι n) :
    MonoidAlgebra R (FreeGroup ι) :=
  freeAugmentationWord R ι w.toList

@[simp]
theorem free_vector_nil
    (R ι : Type*) [CommRing R] :
    freeVectorWord R ι (List.Vector.nil : List.Vector ι 0) = 1 :=
  rfl

@[simp]
theorem free_vector_cons
    (R ι : Type*) [CommRing R]
    {n : ℕ}
    (i : ι) (w : List.Vector ι n) :
    freeVectorWord R ι (List.Vector.cons i w) =
      freeVectorWord R ι w *
        augmentationDifference R (FreeGroup ι) (FreeGroup.of i) := by
  simp [freeVectorWord, List.Vector.toList_cons]

/-- Fixed-length augmentation monomials of a free group are linearly independent. -/
theorem vector_linear_independent
    (R ι : Type*) [CommRing R] [Finite ι]
    (n : ℕ) :
    LinearIndependent R
      (freeVectorWord R ι :
        List.Vector ι n → MonoidAlgebra R (FreeGroup ι)) := by
  letI := Fintype.ofFinite ι
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro coeff hcoeff w
  have hread :=
    congrArg
      (fun x =>
        iteratedFoxDerivative R ι w.toList x)
      hcoeff
  simp only [map_sum, map_smul] at hread
  have hsum :
      (∑ x,
          if w.toList = x.toList then
            coeff x • (1 : MonoidAlgebra R (FreeGroup ι))
          else 0) = 0 := by
    simpa [freeVectorWord] using hread
  rw [Finset.sum_eq_single w] at hsum
  · have hone :=
      congrArg
        (fun z : MonoidAlgebra R (FreeGroup ι) => z 1)
        hsum
    simpa [MonoidAlgebra.one_def] using hone
  · intro x _hx hxw
    have hlist : w.toList ≠ x.toList := by
      intro h
      exact hxw (List.Vector.toList_injective h.symm)
    simp [hlist]
  · intro hw
    exact (hw (Finset.mem_univ w)).elim

/--
An iterated Fox derivative lowers augmentation degree by the length of its
derivative word.
-/
theorem iterated_derivative_length
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :
    ∀ (v : List ι) {n : ℕ} {x : MonoidAlgebra R (FreeGroup ι)},
      x ∈ (GShafar.augmentationIdeal R (FreeGroup ι)) ^ n →
      iteratedFoxDerivative R ι v x ∈
        (GShafar.augmentationIdeal R (FreeGroup ι)) ^ (n - v.length)
  | [], _, _, hx => by simpa using hx
  | i :: v, _, _, hx => by
      rw [iterated_derivative_cons]
      have hderivative :=
        fox_derivative_pred
          R ι i hx
      have hiterated :=
        iterated_derivative_length
          R ι v hderivative
      simpa [Nat.sub_sub, Nat.add_comm] using hiterated

/-- Scalar coordinate obtained by augmenting an iterated Fox derivative. -/
noncomputable def freeAugmentationCoefficient
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]
    (v : List ι) :
    MonoidAlgebra R (FreeGroup ι) →ₗ[R] R :=
  (GShafar.augmentationHom R (FreeGroup ι)).toLinearMap.comp
    (iteratedFoxDerivative R ι v)

/-- The scalar Fox coordinate reads back a same-length augmentation word. -/
@[simp]
theorem free_coefficient_word
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]
    (v w : List ι)
    (h : v.length = w.length) :
    freeAugmentationCoefficient R ι v
        (freeAugmentationWord R ι w) =
      if v = w then 1 else 0 := by
  simp [freeAugmentationCoefficient,
    iterated_fox_derivative R ι v w h]

/--
The length-`n` scalar Fox coordinate vanishes on the `(n+1)`st augmentation
power.  This is the denominator-killing statement needed to descend the
coordinate to the degree-`n` augmentation layer.
-/
theorem free_coefficient_succ
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]
    {n : ℕ}
    (v : List.Vector ι n)
    {x : MonoidAlgebra R (FreeGroup ι)}
    (hx :
      x ∈ (GShafar.augmentationIdeal R (FreeGroup ι)) ^ (n + 1)) :
    freeAugmentationCoefficient R ι v.toList x = 0 := by
  have hiterated :=
    iterated_derivative_length
      R ι v.toList hx
  have hmem :
      iteratedFoxDerivative R ι v.toList x ∈
        GShafar.augmentationIdeal R (FreeGroup ι) := by
    simpa [List.Vector.toList_length, Submodule.pow_one] using hiterated
  change
    GShafar.augmentationHom R (FreeGroup ι)
      (iteratedFoxDerivative R ι v.toList x) = 0
  simpa [GShafar.augmentationIdeal] using hmem

/-- A fixed-length free augmentation monomial, viewed as an element of `I^n`. -/
def freeVectorRep
    (R ι : Type*) [CommRing R]
    {n : ℕ}
    (w : List.Vector ι n) :
    GroupAlgebra.augmentationPowerSubmodule R (FreeGroup ι) n := by
  refine ⟨freeVectorWord R ι w, ?_⟩
  change
    freeAugmentationWord R ι w.toList ∈
      GroupAlgebra.augmentationPower R (FreeGroup ι) n
  simpa [GroupAlgebra.augmentationPower,
    ← golod_shafarevich_algebra] using
      free_ideal_pow R ι w.toList

/-- The class of a fixed-length free augmentation monomial in `I^n / I^(n+1)`. -/
def freeVectorLayer
    (R ι : Type*) [CommRing R]
    {n : ℕ}
    (w : List.Vector ι n) :
    GroupAlgebra.augmentationLayer R (FreeGroup ι) n :=
  Submodule.Quotient.mk (freeVectorRep R ι w)

/--
The scalar Fox coordinate descends to the augmentation layer because it
vanishes on `I^(n+1)`.
-/
noncomputable def freeLayerCoordinate
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]
    {n : ℕ}
    (v : List.Vector ι n) :
    GroupAlgebra.augmentationLayer R (FreeGroup ι) n →ₗ[R] R :=
  (GroupAlgebra.augmentationLayerDenom R (FreeGroup ι) n).liftQ
    ((freeAugmentationCoefficient R ι v.toList).domRestrict
      (GroupAlgebra.augmentationPowerSubmodule R (FreeGroup ι) n))
    (by
      intro x hx
      rw [LinearMap.mem_ker]
      apply
        free_coefficient_succ
          R ι v
      have hx' :
          (x : MonoidAlgebra R (FreeGroup ι)) ∈
            GroupAlgebra.augmentationPowerSubmodule
              R (FreeGroup ι) (n + 1) :=
        hx
      simpa [GroupAlgebra.augmentationPowerSubmodule,
        GroupAlgebra.augmentationPower,
        ← golod_shafarevich_algebra] using hx')

@[simp]
theorem free_coordinate_mk
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]
    {n : ℕ}
    (v : List.Vector ι n)
    (x : GroupAlgebra.augmentationPowerSubmodule R (FreeGroup ι) n) :
    freeLayerCoordinate R ι v (Submodule.Quotient.mk x) =
      freeAugmentationCoefficient R ι v.toList x :=
  rfl

/-- The descended degree-`n` Fox coordinates are Kronecker coordinates. -/
@[simp]
theorem free_vector_word
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]
    {n : ℕ}
    (v w : List.Vector ι n) :
    freeLayerCoordinate R ι v
        (freeVectorLayer R ι w) =
      if v = w then 1 else 0 := by
  rw [freeVectorLayer,
    free_coordinate_mk]
  change
    freeAugmentationCoefficient R ι v.toList
        (freeAugmentationWord R ι w.toList) =
      if v = w then 1 else 0
  rw [free_coefficient_word
    R ι v.toList w.toList (by simp)]
  by_cases h : v = w
  · simp [h]
  · have hlist : v.toList ≠ w.toList := by
      intro hlist
      exact h (List.Vector.toList_injective hlist)
    simp [h, hlist]

/--
The degree-`n` free augmentation monomials remain linearly independent after
passing to `I^n / I^(n+1)`.
-/
theorem free_vector_independent
    (R ι : Type*) [CommRing R] [Finite ι]
    (n : ℕ) :
    LinearIndependent R
      (freeVectorLayer R ι :
        List.Vector ι n →
          GroupAlgebra.augmentationLayer R (FreeGroup ι) n) := by
  letI := Fintype.ofFinite ι
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro coeff hcoeff w
  have hread :=
    congrArg (freeLayerCoordinate R ι w) hcoeff
  simp only [map_sum, map_smul, map_zero,
    free_vector_word] at hread
  have hsum :
      (∑ x, if w = x then coeff x • (1 : R) else 0) = 0 := by
    simpa using hread
  rw [Finset.sum_eq_single w] at hsum
  · simpa using hsum
  · intro x _hx hxw
    have hwx : w ≠ x := Ne.symm hxw
    simp [hwx]
  · intro hw
    exact (hw (Finset.mem_univ w)).elim

/-- Splitting off the rightmost augmentation boundary identifies words of
length `n + 1` with a generator and a word of length `n`. -/
def freeVectorSucc
    (ι : Type*) (n : ℕ) :
    List.Vector ι (n + 1) ≃ ι × List.Vector ι n where
  toFun w := (w.head, w.tail)
  invFun p := List.Vector.cons p.1 p.2
  left_inv w := List.Vector.cons_head_tail w
  right_inv p := by simp

/--
The boundary coefficient obtained by repeatedly applying the Fox derivative
specified by the rightmost letters of an augmentation word.
-/
noncomputable def freeBoundaryCoefficient
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :
    (n : ℕ) →
      MonoidAlgebra R (FreeGroup ι) →
      List.Vector ι n →
      MonoidAlgebra R (FreeGroup ι)
  | 0, x, _ => x
  | n + 1, x, w =>
      freeBoundaryCoefficient R ι n
        (freeFoxDerivative R ι w.head x) w.tail

@[simp]
theorem free_boundary_coefficient
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]
    (x : MonoidAlgebra R (FreeGroup ι))
    (w : List.Vector ι 0) :
    freeBoundaryCoefficient R ι 0 x w = x :=
  rfl

@[simp]
theorem free_boundary_succ
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]
    (n : ℕ)
    (x : MonoidAlgebra R (FreeGroup ι))
    (w : List.Vector ι (n + 1)) :
    freeBoundaryCoefficient R ι (n + 1) x w =
      freeBoundaryCoefficient R ι n
        (freeFoxDerivative R ι w.head x) w.tail :=
  rfl

/--
Every element of `I^n` is an exact sum of its iterated Fox boundary
coefficients times the fixed-length augmentation monomials.
-/
theorem free_boundary_vector
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :
    ∀ {n : ℕ} {x : MonoidAlgebra R (FreeGroup ι)},
      x ∈ (GShafar.augmentationIdeal R (FreeGroup ι)) ^ n →
      x =
        ∑ w : List.Vector ι n,
          freeBoundaryCoefficient R ι n x w *
            freeVectorWord R ι w := by
  intro n
  induction n with
  | zero =>
      intro x _hx
      rw [Fintype.sum_eq_single (List.Vector.nil : List.Vector ι 0)]
      · simp
      · intro w hne
        exact (hne (Subsingleton.elim _ _)).elim
  | succ n ih =>
      intro x hx
      have hxI :
          x ∈ GShafar.augmentationIdeal R (FreeGroup ι) := by
        simpa only [Submodule.pow_one] using
          Ideal.pow_le_pow_right (by omega : 1 ≤ n + 1) hx
      have hderivative (j : ι) :
          freeFoxDerivative R ι j x ∈
            (GShafar.augmentationIdeal R (FreeGroup ι)) ^ n := by
        simpa using
          fox_derivative_pred R ι j hx
      calc
        x =
            ∑ j, freeFoxDerivative R ι j x *
              augmentationDifference R (FreeGroup ι) (FreeGroup.of j) :=
          free_derivative_difference
            R ι hxI
        _ =
            ∑ j, (∑ w : List.Vector ι n,
                freeBoundaryCoefficient R ι n
                    (freeFoxDerivative R ι j x) w *
                  freeVectorWord R ι w) *
              augmentationDifference R (FreeGroup ι) (FreeGroup.of j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          nth_rewrite 1 [ih (hderivative j)]
          rfl
        _ =
            ∑ j, ∑ w : List.Vector ι n,
              freeBoundaryCoefficient R ι n
                  (freeFoxDerivative R ι j x) w *
                freeVectorWord R ι w *
                  augmentationDifference R (FreeGroup ι) (FreeGroup.of j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Finset.sum_mul]
        _ =
            ∑ w : List.Vector ι (n + 1),
              freeBoundaryCoefficient R ι (n + 1) x w *
                freeVectorWord R ι w := by
          rw [← Fintype.sum_prod_type']
          apply Fintype.sum_equiv
            (freeVectorSucc ι n).symm
          intro p
          rcases p with ⟨j, w⟩
          simp [freeVectorSucc,
            free_vector_cons, mul_assoc]

/-- A left algebra multiple of a degree-`n` augmentation word, still viewed as
an element of `I^n`. -/
def freeBoundaryRep
    (R ι : Type*) [CommRing R]
    {n : ℕ}
    (a : MonoidAlgebra R (FreeGroup ι))
    (w : List.Vector ι n) :
    GroupAlgebra.augmentationPowerSubmodule R (FreeGroup ι) n :=
  ⟨a * freeVectorWord R ι w,
    Ideal.mul_mem_left
      (GroupAlgebra.augmentationPower R (FreeGroup ι) n) a
      (freeVectorRep R ι w).property⟩

/--
Modulo `I^(n+1)`, a left algebra coefficient acts on a degree-`n` augmentation
word only through its scalar augmentation.
-/
theorem free_boundary_smul
    (R ι : Type*) [CommRing R]
    {n : ℕ}
    (a : MonoidAlgebra R (FreeGroup ι))
    (w : List.Vector ι n) :
    Submodule.Quotient.mk
        (freeBoundaryRep R ι a w) =
      GroupAlgebra.augmentation R (FreeGroup ι) a •
        freeVectorLayer R ι w := by
  rw [freeVectorLayer,
    ← Submodule.Quotient.mk_smul]
  apply
    (Submodule.Quotient.eq
      (GroupAlgebra.augmentationLayerDenom R (FreeGroup ι) n)).mpr
  change
    (a * freeVectorWord R ι w -
        ((GroupAlgebra.augmentation R (FreeGroup ι) a) •
            freeVectorRep R ι w :
          GroupAlgebra.augmentationPowerSubmodule R (FreeGroup ι) n) :
      MonoidAlgebra R (FreeGroup ι)) ∈
      GroupAlgebra.augmentationPower R (FreeGroup ι) (n + 1)
  simp only [Submodule.coe_smul_of_tower]
  have haI :=
    GroupAlgebra.sub_algebra_augmentation
      R (FreeGroup ι) a
  have hw :=
    (freeVectorRep R ι w).property
  have hprod :=
    GroupAlgebra.mul_augmentation_add
      (R := R) (G := FreeGroup ι) haI hw
  simpa [sub_mul, Algebra.smul_def, Nat.one_add] using hprod

/--
The exact Fox expansion descends to a scalar linear combination of the
fixed-length augmentation-word classes.
-/
theorem vector_boundary_smul
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]
    {n : ℕ}
    (x : GroupAlgebra.augmentationPowerSubmodule R (FreeGroup ι) n) :
    Submodule.Quotient.mk x =
      ∑ w : List.Vector ι n,
        GroupAlgebra.augmentation R (FreeGroup ι)
            (freeBoundaryCoefficient R ι n x w) •
          freeVectorLayer R ι w := by
  have hx :
      (x : MonoidAlgebra R (FreeGroup ι)) ∈
        (GShafar.augmentationIdeal R (FreeGroup ι)) ^ n := by
    simp [GroupAlgebra.augmentationPowerSubmodule,
      GroupAlgebra.augmentationPower]
  have hexpand :=
    free_boundary_vector
      R ι hx
  calc
    Submodule.Quotient.mk x =
        Submodule.Quotient.mk
          (∑ w : List.Vector ι n,
            freeBoundaryRep R ι
              (freeBoundaryCoefficient R ι n x w) w) := by
      congr 1
      apply Subtype.ext
      simpa [freeBoundaryRep] using hexpand
    _ =
        ∑ w : List.Vector ι n,
          Submodule.Quotient.mk
            (freeBoundaryRep R ι
              (freeBoundaryCoefficient R ι n x w) w) := by
      simpa only [Submodule.mkQ_apply] using
        map_sum
          (GroupAlgebra.augmentationLayerDenom R (FreeGroup ι) n).mkQ
          (fun w : List.Vector ι n =>
            freeBoundaryRep R ι
              (freeBoundaryCoefficient R ι n x w) w)
          Finset.univ
    _ =
        ∑ w : List.Vector ι n,
          GroupAlgebra.augmentation R (FreeGroup ι)
              (freeBoundaryCoefficient R ι n x w) •
            freeVectorLayer R ι w := by
      apply Finset.sum_congr rfl
      intro w _hw
      exact free_boundary_smul R ι _ _

/-- The fixed-length augmentation-word classes span `I^n / I^(n+1)`. -/
theorem free_vector_top
    (R ι : Type*) [CommRing R] [Finite ι]
    (n : ℕ) :
    Submodule.span R
        (Set.range (freeVectorLayer R ι :
          List.Vector ι n →
            GroupAlgebra.augmentationLayer R (FreeGroup ι) n)) =
      ⊤ := by
  letI := Fintype.ofFinite ι
  classical
  apply top_unique
  intro y _hy
  refine Quotient.inductionOn' y ?_
  intro x
  change Submodule.Quotient.mk x ∈
    Submodule.span R (Set.range (freeVectorLayer R ι))
  rw [vector_boundary_smul
    R ι x]
  apply Submodule.sum_mem
  intro w _hw
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨w, rfl⟩)

/-- The tensor-word basis of the free-group augmentation layer `I^n / I^(n+1)`. -/
noncomputable def freeLayerBasis
    (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι]
    (n : ℕ) :
    Module.Basis (List.Vector ι n) R
      (GroupAlgebra.augmentationLayer R (FreeGroup ι) n) :=
  Module.Basis.mk
    (free_vector_independent R ι n)
    (by rw [free_vector_top R ι n])

end TBluepr
end Towers
