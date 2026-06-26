import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Map
import Submission.Group.Zassenhaus.MultiplicativelyDescending

/-!
# Weighted noncommutative formal series

This file formalizes the additive calculation in Section 4 of Efrat--Chapman.
A noncommutative formal power series is represented coefficientwise as a
function on the free monoid. The submodules below are the additive ideals
appearing in Lemma 4.1.
-/

namespace EChapma

variable (R X : Type*) [CommRing R]

/-- Noncommutative formal series in the alphabet `X`, viewed coefficientwise. -/
abbrev NSeries := FreeMonoid X → R

namespace NSeries

variable {R X}

/-- The additive subgroup of series with zero constant coefficient. -/
def augmentationSubmodule : Submodule R (NSeries R X) where
  carrier := {f | f 1 = 0}
  zero_mem' := rfl
  add_mem' {a b} hf hg := by
    change a 1 = 0 at hf
    change b 1 = 0 at hg
    change a 1 + b 1 = 0
    simp [hf, hg]
  smul_mem' r f hf := by
    change f 1 = 0 at hf
    change r * f 1 = 0
    simp [hf]

@[simp]
theorem mem_augmentationSubmodule {f : NSeries R X} :
    f ∈ augmentationSubmodule (R := R) (X := X) ↔ f 1 = 0 :=
  Iff.rfl

/--
The coefficientwise model of
`c_R^(e,n) = ∑_{i=1}^n e(n,i)c_R^i + c_R^(n+1)`.
-/
def weightedSubmodule (e : MDescen) (n : ℕ) :
    Submodule R (NSeries R X) where
  carrier := {f |
    f 1 = 0 ∧
      ∀ w, 1 ≤ w.length → w.length ≤ n → ((e n w.length : ℕ) : R) ∣ f w}
  zero_mem' := by
    refine ⟨rfl, ?_⟩
    intro w hw hwn
    exact dvd_zero _
  add_mem' hf hg := by
    refine ⟨by simp [hf.1, hg.1], ?_⟩
    intro w hw hwn
    exact dvd_add (hf.2 w hw hwn) (hg.2 w hw hwn)
  smul_mem' r f hf := by
    refine ⟨by simp [hf.1], ?_⟩
    intro w hw hwn
    exact dvd_mul_of_dvd_right (hf.2 w hw hwn) r

@[simp]
theorem mem_weightedSubmodule
    {e : MDescen} {n : ℕ}
    {f : NSeries R X} :
    f ∈ weightedSubmodule (R := R) (X := X) e n ↔
      f 1 = 0 ∧
        ∀ w, 1 ≤ w.length → w.length ≤ n → ((e n w.length : ℕ) : R) ∣ f w :=
  Iff.rfl

/--
The coefficientwise model of `e(n,d)c_R + c_R^(d+1)`: coefficients of
positive degree at most `d` are divisible by `e(n,d)`.
-/
def truncationSubmodule (e : MDescen) (n d : ℕ) :
    Submodule R (NSeries R X) where
  carrier := {f |
    f 1 = 0 ∧
      ∀ w, 1 ≤ w.length → w.length ≤ d → ((e n d : ℕ) : R) ∣ f w}
  zero_mem' := by
    refine ⟨rfl, ?_⟩
    intro w hw hwd
    exact dvd_zero _
  add_mem' hf hg := by
    refine ⟨by simp [hf.1, hg.1], ?_⟩
    intro w hw hwd
    exact dvd_add (hf.2 w hw hwd) (hg.2 w hw hwd)
  smul_mem' r f hf := by
    refine ⟨by simp [hf.1], ?_⟩
    intro w hw hwd
    exact dvd_mul_of_dvd_right (hf.2 w hw hwd) r

@[simp]
theorem mem_truncationSubmodule
    {e : MDescen} {n d : ℕ}
    {f : NSeries R X} :
    f ∈ truncationSubmodule (R := R) (X := X) e n d ↔
      f 1 = 0 ∧
        ∀ w, 1 ≤ w.length → w.length ≤ d → ((e n d : ℕ) : R) ∣ f w :=
  Iff.rfl

/-- Series whose coefficients below degree `m` vanish. This is `d_R^m`. -/
def orderLeastSubmodule (m : ℕ) :
    Submodule R (NSeries R X) where
  carrier := {f | ∀ w, w.length < m → f w = 0}
  zero_mem' := by simp
  add_mem' hf hg := by
    intro w hw
    simp [hf w hw, hg w hw]
  smul_mem' r f hf := by
    intro w hw
    simp [hf w hw]

@[simp]
theorem order_least_submodule
    {m : ℕ} {f : NSeries R X} :
    f ∈ orderLeastSubmodule (R := R) (X := X) m ↔
      ∀ w, w.length < m → f w = 0 :=
  Iff.rfl

/-- Multiplication of every coefficient by a fixed scalar, as a linear map. -/
def scalarLinearMap (a : R) :
    NSeries R X →ₗ[R] NSeries R X where
  toFun f := a • f
  map_add' f g := by
    ext w
    change a * (f w + g w) = a * f w + a * g w
    exact mul_add _ _ _
  map_smul' r f := by
    ext w
    change a * (r * f w) = r * (a * f w)
    ac_rfl

@[simp]
theorem scalar_linear
    (a : R) (f : NSeries R X) :
    scalarLinearMap (R := R) (X := X) a f = a • f :=
  rfl

/-- The coefficientwise description of `a d_R^m + d_R^(m+1)`. -/
def boundarySubmodule (a : R) (m : ℕ) :
    Submodule R (NSeries R X) where
  carrier := {f |
    (∀ w, w.length < m → f w = 0) ∧
      ∀ w, w.length = m → a ∣ f w}
  zero_mem' := by
    refine ⟨by simp, ?_⟩
    intro w hw
    exact dvd_zero a
  add_mem' hf hg := by
    refine ⟨?_, ?_⟩
    · intro w hw
      simp [hf.1 w hw, hg.1 w hw]
    · intro w hw
      exact dvd_add (hf.2 w hw) (hg.2 w hw)
  smul_mem' r f hf := by
    refine ⟨?_, ?_⟩
    · intro w hw
      simp [hf.1 w hw]
    · intro w hw
      exact dvd_mul_of_dvd_right (hf.2 w hw) r

@[simp]
theorem mem_boundarySubmodule
    {a : R} {m : ℕ} {f : NSeries R X} :
    f ∈ boundarySubmodule (R := R) (X := X) a m ↔
      (∀ w, w.length < m → f w = 0) ∧
        ∀ w, w.length = m → a ∣ f w :=
  Iff.rfl

/--
The coefficientwise boundary condition is exactly the sum
`a d_R^m + d_R^(m+1)`.
-/
theorem boundary_submodule_least
    (a : R) (m : ℕ) :
    boundarySubmodule (R := R) (X := X) a m =
      (orderLeastSubmodule (R := R) (X := X) m).map
          (scalarLinearMap (R := R) (X := X) a) ⊔
        orderLeastSubmodule (R := R) (X := X) (m + 1) := by
  apply le_antisymm
  · intro f hf
    classical
    let g : NSeries R X := fun w =>
      if hw : w.length = m then Classical.choose (hf.2 w hw) else 0
    have hg : g ∈ orderLeastSubmodule (R := R) (X := X) m := by
      intro w hw
      simp only [g]
      split
      · next heq => omega
      · rfl
    have hag :
        scalarLinearMap (R := R) (X := X) a g ∈
          (orderLeastSubmodule (R := R) (X := X) m).map
            (scalarLinearMap (R := R) (X := X) a) :=
      ⟨g, hg, rfl⟩
    have htail :
        f - scalarLinearMap (R := R) (X := X) a g ∈
          orderLeastSubmodule (R := R) (X := X) (m + 1) := by
      intro w hw
      have hle : w.length ≤ m := by omega
      by_cases hlt : w.length < m
      · have hne : w.length ≠ m := by omega
        simp [g, hne, hf.1 w hlt]
      · have heq : w.length = m := by omega
        have hchoose := Classical.choose_spec (hf.2 w heq)
        have hgw : g w = Classical.choose (hf.2 w heq) := by
          simp only [g, dif_pos heq]
        change f w - a * g w = 0
        rw [hgw]
        exact sub_eq_zero.mpr hchoose
    simpa using Submodule.add_mem_sup hag htail
  · refine sup_le ?_ ?_
    · rintro f ⟨g, hg, rfl⟩
      refine ⟨?_, ?_⟩
      · intro w hw
        change a * g w = 0
        simp [hg w hw]
      · intro w hw
        refine ⟨g w, ?_⟩
        rfl
    · intro f hf
      refine ⟨?_, ?_⟩
      · intro w hw
        exact hf w (by omega)
      · intro w hw
        rw [hf w (by omega)]
        exact dvd_zero a

/--
Efrat--Chapman, Lemma 4.1: the weighted ideal is the intersection of its
degreewise divisibility truncations.
-/
theorem i_inf_truncation
    (e : MDescen) {n : ℕ} (hn : 1 ≤ n) :
    weightedSubmodule (R := R) (X := X) e n =
      ⨅ d : {d : ℕ // 1 ≤ d ∧ d ≤ n},
        truncationSubmodule (R := R) (X := X) e n d := by
  ext f
  constructor
  · intro hf
    simp only [Submodule.mem_iInf]
    intro d
    refine ⟨hf.1, ?_⟩
    intro w hw hwd
    have hed : e n d ∣ e n w.length :=
      e.dvd_of_le hw hwd d.property.2
    exact
      (Nat.cast_dvd_cast (α := R) hed).trans
        (hf.2 w hw (hwd.trans d.property.2))
  · intro hf
    simp only [Submodule.mem_iInf] at hf
    refine ⟨(hf ⟨1, le_rfl, hn⟩).1, ?_⟩
    intro w hw hwn
    exact (hf ⟨w.length, hw, hwn⟩).2 w hw le_rfl

/--
Efrat--Chapman, Corollary 4.2:
`d_R^(e,n) ∩ d_R^m ⊆ e(n,m)d_R^m + d_R^(m+1)`.
-/
theorem inf_least_sup
    (e : MDescen) {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    weightedSubmodule (R := R) (X := X) e n ⊓
        orderLeastSubmodule (R := R) (X := X) m ≤
      (orderLeastSubmodule (R := R) (X := X) m).map
          (scalarLinearMap (R := R) (X := X) (e n m : R)) ⊔
        orderLeastSubmodule (R := R) (X := X) (m + 1) := by
  rw [← boundary_submodule_least]
  intro f hf
  refine ⟨hf.2, ?_⟩
  intro w hw
  simpa [hw] using hf.1.2 w (by omega) (by omega)

end NSeries

end EChapma
