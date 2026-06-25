import Towers.Algebra.Magnus.MagnusFunctoriality
import Towers.Algebra.Magnus.MagnusWeightedCoefficients
import Towers.Algebra.Magnus.UniversalUnitriangularKernels
import Mathlib.RingTheory.Ideal.Quotient.Basic


/-!
# Weighted intersections of canonical unitriangular kernels

This file proves the canonical-word equality in Efrat--Chapman, Theorem 5.3.
At degree `d`, coefficients are reduced modulo the principal ideal generated
by `e(n,d)`.
-/

noncomputable section

namespace EChapma
namespace MSeries

variable {R X : Type*} [CommRing R]

/-- The coefficient ring `R / e(n,d)R`. -/
abbrev weightedCoefficientQuotient
    (R : Type*) [CommRing R]
    (e : MDescen) (n d : ℕ) :=
  R ⧸ Ideal.span ({((e n d : ℕ) : R)} : Set R)

/-- The quotient map `R → R / e(n,d)R`. -/
def weightedCoefficient
    (e : MDescen) (n d : ℕ) :
    R →+* weightedCoefficientQuotient R e n d :=
  Ideal.Quotient.mk
    (Ideal.span ({((e n d : ℕ) : R)} : Set R))

theorem weighted_coefficient_zero
    (e : MDescen) (n d : ℕ) (r : R) :
    weightedCoefficient (R := R) e n d r = 0 ↔
      ((e n d : ℕ) : R) ∣ r := by
  change
    Ideal.Quotient.mk
        (Ideal.span ({((e n d : ℕ) : R)} : Set R)) r =
      0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

/-- The intersection of all canonical degree-`d` word-representation kernels
over `R / e(n,d)R`, for `1 ≤ d < n`. -/
def weightedCanonicalIntersection
    (e : MDescen) (n : ℕ) :
    Subgroup (FreeGroup X) :=
  ⨅ d : {d : ℕ // 1 ≤ d ∧ d < n},
    ⨅ xs : {xs : List X // xs.length = d.1},
      MonoidHom.ker
        (wordCoefficientRepresentation
          (R := weightedCoefficientQuotient R e n d.1) xs.1)

/-- The intersection of all degreewise homomorphism kernels occurring in
Efrat--Chapman, Theorem 5.3. -/
def weightedUnitriangularIntersection
    (e : MDescen) (n : ℕ) :
    Subgroup (FreeGroup X) :=
  ⨅ d : {d : ℕ // 1 ≤ d ∧ d < n},
    unitriangularKernelIntersection
      (R := weightedCoefficientQuotient R e n d.1)
      (X := X) (d.1 + 1)

/-- The canonical-word equality in Efrat--Chapman, Theorem 5.3:
the weighted Magnus subgroup is detected degree-by-degree by canonical
unitriangular representations over `R / e(n,d)R`. -/
theorem magnus_weighted_intersection
    (e : MDescen) {n : ℕ} (hn : 1 ≤ n) :
    magnusWeightedSubgroup (R := R) (X := X) e n =
      weightedCanonicalIntersection
        (R := R) (X := X) e n := by
  apply le_antisymm
  · intro g hg
    have hcoeff :=
      (weighted_ideal_coefficients
        (R := R) (X := X) e hn).mp
        ((magnus_weighted_subgroup
          (R := R) (X := X)).mp hg)
    change
      g ∈ ⨅ d : {d : ℕ // 1 ≤ d ∧ d < n},
        ⨅ xs : {xs : List X // xs.length = d.1},
          MonoidHom.ker
            (wordCoefficientRepresentation
              (R := weightedCoefficientQuotient R e n d.1)
              xs.1)
    rw [Subgroup.mem_iInf]
    intro d
    rw [Subgroup.mem_iInf]
    intro xs
    let q :=
      weightedCoefficient (R := R) e n d.1
    have horder :
        g ∈ magnusOrderSubgroup
          (R := weightedCoefficientQuotient R e n d.1)
          (X := X) (d.1 + 1) := by
      change
        VanishesBelow
          (magnusDifference
            (R := weightedCoefficientQuotient R e n d.1) g)
          (d.1 + 1)
      intro w hw
      rw [← coefficients_magnus_difference q g]
      change q (magnusDifference (R := R) g w) = 0
      rw [weighted_coefficient_zero]
      by_cases hwzero : w.length = 0
      · have hwone : w = 1 :=
          FreeMonoid.length_eq_zero.mp hwzero
        subst w
        rw [hcoeff.1]
        exact dvd_zero _
      · have hwpos : 1 ≤ w.length :=
          Nat.one_le_iff_ne_zero.mpr hwzero
        have hwd : w.length ≤ d.1 := by omega
        have hed : e n d.1 ∣ e n w.length :=
          e.dvd_of_le hwpos hwd d.2.2.le
        exact
          (Nat.cast_dvd_cast (α := R) hed).trans
            (hcoeff.2 w hwpos
              (hwd.trans d.2.2.le))
    have hintersection :
        g ∈ wordCoefficientIntersection
          (R := weightedCoefficientQuotient R e n d.1)
          (X := X) (d.1 + 1) := by
      rw [← magnus_coefficient_intersection
        (R := weightedCoefficientQuotient R e n d.1)
        (X := X) (d.1 + 1) (by omega)]
      exact horder
    exact
      (Subgroup.mem_iInf.mp hintersection)
        ⟨xs.1, by omega⟩
  · intro g hg
    rw [magnus_weighted_subgroup]
    apply
      (weighted_ideal_coefficients
        (R := R) (X := X) e hn).mpr
    constructor
    · exact magnus_difference_ideal
        (R := R) (X := X) g
    · intro w hwpos hwn
      by_cases htop : w.length = n
      · rw [htop, e.diagonal n hn]
        simp
      · have hwlt : w.length < n := lt_of_le_of_ne hwn htop
        let d : {d : ℕ // 1 ≤ d ∧ d < n} :=
          ⟨w.length, hwpos, hwlt⟩
        let q :=
          weightedCoefficient
            (R := R) e n w.length
        have hdKernels :
            g ∈ wordCoefficientIntersection
              (R := weightedCoefficientQuotient
                R e n w.length)
              (X := X) (w.length + 1) := by
          change
            g ∈ ⨅ xs :
                {xs : List X //
                  xs.length = w.length + 1 - 1},
              MonoidHom.ker
                (wordCoefficientRepresentation
                  (R := weightedCoefficientQuotient
                    R e n w.length) xs.1)
          rw [Subgroup.mem_iInf]
          intro xs
          have hd :=
            (Subgroup.mem_iInf.mp hg) d
          exact
            (Subgroup.mem_iInf.mp hd)
              ⟨xs.1, by
                change xs.1.length = w.length
                simp⟩
        have horder :
            g ∈ magnusOrderSubgroup
              (R := weightedCoefficientQuotient
                R e n w.length)
              (X := X) (w.length + 1) := by
          rw [magnus_coefficient_intersection
            (R := weightedCoefficientQuotient
              R e n w.length)
            (X := X) (w.length + 1) (by omega)]
          exact hdKernels
        have hzero :
            magnusDifference
                (R := weightedCoefficientQuotient
                  R e n w.length) g w =
              0 :=
          horder w (by omega)
        rw [← coefficients_magnus_difference q g] at hzero
        change
          q (magnusDifference (R := R) g w) = 0 at hzero
        exact
          (weighted_coefficient_zero
            (R := R) e n w.length
            (magnusDifference (R := R) g w)).mp hzero

/-- Efrat--Chapman, Theorem 5.3 in its all-homomorphisms form: the weighted
Magnus subgroup is the degreewise intersection of kernels of all maps to
the corresponding unitriangular groups over `R / e(n,d)R`. -/
theorem magnus_unitriangular_intersection
    (e : MDescen) {n : ℕ} (hn : 1 ≤ n) :
    magnusWeightedSubgroup (R := R) (X := X) e n =
      weightedUnitriangularIntersection
        (R := R) (X := X) e n := by
  rw [magnus_weighted_intersection
    (R := R) (X := X) e hn]
  apply le_antisymm
  · intro g hg
    change
      g ∈ ⨅ d : {d : ℕ // 1 ≤ d ∧ d < n},
        unitriangularKernelIntersection
          (R := weightedCoefficientQuotient R e n d.1)
          (X := X) (d.1 + 1)
    rw [Subgroup.mem_iInf]
    intro d
    have hd := (Subgroup.mem_iInf.mp hg) d
    have hd' :
        g ∈ wordCoefficientIntersection
          (R := weightedCoefficientQuotient R e n d.1)
          (X := X) (d.1 + 1) := by
      simpa [wordCoefficientIntersection] using hd
    rw [← order_unitriangular_intersection
      (R := weightedCoefficientQuotient R e n d.1)
      (X := X) (d.1 + 1) (by omega)]
    rw [magnus_coefficient_intersection
      (R := weightedCoefficientQuotient R e n d.1)
      (X := X) (d.1 + 1) (by omega)]
    exact hd'
  · intro g hg
    change
      g ∈ ⨅ d : {d : ℕ // 1 ≤ d ∧ d < n},
        ⨅ xs : {xs : List X // xs.length = d.1},
          MonoidHom.ker
            (wordCoefficientRepresentation
              (R := weightedCoefficientQuotient R e n d.1)
              xs.1)
    rw [Subgroup.mem_iInf]
    intro d
    have hd := (Subgroup.mem_iInf.mp hg) d
    have horder :
        g ∈ magnusOrderSubgroup
          (R := weightedCoefficientQuotient R e n d.1)
          (X := X) (d.1 + 1) := by
      rw [order_unitriangular_intersection
        (R := weightedCoefficientQuotient R e n d.1)
        (X := X) (d.1 + 1) (by omega)]
      exact hd
    have hd' :
        g ∈ wordCoefficientIntersection
          (R := weightedCoefficientQuotient R e n d.1)
          (X := X) (d.1 + 1) := by
      rw [← magnus_coefficient_intersection
        (R := weightedCoefficientQuotient R e n d.1)
        (X := X) (d.1 + 1) (by omega)]
      exact horder
    simpa [wordCoefficientIntersection] using hd'

end MSeries
end EChapma
