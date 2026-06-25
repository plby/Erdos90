import Towers.ClassField.Ideles.IdeleNorm
import Towers.ClassField.NormIndex.UnitsPlacesIdeles

/-!
# Chapter VII, Section 4, Corollary 4.4

The first inequality says that, for a cyclic extension `L/K` of degree `n`,
the index of `Kˣ · Nm(I_L)` in `I_K` is at least `n`.

The numerical argument in the source is made explicit below: if a Herbrand
quotient has the positive integral value `n`, then its numerator has cardinal
at least `n`.  The sole arithmetic comparison left as a bridge identifies
that numerator with the index of the literal subgroup
`Kˣ · Nm(I_L) ⊆ I_K`.
-/

namespace Towers.CField.NIndex

open IsDedekindDomain NumberField Representation
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

/-- A positive integral Herbrand quotient is bounded above by the cardinality
of its numerator.  This is the cardinal calculation used in the one-line
proof of Corollary 4.4. -/
theorem nat_herbrand_value
    {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep ℤ G) (n : ℕ)
    (h : HerbrandQuotientValue A (n : ℚ)) :
    n ≤ Nat.card (tateZero A) := by
  letI : Finite (tateZero A) := h.1
  letI : Finite (tateNegOne A) := h.2.1
  have hdenPos : 0 < Nat.card (tateNegOne A) := Nat.card_pos
  have hdenNe : (Nat.card (tateNegOne A) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hdenPos)
  have hproduct :
      (Nat.card (tateZero A) : ℚ) =
        (n : ℚ) * Nat.card (tateNegOne A) :=
    (div_eq_iff hdenNe).mp h.2.2
  have hdenOne :
      (1 : ℚ) ≤ Nat.card (tateNegOne A) := by
    exact_mod_cast hdenPos
  have hrat :
      (n : ℚ) ≤ Nat.card (tateZero A) := by
    calc
      (n : ℚ) = (n : ℚ) * 1 := (mul_one _).symm
      _ ≤ (n : ℚ) * Nat.card (tateNegOne A) :=
        mul_le_mul_of_nonneg_left hdenOne (Nat.cast_nonneg n)
      _ = Nat.card (tateZero A) := hproduct.symm
  exact_mod_cast hrat

/-- The exact quotient comparison used after Lemma 4.1.  It identifies the
numerator `C_L^G / Nm(C_L)` of the Herbrand quotient with the cosets of the
literal subgroup `Kˣ · Nm(I_L)` in the literal idèle group `I_K`.

This bridge contains only the equality of those two finite cardinalities; in
particular, it contains neither the first inequality nor any bound on either
side. -/
def TateIndexBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)],
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    Nat.card
        (tateZero
          (classCokernelRepresentation (K := K) (L := L))) =
      (principalIdeles (NumberField.RingOfIntegers K) K ⊔
        ideleNormSubgroup (K := K) (L := L)).index

/-- Corollary 4.4 follows exactly from Theorem 4.3 and the identification of
its numerator with the displayed idèle index. -/
theorem natHerbrandStatement
    (h43 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
          letI : CommGroup Gal(L/K) := IsCyclic.commGroup
          HerbrandQuotientValue
            (classCokernelRepresentation (K := K) (L := L))
            (Module.finrank K L : ℚ)))
    (hindex : TateIndexBridge.{u}) :
    (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          Module.finrank K L ≤
            (principalIdeles (NumberField.RingOfIntegers K) K ⊔
              ideleNormSubgroup (K := K) (L := L)).index) := by
  intro K L _ _ _ _ _ _ _ _
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  rw [← hindex K L]
  exact nat_herbrand_value
    (classCokernelRepresentation (K := K) (L := L))
    (Module.finrank K L) (h43 K L)

end

end Towers.CField.NIndex
