import Submission.ClassField.ArtinLSeries.GaussNonsplitCount
import Submission.ClassField.HigherReciprocity.CubicReciprocity
import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# Chapter VIII, Section 10: Gauss's split-prime point count

This file proves the remaining finite-field calculation in Gauss's theorem.
For a prime `p ≡ 1 (mod 3)`, a cubic character on `ZMod p` converts the
point count into a pair of conjugate Jacobi sums.  Their product is `p`, and
the standard congruence for a cubic Jacobi sum selects exactly Gauss's
normalized coefficient.
-/

namespace Submission.CField.ALSeries

open scoped BigOperators
open Submission.NumberTheory
open Submission.CField.HRecip

noncomputable section

private abbrev E := EInts

private abbrev cubicRoot : E := EIntege.zeta

private theorem cubic_root_primitive :
    IsPrimitiveRoot cubicRoot 3 := by
  apply IsPrimitiveRoot.mk_of_lt cubicRoot (by norm_num)
  · exact EIntege.zeta_pow_three
  · intro n hn hlt
    have hnCases : n = 1 ∨ n = 2 := by omega
    rcases hnCases with rfl | rfl
    · simpa using EIntege.zeta_ne_one
    · intro hsquare
      apply EIntege.zeta_ne_one
      calc
        cubicRoot = cubicRoot * 1 := by rw [mul_one]
        _ = cubicRoot * cubicRoot ^ 2 := by rw [hsquare]
        _ = cubicRoot ^ 3 := by ring
        _ = 1 := EIntege.zeta_pow_three

private theorem star_cubicRoot : star cubicRoot = cubicRoot ^ 2 := by
  ext <;> norm_num [cubicRoot, EIntege.zeta,
    EInts.omega, pow_two, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one]

/-- At a split prime there is a cubic character whose kernel on nonzero
elements is precisely the subgroup of cubes. -/
private theorem exists_cubicCharacter
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1) :
    ∃ χ : MulChar (ZMod p) E,
      χ ^ 3 = 1 ∧ χ ≠ 1 ∧ χ ^ 2 ≠ 1 ∧
        MulChar.starComp χ = χ ^ 2 ∧
        ∀ a : ZMod p, a ≠ 0 →
          (χ a = 1 ↔ ∃ x : ZMod p, x ^ 3 = a) := by
  letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime Fact.out
  obtain ⟨g, hg⟩ := (inferInstance : IsCyclic (ZMod p)ˣ).exists_generator
  have hthreeNe : (3 : ℕ) ≠ 0 := by norm_num
  let hζunit : IsUnit cubicRoot := cubic_root_primitive.isUnit hthreeNe
  let ζu : Eˣ := hζunit.unit
  have hζuVal : (ζu : E) = cubicRoot := hζunit.unit_spec
  have hthree : 3 ∣ p - 1 := by
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  have hζcard : ζu ∈ rootsOfUnity (Fintype.card (ZMod p)ˣ) E := by
    rw [ZMod.card_units p, mem_rootsOfUnity, Units.ext_iff,
      Units.val_pow_eq_pow_val, Units.val_one, hζuVal]
    exact (cubic_root_primitive.pow_eq_one_iff_dvd _).2 hthree
  let χ : MulChar (ZMod p) E := MulChar.ofRootOfUnity hζcard hg
  have hχg : χ (g : ZMod p) = cubicRoot := by
    simpa [χ, hζuVal] using MulChar.ofRootOfUnity_spec hζcard hg
  have hχthree : χ ^ 3 = 1 := by
    apply (MulChar.eq_iff hg (χ ^ 3) 1).2
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hχg,
      EIntege.zeta_pow_three]
  have hχne : χ ≠ 1 := by
    intro h
    have heval := congrArg (fun φ : MulChar (ZMod p) E ↦ φ (g : ZMod p)) h
    have : cubicRoot = 1 := by
      simpa [hχg, MulChar.one_apply_coe] using heval
    exact EIntege.zeta_ne_one this
  have hχsqne : χ ^ 2 ≠ 1 := by
    intro h
    have heval := congrArg
      (fun φ : MulChar (ZMod p) E ↦ φ (g : ZMod p)) h
    have hrootSquare : cubicRoot ^ 2 = 1 := by
      simpa [MulChar.pow_apply_coe, MulChar.one_apply_coe, hχg] using heval
    exact cubic_root_primitive.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
      hrootSquare
  have hχstar : MulChar.starComp χ = χ ^ 2 := by
    apply (MulChar.eq_iff hg (MulChar.starComp χ) (χ ^ 2)).2
    rw [MulChar.starComp_apply, MulChar.pow_apply_coe, hχg]
    change star cubicRoot = cubicRoot ^ 2
    exact star_cubicRoot
  refine ⟨χ, hχthree, hχne, hχsqne, hχstar, ?_⟩
  intro a ha
  constructor
  · intro hχa
    let u : (ZMod p)ˣ := Units.mk0 a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
    have hζpow : ζu ^ k = 1 := by
      have hχgUnit : χ.toUnitHom g = ζu := by
        apply Units.ext
        simpa [MulChar.coe_toUnitHom, hζuVal] using hχg
      calc
        ζu ^ k = χ.toUnitHom g ^ k := by rw [hχgUnit]
        _ = χ.toUnitHom (g ^ k) := by rw [map_zpow]
        _ = χ.toUnitHom u := by rw [hk]
        _ = 1 := by
          apply Units.ext
          simpa [u, MulChar.coe_toUnitHom] using hχa
    have hζuPrimitive : IsPrimitiveRoot ζu 3 := by
      rw [← IsPrimitiveRoot.coe_units_iff, hζuVal]
      exact cubic_root_primitive
    obtain ⟨l, hl⟩ := (hζuPrimitive.zpow_eq_one_iff_dvd k).mp hζpow
    refine ⟨((g ^ l : (ZMod p)ˣ) : ZMod p), ?_⟩
    have hunit : (g ^ l) ^ 3 = u := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, ← hl, hk]
    simpa [u] using congrArg Units.val hunit
  · rintro ⟨x, rfl⟩
    have hx : x ≠ 0 := by
      intro hx
      subst x
      simp at ha
    have heval := congrArg
      (fun φ : MulChar (ZMod p) E ↦ φ x) hχthree
    rw [map_pow]
    change (χ ^ 3) x = (1 : MulChar (ZMod p) E) x at heval
    rw [MulChar.pow_apply' χ (by norm_num), MulChar.one_apply hx.isUnit] at heval
    exact heval

private abbrev CubeRootFiber (p : ℕ) (a : ZMod p) :=
  {x : ZMod p // x ^ 3 = a}

/-- A split prime contains all three cube roots of unity in its residue
field. -/
private theorem primitive_cube_zmod
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1) :
    ∃ μ : ZMod p, IsPrimitiveRoot μ 3 := by
  letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime Fact.out
  have hthree : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units p]
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  have hcard := IsCyclic.card_orderOf_eq_totient hthree
  have hpos : 0 < ({u : (ZMod p)ˣ | orderOf u = 3} : Finset (ZMod p)ˣ).card := by
    rw [hcard]
    norm_num
  obtain ⟨μu, hμu⟩ := Finset.card_pos.mp hpos
  have horder : orderOf μu = 3 := (Finset.mem_filter.mp hμu).2
  refine ⟨(μu : ZMod p), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff]
  exact IsPrimitiveRoot.iff_orderOf.mpr horder

private theorem cube_fiber_ne
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1)
    {a : ZMod p} (ha : a ≠ 0) :
    Fintype.card (CubeRootFiber p a) =
      if ∃ x : ZMod p, x ^ 3 = a then 3 else 0 := by
  obtain ⟨μ, hμ⟩ := primitive_cube_zmod p hpmod
  let e : CubeRootFiber p a ≃
      {x : ZMod p // x ∈ (Polynomial.nthRoots 3 a).toFinset} :=
    { toFun := fun x ↦ ⟨x, by
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
        exact x.property⟩
      invFun := fun x ↦ ⟨x, by
        rw [← Polynomial.mem_nthRoots (by norm_num), ← Multiset.mem_toFinset]
        exact x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    Fintype.card (CubeRootFiber p a) =
        Fintype.card {x : ZMod p //
          x ∈ (Polynomial.nthRoots 3 a).toFinset} := Fintype.card_congr e
    _ = (Polynomial.nthRoots 3 a).toFinset.card :=
      Fintype.card_coe _
    _ = (Polynomial.nthRoots 3 a).card :=
      Multiset.toFinset_card_of_nodup (hμ.nthRoots_nodup ha)
    _ = if ∃ x : ZMod p, x ^ 3 = a then 3 else 0 := by
      by_cases h : ∃ x : ZMod p, x ^ 3 = a
      · rw [hμ.card_nthRoots, if_pos h, if_pos h]
      · rw [hμ.card_nthRoots, if_neg h, if_neg h]

/-- The familiar cubic-character formula for the number of cube roots:
`#\{x | x³ = a\} = 1 + χ(a) + χ(a)²`. -/
private theorem card_cube_fiber
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1)
    (χ : MulChar (ZMod p) E)
    (hχthree : χ ^ 3 = 1)
    (hcube : ∀ a : ZMod p, a ≠ 0 →
      (χ a = 1 ↔ ∃ x : ZMod p, x ^ 3 = a))
    (a : ZMod p) :
    (Fintype.card (CubeRootFiber p a) : E) =
      1 + χ a + (χ ^ 2) a := by
  by_cases ha : a = 0
  · subst a
    let e : CubeRootFiber p 0 ≃ Unit :=
      { toFun := fun _ ↦ Unit.unit
        invFun := fun _ ↦ ⟨0, by simp⟩
        left_inv := fun x ↦ by
          apply Subtype.ext
          exact (eq_zero_of_pow_eq_zero x.property).symm
        right_inv := fun _ ↦ rfl }
    rw [Fintype.card_congr e]
    have hχzero : χ 0 = 0 := χ.map_zero
    have hχsqzero : (χ ^ 2) 0 = 0 := (χ ^ 2).map_zero
    rw [hχzero, hχsqzero]
    norm_num
  · rw [cube_fiber_ne p hpmod ha]
    by_cases hχa : χ a = 1
    · have hexists : ∃ x : ZMod p, x ^ 3 = a := (hcube a ha).mp hχa
      rw [if_pos hexists, MulChar.pow_apply' χ (by norm_num), hχa]
      norm_num
    · have hnexists : ¬ ∃ x : ZMod p, x ^ 3 = a := by
        intro h
        exact hχa ((hcube a ha).mpr h)
      rw [if_neg hnexists, Nat.cast_zero, MulChar.pow_apply' χ (by norm_num)]
      have heval := congrArg
        (fun φ : MulChar (ZMod p) E ↦ φ a) hχthree
      change (χ ^ 3) a = (1 : MulChar (ZMod p) E) a at heval
      rw [MulChar.pow_apply' χ (by norm_num),
        MulChar.one_apply (isUnit_iff_ne_zero.mpr ha)] at heval
      have hfactor :
          (χ a - 1) * ((χ a) ^ 2 + χ a + 1) = 0 := by
        calc
          (χ a - 1) * ((χ a) ^ 2 + χ a + 1) =
              (χ a) ^ 3 - 1 := by ring
          _ = 0 := by rw [heval, sub_self]
      have hsum : (χ a) ^ 2 + χ a + 1 = 0 :=
        (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hχa)
      simpa [add_comm, add_left_comm, add_assoc] using hsum.symm

private def cubeSigmaEquiv (p : ℕ) :
    ZMod p ≃ Σ a : ZMod p, CubeRootFiber p a where
  toFun x := ⟨x ^ 3, x, rfl⟩
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨a, x, hx⟩
    subst a
    rfl

/-- Push a sum through the cubing map, with the cubic character recording
the cardinality of every fibre. -/
private theorem cube_character_weighted
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1)
    (χ : MulChar (ZMod p) E)
    (hχthree : χ ^ 3 = 1)
    (hcube : ∀ a : ZMod p, a ≠ 0 →
      (χ a = 1 ↔ ∃ x : ZMod p, x ^ 3 = a))
    (f : ZMod p → E) :
    ∑ x : ZMod p, f (x ^ 3) =
      ∑ a : ZMod p, (1 + χ a + (χ ^ 2) a) * f a := by
  calc
    ∑ x : ZMod p, f (x ^ 3) =
        ∑ x : Σ a : ZMod p, CubeRootFiber p a, f x.1 := by
          simpa [cubeSigmaEquiv] using
            (Equiv.sum_comp (cubeSigmaEquiv p) (fun x ↦ f x.1))
    _ = ∑ a : ZMod p, ∑ _x : CubeRootFiber p a, f a :=
      Fintype.sum_sigma' (fun a (_x : CubeRootFiber p a) ↦ f a)
    _ = ∑ a : ZMod p, (Fintype.card (CubeRootFiber p a) : E) * f a := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [nsmul_eq_mul]
    _ = ∑ a : ZMod p, (1 + χ a + (χ ^ 2) a) * f a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [card_cube_fiber p hpmod χ hχthree hcube a]

private theorem cubic_character_neg
    {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) E)
    (hcube : ∀ a : ZMod p, a ≠ 0 →
      (χ a = 1 ↔ ∃ x : ZMod p, x ^ 3 = a)) :
    χ (-1) = 1 := by
  apply (hcube (-1) (neg_ne_zero.mpr one_ne_zero)).mpr
  exact ⟨-1, by ring⟩

private theorem cubic_sq_inv
    {p : ℕ} (χ : MulChar (ZMod p) E) (hχthree : χ ^ 3 = 1) :
    χ ^ 2 = χ⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  simpa [← pow_succ'] using hχthree

private theorem sum_character_neg
    {p : ℕ} [Fact p.Prime]
    (φ : MulChar (ZMod p) E) (hφ : φ ≠ 1) :
    ∑ a : ZMod p, φ (-1 - a) = 0 := by
  calc
    ∑ a : ZMod p, φ (-1 - a) = ∑ a : ZMod p, φ a := by
      simpa using (Equiv.sum_comp (Equiv.subLeft (-1 : ZMod p)) φ)
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hφ

/-- Changing `a` to `-a` converts the shifted character convolution into
the standard Jacobi sum. -/
private theorem sum_character_jacobi
    {p : ℕ} [Fact p.Prime]
    (φ ψ : MulChar (ZMod p) E)
    (hφneg : φ (-1) = 1) (hψneg : ψ (-1) = 1) :
    ∑ a : ZMod p, φ a * ψ (-1 - a) = jacobiSum φ ψ := by
  calc
    ∑ a : ZMod p, φ a * ψ (-1 - a) =
        ∑ x : ZMod p, φ (-x) * ψ (-1 - (-x)) := by
          simpa using (Equiv.sum_comp (Equiv.neg (ZMod p))
            (fun a ↦ φ a * ψ (-1 - a))).symm
    _ = ∑ x : ZMod p, φ x * ψ (1 - x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [show -x = (-1 : ZMod p) * x by ring, map_mul, hφneg, one_mul]
      rw [show -1 - (-1 : ZMod p) * x = (-1 : ZMod p) * (1 - x) by ring,
        map_mul, hψneg, one_mul]
    _ = jacobiSum φ ψ := rfl

private theorem cubic_character_cube
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1)
    (χ : MulChar (ZMod p) E)
    (hχthree : χ ^ 3 = 1) (hχne : χ ≠ 1)
    (hcube : ∀ a : ZMod p, a ≠ 0 →
      (χ a = 1 ↔ ∃ x : ZMod p, x ^ 3 = a)) :
    ∑ x : ZMod p, χ (-1 - x ^ 3) = jacobiSum χ χ - 1 := by
  have hχneg : χ (-1) = 1 := cubic_character_neg χ hcube
  have hχsqneg : (χ ^ 2) (-1) = 1 := by
    rw [MulChar.pow_apply' χ (by norm_num), hχneg]
    norm_num
  have hχsqinv : χ ^ 2 = χ⁻¹ := cubic_sq_inv χ hχthree
  rw [show (∑ x : ZMod p, χ (-1 - x ^ 3)) =
      ∑ a : ZMod p, (1 + χ a + (χ ^ 2) a) * χ (-1 - a) by
        simpa using cube_character_weighted p hpmod χ
          hχthree hcube (fun a ↦ χ (-1 - a))]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [one_mul]
  rw [
    sum_character_neg χ hχne,
    sum_character_jacobi χ χ hχneg hχneg,
    sum_character_jacobi (χ ^ 2) χ hχsqneg hχneg]
  have hcross : jacobiSum (χ ^ 2) χ = -1 := by
    rw [jacobiSum_comm, hχsqinv, jacobiSum_nontrivial_inv hχne, hχneg]
  rw [hcross]
  ring

private theorem character_sq_cube
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1)
    (χ : MulChar (ZMod p) E)
    (hχthree : χ ^ 3 = 1) (hχne : χ ≠ 1)
    (hχsqne : χ ^ 2 ≠ 1)
    (hcube : ∀ a : ZMod p, a ≠ 0 →
      (χ a = 1 ↔ ∃ x : ZMod p, x ^ 3 = a)) :
    ∑ x : ZMod p, (χ ^ 2) (-1 - x ^ 3) =
      jacobiSum (χ ^ 2) (χ ^ 2) - 1 := by
  have hχneg : χ (-1) = 1 := cubic_character_neg χ hcube
  have hχsqneg : (χ ^ 2) (-1) = 1 := by
    rw [MulChar.pow_apply' χ (by norm_num), hχneg]
    norm_num
  have hχsqinv : χ ^ 2 = χ⁻¹ := cubic_sq_inv χ hχthree
  rw [show (∑ x : ZMod p, (χ ^ 2) (-1 - x ^ 3)) =
      ∑ a : ZMod p, (1 + χ a + (χ ^ 2) a) * (χ ^ 2) (-1 - a) by
        simpa using cube_character_weighted p hpmod χ
          hχthree hcube (fun a ↦ (χ ^ 2) (-1 - a))]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [one_mul]
  rw [
    sum_character_neg (χ ^ 2) hχsqne,
    sum_character_jacobi χ (χ ^ 2) hχneg hχsqneg,
    sum_character_jacobi (χ ^ 2) (χ ^ 2)
      hχsqneg hχsqneg]
  have hcross : jacobiSum χ (χ ^ 2) = -1 := by
    rw [hχsqinv, jacobiSum_nontrivial_inv hχne, hχneg]
  rw [hcross]
  ring

private def gaussChartSigma (p : ℕ) :
    FermatCubicChart p ≃
      Σ y : ZMod p, CubeRootFiber p (-1 - y ^ 3) where
  toFun q := ⟨q.1.1, q.1.2, by linear_combination q.property⟩
  invFun q := ⟨(q.1, q.2.1), by linear_combination q.2.property⟩
  left_inv q := by
    rcases q with ⟨⟨y, x⟩, h⟩
    rfl
  right_inv q := by
    rcases q with ⟨y, x, h⟩
    rfl

private theorem fermat_chart_cast
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1)
    (χ : MulChar (ZMod p) E)
    (hχthree : χ ^ 3 = 1) (hχne : χ ≠ 1)
    (hχsqne : χ ^ 2 ≠ 1)
    (hcube : ∀ a : ZMod p, a ≠ 0 →
      (χ a = 1 ↔ ∃ x : ZMod p, x ^ 3 = a)) :
    (Fintype.card (FermatCubicChart p) : E) =
      (p : E) - 2 + jacobiSum χ χ +
        jacobiSum (χ ^ 2) (χ ^ 2) := by
  have hcardNat :
      Fintype.card (FermatCubicChart p) =
        ∑ y : ZMod p, Fintype.card (CubeRootFiber p (-1 - y ^ 3)) := by
    calc
      Fintype.card (FermatCubicChart p) =
          Fintype.card (Σ y : ZMod p, CubeRootFiber p (-1 - y ^ 3)) :=
        Fintype.card_congr (gaussChartSigma p)
      _ = ∑ y : ZMod p,
          Fintype.card (CubeRootFiber p (-1 - y ^ 3)) := Fintype.card_sigma
  have hcardCast := congrArg (fun n : ℕ ↦ (n : E)) hcardNat
  calc
    (Fintype.card (FermatCubicChart p) : E) =
        ∑ y : ZMod p,
          (Fintype.card (CubeRootFiber p (-1 - y ^ 3)) : E) := by
            simpa using hcardCast
    _ = ∑ y : ZMod p,
        (1 + χ (-1 - y ^ 3) + (χ ^ 2) (-1 - y ^ 3)) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact card_cube_fiber p hpmod χ hχthree hcube _
    _ = (∑ _y : ZMod p, (1 : E)) +
        (∑ y : ZMod p, χ (-1 - y ^ 3)) +
        ∑ y : ZMod p, (χ ^ 2) (-1 - y ^ 3) := by
      simp only [Finset.sum_add_distrib]
    _ = (p : E) + (jacobiSum χ χ - 1) +
        (jacobiSum (χ ^ 2) (χ ^ 2) - 1) := by
      rw [cubic_character_cube p hpmod χ hχthree
          hχne hcube,
        character_sq_cube p hpmod χ hχthree
          hχne hχsqne hcube]
      simp [ZMod.card]
    _ = (p : E) - 2 + jacobiSum χ χ +
        jacobiSum (χ ^ 2) (χ ^ 2) := by ring

private def gaussFermatChart (p : ℕ) :
    GaussFermatChart p ≃ CubeRootFiber p (-1) where
  toFun z := ⟨z, by linear_combination z.property⟩
  invFun z := ⟨z, by linear_combination z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem gauss_chart_cast
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1)
    (χ : MulChar (ZMod p) E)
    (hχthree : χ ^ 3 = 1)
    (hcube : ∀ a : ZMod p, a ≠ 0 →
      (χ a = 1 ↔ ∃ x : ZMod p, x ^ 3 = a)) :
    (Fintype.card (GaussFermatChart p) : E) = 3 := by
  have hcard := congrArg (fun n : ℕ ↦ (n : E))
    (Fintype.card_congr (gaussFermatChart p))
  change (Fintype.card (GaussFermatChart p) : E) =
    (Fintype.card (CubeRootFiber p (-1)) : E) at hcard
  rw [hcard, card_cube_fiber p hpmod χ hχthree hcube]
  have hχneg : χ (-1) = 1 := cubic_character_neg χ hcube
  rw [MulChar.pow_apply' χ (by norm_num), hχneg]
  norm_num

private theorem jacobi_sq_star
    {p : ℕ} [NeZero p] (χ : MulChar (ZMod p) E)
    (hχstar : MulChar.starComp χ = χ ^ 2) :
    jacobiSum (χ ^ 2) (χ ^ 2) = star (jacobiSum χ χ) := by
  have h := jacobiSum_ringHomComp χ χ (starRingEnd E)
  change jacobiSum (MulChar.starComp χ) (MulChar.starComp χ) =
    star (jacobiSum χ χ) at h
  simpa [hχstar] using h

/-- The norm identity `J(χ,χ) * conjugate(J(χ,χ)) = p`. -/
private theorem jacobiSum_norm
    (p : ℕ) [Fact p.Prime]
    (χ : MulChar (ZMod p) E)
    (hχthree : χ ^ 3 = 1) (hχne : χ ≠ 1)
    (hχsqne : χ ^ 2 ≠ 1)
    (hχstar : MulChar.starComp χ = χ ^ 2) :
    (jacobiSum χ χ).norm = (p : ℤ) := by
  let Q := FractionRing E
  let f : E →+* Q := algebraMap E Q
  let χQ : MulChar (ZMod p) Q := χ.ringHomComp f
  have hf : Function.Injective f := IsFractionRing.injective E Q
  have hχQ : χQ ≠ 1 := by
    exact (MulChar.ringHomComp_ne_one_iff hf).mpr hχne
  have hχQsq : χQ * χQ ≠ 1 := by
    rw [← pow_two]
    intro h
    apply hχsqne
    apply MulChar.injective_ringHomComp hf
    change (χ ^ 2).ringHomComp f = (1 : MulChar (ZMod p) E).ringHomComp f
    calc
      (χ ^ 2).ringHomComp f = χQ ^ 2 := (MulChar.ringHomComp_pow χ f 2).symm
      _ = 1 := h
      _ = (1 : MulChar (ZMod p) E).ringHomComp f :=
        (MulChar.ringHomComp_one f).symm
  have hchar : ringChar Q ≠ ringChar (ZMod p) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]
    exact (Fact.out : p.Prime).ne_zero.symm
  have hprodQ := jacobiSum_mul_jacobiSum_inv hchar hχQ hχQ hχQsq
  have hχsqinv : χ ^ 2 = χ⁻¹ := cubic_sq_inv χ hχthree
  have hχQinv : χQ⁻¹ = (χ ^ 2).ringHomComp f := by
    rw [MulChar.ringHomComp_inv, hχsqinv]
  rw [hχQinv, jacobiSum_ringHomComp, jacobiSum_ringHomComp] at hprodQ
  have hprod : jacobiSum χ χ * jacobiSum (χ ^ 2) (χ ^ 2) = (p : E) := by
    apply hf
    rw [map_mul]
    simpa using hprodQ
  rw [jacobi_sq_star χ hχstar] at hprod
  have hnorm := QuadraticAlgebra.algebraMap_norm_eq_mul_star (jacobiSum χ χ)
  have hcast : ((jacobiSum χ χ).norm : E) = (p : E) := hnorm.trans hprod
  have hre := congrArg QuadraticAlgebra.re hcast
  simpa using hre

private theorem cubic_sub_sq :
    (cubicRoot - 1) ^ 2 = -3 * cubicRoot := by
  have hfactor :
      (cubicRoot - 1) * (cubicRoot ^ 2 + cubicRoot + 1) = 0 := by
    calc
      (cubicRoot - 1) * (cubicRoot ^ 2 + cubicRoot + 1) =
          cubicRoot ^ 3 - 1 := by ring
      _ = 0 := by rw [EIntege.zeta_pow_three, sub_self]
  have hgeom : cubicRoot ^ 2 + cubicRoot + 1 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left
      (sub_ne_zero.mpr EIntege.zeta_ne_one)
  linear_combination hgeom

/-- A cubic Jacobi sum is congruent to `-1` modulo `3` in the Eisenstein
integers. -/
private theorem jacobi_sum_neg
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1)
    (χ : MulChar (ZMod p) E) (hχthree : χ ^ 3 = 1) :
    ∃ q : E, jacobiSum χ χ = -1 + 3 * q := by
  have hthree : 3 ∣ Fintype.card (ZMod p) - 1 := by
    rw [ZMod.card]
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  obtain ⟨z, hzmem, hz⟩ := exists_jacobiSum_eq_neg_one_add
    (F := ZMod p) (R := E) (n := 3) (by norm_num)
      hχthree hχthree hthree cubic_root_primitive
  refine ⟨-z * cubicRoot, ?_⟩
  rw [hz, cubic_sub_sq]
  ring

private def jacobiCoefficient {p : ℕ} [NeZero p]
    (χ : MulChar (ZMod p) E) : ℤ :=
  2 * (jacobiSum χ χ).re + (jacobiSum χ χ).im

/-- The Jacobi-sum trace is precisely a coefficient satisfying Gauss's
normalization `A ≡ 1 (mod 3)` and `4p = A² + 27B²`. -/
private theorem jacobi_gauss_normalized
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1)
    (χ : MulChar (ZMod p) E)
    (hχthree : χ ^ 3 = 1) (hχne : χ ≠ 1)
    (hχsqne : χ ^ 2 ≠ 1)
    (hχstar : MulChar.starComp χ = χ ^ 2) :
    GaussNormalizedCoefficient p (jacobiCoefficient χ) := by
  let J : E := jacobiSum χ χ
  obtain ⟨q, hJcong⟩ :=
    jacobi_sum_neg p hpmod χ hχthree
  have hre := congrArg QuadraticAlgebra.re hJcong
  have him := congrArg QuadraticAlgebra.im hJcong
  change J.re = (-1 + 3 * q).re at hre
  change J.im = (-1 + 3 * q).im at him
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat,
    neg_zero, zero_add, zero_mul, mul_zero] at hre him
  have hAeq : jacobiCoefficient χ = -2 + 3 * (2 * q.re + q.im) := by
    dsimp [jacobiCoefficient, J] at hre him ⊢
    omega
  constructor
  · rw [hAeq]
    push_cast
    have hthreeZMod : (3 : ZMod 3) = 0 := by decide
    rw [hthreeZMod, zero_mul, add_zero]
    decide
  · refine ⟨q.im, ?_⟩
    have hnorm := jacobiSum_norm p χ hχthree hχne hχsqne hχstar
    have hformula := EInts.norm_formula J
    change J.norm = J.re ^ 2 + J.re * J.im + J.im ^ 2 at hformula
    change J.norm = (p : ℤ) at hnorm
    rw [hnorm] at hformula
    change 4 * (p : ℤ) = (2 * J.re + J.im) ^ 2 + 27 * q.im ^ 2
    calc
      4 * (p : ℤ) =
          4 * (J.re ^ 2 + J.re * J.im + J.im ^ 2) := by rw [hformula]
      _ = (2 * J.re + J.im) ^ 2 + 3 * J.im ^ 2 := by ring
      _ = (2 * J.re + J.im) ^ 2 + 27 * q.im ^ 2 := by rw [him]; ring

private theorem jacobiCoefficient_cast
    {p : ℕ} [NeZero p] (χ : MulChar (ZMod p) E) :
    (jacobiCoefficient χ : E) =
      jacobiSum χ χ + star (jacobiSum χ χ) := by
  apply QuadraticAlgebra.ext
  · simp [jacobiCoefficient, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat]
    ring
  · simp [jacobiCoefficient, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat]

private theorem gauss_fermat_coefficient
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1)
    (χ : MulChar (ZMod p) E)
    (hχthree : χ ^ 3 = 1) (hχne : χ ≠ 1)
    (hχsqne : χ ^ 2 ≠ 1)
    (hχstar : MulChar.starComp χ = χ ^ 2)
    (hcube : ∀ a : ZMod p, a ≠ 0 →
      (χ a = 1 ↔ ∃ x : ZMod p, x ^ 3 = a)) :
    (gaussFermatCount p : E) =
      (p : E) + 1 + (jacobiCoefficient χ : E) := by
  have hfirst := fermat_chart_cast p hpmod χ
    hχthree hχne hχsqne hcube
  have hsecond := gauss_chart_cast p hpmod χ
    hχthree hcube
  have hconj := jacobi_sq_star χ hχstar
  have htrace := jacobiCoefficient_cast χ
  change (Fintype.card
    (FermatCubicChart p ⊕ GaussFermatChart p) : E) = _
  rw [Fintype.card_sum, Nat.cast_add, hfirst, hsecond, hconj]
  rw [htrace]
  ring

/-- Gauss's split-prime point count, with the coefficient stated exactly as
in the corrected source theorem. -/
theorem gauss_fermat_point
    (p : ℕ) [Fact p.Prime] (hpmod : p % 3 = 1)
    (A : ℤ) (hA : GaussNormalizedCoefficient p A) :
    (gaussFermatCount p : ℤ) = (p : ℤ) + 1 + A := by
  obtain ⟨χ, hχthree, hχne, hχsqne, hχstar, hcube⟩ :=
    exists_cubicCharacter p hpmod
  have hAJ := jacobi_gauss_normalized p hpmod χ
    hχthree hχne hχsqne hχstar
  have hcoeff : jacobiCoefficient χ = A :=
    gauss_normalized_unique p (jacobiCoefficient χ) A hAJ hA
  have hcount := gauss_fermat_coefficient p hpmod χ
    hχthree hχne hχsqne hχstar hcube
  rw [hcoeff] at hcount
  have hre := congrArg QuadraticAlgebra.re hcount
  simpa using hre

/-- The formerly isolated split-prime bridge is discharged by the cubic
Jacobi-sum calculation. -/
theorem gaussFermatPoint :
    GaussFermatPoint := by
  intro p _ hpmod A hA
  exact gauss_fermat_point
    p hpmod A hA

/-- Gauss's corrected point-count theorem is now unconditional. -/
theorem fermatPointCount : (∀ (p : ℕ) [Fact p.Prime],
      (p % 3 ≠ 1 →
        (gaussFermatCount p : ℤ) = (p : ℤ) + 1) ∧
      (p % 3 = 1 →
        (∃! A : ℤ, GaussNormalizedCoefficient p A) ∧
        ∀ A : ℤ, GaussNormalizedCoefficient p A →
          (gaussFermatCount p : ℤ) = (p : ℤ) + 1 + A)) :=
  fermat_point_split gaussFermatPoint

end

end Submission.CField.ALSeries
