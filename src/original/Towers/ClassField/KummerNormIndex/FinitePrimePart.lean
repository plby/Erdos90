import Towers.NumberTheory.Units.SUnits
import Towers.ClassField.KummerNormIndex.GalMLMK

/-!
# Chapter VII, Section 6, Lemma 6.3

For the set `T` selected in Lemma 6.2, an `S`-unit is a `p`th power in `L`
if and only if it is a `p`th power in every completion `K_v`, `v ∈ T`.

The predicates below are literal existential `p`th-power statements in the
fields `L` and `v.adicCompletion K`.  The proof that the Frobenius basis
generates `Gal(M/L)` is carried out here.  The remaining bridge is precisely
the Kummer/fixed-field and local-completion comparison in Milne's proof.
-/

namespace Towers.CField.KNIndex

open scoped IsMulCommutative

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.NIndex

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  RingOfIntegers K

/-- The finite-prime part of a set of number-field places.  Infinite places
do not impose an additional condition on the `S`-unit group. -/
def finitePrimePart
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (NumberFieldPlace K)) : Set (FinitePrime K) :=
  {v | (Sum.inl v : NumberFieldPlace K) ∈ S}

/-- The arithmetic `S`-unit group used throughout the Kummer norm-index
argument, distinguished from the representation-theoretic group with the
same short name. -/
abbrev ArithmeticSUnits
    (K : Type u) [Field K] [NumberField K]
    (S : Set (FinitePrime K)) :=
  Towers.NumberTheory.Milne.SUnits K S

/-- The literal assertion that `a` becomes a `p`th power in `L`. -/
def PthPowerExtension
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (p : ℕ) (a : Kˣ) : Prop :=
  ∃ b : L, b ^ p = algebraMap K L (a : K)

/-- The literal assertion that `a` becomes a `p`th power in the completion
`K_v`. -/
def PthPowerCompletion
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (a : Kˣ) (v : FinitePrime K) : Prop :=
  ∃ b : v.adicCompletion K,
    b ^ p = algebraMap K (v.adicCompletion K) (a : K)

/-- The conclusion of Lemma 6.3 for one actual finite set `T`. -/
def PowerDetection
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [Algebra K L]
    (p : ℕ) (S : Finset (NumberFieldPlace K))
    (T : Finset (FinitePrime K)) : Prop :=
  ∀ a : ArithmeticSUnits K (finitePrimePart K S),
    PthPowerExtension K L p (a : Kˣ) ↔
      ∀ v : FinitePrime K, v ∈ T →
        PthPowerCompletion K p (a : Kˣ) v

/-- The part of the preceding definition `M = K[U(S)^(1/p)]` used in
Lemma 6.3: every `S`-unit has a chosen `p`th root in `M`. -/
def ContainsPthRoots
    (K M : Type u) [Field K] [Field M]
    [NumberField K] [Algebra K M]
    (p : ℕ) (S : Finset (NumberFieldPlace K)) : Prop :=
  ∀ a : ArithmeticSUnits K (finitePrimePart K S),
    ∃ z : M, z ^ p = algebraMap K M (((a : Kˣ) : K))

variable {K L M : Type u}
  [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [NumberField M]
  [Algebra K L] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional L M]
  [IsGalois L M] [IsAbelianGalois K M]

/-- The assertion of Lemma 6.2 with its finite set `T` exposed.  This is
definitionally the body of `HasFrobeniusBasis` after choosing `T`. -/
def FrobeniusBasis
    (p : ℕ) (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
    (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)) : Prop :=
  letI : IsMulCommutative Gal(M/L) :=
    gal_ml_commutative (K := K) (L := L) (M := M)
  letI : Module (ZMod p) (Additive Gal(M/L)) :=
    exponentPModule p (gal_ml_pow
      (K := K) (L := L) (M := M) p hexponent)
  ∃ (i : Type u) (fi : Fintype i),
    letI : Fintype i := fi
    ∃ (indexPrime : i → T) (w : i → FinitePrime M)
      (b : Module.Basis i (ZMod p) (Additive Gal(M/L))),
      Function.Bijective indexPrime ∧
        (∀ q : FinitePrime K, q ∈ T →
          (Sum.inl q : NumberFieldPlace K) ∉ S) ∧
        (∀ j, (w j).under (OK K) = (indexPrime j : FinitePrime K)) ∧
        (∀ j, b j = Additive.ofMul
          (numberFrobeniusElement (K := L) (w j))) ∧
        (∀ j,
          galMLMK (K := K) (L := L) (M := M)
              (numberFrobeniusElement (K := L) (w j)) =
            numberFrobeniusElement (K := K) (w j))

omit [FiniteDimensional K L] in
/-- Exposing the set `T` does not change the content of Lemma 6.2. -/
theorem frobenius_basis
    (p : ℕ) (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
    (S : Finset (NumberFieldPlace K)) :
    HasFrobeniusBasis (K := K) (L := L) (M := M)
        p hexponent S ↔
      ∃ T : Finset (FinitePrime K),
        FrobeniusBasis (K := K) (L := L) (M := M)
          p hexponent S T := by
  rfl

/-- The one missing arithmetic comparison in Lemma 6.3.

For an explicitly supplied `p`th root `z ∈ M` of an `S`-unit, it records:

* the fixed-field criterion: the unit is a `p`th power in `L` exactly when
  every element of `Gal(M/L)` fixes `z`;
* the local criterion at each selected prime: it is a `p`th power in `K_v`
  exactly when the corresponding `M/K` Frobenius fixes `z`.

These are precisely the Kummer/fixed-field and `L_w = K_v` steps in the
source.  No basis-generation or desired global-local equivalence is assumed.
-/
def KummerFixedBridge : Prop :=
  ∀ (p : ℕ) (_hp : p.Prime)
    (K L M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [IsGalois L M] [IsAbelianGalois K M],
    (primitiveRoots p K).Nonempty →
    ∀ (_hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
      (S : Finset (NumberFieldPlace K)),
      (∀ Q : FinitePrime M,
        (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
          Algebra.IsUnramifiedAt (OK K) Q.asIdeal) →
      ∀
      (T : Finset (FinitePrime K))
        (i : Type u) (fi : Fintype i),
        letI : Fintype i := fi
        ∀ (indexPrime : i → T) (w : i → FinitePrime M),
          (∀ q : FinitePrime K, q ∈ T →
            (Sum.inl q : NumberFieldPlace K) ∉ S) →
          (∀ j, (w j).under (OK K) =
            (indexPrime j : FinitePrime K)) →
          (∀ j,
            galMLMK (K := K) (L := L) (M := M)
                (numberFrobeniusElement (K := L) (w j)) =
              numberFrobeniusElement (K := K) (w j)) →
          (∀ j,
            numberFrobeniusElement (K := L) (w j) ≠ 1) →
          ∀ (a : ArithmeticSUnits K (finitePrimePart K S)) (z : M),
            z ^ p = algebraMap K M ((((a : Kˣ) : K))) →
              (PthPowerExtension K L p (a : Kˣ) ↔
                ∀ sigma : Gal(M/L), sigma z = z) ∧
              (∀ j,
                PthPowerCompletion K p (a : Kˣ)
                    (indexPrime j : FinitePrime K) ↔
                  numberFrobeniusElement (K := K) (w j) z = z)

/-- Scalar multiplication by a natural residue class on `Additive A`
corresponds to taking a power in `A`. -/
private theorem mul_cast_smul
    {p : ℕ} {A : Type u} [CommGroup A]
    [Module (ZMod p) (Additive A)] (n : ℕ) (x : Additive A) :
    Additive.toMul (((n : ZMod p) • x : Additive A)) =
      (Additive.toMul x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsmul :
          (((Nat.succ n : ℕ) : ZMod p) • x : Additive A) =
            ((n : ZMod p) • x + x) := by
        simp [Nat.cast_succ, add_smul]
      rw [hsmul]
      simp [ih, pow_succ]

/-- A spanning set of the canonical `ZMod p`-module generates the original
commutative group. -/
private theorem closure_top_span
    {p : ℕ} {A : Type u} [CommGroup A] [NeZero p]
    [Module (ZMod p) (Additive A)] {S : Set A}
    (hS : Submodule.span (ZMod p) (Additive.ofMul '' S) = ⊤) :
    Subgroup.closure S = ⊤ := by
  let H : Subgroup A := Subgroup.closure S
  let W : Submodule (ZMod p) (Additive A) :=
    { carrier := {x : Additive A | Additive.toMul x ∈ H}
      zero_mem' := by
        change (1 : A) ∈ H
        exact H.one_mem
      add_mem' := by
        intro x y hx hy
        change Additive.toMul (x + y) ∈ H
        simpa using H.mul_mem hx hy
      smul_mem' := by
        intro r x hx
        change Additive.toMul (r • x) ∈ H
        have hr : ((r.val : ℕ) : ZMod p) = r := ZMod.natCast_zmod_val r
        rw [← hr]
        rw [mul_cast_smul (p := p) (A := A) r.val x]
        exact H.pow_mem hx r.val }
  have hspanLe : Submodule.span (ZMod p) (Additive.ofMul '' S) ≤ W := by
    refine Submodule.span_le.2 ?_
    intro y hy
    rcases hy with ⟨a, ha, rfl⟩
    change a ∈ H
    exact Subgroup.subset_closure ha
  apply le_antisymm le_top
  intro a _
  have haW : Additive.ofMul a ∈ W := by
    apply hspanLe
    rw [hS]
    trivial
  exact haW

/-- A `ZMod p`-basis of `Additive G` generates `G` as a group. -/
private theorem range_basis_top
    {p : ℕ} {G : Type u} [CommGroup G] [NeZero p]
    [Module (ZMod p) (Additive G)] {i : Type u}
    (b : Module.Basis i (ZMod p) (Additive G)) :
    Subgroup.closure (Set.range fun j ↦ Additive.toMul (b j)) = ⊤ := by
  apply closure_top_span (p := p)
  have himage :
      Additive.ofMul '' (Set.range fun j ↦ Additive.toMul (b j)) =
        Set.range b := by
    ext x
    constructor
    · rintro ⟨g, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Additive.toMul (b j), ⟨j, rfl⟩, rfl⟩
  rw [himage]
  exact b.span_eq

/-- Lemma 6.3 for the actual set `T` and Frobenius basis supplied by
Lemma 6.2. -/
theorem power_detection
    (hbridge : KummerFixedBridge.{u})
    (p : ℕ) (hp : p.Prime)
    (hroot : (primitiveRoots p K).Nonempty)
    (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
    (S : Finset (NumberFieldPlace K))
    (hunramified : ∀ Q : FinitePrime M,
      (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
        Algebra.IsUnramifiedAt (OK K) Q.asIdeal)
    (hcontains : ContainsPthRoots K M p S)
    (T : Finset (FinitePrime K))
    (hT : FrobeniusBasis
      (K := K) (L := L) (M := M) p hexponent S T) :
    PowerDetection K L p S T := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : IsMulCommutative Gal(M/L) :=
    gal_ml_commutative (K := K) (L := L) (M := M)
  letI : Module (ZMod p) (Additive Gal(M/L)) :=
    exponentPModule p (gal_ml_pow
      (K := K) (L := L) (M := M) p hexponent)
  rcases hT with ⟨i, fi, indexPrime, w, b, hindex, hdisjoint,
    hunder, hbasis, hcompat⟩
  letI : Fintype i := fi
  intro a
  obtain ⟨z, hzpow⟩ := hcontains a
  have hfrobNe (j : i) :
      numberFrobeniusElement (K := L) (w j) ≠ 1 := by
    intro hfrob
    have hbzero : b j = 0 := by
      rw [hbasis j, hfrob]
      rfl
    exact b.ne_zero j hbzero
  obtain ⟨hglobal, hlocal⟩ :=
    hbridge p hp K L M hroot hexponent S hunramified T i fi indexPrime w
      hdisjoint hunder hcompat hfrobNe a z hzpow
  constructor
  · intro hpower v hvT
    obtain ⟨j, hj⟩ := hindex.2 ⟨v, hvT⟩
    have hfixedML :
        numberFrobeniusElement (K := L) (w j) z = z :=
      (hglobal.mp hpower) _
    have hfixedMK :
        numberFrobeniusElement (K := K) (w j) z = z := by
      rw [← hcompat j]
      exact hfixedML
    have hjpower := (hlocal j).mpr hfixedMK
    have hv : (indexPrime j : FinitePrime K) = v :=
      congrArg Subtype.val hj
    simpa only [hv] using hjpower
  · intro hpower
    have hfixedBasis (j : i) :
        numberFrobeniusElement (K := L) (w j) z = z := by
      have hlocalPower : PthPowerCompletion K p (a : Kˣ)
          (indexPrime j : FinitePrime K) :=
        hpower (indexPrime j : FinitePrime K) (indexPrime j).property
      have hfixedMK := (hlocal j).mp hlocalPower
      have hmapped :
          galMLMK (K := K) (L := L) (M := M)
              (numberFrobeniusElement (K := L) (w j)) z = z := by
        rw [hcompat j]
        exact hfixedMK
      exact hmapped
    let generators : Set Gal(M/L) :=
      Set.range fun j ↦ Additive.toMul (b j)
    have hgenerates : Subgroup.closure generators = ⊤ :=
      range_basis_top b
    let fixedSubgroup : Subgroup Gal(M/L) :=
      { carrier := {sigma | sigma z = z}
        one_mem' := rfl
        mul_mem' := by
          intro sigma tau hsigma htau
          change sigma (tau z) = z
          rw [htau, hsigma]
        inv_mem' := by
          intro sigma hsigma
          apply sigma.injective
          simpa using hsigma.symm }
    have hgenerators : generators ⊆ fixedSubgroup := by
      rintro sigma ⟨j, rfl⟩
      change Additive.toMul (b j) z = z
      rw [hbasis j]
      exact hfixedBasis j
    have htopLe : (⊤ : Subgroup Gal(M/L)) ≤ fixedSubgroup := by
      rw [← hgenerates]
      exact (Subgroup.closure_le fixedSubgroup).2 hgenerators
    apply hglobal.mpr
    intro sigma
    exact htopLe trivial

/-- The narrow Kummer/local bridge gives the source statement. -/
theorem part_statement_bridge
    (hbridge : KummerFixedBridge.{u}) :
    (∀ (p : ℕ) (_hp : p.Prime)
          (K L M : Type u)
          [Field K] [Field L] [Field M]
          [NumberField K] [NumberField L] [NumberField M]
          [Algebra K L] [Algebra L M] [Algebra K M]
          [IsScalarTower K L M]
          [FiniteDimensional K L] [FiniteDimensional L M]
          [IsGalois L M] [IsAbelianGalois K M],
          (primitiveRoots p K).Nonempty →
          ∀ (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
            (S : Finset (NumberFieldPlace K)),
            (∀ Q : FinitePrime M,
              (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
                Algebra.IsUnramifiedAt (OK K) Q.asIdeal) →
            ContainsPthRoots K M p S →
            ∀ T : Finset (FinitePrime K),
              FrobeniusBasis (K := K) (L := L) (M := M)
                  p hexponent S T →
                PowerDetection K L p S T) := by
  intro p hp K L M
    _ _ _
    _ _ _
    _ _ _
    _
    _ _
    _ _
    hroot hexponent S hunramified hcontains T hT
  exact power_detection hbridge p hp hroot hexponent S
    hunramified hcontains T hT

end

end Towers.CField.KNIndex
