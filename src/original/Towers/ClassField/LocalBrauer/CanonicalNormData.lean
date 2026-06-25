import Towers.ClassField.LocalBrauer.FiniteExtensionData
import Towers.NumberTheory.Locals.UnramifiedExtensions


/-!
# Congruences underlying norm data at an unramified level

This file isolates the ring-theoretic calculation in Milne's proof that the
norm on the units of an unramified local extension is onto.  A product of
elements congruent to one modulo an ideal is again congruent to one.  More
precisely, on the `m`-th positive layer its linear term is the sum of the
individual errors, while all cross terms lie in the `(m + 1)`-st layer.

The statements are deliberately independent of a presentation of the
unramified extension.  They apply in particular to the product of the
Galois conjugates once the Galois action on an integral model is installed.
-/

namespace Towers.CField.LBrauer

noncomputable section

open scoped BigOperators

universe u v w

section IdealProducts

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- A finite product of elements congruent to one modulo `I` is congruent to
one modulo `I`. -/
theorem prod_sub_one
    {ι : Type v} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, f i - 1 ∈ I) :
    (∏ i ∈ s, f i) - 1 ∈ I := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have haI : f a - 1 ∈ I := hf a (Finset.mem_insert_self a s)
      have hsI : (∏ i ∈ s, f i) - 1 ∈ I :=
        ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have hidentity :
          f a * (∏ i ∈ s, f i) - 1 =
            (f a - 1) * (∏ i ∈ s, f i) + ((∏ i ∈ s, f i) - 1) := by
        ring
      rw [hidentity]
      exact I.add_mem (I.mul_mem_right _ haI) hsI

/-- The nonlinear terms in a product of expressions `1 + aᵢ`, with every
`aᵢ ∈ I^m` and `m > 0`, lie in `I^(m+1)`.  This is the first-order product
calculation that turns the norm into the trace on successive principal-unit
quotients. -/
theorem prod_sub_succ
    {ι : Type v} (s : Finset ι) (a : ι → R) (m : ℕ) (hm : 0 < m)
    (ha : ∀ i ∈ s, a i ∈ I ^ m) :
    (∏ i ∈ s, (1 + a i)) - (1 + ∑ i ∈ s, a i) ∈ I ^ (m + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
      have hx : a x ∈ I ^ m := ha x (Finset.mem_insert_self x s)
      have hs : ∀ i ∈ s, a i ∈ I ^ m :=
        fun i hi ↦ ha i (Finset.mem_insert_of_mem hi)
      have hih := ih hs
      let P : R := ∏ i ∈ s, (1 + a i)
      let S : R := ∑ i ∈ s, a i
      have hS : S ∈ I ^ m := by
        dsimp [S]
        exact Ideal.sum_mem _ fun i hi ↦ hs i hi
      have hpow : I ^ (2 * m) ≤ I ^ (m + 1) := by
        exact Ideal.pow_le_pow_right (by omega)
      have hcross : S * a x ∈ I ^ (m + 1) := by
        apply hpow
        rw [two_mul, pow_add]
        exact Ideal.mul_mem_mul hS hx
      have herror_mul :
          (P - (1 + S)) * (1 + a x) ∈ I ^ (m + 1) :=
        (I ^ (m + 1)).mul_mem_right _ hih
      have hidentity :
          (1 + a x) * P - (1 + (a x + S)) =
            (P - (1 + S)) * (1 + a x) + S * a x := by
        ring
      rw [Finset.prod_insert hxs, Finset.sum_insert hxs, hidentity]
      exact (I ^ (m + 1)).add_mem herror_mul hcross

end IdealProducts

section IdealPowerReflection

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  (f : A →+* B)

/-- If contraction identifies a target ideal power with a source ideal
power, membership in that target power reflects downstairs. -/
theorem ideal_pow_comap
    (I : Ideal A) (J : Ideal B) (m : ℕ)
    (hIJ : (J ^ m).comap f = I ^ m)
    (a : A) (ha : f a ∈ J ^ m) : a ∈ I ^ m := by
  rw [← hIJ]
  exact ha

end IdealPowerReflection

section EquivariantProducts

variable {R : Type u} [CommRing R] {G : Type v} [Group G]
  [MulSemiringAction G R]

/-- Every automorphism in a finite group action on a local ring preserves
every power of its maximal ideal. -/
theorem smul_maximal_pow
    [IsLocalRing R] (g : G) (m : ℕ) {x : R}
    (hx : x ∈ (IsLocalRing.maximalIdeal R) ^ m) :
    g • x ∈ (IsLocalRing.maximalIdeal R) ^ m := by
  let e : R ≃+* R := MulSemiringAction.toRingAut G R g
  have hmap :
      ((IsLocalRing.maximalIdeal R) ^ m).map e =
        (IsLocalRing.maximalIdeal R) ^ m := by
    rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
  rw [← hmap]
  exact Ideal.mem_map_of_mem e hx

variable [Fintype G]

/-- The product over a finite automorphism group preserves the `m`-th
principal congruence. -/
theorem galois_maximal_pow
    [IsLocalRing R] (m : ℕ) {x : R}
    (hx : x - 1 ∈ (IsLocalRing.maximalIdeal R) ^ m) :
    (∏ g : G, g • x) - 1 ∈ (IsLocalRing.maximalIdeal R) ^ m := by
  apply prod_sub_one
  intro g _
  simpa [smul_sub] using smul_maximal_pow g m hx

/-- Modulo the next maximal-ideal power, the product of the conjugates of
`1 + a` is `1` plus the sum of the conjugates of `a`. -/
theorem galois_mod_succ
    [IsLocalRing R] (m : ℕ) (hm : 0 < m) {a : R}
    (ha : a ∈ (IsLocalRing.maximalIdeal R) ^ m) :
    (∏ g : G, g • (1 + a)) - (1 + ∑ g : G, g • a) ∈
      (IsLocalRing.maximalIdeal R) ^ (m + 1) := by
  simp_rw [smul_add, smul_one]
  apply prod_sub_succ _ Finset.univ _ m hm
  intro g _
  exact smul_maximal_pow g m ha

/-- If contraction identifies the relevant maximal-ideal powers, a source
element whose image is the product of conjugates of an `m`-th principal
unit is itself an `m`-th principal unit. -/
theorem sub_galois_product
    {A : Type u} [CommRing A] [IsLocalRing A] [IsLocalRing R]
    (f : A →+* R)
    (m : ℕ) (a : A) (x : R)
    (hcomap : ((IsLocalRing.maximalIdeal R) ^ m).comap f =
      (IsLocalRing.maximalIdeal A) ^ m)
    (hprod : f a = ∏ g : G, g • x)
    (hx : x - 1 ∈ (IsLocalRing.maximalIdeal R) ^ m) :
    a - 1 ∈ (IsLocalRing.maximalIdeal A) ^ m := by
  apply ideal_pow_comap f _ _ m hcomap (a - 1)
  rw [map_sub, map_one, hprod]
  exact galois_maximal_pow m hx

end EquivariantProducts

section ResidueNorm

open IsLocalRing

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
  {G : Type w} [Group G] [Fintype G] [MulSemiringAction G B]
  [Module.Finite (ResidueField A) (ResidueField B)]
  [IsGalois (ResidueField A) (ResidueField B)]

/-- Reduction of a Galois product is the residue-field norm, provided the
given action reduces to all residue-field automorphisms.  The unramified
Galois-group equivalence supplies exactly the two hypotheses `e` and
`hreduce` in applications. -/
theorem residue_equivariant_product
    (e : G ≃* Gal((ResidueField B)/(ResidueField A)))
    (hreduce : ∀ (g : G) (b : B),
      e g (residue B b) = residue B (g • b))
    (a : A) (b : B) (hprod : algebraMap A B a = ∏ g : G, g • b) :
    residue A a = Algebra.norm (ResidueField A) (residue B b) := by
  apply (algebraMap (ResidueField A) (ResidueField B)).injective
  calc
    algebraMap (ResidueField A) (ResidueField B) (residue A a) =
        residue B (algebraMap A B a) := ResidueField.algebraMap_residue a
    _ = residue B (∏ g : G, g • b) := by rw [hprod]
    _ = ∏ g : G, residue B (g • b) := by simp
    _ = ∏ g : G, e g (residue B b) := by
      apply Finset.prod_congr rfl
      intro g _
      exact (hreduce g b).symm
    _ = ∏ σ : Gal((ResidueField B)/(ResidueField A)),
          σ (residue B b) :=
      Fintype.prod_equiv e.toEquiv _ _ fun _ ↦ rfl
    _ = algebraMap (ResidueField A) (ResidueField B)
          (Algebra.norm (ResidueField A) (residue B b)) := by
      rw [Algebra.norm_eq_prod_automorphisms]

/-- Reduction of the sum of all Galois conjugates is the residue-field
trace, under the same reduction-compatible Galois-group equivalence. -/
theorem residue_equivariant_sum
    (e : G ≃* Gal((ResidueField B)/(ResidueField A)))
    (hreduce : ∀ (g : G) (b : B),
      e g (residue B b) = residue B (g • b))
    (a : A) (b : B) (hsum : algebraMap A B a = ∑ g : G, g • b) :
    residue A a = Algebra.trace (ResidueField A) (ResidueField B)
      (residue B b) := by
  apply (algebraMap (ResidueField A) (ResidueField B)).injective
  calc
    algebraMap (ResidueField A) (ResidueField B) (residue A a) =
        residue B (algebraMap A B a) := ResidueField.algebraMap_residue a
    _ = residue B (∑ g : G, g • b) := by rw [hsum]
    _ = ∑ g : G, residue B (g • b) := by simp
    _ = ∑ g : G, e g (residue B b) := by
      apply Finset.sum_congr rfl
      intro g _
      exact (hreduce g b).symm
    _ = ∑ σ : Gal((ResidueField B)/(ResidueField A)),
          σ (residue B b) :=
      Fintype.sum_equiv e.toEquiv _ _ fun _ ↦ rfl
    _ = algebraMap (ResidueField A) (ResidueField B)
          (Algebra.trace (ResidueField A) (ResidueField B)
            (residue B b)) := by
      rw [trace_eq_sum_automorphisms]

end ResidueNorm

section UnramifiedReduction

open IsLocalRing

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsDomain A] [IsDedekindDomain A] [IsDedekindDomain B]
  [IsLocalRing A] [IsLocalRing B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [IsLocalHom (algebraMap A B)]
  [Group G] [Finite G]
  [MulSemiringAction G B] [IsGaloisGroup G A B]
  [(maximalIdeal B).LiesOver (maximalIdeal A)]
  [Algebra.IsUnramifiedAt A (maximalIdeal B)]

noncomputable local instance : Fintype G := Fintype.ofFinite G

omit [IsLocalHom (algebraMap A B)] in
/-- The unramified Galois-group equivalence is induced by reduction, hence
acts on the residue class of an integral element by reducing its conjugate. -/
theorem galois_residue_field
    (hA : maximalIdeal A ≠ ⊥) (hB : maximalIdeal B ≠ ⊥)
    (g : G) (b : B) :
    (Towers.NumberTheory.Milne.galois_unramified_local
        (R := A) (S := B) (G := G) (maximalIdeal A) hA hB g)
        (residue B b) = residue B (g • b) := by
  rfl

/-- In an unramified local Galois extension of integral models, reduction of
the Galois product is the norm in the residue-field extension. -/
theorem residue_galois_unramified
    (hA : maximalIdeal A ≠ ⊥) (hB : maximalIdeal B ≠ ⊥)
    (a : A) (b : B) (hprod : algebraMap A B a = ∏ g : G, g • b) :
    residue A a = Algebra.norm (ResidueField A) (residue B b) := by
  letI : IsGalois (ResidueField A) (ResidueField B) :=
    Towers.NumberTheory.Milne.residue_unramified_local
      (R := A) (S := B) (G := G) (maximalIdeal A)
  let e : G ≃* Gal((ResidueField B)/(ResidueField A)) :=
    Towers.NumberTheory.Milne.galois_unramified_local
      (R := A) (S := B) (G := G) (maximalIdeal A) hA hB
  exact residue_equivariant_product e
    (galois_residue_field hA hB) a b hprod

/-- In the same extension, reduction of the sum of the Galois conjugates is
the trace in the residue-field extension. -/
theorem residue_sum_unramified
    (hA : maximalIdeal A ≠ ⊥) (hB : maximalIdeal B ≠ ⊥)
    (a : A) (b : B) (hsum : algebraMap A B a = ∑ g : G, g • b) :
    residue A a = Algebra.trace (ResidueField A) (ResidueField B)
      (residue B b) := by
  letI : IsGalois (ResidueField A) (ResidueField B) :=
    Towers.NumberTheory.Milne.residue_unramified_local
      (R := A) (S := B) (G := G) (maximalIdeal A)
  let e : G ≃* Gal((ResidueField B)/(ResidueField A)) :=
    Towers.NumberTheory.Milne.galois_unramified_local
      (R := A) (S := B) (G := G) (maximalIdeal A) hA hB
  exact residue_equivariant_sum e
    (galois_residue_field hA hB) a b hsum

/-- The integral-model form of Milne's successive-layer norm calculation.
For an error `b ∈ maximalIdeal B ^ m`, the product of the conjugates of
`1 + b` is congruent modulo the next power to `1` plus its Galois sum, and
reduction of that sum is the residue trace. -/
theorem galois_congruence_unramified
    (hA : maximalIdeal A ≠ ⊥) (hB : maximalIdeal B ≠ ⊥)
    (m : ℕ) (hm : 0 < m) (a : A) (b : B)
    (hb : b ∈ (maximalIdeal B) ^ m)
    (hsum : algebraMap A B a = ∑ g : G, g • b) :
    (∏ g : G, g • (1 + b)) - (1 + algebraMap A B a) ∈
        (maximalIdeal B) ^ (m + 1) ∧
      residue A a = Algebra.trace (ResidueField A) (ResidueField B)
        (residue B b) := by
  constructor
  · rw [hsum]
    exact galois_mod_succ m hm hb
  · exact residue_sum_unramified hA hB a b hsum

end UnramifiedReduction

end

end Towers.CField.LBrauer
