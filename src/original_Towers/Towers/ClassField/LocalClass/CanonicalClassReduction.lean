import Towers.ClassField.LocalClass.FiniteRelativeCardinality
import Towers.ClassField.CrossedProducts.SplitNonemptyHom
import Towers.ClassField.LocalBrauer.DivisionOrder

/-!
# Lemma III.2.2: reduction to the canonical degree class

Let `n` be positive.  The class of local invariant `1 / n` has order exactly
`n`.  Moreover, if this single class is split by an extension `L / K`, then
every class whose invariant is killed by `n` is split by `L`.  Thus the
lower-bound part of Lemma III.2.2 reduces to proving that a degree-`n` local
extension splits the canonical class of invariant `1 / n`.

This reduction uses neither the local-invariant base-change formula nor a
cardinality hypothesis on the relative Brauer group.
-/

namespace Towers.CField.LClass

noncomputable section

open BGroups LBrauer

variable (K : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- The canonical local Brauer class of invariant `1 / n`. -/
noncomputable def canonicalBrauerClass (n : ℕ) [NeZero n] :
    BrauerGroup K :=
  (carryBrauerInvariant K).symm
    (Multiplicative.ofAdd
      ((1 : ℚ) / (n : ℚ) : LocalInvariant))

@[simp]
theorem canonical_carry_brauer
    (n : ℕ) [NeZero n] :
    carryBrauerInvariant K
        (canonicalBrauerClass K n) =
      Multiplicative.ofAdd
        ((1 : ℚ) / (n : ℚ) : LocalInvariant) :=
  (carryBrauerInvariant K).apply_symm_apply _

/-- The canonical class of invariant `1 / n` has period exactly `n`. -/
theorem order_brauer_class (n : ℕ) [NeZero n] :
    orderOf (canonicalBrauerClass K n) = n := by
  let e := carryBrauerInvariant K
  let c := canonicalBrauerClass K n
  rw [← e.orderOf_eq c]
  change addOrderOf (e c).toAdd = n
  rw [show e c = Multiplicative.ofAdd
      ((1 : ℚ) / (n : ℚ) : LocalInvariant) by
    simp [e, c,
      canonical_carry_brauer]]
  simpa using AddCircle.addOrderOf_period_div
    (p := (1 : ℚ)) (NeZero.pos n)

/-- The canonical degree-`n` class has a central division-algebra
representative of degree `n`. -/
theorem division_brauer_class
    (n : ℕ) [NeZero n] :
    ∃ (D : Type) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Algebra.IsCentral K D) (_ : Module.Finite K D),
      brauerClass K (centralDivisionCSA K D) =
          canonicalBrauerClass K n ∧
        Module.finrank K D = n ^ 2 := by
  obtain ⟨A, hA⟩ := Quotient.exists_rep (canonicalBrauerClass K n)
  obtain ⟨D, hDdiv, hDalg, hDcentral, hDfinite, hAD⟩ :=
    division_brauer_representative K A
  letI : DivisionRing D := hDdiv
  letI : Algebra K D := hDalg
  letI : Algebra.IsCentral K D := hDcentral
  letI : Module.Finite K D := hDfinite
  have hclass : brauerClass K (centralDivisionCSA K D) =
      canonicalBrauerClass K n :=
    ((brauer_class K A (centralDivisionCSA K D)).2 hAD).symm.trans hA
  have hsqrt : Nat.sqrt (Module.finrank K D) = n := by
    rw [← brauer_division_finrank K D,
      hclass, order_brauer_class]
  obtain ⟨d, hd⟩ := finrank_simple_square K D
  have hdn : d = n := by
    simpa [hd] using hsqrt
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance,
    hclass, ?_⟩
  simpa [hdn] using hd

/-- The inverse absolute invariant, restricted to the subgroup killed by
`n`. -/
noncomputable def invariantTorsionBrauer (n : ℕ) [NeZero n] :
    invariantPowTorsion n →* BrauerGroup K :=
  (carryBrauerInvariant K).symm.toMonoidHom.comp
    (invariantPowTorsion n).subtype

theorem torsion_brauer_injective
    (n : ℕ) [NeZero n] :
    Function.Injective (invariantTorsionBrauer K n) := by
  intro x y hxy
  apply Subtype.ext
  exact (carryBrauerInvariant K).symm.injective hxy

@[simp]
theorem torsion_brauer_div
    (n : ℕ) [NeZero n] :
    invariantTorsionBrauer K n
        (invariantDivTorsion n) =
      canonicalBrauerClass K n := by
  apply (carryBrauerInvariant K).injective
  simp [invariantTorsionBrauer,
    canonicalBrauerClass,
    div_torsion_coe]

/-- The element `1 / n` generates all of the multiplicative `n`-torsion in
the local invariant group. -/
theorem invariant_div_torsion
    (n : ℕ) [NeZero n]
    (x : invariantPowTorsion n) :
    ∃ i : ℕ, x = (invariantDivTorsion n) ^ i := by
  let e : Multiplicative (ZMod n) ≃*
      invariantPowTorsion n :=
    (torsionZMod n).toMultiplicative.trans
      (invariantTorsionPow n)
  obtain ⟨z, rfl⟩ := e.surjective x
  refine ⟨z.toAdd.val, ?_⟩
  change e z = (e (Multiplicative.ofAdd (1 : ZMod n))) ^ z.toAdd.val
  rw [← map_pow]
  congr 1
  apply Multiplicative.toAdd.injective
  simp

variable (L : Type)
  [Field L] [Algebra K L]

/-- For a degree-`n` division representative of the canonical class and a
degree-`n` extension `L / K`, the one missing splitting assertion is exactly
the existence of a `K`-embedding `L → D`. -/
theorem brauer_nonempty_alg
    (n : ℕ) [NeZero n]
    [Module.Finite K L]
    (D : Type) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [Module.Finite K D]
    (hclass : brauerClass K (centralDivisionCSA K D) =
      canonicalBrauerClass K n)
    (hD : Module.finrank K D = n ^ 2)
    (hL : Module.finrank K L = n) :
    canonicalBrauerClass K n ∈ relativeBrauerGroup K L ↔
      Nonempty (L →ₐ[K] D) := by
  rw [← hclass, brauer_relative_split]
  exact CProduca.split_nonempty_alg K L D n hD hL

/-- If the canonical class `1 / n` is split by `L`, restriction of the
inverse local invariant gives a homomorphism from all `n`-torsion into the
relative Brauer group. -/
noncomputable def torsionBrauerCanonical
    (n : ℕ) [NeZero n]
    (hcanonical : canonicalBrauerClass K n ∈
      relativeBrauerGroup K L) :
    invariantPowTorsion n →* relativeBrauerGroup K L :=
  (invariantTorsionBrauer K n).codRestrict
    (relativeBrauerGroup K L) fun x ↦ by
      obtain ⟨i, rfl⟩ :=
        invariant_div_torsion n x
      rw [map_pow, torsion_brauer_div]
      exact (relativeBrauerGroup K L).pow_mem hcanonical i

/-- The preceding map is injective.  This is precisely the lower-bound
injection required in Lemma III.2.2 once the canonical degree class is known
to be split. -/
theorem torsion_relative_injective
    (n : ℕ) [NeZero n]
    (hcanonical : canonicalBrauerClass K n ∈
      relativeBrauerGroup K L) :
    Function.Injective
      (torsionBrauerCanonical
        K L n hcanonical) := by
  intro x y hxy
  apply torsion_brauer_injective K n
  exact congrArg Subtype.val hxy

/-- Membership of the canonical generator is equivalent to containment of
the whole `n`-torsion image in the relative Brauer group. -/
theorem brauer_forall_torsion
    (n : ℕ) [NeZero n] :
    canonicalBrauerClass K n ∈ relativeBrauerGroup K L ↔
      ∀ x : invariantPowTorsion n,
        invariantTorsionBrauer K n x ∈
          relativeBrauerGroup K L := by
  constructor
  · intro h x
    exact (torsionBrauerCanonical K L n h x).property
  · intro h
    simpa using h (invariantDivTorsion n)

end

end Towers.CField.LClass
