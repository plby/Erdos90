import Towers.ClassField.HerbrandQuotients.PlaceLattice
import Towers.ClassField.Shifting.Exceptional
import Towers.ClassField.Shifting.TateZero

/-!
# The permutation-lattice calculation in Proposition VII.3.1

For a finite transitive `G`-set `W`, the invariants and coinvariants of the
integral permutation lattice `W → ℤ` are both canonically copies of `ℤ`.
Under these identifications the norm is multiplication by the order of the
stabilizer of any chosen point.  This is the lattice calculation used in the
proof of Proposition VII.3.1.
-/

namespace Towers.CField.HQuotie

open CategoryTheory Representation
open Towers.CField.ICohomo
open scoped BigOperators

noncomputable section

universe u v

section IsoTransport

variable {k : Type v} {G : Type u} [CommRing k] [Group G] [Fintype G]

private noncomputable def permutationCoinvariantsLinear
    {A B : Rep k G} (e : A ≅ B) :
    A.ρ.Coinvariants ≃ₗ[k] B.ρ.Coinvariants :=
  ((Rep.coinvariantsFunctor k G).mapIso e).toLinearEquiv

private noncomputable def permutationInvariantsLinear
    {A B : Rep k G} (e : A ≅ B) :
    A.ρ.invariants ≃ₗ[k] B.ρ.invariants :=
  ((Rep.invariantsFunctor k G).mapIso e).toLinearEquiv

private theorem permutation_norm_natural
    {A B : Rep k G} (e : A ≅ B) (x : A.ρ.Coinvariants) :
    normCoinvariantsInvariants B
        (permutationCoinvariantsLinear e x) =
      permutationInvariantsLinear e
        (normCoinvariantsInvariants A x) := by
  induction x using Representation.Coinvariants.induction_on with
  | _ y =>
      apply Subtype.ext
      change B.ρ.norm (e.hom y) = e.hom (A.ρ.norm y)
      exact congrArg (fun q : A ⟶ B => q.hom y) (Rep.norm_comm e.hom)

private theorem permutation_norm_kernel
    {A B : Rep k G} (e : A ≅ B) :
    (LinearMap.ker (normCoinvariantsInvariants A)).map
        (permutationCoinvariantsLinear e).toLinearMap =
      LinearMap.ker (normCoinvariantsInvariants B) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change normCoinvariantsInvariants A y = 0 at hy
    change normCoinvariantsInvariants B
      (permutationCoinvariantsLinear e y) = 0
    rw [permutation_norm_natural, hy, map_zero]
  · intro hx
    refine ⟨(permutationCoinvariantsLinear e).symm x, ?_, ?_⟩
    · change normCoinvariantsInvariants A
        ((permutationCoinvariantsLinear e).symm x) = 0
      apply (permutationInvariantsLinear e).injective
      rw [← permutation_norm_natural]
      simpa using LinearMap.mem_ker.mp hx
    · exact (permutationCoinvariantsLinear e).apply_symm_apply x

noncomputable def tateLinearIso
    {A B : Rep k G} (e : A ≅ B) :
    tateNegOne A ≃ₗ[k] tateNegOne B :=
  ((permutationCoinvariantsLinear e).submoduleMap
      (LinearMap.ker (normCoinvariantsInvariants A))).trans
    (LinearEquiv.ofEq _ _ (permutation_norm_kernel e))

private theorem permutation_norm_range
    {A B : Rep k G} (e : A ≅ B) :
    (LinearMap.range (normCoinvariantsInvariants A)).map
        (permutationInvariantsLinear e).toLinearMap =
      LinearMap.range (normCoinvariantsInvariants B) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨permutationCoinvariantsLinear e z,
      permutation_norm_natural e z⟩
  · rintro ⟨z, rfl⟩
    refine ⟨(permutationInvariantsLinear e).symm
      (normCoinvariantsInvariants B z), ?_, ?_⟩
    · refine ⟨(permutationCoinvariantsLinear e).symm z, ?_⟩
      apply (permutationInvariantsLinear e).injective
      rw [← permutation_norm_natural]
      simp
    · simp

noncomputable def tateEquivIso
    {A B : Rep k G} (e : A ≅ B) :
    tateZero A ≃ₗ[k] tateZero B :=
  Submodule.Quotient.equiv
    (LinearMap.range (normCoinvariantsInvariants A))
    (LinearMap.range (normCoinvariantsInvariants B))
    (permutationInvariantsLinear e) (permutation_norm_range e)

end IsoTransport

section IsoHerbrandTransport

variable {G : Type u} [CommGroup G] [Fintype G]

/-- The low-Tate cardinal definition of the Herbrand quotient is invariant
under an isomorphism of integral representations. -/
theorem herbrand_value_iso
    {A B : Rep ℤ G} (e : A ≅ B) (q : ℚ) :
    HerbrandQuotientValue A q ↔ HerbrandQuotientValue B q := by
  let e₀ := tateEquivIso e
  let e₁ := tateLinearIso e
  constructor
  · intro hA
    letI : Finite (tateZero A) := hA.1
    letI : Finite (tateNegOne A) := hA.2.1
    letI : Finite (tateZero B) :=
      Finite.of_equiv (tateZero A) e₀.toEquiv
    letI : Finite (tateNegOne B) :=
      Finite.of_equiv (tateNegOne A) e₁.toEquiv
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [Nat.card_congr e₀.symm.toEquiv, Nat.card_congr e₁.symm.toEquiv]
    exact hA.2.2
  · intro hB
    let f₀ := tateEquivIso e.symm
    let f₁ := tateLinearIso e.symm
    letI : Finite (tateZero B) := hB.1
    letI : Finite (tateNegOne B) := hB.2.1
    letI : Finite (tateZero A) :=
      Finite.of_equiv (tateZero B) f₀.toEquiv
    letI : Finite (tateNegOne A) :=
      Finite.of_equiv (tateNegOne B) f₁.toEquiv
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [Nat.card_congr f₀.symm.toEquiv, Nat.card_congr f₁.symm.toEquiv]
    exact hB.2.2

end IsoHerbrandTransport

section TransitivePermutation

variable (G W : Type u) [Group G] [MulAction G W]

/-- Integral functions on a `G`-set, with the contragredient permutation
action `(g f)(w) = f(g⁻¹ w)`. -/
noncomputable def orbitFunctionRepresentation : Rep ℤ G :=
  Rep.of
    { toFun := fun g =>
        { toFun := fun (f : W → ℤ) w => f (g⁻¹ • w)
          map_add' := fun f h => by ext w; rfl
          map_smul' := fun r f => by ext w; simp }
      map_one' := by
        apply LinearMap.ext
        intro f
        funext w
        change f (1⁻¹ • w) = f w
        rw [inv_one, one_smul]
      map_mul' := by
        intro g h
        apply LinearMap.ext
        intro f
        funext w
        change f ((g * h)⁻¹ • w) = f (h⁻¹ • (g⁻¹ • w))
        rw [mul_inv_rev, mul_smul] }

@[simp]
theorem orbit_function_representation
    (g : G) (f : W → ℤ) (w : W) :
    ((orbitFunctionRepresentation G W).ρ g f) w =
      f (g⁻¹ • w) := by
  rfl

variable [Finite W]

local instance : Fintype W := Fintype.ofFinite W
local instance : DecidableEq W := Classical.decEq W

/-- Sum all coordinates of an integral function on a finite `G`-set. -/
private def orbitIntegerSum : (W → ℤ) →ₗ[ℤ] ℤ where
  toFun f := ∑ w, f w
  map_add' f h := Finset.sum_add_distrib
  map_smul' r f := by simp [Finset.mul_sum]

private theorem orbit_integer_invariant (g : G) :
    orbitIntegerSum W ∘ₗ
        (orbitFunctionRepresentation G W).ρ g =
      orbitIntegerSum W := by
  apply LinearMap.ext
  intro f
  change (∑ w, f (g⁻¹ • w)) = ∑ w, f w
  simpa only [MulAction.toPerm_apply] using
    Equiv.sum_comp (MulAction.toPerm g⁻¹) f

/-- Summing coordinates descends to the coinvariants. -/
private def orbitCoinvariantSum :
    (orbitFunctionRepresentation G W).ρ.Coinvariants →ₗ[ℤ] ℤ :=
  Representation.Coinvariants.lift
    (orbitFunctionRepresentation G W).ρ
    (orbitIntegerSum W) (orbit_integer_invariant G W)

variable (w0 : W)

/-- Put an integer at the distinguished orbit point and zero elsewhere, then
pass to coinvariants. -/
private def orbitCoinvariantSingle :
    ℤ →ₗ[ℤ] (orbitFunctionRepresentation G W).ρ.Coinvariants :=
  Representation.Coinvariants.mk
      (orbitFunctionRepresentation G W).ρ ∘ₗ
    LinearMap.single ℤ (fun _ : W => ℤ) w0

@[simp]
private theorem orbit_integer_single (z : ℤ) :
    orbitIntegerSum W (Pi.single w0 z) = z := by
  simp [orbitIntegerSum]

@[simp]
private theorem coinvariant_sum_single (z : ℤ) :
    orbitCoinvariantSum G W
        (Representation.Coinvariants.mk
          (orbitFunctionRepresentation G W).ρ
          (Pi.single w0 z)) = z := by
  change orbitIntegerSum W (Pi.single w0 z) = z
  exact orbit_integer_single W w0 z

omit [Finite W] in
private theorem orbit_action_single (g : G) (z : ℤ) :
    (orbitFunctionRepresentation G W).ρ g (Pi.single w0 z) =
      Pi.single (g • w0) z := by
  funext w
  rw [orbit_function_representation]
  by_cases h : w = g • w0
  · subst w
    rw [inv_smul_smul]
    simp
  · have h' : g⁻¹ • w ≠ w0 := by
      intro heq
      apply h
      calc
        w = g • (g⁻¹ • w) := (smul_inv_smul g w).symm
        _ = g • w0 := congrArg (fun x => g • x) heq
    rw [Pi.single_eq_of_ne h']
    rw [Pi.single_eq_of_ne h]

variable [MulAction.IsPretransitive G W]

omit [Finite W] in
private theorem coinvariant_single (w : W) (z : ℤ) :
    Representation.Coinvariants.mk
        (orbitFunctionRepresentation G W).ρ
        (Pi.single w z) =
      Representation.Coinvariants.mk
          (orbitFunctionRepresentation G W).ρ
        (Pi.single w0 z) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G w0 w
  rw [← hg, ← orbit_action_single G W w0 g z]
  exact Representation.Coinvariants.mk_self_apply
    (orbitFunctionRepresentation G W).ρ g (Pi.single w0 z)

private theorem orbit_coinvariant_single
    (q : (orbitFunctionRepresentation G W).ρ.Coinvariants) :
    orbitCoinvariantSingle G W w0 (orbitCoinvariantSum G W q) = q := by
  induction q using Representation.Coinvariants.induction_on with
  | _ f =>
      change Representation.Coinvariants.mk
          (orbitFunctionRepresentation G W).ρ
          (Pi.single w0 (∑ w, f w)) =
        Representation.Coinvariants.mk
          (orbitFunctionRepresentation G W).ρ f
      calc
        _ = Representation.Coinvariants.mk
            (orbitFunctionRepresentation G W).ρ
            (∑ w, Pi.single w0 (f w)) := by
              apply congrArg
                (Representation.Coinvariants.mk
                  (orbitFunctionRepresentation G W).ρ)
              exact map_sum
                (LinearMap.single ℤ (fun _ : W => ℤ) w0)
                (fun w => f w) Finset.univ
        _ = ∑ w, Representation.Coinvariants.mk
            (orbitFunctionRepresentation G W).ρ
            (Pi.single w0 (f w)) := by rw [map_sum]
        _ = ∑ w, Representation.Coinvariants.mk
            (orbitFunctionRepresentation G W).ρ
            (Pi.single w (f w)) := by
              apply Finset.sum_congr rfl
              intro w _
              exact (coinvariant_single G W w0 w (f w)).symm
        _ = Representation.Coinvariants.mk
            (orbitFunctionRepresentation G W).ρ
            (∑ w, Pi.single w (f w)) := by rw [map_sum]
        _ = _ := congrArg
          (Representation.Coinvariants.mk
            (orbitFunctionRepresentation G W).ρ)
          (Finset.univ_sum_single f)

/-- For a transitive finite `G`-set, summing coordinates identifies the
coinvariants of `W → ℤ` with `ℤ`. -/
noncomputable def orbitCoinvariantsEquiv :
    (orbitFunctionRepresentation G W).ρ.Coinvariants ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofLinear (orbitCoinvariantSum G W)
    (orbitCoinvariantSingle G W w0)
    (LinearMap.ext fun z => coinvariant_sum_single G W w0 z)
    (LinearMap.ext fun q => orbit_coinvariant_single G W w0 q)

/-- Evaluation at one point identifies invariant integral functions on a
transitive set with `ℤ`. -/
noncomputable def orbitInvariantsEquiv :
    (orbitFunctionRepresentation G W).ρ.invariants ≃ₗ[ℤ] ℤ where
  toFun x := x.1 w0
  invFun z := ⟨fun _ => z, by
    rw [Representation.mem_invariants]
    intro g
    rfl⟩
  map_add' x y := rfl
  map_smul' r x := rfl
  left_inv x := by
    apply Subtype.ext
    funext w
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G w0 w
    have h := congrArg (fun f => f w0) (x.2 g⁻¹)
    simp only [orbit_function_representation, inv_inv] at h
    exact h.symm
  right_inv z := rfl

variable [Fintype G]

omit [Finite W] [MulAction.IsPretransitive G W] in
/-- The norm of a function supported at `w0`, evaluated at `w0`, counts
exactly the elements of the stabilizer of `w0`. -/
private theorem orbit_norm_single (z : ℤ) :
    ((orbitFunctionRepresentation G W).ρ.norm
        (Pi.single w0 z)) w0 =
      Fintype.card (MulAction.stabilizer G w0) • z := by
  simp only [Representation.norm, LinearMap.sum_apply]
  change (LinearMap.proj w0 : (W → ℤ) →ₗ[ℤ] ℤ) (∑ d : G,
    (orbitFunctionRepresentation G W).ρ d (Pi.single w0 z)) = _
  rw [map_sum]
  simp only [LinearMap.proj_apply, orbit_function_representation]
  rw [← Equiv.sum_comp (Equiv.inv G)
    (fun g : G => (Pi.single w0 z : W → ℤ) (g⁻¹ • w0))]
  simp only [Equiv.inv_apply, inv_inv, Pi.single_apply]
  rw [← Finset.sum_filter]
  simp [Fintype.card_subtype]

/-- In the invariant and coinvariant coordinates above, the norm is
multiplication by the stabilizer order. -/
theorem orbit_norm_equiv
    (q : (orbitFunctionRepresentation G W).ρ.Coinvariants) :
    orbitInvariantsEquiv G W w0
        (normCoinvariantsInvariants
          (orbitFunctionRepresentation G W) q) =
      Fintype.card (MulAction.stabilizer G w0) •
        orbitCoinvariantsEquiv G W w0 q := by
  rw [← orbit_coinvariant_single G W w0 q]
  change ((orbitFunctionRepresentation G W).ρ.norm
      (Pi.single w0 (orbitCoinvariantSum G W q))) w0 =
    Fintype.card (MulAction.stabilizer G w0) •
      orbitIntegerSum W (Pi.single w0 (orbitCoinvariantSum G W q))
  rw [orbit_integer_single]
  exact orbit_norm_single G W w0 (orbitCoinvariantSum G W q)

/-- Reduction modulo the stabilizer order, after evaluating an invariant
function at the distinguished point. -/
private def orbitZMod :
    (orbitFunctionRepresentation G W).ρ.invariants →+
      ZMod (Fintype.card (MulAction.stabilizer G w0)) where
  toFun x := orbitInvariantsEquiv G W w0 x
  map_zero' := by simp
  map_add' x y := by simp

omit [Finite W] in
private theorem orbit_z_surjective :
    Function.Surjective (orbitZMod G W w0) := by
  intro a
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  refine ⟨(orbitInvariantsEquiv G W w0).symm z, ?_⟩
  simp [orbitZMod]

/-- The image of the permutation-lattice norm consists precisely of the
invariant functions whose common value is divisible by the stabilizer
order. -/
private theorem orbit_range_mod :
    (LinearMap.range (normCoinvariantsInvariants
      (orbitFunctionRepresentation G W))).toAddSubgroup =
      (orbitZMod G W w0).ker := by
  ext y
  change y ∈ LinearMap.range
      (normCoinvariantsInvariants
        (orbitFunctionRepresentation G W)) ↔
    y ∈ (orbitZMod G W w0).ker
  constructor
  · rintro ⟨q, rfl⟩
    rw [AddMonoidHom.mem_ker]
    change ((orbitInvariantsEquiv G W w0
      (normCoinvariantsInvariants
        (orbitFunctionRepresentation G W) q) : ℤ) :
          ZMod (Fintype.card (MulAction.stabilizer G w0))) = 0
    rw [orbit_norm_equiv]
    simp
  · intro hy
    rw [AddMonoidHom.mem_ker] at hy
    change ((orbitInvariantsEquiv G W w0 y : ℤ) :
      ZMod (Fintype.card (MulAction.stabilizer G w0))) = 0 at hy
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨(orbitCoinvariantsEquiv G W w0).symm z, ?_⟩
    apply (orbitInvariantsEquiv G W w0).injective
    rw [orbit_norm_equiv, LinearEquiv.apply_symm_apply]
    simpa [nsmul_eq_mul] using hz.symm

/-- Degree-zero Tate cohomology of one transitive integral permutation
lattice is the cyclic group whose order is the stabilizer order. -/
noncomputable def orbitTateAdd :
    tateZero (orbitFunctionRepresentation G W) ≃+
      ZMod (Fintype.card (MulAction.stabilizer G w0)) :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (orbit_range_mod G W w0)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (orbitZMod G W w0)
      (orbit_z_surjective G W w0))

/-- The norm on coinvariants of a transitive integral permutation lattice is
injective. -/
theorem orbit_norm_injective (w0 : W) :
    Function.Injective (normCoinvariantsInvariants
      (orbitFunctionRepresentation G W)) := by
  intro x y hxy
  apply (orbitCoinvariantsEquiv G W w0).injective
  have h := congrArg (orbitInvariantsEquiv G W w0) hxy
  rw [orbit_norm_equiv, orbit_norm_equiv] at h
  have hcard : Fintype.card (MulAction.stabilizer G w0) ≠ 0 :=
    Fintype.card_ne_zero
  have hcardInt : (Fintype.card (MulAction.stabilizer G w0) : ℤ) ≠ 0 := by
    exact_mod_cast hcard
  apply mul_left_cancel₀ hcardInt
  simpa [nsmul_eq_mul] using h

/-- Consequently degree `-1` Tate cohomology of a transitive integral
permutation lattice is trivial. -/
theorem orbit_tate_subsingleton (w0 : W) :
    Subsingleton
      (tateNegOne (orbitFunctionRepresentation G W)) :=
  ⟨fun x y => Subtype.ext
    (orbit_norm_injective G W w0 (x.2.trans y.2.symm))⟩

end TransitivePermutation

section TransitivePermutationHerbrand

variable (G W : Type u) [CommGroup G] [MulAction G W]
  [Fintype G] [Finite W] [MulAction.IsPretransitive G W]
  (w0 : W)

local instance : Fintype W := Fintype.ofFinite W
local instance : DecidableEq W := Classical.decEq W

/-- A transitive integral permutation lattice has Herbrand quotient equal
to the order of a point stabilizer. -/
theorem function_herbrand_value :
    HerbrandQuotientValue (orbitFunctionRepresentation G W)
      (Fintype.card (MulAction.stabilizer G w0) : ℚ) := by
  let e₀ := orbitTateAdd G W w0
  letI : Finite
      (tateZero (orbitFunctionRepresentation G W)) :=
    Finite.of_equiv (ZMod (Fintype.card (MulAction.stabilizer G w0)))
      e₀.symm.toEquiv
  letI : Subsingleton
      (tateNegOne (orbitFunctionRepresentation G W)) :=
    orbit_tate_subsingleton G W w0
  letI : Finite
      (tateNegOne (orbitFunctionRepresentation G W)) :=
    inferInstance
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hzero :
      Nat.card (tateZero
        (orbitFunctionRepresentation G W)) =
        Fintype.card (MulAction.stabilizer G w0) := by
    calc
      _ = Nat.card (ZMod (Fintype.card (MulAction.stabilizer G w0))) :=
        Nat.card_congr e₀.toEquiv
      _ = _ := Nat.card_zmod _
  have hneg :
      Nat.card (tateNegOne
        (orbitFunctionRepresentation G W)) = 1 :=
    Nat.card_unique
  rw [hzero, hneg]
  norm_num

end TransitivePermutationHerbrand

end

end Towers.CField.HQuotie
