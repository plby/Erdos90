import Submission.ClassField.HerbrandQuotients.PermutationHerbrand

/-!
# The Herbrand quotient of the place lattice in Proposition VII.3.1

The places above `S` are a disjoint union of transitive Galois orbits, one
over each base place.  This file computes the low Tate groups of the literal
integral permutation lattice on that disjoint union.
-/

namespace Submission.CField.HQuotie

open IsDedekindDomain NumberField Representation
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open scoped BigOperators

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

section PlaceFibers

variable [Finite Gal(L/K)]

local instance : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)

local instance upperPlaceDecidableEq
    (S : Finset (NumberFieldPlace K)) :
    DecidableEq (upperPlacesAt (K := K) (L := L) S) := Classical.decEq _

local instance upperPlaceFiberFintype (v : NumberFieldPlace K) :
    Fintype (CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute v)) := Fintype.ofFinite _

local instance upperPlaceFiberDecidableEq (v : NumberFieldPlace K) :
    DecidableEq (CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute v)) := Classical.decEq _

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L]
  [Finite Gal(L/K)] in
@[simp]
theorem upper_function_representation
    (S : Finset (NumberFieldPlace K)) (sigma : Gal(L/K))
    (f : upperPlacesAt (K := K) (L := L) S → ℤ)
    (t : upperPlacesAt (K := K) (L := L) S) :
    ((upperFunctionRepresentation (K := K) (L := L) S).ρ
      sigma f) t = f (sigma⁻¹ • t) := by
  rfl

/-- Sum the coordinates in each fibre over a base place. -/
private def upperFiberSum
    (S : Finset (NumberFieldPlace K)) :
    (upperPlacesAt (K := K) (L := L) S → ℤ) →ₗ[ℤ] (S → ℤ) where
  toFun f v := ∑ z : CompletionPlacesAbove (L := L)
    (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)), f ⟨v, z⟩
  map_add' f h := by ext v; exact Finset.sum_add_distrib
  map_smul' r f := by ext v; simp [Finset.mul_sum]

omit [Finite Gal(L/K)] in
private theorem upper_fiber_invariant
    (S : Finset (NumberFieldPlace K)) (sigma : Gal(L/K)) :
    upperFiberSum (K := K) (L := L) S ∘ₗ
        (upperFunctionRepresentation (K := K) (L := L) S).ρ
          sigma =
      upperFiberSum (K := K) (L := L) S := by
  apply LinearMap.ext
  intro f
  funext v
  change (∑ z, f ⟨v, sigma⁻¹ • z⟩) = ∑ z, f ⟨v, z⟩
  simpa only [MulAction.toPerm_apply] using
    Equiv.sum_comp (MulAction.toPerm sigma⁻¹) (fun z => f ⟨v, z⟩)

/-- Fibrewise coordinate sums descend to coinvariants. -/
private def upperCoinvariantSum
    (S : Finset (NumberFieldPlace K)) :
    (upperFunctionRepresentation (K := K) (L := L) S).ρ.Coinvariants
      →ₗ[ℤ] (S → ℤ) :=
  Representation.Coinvariants.lift
    (upperFunctionRepresentation (K := K) (L := L) S).ρ
    (upperFiberSum (K := K) (L := L) S)
    (upper_fiber_invariant (K := K) (L := L) S)

/-- Put one prescribed integer at the chosen upper place in each fibre. -/
private def upperChosenFunction
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    (S → ℤ) →ₗ[ℤ] (upperPlacesAt (K := K) (L := L) S → ℤ) where
  toFun a t := (Pi.single (w t.1) (a t.1) :
    CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (t.1 : NumberFieldPlace K)) → ℤ) t.2
  map_add' a b := by
    funext t
    rcases t with ⟨v, t⟩
    change (Pi.single (w v) (a v + b v) :
        CompletionPlacesAbove (L := L)
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) → ℤ) t =
      (Pi.single (w v) (a v) :
        CompletionPlacesAbove (L := L)
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) → ℤ) t +
      (Pi.single (w v) (b v) :
        CompletionPlacesAbove (L := L)
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) → ℤ) t
    by_cases ht : t = w v
    · subst t
      simp
    · rw [Pi.single_eq_of_ne ht, Pi.single_eq_of_ne ht,
        Pi.single_eq_of_ne ht]
      simp
  map_smul' r a := by
    funext t
    rcases t with ⟨v, t⟩
    change (Pi.single (w v) (r * a v) :
        CompletionPlacesAbove (L := L)
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) → ℤ) t =
      r * (Pi.single (w v) (a v) :
        CompletionPlacesAbove (L := L)
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) → ℤ) t
    by_cases ht : t = w v
    · subst t
      simp
    · rw [Pi.single_eq_of_ne ht, Pi.single_eq_of_ne ht]
      simp

/-- The chosen-point function, passed to coinvariants. -/
private def upperCoinvariantChosen
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    (S → ℤ) →ₗ[ℤ]
      (upperFunctionRepresentation (K := K) (L := L) S).ρ.Coinvariants :=
  Representation.Coinvariants.mk
      (upperFunctionRepresentation (K := K) (L := L) S).ρ ∘ₗ
    upperChosenFunction (K := K) (L := L) S w

omit [Finite Gal(L/K)] in
@[simp]
private theorem upper_fiber_chosen
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)))
    (a : S → ℤ) :
    upperFiberSum (K := K) (L := L) S
      (upperChosenFunction (K := K) (L := L) S w a) = a := by
  funext v
  change (∑ z, Pi.single (w v) (a v) z) = a v
  simp

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L]
  [Finite Gal(L/K)] in
private theorem upper_action_single
    (S : Finset (NumberFieldPlace K))
    (sigma : Gal(L/K))
    (t : upperPlacesAt (K := K) (L := L) S) (z : ℤ) :
    (upperFunctionRepresentation (K := K) (L := L) S).ρ
        sigma (Pi.single t z) =
      Pi.single (sigma • t) z := by
  funext x
  rw [upper_function_representation]
  by_cases h : x = sigma • t
  · subst x
    have hinv : sigma⁻¹ • (sigma • t) = t := inv_smul_smul sigma t
    rw [hinv]
    simp
  · have h' : sigma⁻¹ • x ≠ t := by
      intro heq
      apply h
      calc
        x = sigma • (sigma⁻¹ • x) := (smul_inv_smul sigma x).symm
        _ = sigma • t := congrArg (fun y => sigma • y) heq
    rw [Pi.single_eq_of_ne h']
    rw [Pi.single_eq_of_ne h]

omit [Finite Gal(L/K)] in
private theorem upper_coinvariant_chosen
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)))
    (t : upperPlacesAt (K := K) (L := L) S) (z : ℤ) :
    Representation.Coinvariants.mk
        (upperFunctionRepresentation (K := K) (L := L) S).ρ
        (Pi.single t z) =
      Representation.Coinvariants.mk
        (upperFunctionRepresentation (K := K) (L := L) S).ρ
        (Pi.single (⟨t.1, w t.1⟩ : upperPlacesAt (K := K) (L := L) S) z) := by
  letI := upper_fiber_pretransitive (K := K) (L := L)
    (t.1 : NumberFieldPlace K)
  obtain ⟨sigma, hsigma⟩ := MulAction.exists_smul_eq Gal(L/K) (w t.1) t.2
  have hsigmaT : sigma •
      (⟨t.1, w t.1⟩ : upperPlacesAt (K := K) (L := L) S) = t := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq hsigma
  rw [← hsigmaT, ← upper_action_single (K := K) (L := L)]
  exact Representation.Coinvariants.mk_self_apply
    (upperFunctionRepresentation (K := K) (L := L) S).ρ
    sigma (Pi.single (⟨t.1, w t.1⟩ :
      upperPlacesAt (K := K) (L := L) S) z)

omit [Finite Gal(L/K)] in
private theorem chosen_fiber_single
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)))
    (t : upperPlacesAt (K := K) (L := L) S) (z : ℤ) :
    upperChosenFunction (K := K) (L := L) S w
        (upperFiberSum (K := K) (L := L) S (Pi.single t z)) =
      Pi.single (⟨t.1, w t.1⟩ : upperPlacesAt (K := K) (L := L) S) z := by
  classical
  rcases t with ⟨v, t⟩
  funext x
  rcases x with ⟨v', x⟩
  by_cases hv : v' = v
  · subst v'
    change (Pi.single (w v)
        (∑ y, (Pi.single (⟨v, t⟩ :
          upperPlacesAt (K := K) (L := L) S) z :
            upperPlacesAt (K := K) (L := L) S → ℤ) ⟨v, y⟩) :
          CompletionPlacesAbove (L := L)
            (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) → ℤ) x =
      (Pi.single (⟨v, w v⟩ :
        upperPlacesAt (K := K) (L := L) S) z :
          upperPlacesAt (K := K) (L := L) S → ℤ) ⟨v, x⟩
    have hsum :
        (∑ y, (Pi.single (⟨v, t⟩ :
          upperPlacesAt (K := K) (L := L) S) z :
            upperPlacesAt (K := K) (L := L) S → ℤ) ⟨v, y⟩) = z := by
      simp only [Pi.single_apply]
      simp
    rw [hsum]
    by_cases hx : x = w v
    · subst x
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hx]
      have hsigma : (⟨v, x⟩ :
          upperPlacesAt (K := K) (L := L) S) ≠ ⟨v, w v⟩ := by
        intro h
        exact hx (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
      rw [Pi.single_eq_of_ne hsigma]
  · change (Pi.single (w v')
        (∑ y, (Pi.single (⟨v, t⟩ :
          upperPlacesAt (K := K) (L := L) S) z :
            upperPlacesAt (K := K) (L := L) S → ℤ) ⟨v', y⟩) :
          CompletionPlacesAbove (L := L)
            (coinvariantsInvariantsAbsolute (v' : NumberFieldPlace K)) → ℤ) x =
      (Pi.single (⟨v, w v⟩ :
        upperPlacesAt (K := K) (L := L) S) z :
          upperPlacesAt (K := K) (L := L) S → ℤ) ⟨v', x⟩
    have hsigma : ∀ (y : CompletionPlacesAbove (L := L)
        (coinvariantsInvariantsAbsolute (v' : NumberFieldPlace K))),
        (⟨v', y⟩ : upperPlacesAt (K := K) (L := L) S) ≠ ⟨v, t⟩ := by
      intro y h
      exact hv (congrArg Sigma.fst h)
    have hchosen : (⟨v', x⟩ :
        upperPlacesAt (K := K) (L := L) S) ≠ ⟨v, w v⟩ := by
      intro h
      exact hv (congrArg Sigma.fst h)
    simp only [Pi.single_apply]
    simp [hsigma, hchosen]

omit [Finite Gal(L/K)] in
private theorem coinvariant_chosen_sum
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)))
    (q : (upperFunctionRepresentation
      (K := K) (L := L) S).ρ.Coinvariants) :
    upperCoinvariantChosen (K := K) (L := L) S w
        (upperCoinvariantSum (K := K) (L := L) S q) = q := by
  induction q using Representation.Coinvariants.induction_on with
  | _ f =>
      induction f using Pi.single_induction with
      | zero =>
          change upperCoinvariantChosen (K := K) (L := L) S w
              (upperFiberSum (K := K) (L := L) S 0) =
            Representation.Coinvariants.mk
              (upperFunctionRepresentation
                (K := K) (L := L) S).ρ 0
          rw [map_zero, map_zero]
          exact (map_zero (Representation.Coinvariants.mk
            (upperFunctionRepresentation
              (K := K) (L := L) S).ρ)).symm
      | add f h hf hh =>
          change upperCoinvariantChosen (K := K) (L := L) S w
              (upperFiberSum (K := K) (L := L) S f) =
            Representation.Coinvariants.mk
              (upperFunctionRepresentation
                (K := K) (L := L) S).ρ f at hf
          change upperCoinvariantChosen (K := K) (L := L) S w
              (upperFiberSum (K := K) (L := L) S h) =
            Representation.Coinvariants.mk
              (upperFunctionRepresentation
                (K := K) (L := L) S).ρ h at hh
          change upperCoinvariantChosen (K := K) (L := L) S w
              (upperFiberSum (K := K) (L := L) S (f + h)) =
            Representation.Coinvariants.mk
              (upperFunctionRepresentation
                (K := K) (L := L) S).ρ (f + h)
          rw [map_add, map_add, hf, hh]
          exact (map_add (Representation.Coinvariants.mk
            (upperFunctionRepresentation
              (K := K) (L := L) S).ρ) f h).symm
      | single t z =>
          change Representation.Coinvariants.mk
              (upperFunctionRepresentation
                (K := K) (L := L) S).ρ
              (upperChosenFunction (K := K) (L := L) S w
                (upperFiberSum (K := K) (L := L) S
                  (Pi.single t z))) =
            Representation.Coinvariants.mk
              (upperFunctionRepresentation
                (K := K) (L := L) S).ρ (Pi.single t z)
          rw [chosen_fiber_single]
          exact (upper_coinvariant_chosen
            (K := K) (L := L) S w t z).symm

/-- Coinvariants of the full place-permutation lattice are one copy of
`ℤ` for each base place. -/
noncomputable def upperPlaceCoinvariants
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    (upperFunctionRepresentation
      (K := K) (L := L) S).ρ.Coinvariants ≃ₗ[ℤ] (S → ℤ) :=
  LinearEquiv.ofLinear
    (upperCoinvariantSum (K := K) (L := L) S)
    (upperCoinvariantChosen (K := K) (L := L) S w)
    (LinearMap.ext fun a => upper_fiber_chosen
      (K := K) (L := L) S w a)
    (LinearMap.ext fun q => coinvariant_chosen_sum
      (K := K) (L := L) S w q)

/-- An invariant integral function is constant on every fibre. -/
noncomputable def upperPlaceInvariants
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    (upperFunctionRepresentation
      (K := K) (L := L) S).ρ.invariants ≃ₗ[ℤ] (S → ℤ) where
  toFun x v := x.1 ⟨v, w v⟩
  invFun a := ⟨fun t => a t.1, by
    rw [Representation.mem_invariants]
    intro sigma
    funext t
    rfl⟩
  map_add' x y := rfl
  map_smul' r x := rfl
  left_inv x := by
    apply Subtype.ext
    funext t
    rcases t with ⟨v, t⟩
    letI := upper_fiber_pretransitive (K := K) (L := L)
      (v : NumberFieldPlace K)
    obtain ⟨sigma, hsigma⟩ := MulAction.exists_smul_eq Gal(L/K) (w v) t
    have hsigmaT : sigma •
        (⟨v, w v⟩ : upperPlacesAt (K := K) (L := L) S) = ⟨v, t⟩ := by
      apply Sigma.ext
      · rfl
      · exact heq_of_eq hsigma
    have h := congrArg (fun f => f (⟨v, w v⟩ :
      upperPlacesAt (K := K) (L := L) S)) (x.2 sigma⁻¹)
    simp only [upper_function_representation, inv_inv] at h
    rw [hsigmaT] at h
    exact h.symm
  right_inv a := rfl

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- On the chosen coordinate of one fibre, the norm counts precisely its
decomposition group. -/
private theorem upper_place_chosen
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)))
    (a : S → ℤ) (v : S) :
    ((upperFunctionRepresentation (K := K) (L := L) S).ρ.norm
        (upperChosenFunction (K := K) (L := L) S w a)) ⟨v, w v⟩ =
      Fintype.card (CompletionPlaceStabilizer
        (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) •
        a v := by
  simp only [Representation.norm, LinearMap.sum_apply]
  change (LinearMap.proj (⟨v, w v⟩ :
      upperPlacesAt (K := K) (L := L) S) :
      (upperPlacesAt (K := K) (L := L) S → ℤ) →ₗ[ℤ] ℤ)
      (∑ sigma : Gal(L/K),
        (upperFunctionRepresentation (K := K) (L := L) S).ρ
          sigma (upperChosenFunction (K := K) (L := L) S w a)) = _
  rw [map_sum]
  simp only [LinearMap.proj_apply,
    upper_function_representation]
  change (∑ sigma : Gal(L/K),
      (Pi.single (w v) (a v) :
        CompletionPlacesAbove (L := L)
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) → ℤ)
        (sigma⁻¹ • w v)) = _
  rw [← Equiv.sum_comp (Equiv.inv Gal(L/K))
    (fun sigma : Gal(L/K) =>
      (Pi.single (w v) (a v) :
        CompletionPlacesAbove (L := L)
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) → ℤ)
        (sigma⁻¹ • w v))]
  simp only [Equiv.inv_apply, inv_inv, Pi.single_apply]
  rw [← Finset.sum_filter]
  simp [Fintype.card_subtype]

/-- In fibre-sum coordinates, the global norm is diagonal, with diagonal
entry the order of the corresponding decomposition group. -/
theorem upper_place_norm
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)))
    (q : (upperFunctionRepresentation
      (K := K) (L := L) S).ρ.Coinvariants) :
    upperPlaceInvariants (K := K) (L := L) S w
        (normCoinvariantsInvariants
          (upperFunctionRepresentation (K := K) (L := L) S) q) =
      fun v : S => Fintype.card (CompletionPlaceStabilizer
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) •
        upperPlaceCoinvariants (K := K) (L := L) S w q v := by
  rw [← coinvariant_chosen_sum (K := K) (L := L) S w q]
  funext v
  change ((upperFunctionRepresentation (K := K) (L := L) S).ρ.norm
      (upperChosenFunction (K := K) (L := L) S w
        (upperCoinvariantSum (K := K) (L := L) S q))) ⟨v, w v⟩ =
    Fintype.card (CompletionPlaceStabilizer
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) •
      upperFiberSum (K := K) (L := L) S
        (upperChosenFunction (K := K) (L := L) S w
          (upperCoinvariantSum (K := K) (L := L) S q)) v
  rw [upper_fiber_chosen]
  exact upper_place_chosen (K := K) (L := L) S w
    (upperCoinvariantSum (K := K) (L := L) S q) v

/-- The product of the residue groups attached to the fibres over `S`. -/
private abbrev UpperPlaceResidues
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :=
  (v : S) → ZMod (Fintype.card (CompletionPlaceStabilizer
    (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)))

/-- Reduce the common integer value on each fibre modulo the order of its
decomposition group. -/
private def upperInvariantResidues
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    (upperFunctionRepresentation
      (K := K) (L := L) S).ρ.invariants →+
      UpperPlaceResidues (K := K) (L := L) S w where
  toFun x v := upperPlaceInvariants (K := K) (L := L) S w x v
  map_zero' := by funext v; simp
  map_add' x y := by funext v; simp

private theorem upper_residues_surjective
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    Function.Surjective
      (upperInvariantResidues (K := K) (L := L) S w) := by
  intro a
  choose z hz using fun v : S => ZMod.intCast_surjective (a v)
  refine ⟨(upperPlaceInvariants (K := K) (L := L) S w).symm z, ?_⟩
  funext v
  change ((upperPlaceInvariants (K := K) (L := L) S w
    ((upperPlaceInvariants (K := K) (L := L) S w).symm z) v : ℤ) :
      ZMod (Fintype.card (CompletionPlaceStabilizer
        (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)))) = a v
  rw [LinearEquiv.apply_symm_apply]
  exact hz v

/-- The norm image is the kernel of simultaneous fibrewise reduction. -/
private theorem upper_place_range
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    (LinearMap.range (normCoinvariantsInvariants
      (upperFunctionRepresentation
        (K := K) (L := L) S))).toAddSubgroup =
      (upperInvariantResidues (K := K) (L := L) S w).ker := by
  ext y
  change y ∈ LinearMap.range
      (normCoinvariantsInvariants
        (upperFunctionRepresentation (K := K) (L := L) S)) ↔
    y ∈ (upperInvariantResidues (K := K) (L := L) S w).ker
  constructor
  · rintro ⟨q, rfl⟩
    rw [AddMonoidHom.mem_ker]
    funext v
    change ((upperPlaceInvariants (K := K) (L := L) S w
      (normCoinvariantsInvariants
        (upperFunctionRepresentation (K := K) (L := L) S) q) v : ℤ) :
          ZMod (Fintype.card (CompletionPlaceStabilizer
            (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)))) = 0
    rw [congrFun (upper_place_norm (K := K) (L := L) S w q) v]
    simp
  · intro hy
    rw [AddMonoidHom.mem_ker] at hy
    have hyv (v : S) :
        ((upperPlaceInvariants (K := K) (L := L) S w y v : ℤ) :
          ZMod (Fintype.card (CompletionPlaceStabilizer
            (coinvariantsInvariantsAbsolute
              (v : NumberFieldPlace K)) (w v)))) = 0 :=
      congrFun hy v
    have hdvd (v : S) :
        (Fintype.card (CompletionPlaceStabilizer
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) : ℤ) ∣
          upperPlaceInvariants (K := K) (L := L) S w y v := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (hyv v)
    choose z hz using hdvd
    refine ⟨(upperPlaceCoinvariants (K := K) (L := L) S w).symm z, ?_⟩
    apply (upperPlaceInvariants (K := K) (L := L) S w).injective
    funext v
    rw [congrFun (upper_place_norm (K := K) (L := L) S w
      ((upperPlaceCoinvariants (K := K) (L := L) S w).symm z)) v,
      LinearEquiv.apply_symm_apply]
    simpa [nsmul_eq_mul] using (hz v).symm

/-- Degree-zero Tate cohomology of the full place lattice is the product of
the residue groups of its transitive fibres. -/
noncomputable def upperPlaceTate
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    tateZero
        (upperFunctionRepresentation (K := K) (L := L) S) ≃+
      UpperPlaceResidues (K := K) (L := L) S w :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (upper_place_range (K := K) (L := L) S w)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (upperInvariantResidues (K := K) (L := L) S w)
      (upper_residues_surjective (K := K) (L := L) S w))

/-- The norm on coinvariants of the full place-permutation lattice is
injective. -/
theorem upper_place_injective
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    Function.Injective (normCoinvariantsInvariants
      (upperFunctionRepresentation (K := K) (L := L) S)) := by
  intro x y hxy
  apply (upperPlaceCoinvariants (K := K) (L := L) S w).injective
  funext v
  have h := congrArg (upperPlaceInvariants (K := K) (L := L) S w) hxy
  have hv := congrFun h v
  rw [congrFun (upper_place_norm (K := K) (L := L) S w x) v,
    congrFun (upper_place_norm (K := K) (L := L) S w y) v] at hv
  have hcard : Fintype.card (CompletionPlaceStabilizer
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) ≠ 0 :=
    Fintype.card_ne_zero
  have hcardInt : (Fintype.card (CompletionPlaceStabilizer
      (coinvariantsInvariantsAbsolute
        (v : NumberFieldPlace K)) (w v)) : ℤ) ≠ 0 := by
    exact_mod_cast hcard
  apply mul_left_cancel₀ hcardInt
  simpa [nsmul_eq_mul] using hv

theorem upper_neg_subsingleton
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    Subsingleton (tateNegOne
      (upperFunctionRepresentation (K := K) (L := L) S)) :=
  ⟨fun x y => Subtype.ext
    (upper_place_injective (K := K) (L := L) S w
      (x.2.trans y.2.symm))⟩

section HerbrandValue

variable [IsCyclic Gal(L/K)]

/-- The first lattice in Milne's proof has Herbrand quotient equal to the
product of the decomposition-group orders over `S`. -/
theorem upper_function_herbrand
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    HerbrandQuotientValue
      (upperFunctionRepresentation (K := K) (L := L) S)
      (∏ v : S, Nat.card (CompletionPlaceStabilizer
        (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v))) := by
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  let e₀ := upperPlaceTate (K := K) (L := L) S w
  letI : Finite (tateZero
      (upperFunctionRepresentation (K := K) (L := L) S)) :=
    Finite.of_equiv (UpperPlaceResidues (K := K) (L := L) S w)
      e₀.symm.toEquiv
  letI : Subsingleton (tateNegOne
      (upperFunctionRepresentation (K := K) (L := L) S)) :=
    upper_neg_subsingleton (K := K) (L := L) S w
  letI : Finite (tateNegOne
      (upperFunctionRepresentation (K := K) (L := L) S)) :=
    inferInstance
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hzero : Nat.card (tateZero
      (upperFunctionRepresentation (K := K) (L := L) S)) =
      ∏ v : S, Nat.card (CompletionPlaceStabilizer
        (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) := by
    calc
      _ = Nat.card (UpperPlaceResidues (K := K) (L := L) S w) :=
        Nat.card_congr e₀.toEquiv
      _ = ∏ v : S, Nat.card (ZMod (Fintype.card
          (CompletionPlaceStabilizer
            (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)))) :=
        Nat.card_pi
      _ = _ := by
        apply Finset.prod_congr rfl
        intro v _
        rw [Nat.card_zmod, Nat.card_eq_fintype_card]
  have hneg : Nat.card (tateNegOne
      (upperFunctionRepresentation (K := K) (L := L) S)) = 1 :=
    Nat.card_unique
  rw [hzero, hneg]
  norm_num

/-- The same calculation for the literal sublattice `N ⊆ Hom(T, ℝ)`. -/
theorem upper_lattice_herbrand
    (S : Finset (NumberFieldPlace K))
    (w : ∀ v : S, CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))) :
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    HerbrandQuotientValue
      (stableLatticeRepresentation
        (placeFunctionRepresentation (K := K) (L := L) S)
        (upperPlaceLattice (K := K) (L := L) S)
        (upper_lattice_stable (K := K) (L := L) S))
      (∏ v : S, Nat.card (CompletionPlaceStabilizer
        (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v))) := by
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  apply (herbrand_value_iso
    (functionStableLattice (K := K) (L := L) S) _).mp
  exact upper_function_herbrand
    (K := K) (L := L) S w

end HerbrandValue

end PlaceFibers

end

end Submission.CField.HQuotie
