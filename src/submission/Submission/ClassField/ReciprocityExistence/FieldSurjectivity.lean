import Submission.ClassField.ReciprocityExistence.FieldCup
import Submission.ClassField.ReciprocityExistence.CharacterBoundary
import Submission.ClassField.LocalBrauer.CohomologyTransport

/-!
# Cyclic surjectivity for the universe-polymorphic field cup

For a cyclic Galois group, the canonical character in chosen `Z/nZ`
coordinates has carry cocycle as its boundary.  Milne's cyclic `H²`
calculation then proves that the literal multiplicative field cup is onto.
-/

namespace Submission.CField.RExist

open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer

noncomputable section

universe u

variable (n : ℕ) [NeZero n]
variable (G : Type u) [Group G] [IsMulCommutative G] [Fintype G]

/-- The normalized cyclic character transported to a cyclic group in an
arbitrary universe. -/
noncomputable def universeTransportedCharacter
    (e : Multiplicative (ZMod n) ≃* G) :
    Additive G →+ AddCircle (1 : ℚ) :=
  (standardCyclicCharacter n).comp
    e.symm.toMonoidHom.toAdditive

omit [IsMulCommutative G] [Fintype G] in
theorem universe_transported_injective
    (e : Multiplicative (ZMod n) ≃* G) :
    Function.Injective
      (universeTransportedCharacter n G e) :=
  (standard_character_injective n).comp e.symm.injective

omit [IsMulCommutative G] [Fintype G] in
/-- The canonical `[0,1)` lift is the usual representative `g.val / n`. -/
theorem rational_universe_transported
    (e : Multiplicative (ZMod n) ≃* G) (g : G) :
    rationalCharacterLift
        (universeTransportedCharacter n G e) g =
      ((e.symm g).toAdd.val : ℚ) / n := by
  let q : ℚ := ((e.symm g).toAdd.val : ℚ) / n
  have hn : (0 : ℚ) < n := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have hval : ((e.symm g).toAdd.val : ℚ) < n := by
    exact_mod_cast (e.symm g).toAdd.val_lt
  have hq : q ∈ Set.Ico (0 : ℚ) (0 + 1) := by
    constructor
    · exact div_nonneg (by positivity) hn.le
    · simpa [q] using (div_lt_one hn).2 hval
  change (AddCircle.equivIco (1 : ℚ) 0
      (standardCyclicCharacter n
        (Additive.ofMul (e.symm g)))).1 = q
  rw [standard_cyclic_character]
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hq)

omit [IsMulCommutative G] [Fintype G] in
/-- The integral boundary exponent of the transported normalized character
is Milne's carry bit. -/
theorem universe_transported_standard
    (e : Multiplicative (ZMod n) ≃* G) (g h : G) :
    rationalBoundaryExponent
        (universeTransportedCharacter n G e) g h =
      (CCarry.carry (e.symm g).toAdd (e.symm h).toAdd : ℤ) := by
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hcarry := CCarry.val_add_carry
    (e.symm g).toAdd (e.symm h).toAdd
  have hcarryQ :
      ((((e.symm g).toAdd + (e.symm h).toAdd).val : ℚ) +
          (n : ℚ) *
            (CCarry.carry (e.symm g).toAdd
              (e.symm h).toAdd : ℚ)) =
        ((e.symm g).toAdd.val : ℚ) + ((e.symm h).toAdd.val : ℚ) := by
    exact_mod_cast hcarry
  have hq :
      ((rationalBoundaryExponent
          (universeTransportedCharacter n G e) g h : ℤ) : ℚ) =
        ((CCarry.carry (e.symm g).toAdd
          (e.symm h).toAdd : ℕ) : ℚ) := by
    rw [rational_boundary_spec,
      rational_universe_transported,
      rational_universe_transported,
      rational_universe_transported,
      e.symm.map_mul]
    change ((e.symm h).toAdd.val : ℚ) / n -
        (((e.symm g).toAdd + (e.symm h).toAdd).val : ℚ) / n +
        ((e.symm g).toAdd.val : ℚ) / n = _
    field_simp
    linarith
  exact_mod_cast hq

variable (M : Type u) [CommGroup M] [MulDistribMulAction G M]

/-- The multiplicative carry class transported back from the chosen cyclic
coordinates. -/
noncomputable def universeTransportedCarry
    (e : Multiplicative (ZMod n) ≃* G)
    (pi : GroupH2.pulledInvariants (M := M) e) :
    MHTwo G M := by
  letI : MulDistribMulAction (Multiplicative (ZMod n)) M :=
    GroupH2.pulledAction e
  exact (GroupH2.hCyclicModel (M := M) e).symm
    (MHTwo.mk (CCarry.factorSet pi.1 pi.2))

omit [IsMulCommutative G] [Fintype G] in
/-- Cupping an invariant with the transported character gives precisely
the transported carry class. -/
theorem invariant_universe_transported
    (e : Multiplicative (ZMod n) ≃* G)
    (pi : GroupH2.pulledInvariants (M := M) e) :
    let piG := GroupH2.invariantsMulEquiv e pi
    invariantCharacterCup piG.1 piG.2
        (universeTransportedCharacter n G e) =
      universeTransportedCarry n G M e pi := by
  letI : MulDistribMulAction (Multiplicative (ZMod n)) M :=
    GroupH2.pulledAction e
  dsimp only
  rw [invariantCharacterCup,
    universeTransportedCarry]
  change MHTwo.mk _ =
    MHTwo.mk
      (MHTrans.cocycleMap e (MulEquiv.refl M)
        (by intro g m; rfl) (CCarry.factorSet pi.1 pi.2))
  congr 1
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  change pi.1 ^ rationalBoundaryExponent
      (universeTransportedCharacter n G e) g h =
    pi.1 ^ (CCarry.carry (e.symm g).toAdd (e.symm h).toAdd : ℕ)
  rw [universe_transported_standard]
  rw [zpow_natCast]

omit [IsMulCommutative G] [Fintype G] in
private theorem multiplicative_subsingleton_cyclic
    (e : Multiplicative (ZMod n) ≃* G) (h : n = 1) :
    Subsingleton (MHTwo G M) := by
  subst n
  have hG : ∀ g k : G, g = k := by
    intro g k
    apply e.symm.injective
    exact Subsingleton.elim _ _
  constructor
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | _ c d =>
      apply congrArg MHTwo.mk
      apply NMCocycl₂.ext
      rintro ⟨g, k⟩
      rw [hG g 1, hG k 1, c.map_one_fst, d.map_one_fst]

section GlobalField

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative Gal(L/K)]

attribute [local instance] Units.mulDistribMulActionRight

omit [IsMulCommutative Gal(L/K)] in
/-- Every Galois-invariant unit of `L` comes from a unit of `K`, in the
universe-polymorphic setting used by Theorem VII.8.1. -/
theorem global_multiplicative_surjective :
    ∀ x : FMAct.invariants Gal(L/K) Lˣ,
      ∃ a : Kˣ, Units.map (algebraMap K L).toMonoidHom a = x.1 := by
  intro x
  have hfixed : ∀ sigma : Gal(L/K), sigma (x.1 : L) = (x.1 : L) := by
    intro sigma
    exact congrArg Units.val (x.2 sigma)
  obtain ⟨a, ha⟩ :=
    (IsGalois.mem_range_algebraMap_iff_fixed
      (F := K) (E := L) (x.1 : L)).2 hfixed
  have ha0 : a ≠ 0 := by
    intro ha0
    rw [ha0, map_zero] at ha
    exact x.1.ne_zero ha.symm
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Units.ext
  exact ha

omit [IsMulCommutative Gal(L/K)] in
/-- The literal multiplicative field cup is surjective for the transported
normalized cyclic character. -/
theorem global_multiplicative_transported
    (e : Multiplicative (ZMod n) ≃* Gal(L/K)) :
    Function.Surjective
      (multiplicativeFieldCup K L
        (universeTransportedCharacter n Gal(L/K) e)) := by
  intro beta
  by_cases htrivial : n = 1
  · have hsub := multiplicative_subsingleton_cyclic
      n Gal(L/K) Lˣ e htrivial
    refine ⟨0, ?_⟩
    apply Additive.toMul.injective
    apply (CProduc.hRelativeBrauer K L).symm.injective
    exact hsub.elim _ _
  · have hn : 1 < n := by
      have hn0 := NeZero.ne n
      omega
    let pull := GroupH2.hCyclicModel (M := Lˣ) e
    letI : MulDistribMulAction (Multiplicative (ZMod n)) Lˣ :=
      GroupH2.pulledAction e
    let cyclic := CyclicH2.mulInvariantsMod
      (n := n) (M := Lˣ) hn
    let x : MHTwo Gal(L/K) Lˣ :=
      (CProduc.hRelativeBrauer K L).symm beta.toMul
    obtain ⟨pi, hpi⟩ := QuotientGroup.mk'_surjective
      (CyclicH2.norm (n := n) (M := Lˣ)).range (cyclic (pull x))
    have hxcarry :
        x = universeTransportedCarry
          n Gal(L/K) Lˣ e pi := by
      rw [universeTransportedCarry]
      rw [← CyclicH2.symm_mk_carry (n := n) (M := Lˣ) hn pi]
      apply pull.injective
      rw [pull.apply_symm_apply]
      apply cyclic.injective
      rw [cyclic.apply_symm_apply]
      exact hpi.symm
    let piG := GroupH2.invariantsMulEquiv e pi
    obtain ⟨a, ha⟩ := global_multiplicative_surjective K L piG
    refine ⟨Additive.ofMul a, ?_⟩
    apply Additive.toMul.injective
    apply (CProduc.hRelativeBrauer K L).symm.injective
    rw [multiplicative_field_cup,
      (CProduc.hRelativeBrauer K L).symm_apply_apply]
    change multiplicativeCupClass K L a
        (universeTransportedCharacter n Gal(L/K) e) = x
    rw [multiplicativeCupClass]
    have hcup := invariant_universe_transported
      n Gal(L/K) Lˣ e pi
    change invariantCharacterCup
        (Units.map (algebraMap K L).toMonoidHom a) _
          (universeTransportedCharacter n Gal(L/K) e) = x
    calc
      invariantCharacterCup
          (Units.map (algebraMap K L).toMonoidHom a) _
          (universeTransportedCharacter n Gal(L/K) e) =
        invariantCharacterCup piG.1 piG.2
          (universeTransportedCharacter n Gal(L/K) e) := by
            unfold invariantCharacterCup
            apply congrArg MHTwo.mk
            apply NMCocycl₂.ext
            rintro ⟨g, h⟩
            change (Units.map (algebraMap K L).toMonoidHom a) ^
                rationalBoundaryExponent
                  (universeTransportedCharacter
                    n Gal(L/K) e) g h =
              piG.1 ^ rationalBoundaryExponent
                (universeTransportedCharacter
                  n Gal(L/K) e) g h
            rw [ha]
      _ = universeTransportedCarry
          n Gal(L/K) Lˣ e pi := hcup
      _ = x := hxcarry.symm

omit [IsMulCommutative Gal(L/K)] in
/-- A finite cyclic Galois extension admits an injective character for
which the literal universe-polymorphic field cup is surjective. -/
theorem multiplicative_cup_surjective
    [IsCyclic Gal(L/K)] :
    ∃ chi : Additive Gal(L/K) →+ AddCircle (1 : ℚ),
      Function.Injective chi ∧
        Function.Surjective (multiplicativeFieldCup K L chi) := by
  let n := Nat.card Gal(L/K)
  letI : NeZero n := ⟨Nat.card_pos.ne'⟩
  let e : Multiplicative (ZMod n) ≃* Gal(L/K) :=
    zmodCyclicMulEquiv (inferInstance : IsCyclic Gal(L/K))
  exact ⟨universeTransportedCharacter n Gal(L/K) e,
    universe_transported_injective n Gal(L/K) e,
    global_multiplicative_transported n K L e⟩

end GlobalField

end

end Submission.CField.RExist
