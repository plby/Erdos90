import Towers.ClassField.LocalReciprocity.CyclicParameter
import Towers.ClassField.LocalReciprocity.CupPairing
import Towers.ClassField.ReciprocityExistence.FieldSurjectivity
import Towers.ClassField.ReciprocityExistence.CyclicTransport

/-!
# The cyclic normalized-character case of Proposition III.3.6

This file joins the explicit degree-minus-two formula for the local Artin
map to the carry-cocycle description of cup product with the normalized
character of a cyclic Galois group.
-/

namespace Towers.CField.LRecip

open scoped IsMulCommutative

open Towers.CField.LFTheory
open Towers.CField.LClass
open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.RExist

noncomputable section

universe u

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance cyclicValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance cyclicValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative Gal(L/K)]

attribute [local instance] Units.mulDistribMulActionRight

/-- For an abelian extension, the defining inverse relation between the
local Artin map and the norm-residue map, written on representatives. -/
theorem abelian_artin_residue
    (a : Kˣ) (g : Gal(L/K)) :
    abelianArtinHom K L a = g ↔
      localNormResidue K L (Abelianization.of g) =
        QuotientGroup.mk' (normSubgroup K L) a := by
  constructor
  · intro h
    have h' := congrArg (abelianLocalArtin K L).symm h
    simpa [abelianArtinHom, abelianLocalArtin,
      localArtinEquiv, localNormResidue] using h'.symm
  · intro h
    apply (abelianLocalArtin K L).symm.injective
    simpa [abelianArtinHom, abelianLocalArtin,
      localArtinEquiv, localNormResidue] using h.symm

variable {n : ℕ} [NeZero n]

/-- The transported carry class is the inverse image of its invariant
coefficient under the cyclic `H² ≃ Mᴳ/NM` equivalence. -/
theorem universe_transported_carry
    {G M : Type u} [CommGroup G] [Fintype G]
    [CommGroup M] [MulDistribMulAction G M]
    (hn : 1 < n) (e : Multiplicative (ZMod n) ≃* G)
    (pi : GroupH2.pulledInvariants (M := M) e) :
    GroupH2.mulInvariantsMod (M := M) e hn
        (universeTransportedCarry n G M e pi) =
      QuotientGroup.mk' (FMAct.norm G M).range
        (GroupH2.invariantsMulEquiv e pi) := by
  letI : MulDistribMulAction (Multiplicative (ZMod n)) M :=
    GroupH2.pulledAction e
  let pull := GroupH2.hCyclicModel (M := M) e
  let cyclic := CyclicH2.mulInvariantsMod
    (n := n) (M := M) hn
  rw [universeTransportedCarry]
  change GroupH2.invariantsModEquiv e
      (cyclic (pull (pull.symm
        (MHTwo.mk (CCarry.factorSet pi.1 pi.2))))) = _
  rw [pull.apply_symm_apply]
  rw [← CyclicH2.symm_mk_carry (n := n) (M := M) hn pi]
  rw [cyclic.apply_symm_apply]
  rfl

omit [IsGalois K L] [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
/-- The cyclic parameter of the literal field cup is the class of its base
unit modulo the norm. -/
theorem cyclic_multiplicative_cup
    (hn : 1 < n) (e : Multiplicative (ZMod n) ≃* Gal(L/K)) (a : Kˣ) :
    GroupH2.mulInvariantsMod (M := Lˣ) e hn
        (multiplicativeCupClass K L a
          (universeTransportedCharacter n Gal(L/K) e)) =
      QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range
        ⟨Units.map (algebraMap K L).toMonoidHom a,
          multiplicative_base_fixed K L a⟩ := by
  let piG : FMAct.invariants Gal(L/K) Lˣ :=
    ⟨Units.map (algebraMap K L).toMonoidHom a,
      multiplicative_base_fixed K L a⟩
  let pi : GroupH2.pulledInvariants (M := Lˣ) e :=
    (GroupH2.invariantsMulEquiv e).symm piG
  have hcup := invariant_universe_transported
    n Gal(L/K) Lˣ e pi
  have hcup' :
      multiplicativeCupClass K L a
          (universeTransportedCharacter n Gal(L/K) e) =
        universeTransportedCarry
          n Gal(L/K) Lˣ e pi := by
    simpa [multiplicativeCupClass, pi, piG] using hcup
  rw [hcup', universe_transported_carry hn e pi]
  rfl

/-- If a base unit has the chosen cyclic generator as its local Artin
symbol, cupping it with the normalized cyclic character gives the local
fundamental class. -/
theorem global_multiplicative_generator
    (hn : 1 < n) (e : Multiplicative (ZMod n) ≃* Gal(L/K))
    (a : Kˣ)
    (ha : abelianArtinHom K L a =
      e (Multiplicative.ofAdd (1 : ZMod n))) :
    multiplicativeCupClass K L a
        (universeTransportedCharacter n Gal(L/K) e) =
      multiplicativeFundamentalClass K L := by
  let s : Gal(L/K) := e (Multiplicative.ofAdd (1 : ZMod n))
  let piG : FMAct.invariants Gal(L/K) Lˣ :=
    ⟨Units.map (algebraMap K L).toMonoidHom a,
      multiplicative_base_fixed K L a⟩
  let pi : GroupH2.pulledInvariants (M := Lˣ) e :=
    (GroupH2.invariantsMulEquiv e).symm piG
  have hcup := invariant_universe_transported
    n Gal(L/K) Lˣ e pi
  have hcup' :
      multiplicativeCupClass K L a
          (universeTransportedCharacter n Gal(L/K) e) =
        universeTransportedCarry
          n Gal(L/K) Lˣ e pi := by
    simpa [multiplicativeCupClass, pi, piG] using hcup
  let cyclic := GroupH2.mulInvariantsMod
    (M := Lˣ) e hn
  apply cyclic.injective
  rw [hcup', universe_transported_carry hn e pi]
  rw [← mk_fundamental_cocycle K L]
  rw [cyclic_invariants_mk hn e]
  change QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range piG =
    QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range
      (NMCocycl₂.cyclicProductInvariant
        (localFundamentalCocycle K L) s)
  rw [← local_cyclic_invariant K L s]
  have hnorm : localNormResidue K L (Abelianization.of s) =
      QuotientGroup.mk' (normSubgroup K L) a :=
    (abelian_artin_residue K L a s).mp ha
  have hparameter := local_cyclic_product K L s
  apply (galoisInvariantsMod K L).injective
  calc
    galoisInvariantsMod K L
        (QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range piG) =
        QuotientGroup.mk' (normSubgroup K L) a := by
          exact galois_invariants_algebra K L a
    _ = localNormResidue K L (Abelianization.of s) := hnorm.symm
    _ = galoisInvariantsMod K L
        (QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range
          (localCyclicInvariant K L s)) := by
          rw [← hparameter]
          exact
            (galoisInvariantsMod K L).apply_symm_apply _ |>.symm

/-- For every base unit in a nontrivial cyclic extension, its normalized
character cup is the corresponding power of the local fundamental class. -/
theorem global_multiplicative_fundamental
    (hn : 1 < n) (e : Multiplicative (ZMod n) ≃* Gal(L/K)) (a : Kˣ) :
    multiplicativeCupClass K L a
        (universeTransportedCharacter n Gal(L/K) e) =
      multiplicativeFundamentalClass K L ^
        (e.symm (abelianArtinHom K L a)).toAdd.val := by
  let g := abelianArtinHom K L a
  let z := e.symm g
  let k := z.toAdd.val
  let s : Gal(L/K) := e (Multiplicative.ofAdd (1 : ZMod n))
  have hpow : s ^ k = g := by
    calc
      s ^ k = e (Multiplicative.ofAdd (1 : ZMod n) ^ k) := by
        exact (map_pow e (Multiplicative.ofAdd (1 : ZMod n)) k).symm
      _ = e z := congrArg e (CyclicH2.generator_pow_val z).symm
      _ = g := e.apply_symm_apply g
  let cyclic := GroupH2.mulInvariantsMod
    (M := Lˣ) e hn
  let invNorm := galoisInvariantsMod K L
  have hfund : cyclic (multiplicativeFundamentalClass K L) =
      invNorm.symm
        (localNormResidue K L (Abelianization.of s)) := by
    rw [← mk_fundamental_cocycle K L]
    rw [cyclic_invariants_mk hn e]
    change QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range
        (NMCocycl₂.cyclicProductInvariant
          (localFundamentalCocycle K L) s) = _
    rw [← local_cyclic_invariant K L s]
    exact (local_cyclic_product K L s).symm
  have hnorm : localNormResidue K L (Abelianization.of g) =
      QuotientGroup.mk' (normSubgroup K L) a :=
    (abelian_artin_residue K L a g).mp rfl
  apply cyclic.injective
  rw [cyclic_multiplicative_cup K L hn e a,
    map_pow, hfund]
  apply invNorm.injective
  rw [map_pow, invNorm.apply_symm_apply]
  calc
    invNorm
        (QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range
          ⟨Units.map (algebraMap K L).toMonoidHom a,
            multiplicative_base_fixed K L a⟩) =
        QuotientGroup.mk' (normSubgroup K L) a :=
      galois_invariants_algebra K L a
    _ = localNormResidue K L (Abelianization.of g) := hnorm.symm
    _ = (localNormResidue K L (Abelianization.of s)) ^ k := by
      rw [← map_pow, ← map_pow, hpow]

/-- Proposition III.3.6 for the normalized character and an element whose
Artin symbol is the chosen cyclic generator, in the literal multiplicative
cup presentation used in Chapter VII. -/
theorem multiplicative_cup_generator
    (hn : 1 < n) (e : Multiplicative (ZMod n) ≃* Gal(L/K))
    (a : Kˣ)
    (ha : abelianArtinHom K L a =
      e (Multiplicative.ofAdd (1 : ZMod n))) :
    ((relativeHTorsion K L
        (multiplicativeCupClass K L a
          (universeTransportedCharacter n Gal(L/K) e)) :
          invariantPowTorsion (Module.finrank K L)) :
        Multiplicative LocalInvariant).toAdd =
      universeTransportedCharacter n Gal(L/K) e
        (Additive.ofMul (abelianArtinHom K L a)) := by
  rw [global_multiplicative_generator K L hn e a ha]
  rw [invariant_torsion_coe,
    h_brauer_fundamental,
    relative_fundamental_coe,
    canonical_carry_brauer]
  rw [ha]
  have hnrank : n = Module.finrank K L := by
    calc
      n = Fintype.card (Multiplicative (ZMod n)) := by simp
      _ = Fintype.card Gal(L/K) := Fintype.card_congr e.toEquiv
      _ = Module.finrank K L := by
        simpa [Nat.card_eq_fintype_card] using
          (IsGalois.card_aut_eq_finrank K L)
  rw [show universeTransportedCharacter n Gal(L/K) e
      (Additive.ofMul (e (Multiplicative.ofAdd (1 : ZMod n)))) =
        standardCyclicCharacter n
          (Additive.ofMul (Multiplicative.ofAdd (1 : ZMod n))) by
    change standardCyclicCharacter n
        (Additive.ofMul (e.symm (e (Multiplicative.ofAdd (1 : ZMod n))))) = _
    rw [e.symm_apply_apply]]
  change ((1 : ℚ) / (Module.finrank K L : ℚ) : LocalInvariant) =
    standardCyclicCharacter n
      (Additive.ofMul (Multiplicative.ofAdd (1 : ZMod n)))
  rw [standard_cyclic_character]
  change ((1 : ℚ) / (Module.finrank K L : ℚ) : LocalInvariant) =
    (((((1 : ZMod n).val : ℕ) : ℚ) / n : ℚ) : LocalInvariant)
  letI : Fact (1 < n) := ⟨hn⟩
  rw [ZMod.val_one, ← hnrank]
  norm_num

/-- Proposition III.3.6 for the normalized injective character of any
nontrivial cyclic local extension and every base-field unit. -/
theorem multiplicative_cup_cyclic
    (hn : 1 < n) (e : Multiplicative (ZMod n) ≃* Gal(L/K)) (a : Kˣ) :
    ((relativeHTorsion K L
        (multiplicativeCupClass K L a
          (universeTransportedCharacter n Gal(L/K) e)) :
          invariantPowTorsion (Module.finrank K L)) :
        Multiplicative LocalInvariant).toAdd =
      universeTransportedCharacter n Gal(L/K) e
        (Additive.ofMul (abelianArtinHom K L a)) := by
  let k := (e.symm (abelianArtinHom K L a)).toAdd.val
  rw [global_multiplicative_fundamental K L hn e a, map_pow]
  have hfundInv :
      ((relativeHTorsion K L
          (multiplicativeFundamentalClass K L) :
            invariantPowTorsion (Module.finrank K L)) :
          Multiplicative LocalInvariant) =
        Multiplicative.ofAdd
          ((1 : ℚ) / (Module.finrank K L : ℚ) : LocalInvariant) := by
    rw [invariant_torsion_coe,
      h_brauer_fundamental,
      relative_fundamental_coe,
      canonical_carry_brauer]
  change
    (((((relativeHTorsion K L
        (multiplicativeFundamentalClass K L) :
          invariantPowTorsion (Module.finrank K L)) :
        Multiplicative LocalInvariant) ^ k).toAdd) = _)
  rw [hfundInv]
  have hrhs :
      universeTransportedCharacter n Gal(L/K) e
          (Additive.ofMul (abelianArtinHom K L a)) =
        standardCyclicCharacter n
          (Additive.ofMul
            (e.symm (abelianArtinHom K L a))) := by
    rfl
  rw [hrhs, standard_cyclic_character]
  have hnrank : n = Module.finrank K L := by
    calc
      n = Fintype.card (Multiplicative (ZMod n)) := by simp
      _ = Fintype.card Gal(L/K) := Fintype.card_congr e.toEquiv
      _ = Module.finrank K L := by
        simpa [Nat.card_eq_fintype_card] using
          (IsGalois.card_aut_eq_finrank K L)
  change k • ((1 : ℚ) / (Module.finrank K L : ℚ) : LocalInvariant) =
    ((((k : ℕ) : ℚ) / n : ℚ) : LocalInvariant)
  rw [← hnrank]
  change (((k : ℚ) * (1 / n) : ℚ) : LocalInvariant) =
    (((k : ℚ) / n : ℚ) : LocalInvariant)
  congr 1
  ring

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] [IsGalois K L]
  [IsMulCommutative Gal(L/K)] in
/-- In cyclic coordinates, the categorical cup constructed in the literal
statement of Proposition III.3.6 is the additive realization of the
multiplicative cup cocycle used in Chapter VII. -/
theorem cup_boundary_multiplicative
    (e : Multiplicative (ZMod n) ≃* Gal(L/K)) (a : Kˣ) :
    cupCharacterBoundary K L a
        (transportedStandardCharacter n Gal(L/K) e) =
      multiplicative2Additive
        (multiplicativeCupClass K L a
          (universeTransportedCharacter n Gal(L/K) e)) := by
  let piG : FMAct.invariants Gal(L/K) Lˣ :=
    ⟨Units.map (algebraMap K L).toMonoidHom a,
      multiplicative_base_fixed K L a⟩
  let pi : GroupH2.pulledInvariants (M := Lˣ) e :=
    (GroupH2.invariantsMulEquiv e).symm piG
  have hcat := transported_boundary_carry
    n Gal(L/K) Lˣ e pi
  have hmul := invariant_universe_transported
    n Gal(L/K) Lˣ e pi
  calc
    cupCharacterBoundary K L a
        (transportedStandardCharacter n Gal(L/K) e) =
      transportedCyclicBoundary n Gal(L/K) Lˣ e
        (baseUnitInvariant K L a) := by rfl
    _ = multiplicative2Additive
        (universeTransportedCarry
          n Gal(L/K) Lˣ e pi) := by
      simpa [pi, piG, baseUnitInvariant] using hcat
    _ = multiplicative2Additive
        (multiplicativeCupClass K L a
          (universeTransportedCharacter n Gal(L/K) e)) := by
      apply congrArg multiplicative2Additive
      simpa [multiplicativeCupClass, pi, piG] using hmul.symm

/-- The literal `CharacterFormula` of Proposition III.3.6 for the normalized
injective character of a nontrivial cyclic extension. -/
theorem character_formula_normalized
    (hn : 1 < n) (e : Multiplicative (ZMod n) ≃* Gal(L/K)) (a : Kˣ) :
    CharacterFormula K L a
      (transportedStandardCharacter n Gal(L/K) e) := by
  unfold CharacterFormula characterCupInvariant invariantH2
  rw [cup_boundary_multiplicative K L e a]
  let cup := multiplicativeCupClass K L a
    (universeTransportedCharacter n Gal(L/K) e)
  have hcomparison :
      (multiplicativeHCohomology
        (G := Gal(L/K)) (M := Lˣ)).symm
          (Multiplicative.ofAdd (multiplicative2Additive cup)) = cup :=
    (multiplicativeHCohomology
      (G := Gal(L/K)) (M := Lˣ)).symm_apply_apply cup
  rw [hcomparison]
  exact (multiplicative_cup_cyclic K L hn e a).symm

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative Gal(L/K)] in
private theorem cyclicCoordinate_generator
    (e : Multiplicative (ZMod n) ≃* Gal(L/K)) :
    ∀ g : Gal(L/K),
      g ∈ Subgroup.zpowers (e (Multiplicative.ofAdd (1 : ZMod n))) := by
  intro g
  refine ⟨((e.symm g).toAdd.val : ℤ), ?_⟩
  calc
    (e (Multiplicative.ofAdd (1 : ZMod n))) ^
        (e.symm g).toAdd.val =
        e ((Multiplicative.ofAdd (1 : ZMod n)) ^
          (e.symm g).toAdd.val) :=
      (map_pow e (Multiplicative.ofAdd (1 : ZMod n))
        (e.symm g).toAdd.val).symm
    _ = e (e.symm g) := by
      apply congrArg e
      apply Multiplicative.toAdd.injective
      simp
    _ = g := e.apply_symm_apply g

private theorem rational_character_zsmul
    {J : Type} [CommGroup J] [Finite J]
    (g : J) (hg : ∀ x : J, x ∈ Subgroup.zpowers g)
    (chi : RationalCharacter J) :
    ∃ j : ℤ, chi = j •
      multiplicativeRationalCharacter J g hg := by
  letI : Fintype J := Fintype.ofFinite J
  let m := Nat.card J
  let psi := multiplicativeRationalCharacter J g hg
  have hm : 0 < m := Nat.card_pos
  have htors : m • chi (Additive.ofMul g) = 0 := by
    calc
      m • chi (Additive.ofMul g) =
          chi (m • Additive.ofMul g) := (map_nsmul chi m _).symm
      _ = chi (Additive.ofMul (g ^ m)) := rfl
      _ = 0 := by rw [pow_card_eq_one']; exact map_zero chi
  obtain ⟨r, _, hvalue⟩ :=
    (AddCircle.nsmul_eq_zero_iff (p := (1 : ℚ)) hm).mp htors
  let j : ℤ := r
  have hpsi : psi (Additive.ofMul g) =
      (((m : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)) := by
    simp [psi, m, Nat.card_eq_fintype_card]
  have heval : chi (Additive.ofMul g) = j • psi (Additive.ofMul g) := by
    rw [hpsi, ← hvalue, ← AddCircle.coe_zsmul]
    congr 1
    simp [j, div_eq_mul_inv]
  refine ⟨j, ?_⟩
  apply AddMonoidHom.ext
  intro x
  obtain ⟨k, hk⟩ := hg x.toMul
  have hx : x = k • Additive.ofMul g := by
    apply Additive.toMul.injective
    simpa using hk.symm
  rw [hx, map_zsmul, heval, map_zsmul]
  rfl

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
/-- The generator-normalized character defined intrinsically from a cyclic
group agrees with the same character transported from `ZMod n`. -/
theorem multiplicative_character_transported
    (hn : 1 < n) (e : Multiplicative (ZMod n) ≃* Gal(L/K)) :
    multiplicativeRationalCharacter Gal(L/K)
        (e (Multiplicative.ofAdd (1 : ZMod n)))
        (cyclicCoordinate_generator K L e) =
      transportedStandardCharacter n Gal(L/K) e := by
  let g : Gal(L/K) := e (Multiplicative.ofAdd (1 : ZMod n))
  let hg := cyclicCoordinate_generator K L e
  apply AddMonoidHom.ext
  intro x
  obtain ⟨j, hj⟩ := hg x.toMul
  have hx : x = j • Additive.ofMul g := by
    apply Additive.toMul.injective
    simpa using hj.symm
  subst x
  rw [map_zsmul, map_zsmul]
  congr 1
  change
    (multiplicativeRationalCharacter Gal(L/K)
        (e (Multiplicative.ofAdd (1 : ZMod n)))
        (cyclicCoordinate_generator K L e))
          (Additive.ofMul (e (Multiplicative.ofAdd (1 : ZMod n)))) =
      transportedStandardCharacter n Gal(L/K) e
        (Additive.ofMul (e (Multiplicative.ofAdd (1 : ZMod n))))
  rw [multiplicative_rational_character]
  have hncard : Nat.card Gal(L/K) = n := by
    calc
      Nat.card Gal(L/K) = Nat.card (Multiplicative (ZMod n)) :=
        Nat.card_congr e.symm.toEquiv
      _ = n := by simp [Nat.card_eq_fintype_card]
  rw [show transportedStandardCharacter n Gal(L/K) e
      (Additive.ofMul g) =
        standardCyclicCharacter n
          (Additive.ofMul (Multiplicative.ofAdd (1 : ZMod n))) by
    change standardCyclicCharacter n
        (Additive.ofMul (e.symm (e (Multiplicative.ofAdd (1 : ZMod n))))) = _
    rw [e.symm_apply_apply]]
  rw [standard_cyclic_character]
  letI : Fact (1 < n) := ⟨hn⟩
  simp only [toMul_ofMul, toAdd_ofAdd, ZMod.val_one n]
  change (((Nat.card Gal(L/K) : ℚ)⁻¹ : ℚ) : LocalInvariant) =
    (((1 : ℚ) / n : ℚ) : LocalInvariant)
  rw [hncard]
  congr 1
  field_simp

/-- Proposition III.3.6 for every character of a nontrivial cyclic local
extension. -/
theorem characterFormula_cyclic
    (hn : 1 < n) (e : Multiplicative (ZMod n) ≃* Gal(L/K))
    (a : Kˣ) (chi : RationalCharacter Gal(L/K)) :
    CharacterFormula K L a chi := by
  let g : Gal(L/K) := e (Multiplicative.ofAdd (1 : ZMod n))
  let hg := cyclicCoordinate_generator K L e
  obtain ⟨j, hchi⟩ :=
    rational_character_zsmul g hg chi
  let psi := transportedStandardCharacter n Gal(L/K) e
  have hgen : multiplicativeRationalCharacter Gal(L/K) g hg = psi :=
    multiplicative_character_transported K L hn e
  have hchi' : chi = j • psi := hchi.trans (congrArg (j • ·) hgen)
  rw [hchi']
  let cupInCharacter : RationalCharacter Gal(L/K) →+ LocalInvariant :=
    { toFun := fun eta ↦ characterCupInvariant K L a eta
      map_zero' := by
        have h := character_cup_add K L a
          (0 : RationalCharacter Gal(L/K)) 0
        apply add_left_cancel
          (a := characterCupInvariant K L a
            (0 : RationalCharacter Gal(L/K)))
        rw [add_zero, ← h, zero_add]
      map_add' := fun eta theta ↦
        character_cup_add K L a eta theta }
  have hnormalized := character_formula_normalized K L hn e a
  have hcup := cupInCharacter.map_zsmul j psi
  change (j • psi)
      (Additive.ofMul (abelianArtinHom K L a)) =
    characterCupInvariant K L a (j • psi)
  rw [show (j • psi)
      (Additive.ofMul (abelianArtinHom K L a)) =
        j • psi (Additive.ofMul (abelianArtinHom K L a)) by
    rfl]
  rw [hnormalized]
  exact hcup.symm

end

end Towers.CField.LRecip
