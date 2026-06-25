import Mathlib.GroupTheory.GroupAction.Quotient
import Towers.ClassField.Ideles.Ideles
import Towers.ClassField.IdeleCohomology.ConcreteIdeleAction

/-!
# Chapter VII, Section 4, Lemma 4.1

For a finite Galois extension `L/K`, the canonical map on idèle class groups
identifies `C_K` with the subgroup of `G = Gal(L/K)`-fixed classes in `C_L`.

The concrete Galois action on `I_L` is already available in Section 2.  This
file proves that it descends through principal idèles to `C_L`, defines the
canonical quotient map from any compatible idèle-extension map, and reduces
Milne's lemma to the three precise arithmetic interfaces used in its proof:

* construction of the coordinatewise extension map `I_K → I_L`;
* descent of a principal extended idèle to a principal idèle over `K`;
* lifting a fixed idèle class to a fixed idèle, the Hilbert-90 step.
-/

namespace Towers.CField.NIndex

open MulAction
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

private abbrev IK := IdeleGroup (NumberField.RingOfIntegers K) K
private abbrev IL := IdeleGroup (NumberField.RingOfIntegers L) L
private abbrev CK := IdeleClassGroup (NumberField.RingOfIntegers K) K
private abbrev CL := IdeleClassGroup (NumberField.RingOfIntegers L) L

local instance concreteIdeleMulDistribMulAction :
    MulDistribMulAction Gal(L/K)
      (IdeleGroup (NumberField.RingOfIntegers L) L) :=
  idelesGaloisAction (K := K) (L := L)

omit [FiniteDimensional K L] in
/-- The concrete Galois action preserves the subgroup of principal idèles. -/
theorem principal_ideles_smul
    (sigma : Gal(L/K))
    {x : IdeleGroup (NumberField.RingOfIntegers L) L}
    (hx : x ∈ principalIdeles (NumberField.RingOfIntegers L) L) :
    sigma • x ∈ principalIdeles (NumberField.RingOfIntegers L) L := by
  let D := concreteActionData (K := K) (L := L)
  obtain ⟨a, rfl⟩ := hx
  refine ⟨Units.map sigma.toRingEquiv.toRingHom a, ?_⟩
  exact (D.smul_principalIdele sigma a).symm

/-- The quotient-action condition for the principal-idèle subgroup. -/
@[reducible]
noncomputable def principalIdelesAction :
    MulAction.QuotientAction Gal(L/K)
      (principalIdeles (NumberField.RingOfIntegers L) L) := by
  refine ⟨fun sigma x y hxy ↦ ?_⟩
  rw [show (sigma • x)⁻¹ * sigma • y = sigma • (x⁻¹ * y) by
    rw [smul_mul', smul_inv']]
  exact principal_ideles_smul (K := K) (L := L) sigma hxy

local instance principalIdeleQuotientActionInstance :
    MulAction.QuotientAction Gal(L/K)
      (principalIdeles (NumberField.RingOfIntegers L) L) :=
  principalIdelesAction (K := K) (L := L)

/-- The Galois action on `C_L = I_L/L×` induced by the concrete action on
idèles. -/
@[reducible]
noncomputable def ideleGaloisAction :
    MulAction Gal(L/K)
      (IdeleClassGroup (NumberField.RingOfIntegers L) L) := by
  infer_instance

omit [FiniteDimensional K L] in
@[simp]
theorem idele_action_mk
    (sigma : Gal(L/K))
    (x : IdeleGroup (NumberField.RingOfIntegers L) L) :
    letI := ideleGaloisAction (K := K) (L := L)
    sigma • QuotientGroup.mk'
        (principalIdeles (NumberField.RingOfIntegers L) L) x =
      QuotientGroup.mk'
        (principalIdeles (NumberField.RingOfIntegers L) L)
        ((idelesGaloisAction (K := K) (L := L)).smul sigma x) :=
  rfl

/-- The quotient action respects the group law on idèle classes. -/
@[reducible]
noncomputable def ideleDistribAction :
    MulDistribMulAction Gal(L/K)
      (IdeleClassGroup (NumberField.RingOfIntegers L) L) := by
  let qact : MulAction Gal(L/K)
      (IdeleClassGroup (NumberField.RingOfIntegers L) L) := inferInstance
  letI : MulAction Gal(L/K)
      (IdeleClassGroup (NumberField.RingOfIntegers L) L) := qact
  exact
    { qact with
      smul_one := fun sigma ↦ by
        change sigma • QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L)
            (1 : IdeleGroup (NumberField.RingOfIntegers L) L) = _
        change QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers L) L)
              ((idelesGaloisAction (K := K) (L := L)).smul sigma 1) =
          QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers L) L) 1
        exact congrArg
          (QuotientGroup.mk' (principalIdeles (NumberField.RingOfIntegers L) L))
          ((idelesGaloisAction (K := K) (L := L)).smul_one sigma)
      smul_mul := fun sigma a b ↦ by
        refine Quotient.inductionOn₂' a b fun x y ↦ ?_
        change QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers L) L) (sigma • (x * y)) =
          QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers L) L)
              ((sigma • x) * (sigma • y))
        rw [smul_mul'] }

/-- The literal fixed subgroup `C_L^G = H⁰(G,C_L)`. -/
noncomputable def fixedIdeleClasses :
    Subgroup (IdeleClassGroup (NumberField.RingOfIntegers L) L) := by
  letI := ideleDistribAction (K := K) (L := L)
  exact FixedPoints.subgroup Gal(L/K)
    (IdeleClassGroup (NumberField.RingOfIntegers L) L)

omit [FiniteDimensional K L] in
@[simp]
theorem fixed_idele_classes
    (c : IdeleClassGroup (NumberField.RingOfIntegers L) L) :
    c ∈ fixedIdeleClasses (K := K) (L := L) ↔
      letI := ideleGaloisAction (K := K) (L := L)
      ∀ sigma : Gal(L/K), sigma • c = c := by
  rfl

/-- Data characterizing the canonical coordinatewise extension map
`I_K → I_L`.  The first clause is the commutative left square in Milne's
diagram; the second says that an idèle coming from `K` is Galois-fixed. -/
structure IEData where
  toMonoidHom : IK (K := K) →* IL (L := L)
  map_principal (a : Kˣ) :
    toMonoidHom (principalIdele (NumberField.RingOfIntegers K) K a) =
      principalIdele (NumberField.RingOfIntegers L) L
        (Units.map (algebraMap K L) a)
  map_fixed (sigma : Gal(L/K)) (x : IK (K := K)) :
    (idelesGaloisAction (K := K) (L := L)).smul sigma (toMonoidHom x) =
      toMonoidHom x

set_option maxHeartbeats 1000000 in
-- Equality of maps between the dependent restricted products is expensive to elaborate.
omit [FiniteDimensional K L] in
theorem IEData.monoid_homcomp_mainidele
    (E : IEData (K := K) (L := L)) :
    E.toMonoidHom.comp
      (principalIdele (NumberField.RingOfIntegers K) K) =
        (principalIdele (NumberField.RingOfIntegers L) L).comp
          (Units.map (algebraMap K L)) := by
  exact MonoidHom.ext fun a ↦ E.map_principal a

set_option maxHeartbeats 1000000 in
-- Membership in the dependent restricted products is expensive to elaborate.
omit [FiniteDimensional K L] in
theorem IEData.main_ideles_lecomap
    (E : IEData (K := K) (L := L)) :
    principalIdeles (NumberField.RingOfIntegers K) K ≤
      (principalIdeles (NumberField.RingOfIntegers L) L).comap E.toMonoidHom := by
  rw [principalIdeles, principalIdeles, ← Subgroup.map_le_iff_le_comap,
    MonoidHom.map_range, E.monoid_homcomp_mainidele]
  rw [MonoidHom.range_comp]
  exact Subgroup.map_le_range _ _

set_option maxHeartbeats 2000000 in
-- Quotient-group elaboration unfolds the dependent idèle types.
/-- The canonical map `C_K → C_L` induced by a compatible idèle-extension
map. -/
noncomputable def IEData.classMap
    (E : IEData (K := K) (L := L)) : CK (K := K) →* CL (L := L) :=
  QuotientGroup.map
    (principalIdeles (NumberField.RingOfIntegers K) K)
    (principalIdeles (NumberField.RingOfIntegers L) L)
    E.toMonoidHom E.main_ideles_lecomap

omit [FiniteDimensional K L] in
@[simp]
theorem IEData.classMap_mk
    (E : IEData (K := K) (L := L)) (x : IK (K := K)) :
    E.classMap
        (QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers K) K) x) =
      QuotientGroup.mk'
        (principalIdeles (NumberField.RingOfIntegers L) L)
        (E.toMonoidHom x) :=
  QuotientGroup.map_mk' _ _ _ _ _

/-- The canonical class map, with codomain restricted to `C_L^G`. -/
noncomputable def IEData.class_map_fixed
    (E : IEData (K := K) (L := L)) :
    CK (K := K) →* fixedIdeleClasses (K := K) (L := L) where
  toFun c := ⟨E.classMap c, by
    change ∀ sigma : Gal(L/K),
      (ideleDistribAction (K := K) (L := L)).smul
          sigma (E.classMap c) = E.classMap c
    refine Quotient.inductionOn' c fun x sigma ↦ ?_
    calc
      (ideleDistribAction (K := K) (L := L)).smul sigma
          (E.classMap
            (QuotientGroup.mk'
              (principalIdeles (NumberField.RingOfIntegers K) K) x)) =
        (ideleDistribAction (K := K) (L := L)).smul sigma
          (QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers L) L)
            (E.toMonoidHom x)) := congrArg
              ((ideleDistribAction (K := K) (L := L)).smul sigma)
              (E.classMap_mk x)
      _ = QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L)
          ((idelesGaloisAction (K := K) (L := L)).smul sigma
            (E.toMonoidHom x)) := rfl
      _ = QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L)
          (E.toMonoidHom x) := congrArg
            (QuotientGroup.mk' (principalIdeles (NumberField.RingOfIntegers L) L))
            (E.map_fixed sigma x)
      _ = E.classMap
          (QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers K) K) x) :=
              (E.classMap_mk x).symm⟩
  map_one' := Subtype.ext (map_one E.classMap)
  map_mul' x y := Subtype.ext (map_mul E.classMap x y)

/-- Missing restricted-product construction of the coordinatewise canonical
map `I_K → I_L`.  Its two required properties are exactly those stored in
`IEData`. -/
def IdeleExtensionBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    Nonempty (IEData (K := K) (L := L))

/-- Principal descent: an idèle of `K` becomes principal over `L` only when
it was already principal over `K`.  This is the left part of the fixed-point
diagram in Milne's proof. -/
def PrincipalDescentBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : IEData (K := K) (L := L)),
    (principalIdeles (NumberField.RingOfIntegers L) L).comap E.toMonoidHom =
      principalIdeles (NumberField.RingOfIntegers K) K

/-- Fixed-class lifting: every Galois-fixed class in `C_L` has a
representative extended from `I_K`.  This is exactly the `H¹(G,L×)=0`
(Hilbert 90) step of the cohomology sequence. -/
def FixedLiftingBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : IEData (K := K) (L := L)),
    ∀ c : fixedIdeleClasses (K := K) (L := L),
      ∃ x : IK (K := K),
        E.class_map_fixed
          (QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers K) K) x) = c

/-- The three literal inputs above imply the canonical fixed-class
isomorphism. -/
theorem principal_statement_bridges
    (hext : IdeleExtensionBridge.{u})
    (hprincipal : PrincipalDescentBridge.{u})
    (hlift : FixedLiftingBridge.{u}) :
    (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
          ∃ E : IEData (K := K) (L := L),
            Function.Bijective E.class_map_fixed) := by
  intro K L _ _ _ _ _ _ _
  obtain ⟨E⟩ := hext K L
  refine ⟨E, ?_, ?_⟩
  · apply (MonoidHom.ker_eq_bot_iff E.class_map_fixed).mp
    ext c
    constructor
    · intro hc
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
        (principalIdeles (NumberField.RingOfIntegers K) K) c
      have hc' := congrArg Subtype.val hc
      change E.classMap
          (QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers K) K) x) = 1 at hc'
      rw [E.classMap_mk] at hc'
      apply Subgroup.mem_bot.mpr
      apply (QuotientGroup.eq_one_iff x).mpr
      rw [← hprincipal K L E]
      exact (QuotientGroup.eq_one_iff (E.toMonoidHom x)).mp hc'
    · intro hc
      have hc' : c = 1 := Subgroup.mem_bot.mp hc
      subst c
      exact (E.class_map_fixed.ker).one_mem
  · intro c
    obtain ⟨x, hx⟩ := hlift K L E c
    exact ⟨QuotientGroup.mk'
      (principalIdeles (NumberField.RingOfIntegers K) K) x, hx⟩

end

end Towers.CField.NIndex
