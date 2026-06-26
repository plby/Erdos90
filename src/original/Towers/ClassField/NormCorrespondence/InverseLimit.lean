import Towers.ClassField.NormCorrespondence.LocalStatement
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Assembling compatible finite abelian reciprocity maps

The topological abelianization of the absolute Galois group is the Galois
group of the fixed field of the closure of the commutator subgroup.  Its
finite Galois subextensions are therefore abelian.  This file packages a
compatible family of homomorphisms to those finite Galois groups as a point
of their inverse limit and transports it back to the topological
abelianization.

This is the formal inverse-limit step in the construction of the local Artin
map.  The arithmetic construction and compatibility of the finite maps are
deliberately inputs here.
-/

namespace Towers.CField.LFTheory

noncomputable section

open CategoryTheory Opposite
open CategoryTheory.Limits
open FiniteGaloisIntermediateField ProfiniteGrp
open scoped commutatorElement

universe u

variable (K : Type u) [Field K]

/-- The maximal abelian subextension of the chosen separable closure,
realized as the fixed field of the closed commutator subgroup. -/
def maximalAbelianIntermediate :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.fixedField
    (Subgroup.topologicalClosure
      (commutator (LocalAbsoluteGalois K)))

instance maximal_abelian_galois :
    IsGalois K (maximalAbelianIntermediate K) := by
  apply (InfiniteGalois.normal_iff_isGalois
    (maximalAbelianIntermediate K)).mp
  let H : ClosedSubgroup (LocalAbsoluteGalois K) :=
    ⟨Subgroup.topologicalClosure
      (commutator (LocalAbsoluteGalois K)), isClosed_closure⟩
  have hfield : maximalAbelianIntermediate K =
      IntermediateField.fixedField H := rfl
  rw [hfield, InfiniteGalois.fixingSubgroup_fixedField H]
  infer_instance

/-- The quotient definition of the abelianized absolute Galois group agrees
with the Galois group of the maximal abelian fixed field. -/
noncomputable def abelianGaloisMaximal :
    AbsoluteAbelianGalois K ≃*
      Gal(maximalAbelianIntermediate K/K) := by
  let H : ClosedSubgroup (LocalAbsoluteGalois K) :=
    ⟨Subgroup.topologicalClosure
      (commutator (LocalAbsoluteGalois K)), isClosed_closure⟩
  exact InfiniteGalois.normalAutEquivQuotient H

/-- The Galois group of the maximal abelian fixed field is commutative. -/
instance maximal_abelian_commutative :
    IsMulCommutative Gal(maximalAbelianIntermediate K/K) := by
  let e := abelianGaloisMaximal K
  refine ⟨⟨fun sigma tau => ?_⟩⟩
  apply e.symm.injective
  simpa only [map_mul] using mul_comm' (e.symm sigma) (e.symm tau)

instance maximal_abelian_intermediate :
    IsAbelianGalois K (maximalAbelianIntermediate K) where
  toIsGalois := inferInstance
  toIsMulCommutative := inferInstance

/-- A finite level of the maximal abelian extension, lifted back to the
chosen separable closure and bundled in the form used by the statement of
local reciprocity. -/
noncomputable def maximalAbelianSubextension
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) :
    FASubext K := by
  let Lfield : IntermediateField K (SeparableClosure K) :=
    IntermediateField.lift E.toIntermediateField
  let e : E.toIntermediateField ≃ₐ[K] Lfield :=
    IntermediateField.liftAlgEquiv E.toIntermediateField
  letI : Module.Finite K Lfield := Module.Finite.equiv e.toLinearEquiv
  letI : IsGalois K Lfield := IsGalois.of_algEquiv e
  let L : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { toIntermediateField := Lfield
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let eAut : Gal(E/K) ≃* Gal(L/K) := e.autCongr
  letI : IsMulCommutative Gal(L/K) := by
    refine ⟨⟨fun sigma tau => ?_⟩⟩
    apply eAut.symm.injective
    simpa only [map_mul] using
      mul_comm' (eAut.symm sigma) (eAut.symm tau)
  exact ⟨L⟩

/-- The canonical equivalence from a finite maximal-abelian level to its
lift in the chosen separable closure. -/
noncomputable def maximalAbelianLevel
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) :
    E ≃ₐ[K] (maximalAbelianSubextension K E).1 :=
  IntermediateField.liftAlgEquiv E.toIntermediateField

/-- Every finite abelian subextension of the separable closure lies in the
maximal abelian fixed field. -/
theorem subextension_maximal_intermediate
    (L : FASubext K) :
    L.finiteIntermediateField.toIntermediateField ≤
      maximalAbelianIntermediate K := by
  rw [maximalAbelianIntermediate, IntermediateField.le_iff_le]
  let r : LocalAbsoluteGalois K →*
      Gal(L.finiteIntermediateField/K) :=
    AlgEquiv.restrictNormalHom L.finiteIntermediateField
  apply Subgroup.topologicalClosure_minimal
  · rw [← IntermediateField.restrictNormalHom_ker]
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro x ⟨p, q, rfl⟩
    change r ⁅p, q⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact mul_comm' _ _
  · exact L.finiteIntermediateField.fixingSubgroup_isClosed

private theorem abelian_subextension_ext
    {L L' : FASubext K}
    (h : L.finiteIntermediateField =
      L'.finiteIntermediateField) :
    L = L' := by
  cases L
  cases L'
  simpa only [FASubext.mk.injEq] using h

/-- Every finite abelian subextension is one of the lifted finite Galois
levels used by the inverse-limit presentation of the maximal abelian
extension. -/
theorem maximal_abelian_subextension
    (L : FASubext K) :
    ∃ E : FiniteGaloisIntermediateField K
        (maximalAbelianIntermediate K),
      maximalAbelianSubextension K E = L := by
  let M := maximalAbelianIntermediate K
  let i : M →ₐ[K] SeparableClosure K := M.val
  have hLM : L.finiteIntermediateField.toIntermediateField ≤ M :=
    subextension_maximal_intermediate K L
  have hLrange : L.finiteIntermediateField.toIntermediateField ≤
      i.fieldRange := by
    simpa only [i, M, IntermediateField.fieldRange_val] using hLM
  let Efield : IntermediateField K M :=
    L.finiteIntermediateField.toIntermediateField.comap i
  have hmap : Efield.map i =
      L.finiteIntermediateField.toIntermediateField :=
    IntermediateField.map_comap_eq_self hLrange
  let e : Efield ≃ₐ[K] L.finiteIntermediateField :=
    (IntermediateField.equivMap Efield i).trans
      (IntermediateField.equivOfEq hmap)
  letI : Module.Finite K Efield :=
    Module.Finite.equiv e.symm.toLinearEquiv
  letI : IsGalois K Efield := IsGalois.of_algEquiv e.symm
  let E : FiniteGaloisIntermediateField K M :=
    { toIntermediateField := Efield
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  refine ⟨E, ?_⟩
  apply abelian_subextension_ext
  apply FiniteGaloisIntermediateField.val_injective
  change IntermediateField.lift Efield =
    L.finiteIntermediateField.toIntermediateField
  exact hmap

/-- Restriction from the maximal abelian Galois group to a finite level. -/
noncomputable def maximalAbelianRestriction
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) :
    Gal(maximalAbelianIntermediate K/K) →* Gal(E/K) :=
  AlgEquiv.restrictNormalHom E.toIntermediateField

/-- Restriction after the quotient/fixed-field equivalence agrees with the
repository's `localAbelianRestriction`, up to the canonical lift equivalence
of the finite field. -/
theorem abelian_restriction_subextension
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K))
    (q : AbsoluteAbelianGalois K) :
    localAbelianRestriction (maximalAbelianSubextension K E) q =
      (maximalAbelianLevel K E).autCongr
        (maximalAbelianRestriction K E
          (abelianGaloisMaximal K q)) := by
  obtain ⟨sigma, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.topologicalClosure
      (commutator (LocalAbsoluteGalois K))) q
  let H : ClosedSubgroup (LocalAbsoluteGalois K) :=
    ⟨Subgroup.topologicalClosure
      (commutator (LocalAbsoluteGalois K)), isClosed_closure⟩
  have hmax :
      abelianGaloisMaximal K
          (localAbelianizationMap K sigma) =
        AlgEquiv.restrictNormalHom (maximalAbelianIntermediate K) sigma := by
    change InfiniteGalois.normalAutEquivQuotient H
        (localAbelianizationMap K sigma) = _
    exact InfiniteGalois.normalAutEquivQuotient_apply H sigma
  apply AlgEquiv.ext
  intro x
  change (localAbelianRestriction
    (maximalAbelianSubextension K E)
      (localAbelianizationMap K sigma)) x =
    (maximalAbelianLevel K E).autCongr
      (maximalAbelianRestriction K E
        (abelianGaloisMaximal K
          (localAbelianizationMap K sigma))) x
  rw [abelian_restriction_quotient]
  rw [hmax]
  apply Subtype.ext
  simp only [maximalAbelianRestriction,
    AlgEquiv.restrictNormalHom_apply, AlgEquiv.autCongr_apply,
    AlgEquiv.trans_apply]
  let e := maximalAbelianLevel K E
  let tau : Gal(maximalAbelianIntermediate K/K) :=
    AlgEquiv.restrictNormalHom (maximalAbelianIntermediate K) sigma
  let rho : Gal(E/K) :=
    AlgEquiv.restrictNormalHom E.toIntermediateField tau
  change sigma (x : SeparableClosure K) =
    (e (rho (e.symm x)) : SeparableClosure K)
  symm
  calc
    (e (rho (e.symm x)) : SeparableClosure K) =
        (((rho (e.symm x) : E) : maximalAbelianIntermediate K) :
          SeparableClosure K) := rfl
    _ = ((tau ((e.symm x : E) : maximalAbelianIntermediate K) :
          maximalAbelianIntermediate K) : SeparableClosure K) := by
      exact congrArg Subtype.val
        (AlgEquiv.restrictNormalHom_apply E.toIntermediateField tau (e.symm x))
    _ = sigma ((((e.symm x : E) : maximalAbelianIntermediate K) :
          SeparableClosure K)) :=
      AlgEquiv.restrictNormalHom_apply
        (maximalAbelianIntermediate K) sigma
          ((e.symm x : E) : maximalAbelianIntermediate K)
    _ = sigma (x : SeparableClosure K) := by
      exact congrArg sigma (congrArg Subtype.val (e.apply_symm_apply x))

/-- A compatible inverse system of finite reciprocity homomorphisms on all
finite Galois levels of the maximal abelian extension.

Compatibility is stated using the transition maps of Mathlib's finite
Galois-group functor, which avoids choices of algebra structures in towers. -/
structure CAArtin where
  hom (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) :
    Kˣ →* Gal(E/K)
  compatible : ∀ {E F :
      (FiniteGaloisIntermediateField K
        (maximalAbelianIntermediate K))ᵒᵖ}
      (f : E ⟶ F) (x : Kˣ),
    (finGaloisGroupFunctor K (maximalAbelianIntermediate K)).map f
        (hom E.unop x) =
      hom F.unop x

namespace CAArtin

variable (A : CAArtin K)

/-- A compatible finite Artin family as a homomorphism into the inverse
limit of finite Galois groups. -/
noncomputable def toLimit :
    Kˣ →* limit (InfiniteGalois.asProfiniteGaloisGroupFunctor K
      (maximalAbelianIntermediate K)) where
  toFun x :=
    ⟨fun E => A.hom E.unop x, by
      intro E F f
      exact A.compatible f x⟩
  map_one' := by
    apply Subtype.ext
    funext E
    exact map_one (A.hom E.unop)
  map_mul' x y := by
    apply Subtype.ext
    funext E
    exact map_mul (A.hom E.unop) x y

/-- The homomorphism into the Galois group of the maximal abelian extension
assembled from the compatible finite levels. -/
noncomputable def maximalAbelian :
    Kˣ →* Gal(maximalAbelianIntermediate K/K) :=
  (InfiniteGalois.mulEquivToLimit K
      (maximalAbelianIntermediate K)).symm.toMonoidHom.comp
    (toLimit K A)

/-- The global homomorphism into the topological abelianization assembled
from the compatible finite levels. -/
noncomputable def assemble :
    Kˣ →* AbsoluteAbelianGalois K :=
  (abelianGaloisMaximal K).symm.toMonoidHom.comp
    (maximalAbelian K A)

/-- Projection of the assembled maximal-abelian Galois element to a finite
level recovers the prescribed finite Artin homomorphism. -/
@[simp]
theorem proj_maximal_abelian
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) (x : Kˣ) :
    InfiniteGalois.proj E
        (InfiniteGalois.algEquivToLimit K
          (maximalAbelianIntermediate K)
          (maximalAbelian K A x)) =
      A.hom E x := by
  change InfiniteGalois.proj E
      ((InfiniteGalois.mulEquivToLimit K
        (maximalAbelianIntermediate K))
        ((InfiniteGalois.mulEquivToLimit K
          (maximalAbelianIntermediate K)).symm (toLimit K A x))) = _
  have h := congrArg (InfiniteGalois.proj E)
    ((InfiniteGalois.mulEquivToLimit K
      (maximalAbelianIntermediate K)).apply_symm_apply (toLimit K A x))
  exact h

/-- Applying the maximal-abelian Galois equivalence to the assembled global
map gives the inverse-limit assembly before transport. -/
@[simp]
theorem abelian_maximal_assemble (x : Kˣ) :
    abelianGaloisMaximal K (assemble K A x) =
      maximalAbelian K A x := by
  exact (abelianGaloisMaximal K).apply_symm_apply _

/-- The finite projection of the assembled global map is the prescribed
finite Artin map. -/
@[simp]
theorem proj_assemble
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) (x : Kˣ) :
    InfiniteGalois.proj E
        (InfiniteGalois.algEquivToLimit K
          (maximalAbelianIntermediate K)
          (abelianGaloisMaximal K (assemble K A x))) =
      A.hom E x := by
  rw [abelian_maximal_assemble,
    proj_maximal_abelian]

/-- In the original separable-closure formulation, restriction of the
assembled map to a lifted finite level is the prescribed finite map,
transported by the canonical lift equivalence. -/
theorem abelian_restriction_assemble
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) (x : Kˣ) :
    localAbelianRestriction (maximalAbelianSubextension K E)
        (assemble K A x) =
      (maximalAbelianLevel K E).autCongr (A.hom E x) := by
  rw [abelian_restriction_subextension]
  exact congrArg (maximalAbelianLevel K E).autCongr
    (proj_assemble K A E x)

/-- The inverse-limit assembly is unique among homomorphisms with the given
finite projections. -/
theorem assemble_unique
    (phi : Kˣ →* AbsoluteAbelianGalois K)
    (hphi : ∀ (E : FiniteGaloisIntermediateField K
        (maximalAbelianIntermediate K)) (x : Kˣ),
      InfiniteGalois.proj E
          (InfiniteGalois.algEquivToLimit K
            (maximalAbelianIntermediate K)
            (abelianGaloisMaximal K (phi x))) =
        A.hom E x) :
    phi = assemble K A := by
  ext x
  apply (abelianGaloisMaximal K).injective
  apply (InfiniteGalois.mulEquivToLimit K
    (maximalAbelianIntermediate K)).injective
  apply Subtype.ext
  funext E
  change InfiniteGalois.proj E.unop
      (InfiniteGalois.algEquivToLimit K
        (maximalAbelianIntermediate K)
        (abelianGaloisMaximal K (phi x))) =
    InfiniteGalois.proj E.unop
      (InfiniteGalois.algEquivToLimit K
        (maximalAbelianIntermediate K)
        (abelianGaloisMaximal K (assemble K A x)))
  rw [hphi, proj_assemble]

end CAArtin

/-- A compatible family of finite norm-residue equivalences.  The equation
records the homomorphism represented by each quotient equivalence. -/
structure CARecip extends
    CAArtin K where
  equiv (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) :
    (Kˣ ⧸ normSubgroup K E) ≃* Gal(E/K)
  equiv_mk (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) (x : Kˣ) :
    equiv E (QuotientGroup.mk' (normSubgroup K E) x) = hom E x

namespace CARecip

variable (A : CARecip K)

/-- The finite norm-residue equivalence on a lifted separable-closure level. -/
noncomputable def liftedEquiv
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) :
    (Kˣ ⧸ (maximalAbelianSubextension K E).normGroup) ≃*
      Gal((maximalAbelianSubextension K E).1/K) := by
  let e := maximalAbelianLevel K E
  have hNorm : (maximalAbelianSubextension K E).normGroup =
      normSubgroup K E := by
    exact (norm_alg_equiv K E
      (maximalAbelianSubextension K E).1 e).symm
  exact (QuotientGroup.quotientMulEquivOfEq hNorm).trans
    ((A.equiv E).trans e.autCongr)

/-- The lifted finite equivalence evaluates to restriction of the assembled
global reciprocity map. -/
theorem liftedEquiv_mk
    (E : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)) (x : Kˣ) :
    liftedEquiv K A E
        (QuotientGroup.mk'
          (maximalAbelianSubextension K E).normGroup x) =
      localAbelianRestriction (maximalAbelianSubextension K E)
        (CAArtin.assemble K
          A.toCAArtin x) := by
  let e := maximalAbelianLevel K E
  have hNorm : (maximalAbelianSubextension K E).normGroup =
      normSubgroup K E := by
    exact (norm_alg_equiv K E
      (maximalAbelianSubextension K E).1 e).symm
  change e.autCongr
      (A.equiv E
        (QuotientGroup.quotientMulEquivOfEq hNorm
          (QuotientGroup.mk'
            (maximalAbelianSubextension K E).normGroup x))) = _
  have hq : QuotientGroup.quotientMulEquivOfEq hNorm
      (QuotientGroup.mk'
        (maximalAbelianSubextension K E).normGroup x) =
      QuotientGroup.mk' (normSubgroup K E) x := rfl
  rw [hq, A.equiv_mk]
  exact (CAArtin.abelian_restriction_assemble
    K A.toCAArtin E x).symm

end CARecip

section LocalField

variable (F : Type u) [NontriviallyNormedField F]

namespace CARecip

variable (A : CARecip F)

/-- The inverse-limit assembly induces the supplied norm-residue equivalence
on every lifted finite level. -/
theorem induce_recip_assem
    (E : FiniteGaloisIntermediateField F
      (maximalAbelianIntermediate F)) :
    InducesLocalReciprocity F
      (CAArtin.assemble F
        A.toCAArtin)
      (maximalAbelianSubextension F E) := by
  refine ⟨liftedEquiv F A E, ?_⟩
  exact liftedEquiv_mk F A E

/-- The inverse-limit assembly induces the supplied norm-residue
equivalence on every finite abelian subextension of the fixed separable
closure, not only on levels already presented inside the maximal abelian
fixed field. -/
theorem induces_assemble_all
    (L : FASubext F) :
    InducesLocalReciprocity F
      (CAArtin.assemble F
        A.toCAArtin) L := by
  obtain ⟨E, hE⟩ := maximal_abelian_subextension F L
  rw [← hE]
  exact A.induce_recip_assem F E

end CARecip

end LocalField

end

end Towers.CField.LFTheory
