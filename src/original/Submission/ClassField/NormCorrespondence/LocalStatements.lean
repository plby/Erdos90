import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Submission.ClassField.LocalFields.NormSubgroups

/-!
# Chapter I, Section 1: statements of the main local theorems

This file begins the concrete statement API for the local reciprocity and
local existence theorems.  A finite abelian extension is bundled with the
actual field and algebra structures needed to form its norm subgroup.
-/

namespace Submission.CField.LFTheory

noncomputable section

universe u v

/-- A finite abelian extension of `K`.

The extension field is bundled because the local existence theorem quantifies
over extensions rather than over subfields of one preselected algebraic
closure. -/
structure FAExt (K : Type u) [Field K] where
  carrier : Type v
  [field : Field carrier]
  [algebra : Algebra K carrier]
  [finiteDimensional : FiniteDimensional K carrier]
  [isGalois : IsGalois K carrier]
  [isAbelian : IsMulCommutative Gal(carrier/K)]

attribute [instance]
  FAExt.field
  FAExt.algebra
  FAExt.finiteDimensional
  FAExt.isGalois
  FAExt.isAbelian

namespace FAExt

variable {K : Type u} [Field K]

/-- The norm group attached to a finite abelian extension. -/
def normGroup (L : FAExt.{u, v} K) : Subgroup Kˣ :=
  normSubgroup K L.carrier

end FAExt

/-- A finite abelian subextension of a fixed separable closure of `K`.

This is the finite-level object on which an element of the absolute Galois
group can be restricted. -/
structure FASubext (K : Type u) [Field K] where
  finiteIntermediateField :
    FiniteGaloisIntermediateField K (SeparableClosure K)
  [isAbelian :
    IsMulCommutative
      Gal(finiteIntermediateField/K)]

attribute [instance] FASubext.isAbelian

namespace FASubext

variable {K : Type u} [Field K]

instance : Coe (FASubext K)
    (FiniteGaloisIntermediateField K (SeparableClosure K)) where
  coe L := L.finiteIntermediateField

instance (L : FASubext K) : FiniteDimensional K L.1 :=
  L.1.finiteDimensional

instance (L : FASubext K) : IsGalois K L.1 :=
  L.1.isGalois

/-- The norm group attached to a finite abelian subextension of the fixed
separable closure. -/
def normGroup (L : FASubext K) : Subgroup Kˣ :=
  LFTheory.normSubgroup K L.1

/-- A finite abelian subextension, regarded as an abstract bundled finite
abelian extension. -/
def abelianExtension (L : FASubext K) :
    FAExt.{u, u} K where
  carrier := L.1
  field := inferInstance
  algebra := inferInstance
  finiteDimensional := inferInstance
  isGalois := inferInstance
  isAbelian := inferInstance

@[simp]
theorem abelian_extension_group
    (L : FASubext K) :
    L.abelianExtension.normGroup = L.normGroup := rfl

end FASubext

namespace FAExt

variable {K : Type u} [Field K]

/-- A finite abelian extension embedded into the chosen separable closure. -/
noncomputable def separableClosureEmbedding
    (L : FAExt.{u, v} K) :
    L.carrier →ₐ[K] SeparableClosure K :=
  IsSepClosed.lift

/-- The image of a finite abelian extension in the chosen separable
closure. -/
noncomputable def separableClosureField
    (L : FAExt.{u, v} K) :
    IntermediateField K (SeparableClosure K) :=
  L.separableClosureEmbedding.fieldRange

/-- The original extension is canonically equivalent to its chosen image in
the separable closure. -/
noncomputable def algSeparableClosure
    (L : FAExt.{u, v} K) :
    L.carrier ≃ₐ[K] L.separableClosureField :=
  AlgEquiv.ofInjectiveField L.separableClosureEmbedding

/-- Every bundled finite abelian extension determines a finite abelian
subextension of the chosen separable closure. -/
noncomputable def finiteAbelianSubextension
    (L : FAExt.{u, v} K) :
    FASubext K := by
  let E' := L.separableClosureField
  let e := L.algSeparableClosure
  letI : Module.Finite K E' := Module.Finite.equiv e.toLinearEquiv
  letI : IsGalois K E' := IsGalois.of_algEquiv e
  let E : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { E' with
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let eAut : Gal(L.carrier/K) ≃* Gal(E/K) := e.autCongr
  letI : IsMulCommutative Gal(E/K) := by
    refine ⟨⟨fun σ τ ↦ ?_⟩⟩
    apply eAut.symm.injective
    simpa only [map_mul] using mul_comm' (eAut.symm σ) (eAut.symm τ)
  exact { finiteIntermediateField := E }

/-- Passing to the chosen image in the separable closure does not change the
norm subgroup. -/
theorem norm_abelian_subextension
    (L : FAExt.{u, v} K) :
    L.normGroup = L.finiteAbelianSubextension.normGroup := by
  letI : Module.Finite K L.separableClosureField :=
    Module.Finite.equiv L.algSeparableClosure.toLinearEquiv
  change normSubgroup K L.carrier =
    normSubgroup K L.separableClosureField
  exact norm_alg_equiv K L.carrier
    L.separableClosureField L.algSeparableClosure

end FAExt

/-- The absolute Galois group, formed using the chosen separable closure. -/
abbrev LocalAbsoluteGalois (K : Type u) [Field K] :=
  Gal(SeparableClosure K/K)

/-- The Galois group of the maximal abelian extension, realized canonically
as the topological abelianization of the absolute Galois group. -/
abbrev AbsoluteAbelianGalois (K : Type u) [Field K] :=
  TopologicalAbelianization (LocalAbsoluteGalois K)

/-- The quotient map from the absolute Galois group to its topological
abelianization. -/
def localAbelianizationMap (K : Type u) [Field K] :
    LocalAbsoluteGalois K →* AbsoluteAbelianGalois K :=
  QuotientGroup.mk'
    (Subgroup.topologicalClosure
      (commutator (LocalAbsoluteGalois K)))

section LocalAbelianRestriction

open scoped IsMulCommutative

set_option maxHeartbeats 2000000 in
-- Constructing restriction through the Krull topology exceeds the default heartbeat budget.
/-- Restriction from the abelianized absolute Galois group to a finite
abelian subextension. -/
noncomputable def localAbelianRestriction {K : Type u} [Field K]
    (L : FASubext K) :
    AbsoluteAbelianGalois K →*
      Gal(L.finiteIntermediateField/K) :=
  QuotientGroup.lift
    (Subgroup.topologicalClosure
      (commutator (LocalAbsoluteGalois K)))
    (AlgEquiv.restrictNormalHom L.finiteIntermediateField)
    (by
      apply Subgroup.topologicalClosure_minimal
      · rw [commutator_eq_closure, Subgroup.closure_le]
        rintro x ⟨p, q, rfl⟩
        simp [MonoidHom.mem_ker, commutatorElement_def]
      · rw [IntermediateField.restrictNormalHom_ker]
        exact L.finiteIntermediateField.fixingSubgroup_isClosed)

end LocalAbelianRestriction

/-- Restriction after abelianization is ordinary field restriction. -/
@[simp]
theorem abelian_restriction_quotient {K : Type u} [Field K]
    (L : FASubext K) (σ : LocalAbsoluteGalois K) :
    localAbelianRestriction L (localAbelianizationMap K σ) =
      σ.restrictNormalHom L.finiteIntermediateField :=
  rfl

/-- The intrinsic subgroup class occurring in the Local Existence Theorem. -/
def OFSubgro
    {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) : Prop :=
  IsOpen (H : Set G) ∧ H.FiniteIndex

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]

/-- A subgroup of `Kˣ` is a norm group if it is the image of the field norm
from a finite abelian subextension of the fixed separable closure.  Every
abstract finite abelian extension embeds in this closure without changing its
norm group. -/
def LGroup (H : Subgroup Kˣ) : Prop :=
  ∃ L : FASubext K, L.normGroup = H

/-- **Theorem I.1.4 (Local Existence Theorem), statement.**

The norm groups in `Kˣ` are exactly its open subgroups of finite index. -/
def LocalExistenceTheorem : Prop :=
  ∀ H : Subgroup Kˣ,
    LGroup K H ↔
      OFSubgro H

end

end Submission.CField.LFTheory
