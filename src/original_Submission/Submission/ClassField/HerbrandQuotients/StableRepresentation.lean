import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Submission.ClassField.HerbrandQuotients.BaseChangeSpanning
import Submission.ClassField.HerbrandQuotients.HerbrandIsogeny

/-!
# Chapter VII, Section 3, Lemma 3.5

Two `G`-stable full lattices in the same real representation have the same
Herbrand quotient whenever either quotient is defined.
-/

namespace Submission.CField.HQuotie

open Representation
open scoped TensorProduct
open Submission.CField.ICohomo

noncomputable section

universe u

/-- The integral representation on a `G`-stable additive subgroup of a real
representation. -/
def stableLatticeRepresentation
    {G V : Type u} [Group G] [AddCommGroup V] [Module ℝ V]
    (rho : Representation ℝ G V) (M : Submodule ℤ V)
    (hstable : ∀ g x, x ∈ M → rho g x ∈ M) : Rep.{u, 0, u} ℤ G :=
  Rep.of
    { toFun := fun g ↦
        ((rho g).restrictScalars ℤ).restrict fun x hx ↦ hstable g x hx
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp }

/-- The canonical map `ℝ ⊗_ℤ M → V`, `r ⊗ m ↦ r • m`. -/
def fullLatticeRealization
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    (M : Submodule ℤ V) : ℝ ⊗[ℤ] M →ₗ[ℝ] V :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun r ↦
        { toFun := fun m ↦ r • (m : V)
          map_add' := fun x y ↦ smul_add r (x : V) (y : V)
          map_smul' := fun z x ↦ by
            change r • (z • (x : V)) = z • (r • (x : V))
            rw [smul_comm] }
      map_add' := fun r s ↦ by
        ext m
        exact add_smul r s (m : V)
      map_smul' := fun r s ↦ by
        ext m
        exact mul_smul r s (m : V) }

@[simp]
theorem lattice_realization_tmul
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    (M : Submodule ℤ V) (r : ℝ) (m : M) :
    fullLatticeRealization M (r ⊗ₜ m) = r • (m : V) :=
  rfl

/-- Milne's algebraic definition of a full lattice: it is finitely generated
over `ℤ`, and its canonical real scalar extension is the whole ambient real
vector space. -/
def FullRealLattice
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    (M : Submodule ℤ V) : Prop :=
  Module.Finite ℤ M ∧ Function.Bijective (fullLatticeRealization M)

/-- A stable full lattice becomes the ambient real representation after
extension of scalars from `ℤ` to `ℝ`. -/
def stableFullLattice
    {G V : Type u} [Group G] [AddCommGroup V] [Module ℝ V]
    (rho : Representation ℝ G V) (M : Submodule ℤ V)
    (hstable : ∀ g x, x ∈ M → rho g x ∈ M)
    (hfull : FullRealLattice M) :
    (Representation.baseChange ℤ ℝ G
      (stableLatticeRepresentation rho M hstable)
      (stableLatticeRepresentation rho M hstable).ρ).Equiv rho := by
  let e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] V :=
    LinearEquiv.ofBijective (fullLatticeRealization M) hfull.2
  apply Representation.Equiv.mk e
  intro g
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
      change fullLatticeRealization M
          (((stableLatticeRepresentation rho M hstable).ρ g).baseChange ℝ
            (r ⊗ₜ m)) =
        rho g (fullLatticeRealization M (r ⊗ₜ m))
      rw [LinearMap.baseChange_tmul]
      change r • rho g (m : V) = rho g (r • (m : V))
      exact ((rho g).map_smul r (m : V)).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Collapsing the two successive scalar extensions `ℤ → ℚ → ℝ` is
equivariant. -/
def rationalRealChange
    {G : Type u} [Group G] (A : Rep.{u, 0, u} ℤ G) :
    let _ : Module ℤ A := A.hV2
    (Representation.baseChange ℚ ℝ G (ℚ ⊗[ℤ] A)
      (Representation.baseChange ℤ ℚ G A A.ρ)).Equiv
        (Representation.baseChange ℤ ℝ G A A.ρ) := by
  let _ : Module ℤ A := A.hV2
  let e : ℝ ⊗[ℚ] (ℚ ⊗[ℤ] A) ≃ₗ[ℝ] ℝ ⊗[ℤ] A :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ A
  apply Representation.Equiv.mk e
  intro g
  change e.toLinearMap ∘ₗ (((A.ρ g).baseChange ℚ).baseChange ℝ) =
    (A.ρ g).baseChange ℝ ∘ₗ e.toLinearMap
  rw [LinearMap.baseChange_baseChange]
  simp [e]

/-- The rational representations furnished by two stable full lattices in
the same real representation are isomorphic, by Lemma 3.2. -/
theorem lattices_rationally_isomorphic
    {G V : Type u} [Group G] [Finite G]
    [AddCommGroup V] [Module ℝ V]
    (rho : Representation ℝ G V)
    (M N : Submodule ℤ V)
    (hMstable : ∀ g x, x ∈ M → rho g x ∈ M)
    (hNstable : ∀ g x, x ∈ N → rho g x ∈ N)
    (hMfull : FullRealLattice M)
    (hNfull : FullRealLattice N) :
    RationallyIsomorphicRepresentations
      (stableLatticeRepresentation rho M hMstable)
      (stableLatticeRepresentation rho N hNstable) := by
  let RM := stableLatticeRepresentation rho M hMstable
  let RN := stableLatticeRepresentation rho N hNstable
  letI : Module.Finite ℤ RM := hMfull.1
  letI : Module.Finite ℤ RN := hNfull.1
  let eM := stableFullLattice rho M hMstable hMfull
  let eN := stableFullLattice rho N hNstable hNfull
  let e :
      (Representation.baseChange ℚ ℝ G (ℚ ⊗[ℤ] RM)
          (Representation.baseChange ℤ ℚ G RM RM.ρ)).Equiv
        (Representation.baseChange ℚ ℝ G (ℚ ⊗[ℤ] RN)
          (Representation.baseChange ℤ ℚ G RN RN.ρ)) :=
    (rationalRealChange RM).trans
      (eM.trans (eN.symm.trans (rationalRealChange RN).symm))
  exact changeSpanningStatement ℚ ℝ G (ℚ ⊗[ℤ] RM) (ℚ ⊗[ℤ] RN)
    (Representation.baseChange ℤ ℚ G RM RM.ρ)
    (Representation.baseChange ℤ ℚ G RN RN.ρ) ⟨e⟩

/-- Lemma 3.5 is the direct combination of scalar descent (Lemma 3.2) and
the integral rational-isomorphism comparison (Lemma 3.4). -/
theorem stable_representation_isogenies
    : (∀ (G V : Type u) [Group G] [Finite G] [IsCyclic G]
          [AddCommGroup V] [Module ℝ V]
          (rho : Representation ℝ G V)
          (M N : Submodule ℤ V)
          (hMstable : ∀ g x, x ∈ M → rho g x ∈ M)
          (hNstable : ∀ g x, x ∈ N → rho g x ∈ N),
          FullRealLattice M → FullRealLattice N →
            letI : Fintype G := Fintype.ofFinite G
            letI : CommGroup G := IsCyclic.commGroup
            let RM := stableLatticeRepresentation rho M hMstable
            let RN := stableLatticeRepresentation rho N hNstable
            ((DefinedHerbrandQuotient RM →
                ∃ q : ℚ,
                  HerbrandQuotientValue RM q ∧
                    HerbrandQuotientValue RN q) ∧
              (DefinedHerbrandQuotient RN →
                ∃ q : ℚ,
                  HerbrandQuotientValue RM q ∧
                    HerbrandQuotientValue RN q))) := by
  intro G V _ _ _ _ _ rho M N hMstable hNstable hMfull hNfull
  let RM := stableLatticeRepresentation rho M hMstable
  let RN := stableLatticeRepresentation rho N hNstable
  letI : Module.Finite ℤ RM := hMfull.1
  letI : Module.Finite ℤ RN := hNfull.1
  exact herbrandIsogenyStatement G RM RN
    (lattices_rationally_isomorphic rho M N
      hMstable hNstable hMfull hNfull)

end

end Submission.CField.HQuotie
