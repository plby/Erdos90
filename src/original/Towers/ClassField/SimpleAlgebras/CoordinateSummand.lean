import Mathlib.LinearAlgebra.Pi
import Towers.ClassField.SimpleAlgebras.PrefixSum

/-!
# Milne, Class Field Theory, Corollary IV.1.3: source statement

The tracked `simpleDecompositions_unique` theorem treats internal direct sums
of submodules of one ambient module.  Milne's literal statement starts from
two external finite direct-sum decompositions.  A dependent function space
over a finite index type is the corresponding finite direct sum, so this file
transports its coordinate submodules into the common module and applies the
internal theorem.
-/

namespace Towers.CField.SAlgebr

universe u v w x

variable {R : Type u} {M : Type v} [Ring R]
  [AddCommGroup M] [Module R M]

/-- The image in `M` of one coordinate in an external finite direct-sum
decomposition. -/
noncomputable def coordinateSummand
    {n : ℕ} (V : Fin n → Type w)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (e : ((i : Fin n) → V i) ≃ₗ[R] M) (i : Fin n) :
    Submodule R M :=
  (LinearMap.range (LinearMap.single R V i)).map e.toLinearMap

/-- A coordinate module is linearly equivalent to its transported summand. -/
noncomputable def coordinateSummandEquiv
    {n : ℕ} (V : Fin n → Type w)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (e : ((i : Fin n) → V i) ≃ₗ[R] M) (i : Fin n) :
    V i ≃ₗ[R] coordinateSummand V e i := by
  let single : V i →ₗ[R] ((j : Fin n) → V j) := LinearMap.single R V i
  have hinj : Function.Injective single := by
    intro a b hab
    have h := congrArg (fun f => f i) hab
    simpa [single, LinearMap.single_apply] using h
  exact (LinearEquiv.ofInjective single hinj).trans
    (e.submoduleMap (LinearMap.range single))

/-- The transported coordinate summands form an internal direct sum. -/
theorem summand_i_indep
    {n : ℕ} (V : Fin n → Type w)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (e : ((i : Fin n) → V i) ≃ₗ[R] M) :
    iSupIndep (coordinateSummand V e) := by
  have hPi : iSupIndep
      (fun i : Fin n => LinearMap.range (LinearMap.single R V i)) := by
    rw [iSupIndep]
    intro i
    simpa using
      (LinearMap.disjoint_single_single R V ({i} : Set (Fin n))
        {j | j ≠ i} (by simp))
  exact LinearMap.iSupIndep_map e.toLinearMap e.injective hPi

/-- The transported coordinate summands span the common module. -/
theorem summand_i_top
    {n : ℕ} (V : Fin n → Type w)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (e : ((i : Fin n) → V i) ≃ₗ[R] M) :
    ⨆ i, coordinateSummand V e i = ⊤ := by
  rw [show (⨆ i, coordinateSummand V e i) =
      (⨆ i, LinearMap.range (LinearMap.single R V i)).map e.toLinearMap by
        simp only [coordinateSummand, Submodule.map_iSup]]
  rw [LinearMap.iSup_range_single, Submodule.map_top, LinearEquiv.range]

/-- Simplicity is preserved when a coordinate is transported into the common
module. -/
theorem coordinate_summand_simple
    {n : ℕ} (V : Fin n → Type w)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    (e : ((i : Fin n) → V i) ≃ₗ[R] M)
    (hV : ∀ i, IsSimpleModule R (V i)) (i : Fin n) :
    IsSimpleModule R (coordinateSummand V e i) :=
  (coordinateSummandEquiv V e i).isSimpleModule_iff.mp (hV i)

/-- **Corollary IV.1.3 (literal external-decomposition form).**
If one module is linearly equivalent to two finite direct sums of simple
modules, then the numbers of summands agree and an index equivalence matches
linearly equivalent simple summands. -/
theorem simple_external_decompositions
    {r s : ℕ}
    (V : Fin r → Type w) (W : Fin s → Type x)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    (eV : ((i : Fin r) → V i) ≃ₗ[R] M)
    (eW : ((i : Fin s) → W i) ≃ₗ[R] M)
    (hV : ∀ i, IsSimpleModule R (V i))
    (hW : ∀ i, IsSimpleModule R (W i)) :
    r = s ∧ ∃ e : Fin r ≃ Fin s,
      ∀ i, Nonempty (V i ≃ₗ[R] W (e i)) := by
  obtain ⟨e, he⟩ := simpleDecompositions_unique
    (coordinateSummand V eV) (coordinateSummand W eW)
    (summand_i_indep V eV)
    (summand_i_top V eV)
    (summand_i_indep W eW)
    (summand_i_top W eW)
    (coordinate_summand_simple V eV hV)
    (coordinate_summand_simple W eW hW)
  refine ⟨?_, e, ?_⟩
  · simpa using Fintype.card_congr e
  · intro i
    obtain ⟨ei⟩ := he i
    exact ⟨(coordinateSummandEquiv V eV i).trans
      (ei.trans (coordinateSummandEquiv W eW (e i)).symm)⟩

end Towers.CField.SAlgebr
