import Submission.NumberTheory.Dedekind.InvariantFactorKernel
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.Prod

/-!
# Peeling off the final invariant factor

The direct sum indexed by `Fin (n + 1)` splits into its first `n` coordinates and its final
coordinate.  For a lattice quotient with such a presentation, the kernel of the final-coordinate
map is an intermediate lattice whose quotient by the original sublattice has precisely the prefix
presentation.
-/

namespace Submission.NumberTheory.Milne

open scoped DirectSum

/-- Split an invariant-factor direct sum into its prefix and final cyclic quotient. -/
noncomputable def invariantSplitLast
    (A : Type*) [CommRing A]
    (n : ℕ) (b : Fin (n + 1) → Ideal A) :
    DirectSum (Fin (n + 1)) (fun i ↦ idealQuotientModule A (b i)) ≃ₗ[A]
      (DirectSum (Fin n) (fun i ↦ idealQuotientModule A (b i.castSucc))) ×
        idealQuotientModule A (b (Fin.last n)) := by
  classical
  let F : Fin (n + 1) → Type _ := fun i ↦ idealQuotientModule A (b i)
  let KIdeal : Option (Fin n) → Ideal A := fun
    | none => b (Fin.last n)
    | some i => b i.castSucc
  let reindex :
      DirectSum (Fin (n + 1)) F ≃ₗ[A]
        DirectSum (Option (Fin n)) (fun o ↦ F (finSuccEquivLast.symm o)) :=
    DirectSum.lequivCongrLeft A finSuccEquivLast
  let normalize :
      DirectSum (Option (Fin n)) (fun o ↦ F (finSuccEquivLast.symm o)) ≃ₗ[A]
        DirectSum (Option (Fin n)) (fun o ↦ idealQuotientModule A (KIdeal o)) :=
    DFinsupp.mapRange.linearEquiv fun o ↦ by
      cases o with
      | none =>
          exact Submodule.quotEquivOfEq _ _ (by simp [KIdeal])
      | some i =>
          exact Submodule.quotEquivOfEq _ _ (by simp [KIdeal])
  let split :
      DirectSum (Option (Fin n)) (fun o ↦ idealQuotientModule A (KIdeal o)) ≃ₗ[A]
        idealQuotientModule A (KIdeal none) ×
          DirectSum (Fin n) (fun i ↦ idealQuotientModule A (KIdeal (some i))) :=
    DirectSum.lequivProdDirectSum (R := A)
  simpa [F, KIdeal] using
    (reindex ≪≫ₗ normalize ≪≫ₗ split ≪≫ₗ LinearEquiv.prodComm A _ _)

/-- The quotient of the kernel of the final-coordinate map by the original submodule is the
prefix invariant-factor direct sum. -/
theorem invariant_last_prefix
    (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M]
    (N : Submodule A M)
    (n : ℕ) (b : Fin (n + 1) → Ideal A)
    (e : (M ⧸ N) ≃ₗ[A]
      DirectSum (Fin (n + 1)) (fun i ↦ idealQuotientModule A (b i))) :
    let split := invariantSplitLast A n b
    let q : M →ₗ[A] idealQuotientModule A (b (Fin.last n)) :=
      (LinearMap.snd A _ _).comp (split.toLinearMap.comp (e.toLinearMap.comp N.mkQ))
    Nonempty
      ((LinearMap.ker q ⧸ N.comap (LinearMap.ker q).subtype) ≃ₗ[A]
        DirectSum (Fin n) (fun i ↦ idealQuotientModule A (b i.castSucc))) := by
  classical
  dsimp only
  let split := invariantSplitLast A n b
  let total : M →ₗ[A]
      (DirectSum (Fin n) (fun i ↦ idealQuotientModule A (b i.castSucc))) ×
        idealQuotientModule A (b (Fin.last n)) :=
    split.toLinearMap.comp (e.toLinearMap.comp N.mkQ)
  let q : M →ₗ[A] idealQuotientModule A (b (Fin.last n)) :=
    (LinearMap.snd A _ _).comp total
  let prefixMap : LinearMap.ker q →ₗ[A]
      DirectSum (Fin n) (fun i ↦ idealQuotientModule A (b i.castSucc)) :=
    (LinearMap.fst A _ _).comp (total.comp (LinearMap.ker q).subtype)
  have hprefix_surjective : Function.Surjective prefixMap := by
    intro y
    let z := split.symm (y, 0)
    obtain ⟨m, hm⟩ := N.mkQ_surjective (e.symm z)
    have htotal : total m = (y, 0) := by
      simp [total, z, hm]
    have hmq : m ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker]
      simpa [q] using congrArg Prod.snd htotal
    refine ⟨⟨m, hmq⟩, ?_⟩
    simpa [prefixMap] using congrArg Prod.fst htotal
  have hker : LinearMap.ker prefixMap = N.comap (LinearMap.ker q).subtype := by
    ext x
    constructor
    · intro hx
      have hfst : (total x.1).1 = 0 := by
        simpa [prefixMap] using LinearMap.mem_ker.mp hx
      have hsnd : (total x.1).2 = 0 := by
        exact LinearMap.mem_ker.mp x.2
      have htotal : total x.1 = 0 := Prod.ext hfst hsnd
      have hquot : N.mkQ x.1 = 0 := by
        apply e.injective
        apply split.injective
        simpa [total] using htotal
      exact (Submodule.Quotient.mk_eq_zero N).mp hquot
    · intro hx
      rw [LinearMap.mem_ker]
      have hquot : N.mkQ x.1 = 0 :=
        (Submodule.Quotient.mk_eq_zero N).mpr hx
      simp [prefixMap, total, hquot]
  let induced :
      (LinearMap.ker q ⧸ N.comap (LinearMap.ker q).subtype) →ₗ[A]
        DirectSum (Fin n) (fun i ↦ idealQuotientModule A (b i.castSucc)) :=
    (N.comap (LinearMap.ker q).subtype).liftQ prefixMap (by rw [hker])
  refine ⟨LinearEquiv.ofBijective induced ⟨?_, ?_⟩⟩
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot'
      (N.comap (LinearMap.ker q).subtype) prefixMap hker.symm
  · intro y
    obtain ⟨x, hx⟩ := hprefix_surjective y
    exact ⟨Submodule.Quotient.mk x, by simpa [induced] using hx⟩

end Submission.NumberTheory.Milne
