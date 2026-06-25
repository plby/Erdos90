import Towers.ClassField.Reciprocity.RestrictedFactorFamily
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Continuity of finite-layer restricted Artin products

An eventually-unit-trivial family of local homomorphisms is represented on
every principal stage of the restricted product by a genuinely finite
product.  Consequently its `finprod` homomorphism is continuous as soon as
the individual local homomorphisms are continuous.
-/

namespace Towers.CField.Recip

open Filter Set
open scoped RestrictedProduct

noncomputable section

universe u v w

variable {ι : Type u} {G : ι → Type v} [∀ i, CommGroup (G i)]
variable (U : ∀ i, Subgroup (G i))
variable {A : Type w} [CommGroup A]
variable [∀ i, TopologicalSpace (G i)] [TopologicalSpace A]
variable [ContinuousMul A]

namespace RLFam

/-- The restricted product of an eventually-unit-trivial family of
continuous local homomorphisms is continuous. -/
theorem continuous_restricted_hom
    (D : RLFam (A := A) U)
    (hlocal : ∀ i, Continuous (D.localHom i)) :
    Continuous (D.restrictedProductHom U) := by
  rw [RestrictedProduct.continuous_dom]
  intro S hS
  let T : Set ι :=
    {i | ∀ x : G i, x ∈ U i → D.localHom i x = 1}
  have hT : Tᶜ.Finite := by
    rw [← mem_cofinite]
    exact D.eventually_units
  have hSc : Sᶜ.Finite := by
    rw [← mem_cofinite]
    exact le_principal_iff.mp hS
  have hfinite : (S ∩ T)ᶜ.Finite := by
    rw [compl_inter]
    exact hSc.union hT
  change Continuous (fun y => ∏ᶠ i,
    D.localHom i ((RestrictedProduct.inclusion G
      (fun j => (U j : Set (G j))) hS y) i))
  apply continuous_finprod
  · intro i
    exact (hlocal i).comp
      ((RestrictedProduct.continuous_eval i).comp
        (RestrictedProduct.continuous_inclusion hS))
  · intro y
    refine ⟨Set.univ, univ_mem, hfinite.subset ?_⟩
    intro i hi
    by_contra hiF
    have hiST : i ∈ S ∩ T := by
      simpa only [mem_compl_iff, not_not] using hiF
    rcases hi with ⟨z, hz, -⟩
    change D.localHom i ((RestrictedProduct.inclusion G
      (fun j => (U j : Set (G j))) hS z) i) ≠ 1 at hz
    apply hz
    apply hiST.2
    change z i ∈ U i
    exact z.2 hiST.1

end RLFam

end

end Towers.CField.Recip
