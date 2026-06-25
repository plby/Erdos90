import Towers.ClassField.NormCorrespondence.PrimeElementsGenerate

/-!
# Class Field Theory, Chapter I, Claim 1.14

This file isolates the formal argument of Claim I.1.14.  For every prime
element, the finite Lubin--Tate levels together with the maximal unramified
part generate the target field.  Two candidate Artin maps which are trivial
on all those finite levels and agree on the unramified part therefore agree
on that prime element.  Prime elements generate the multiplicative group, so
the two maps agree everywhere.
-/

namespace Towers.CField.NCorr

open Towers.CField.LFTheory

noncomputable section

universe u v

variable {K : Type u} [Field K]
  {E : Type v} [Field E] [Algebra K E]

/-- Two automorphisms of a compositum agree if they agree on each of its two
constituent fields. -/
theorem alg_intermediate_sup
    (L M : IntermediateField K E) (hLM : L ⊔ M = ⊤)
    (sigma tau : E ≃ₐ[K] E)
    (hL : ∀ x : L, sigma (x : E) = tau (x : E))
    (hM : ∀ x : M, sigma (x : E) = tau (x : E)) :
    sigma = tau := by
  let Q : IntermediateField K E :=
    { carrier := {x | sigma x = tau x}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change sigma x = tau x at hx
        change sigma y = tau y at hy
        change sigma (x + y) = tau (x + y)
        rw [map_add, map_add, hx, hy]
      mul_mem' := by
        intro x y hx hy
        change sigma x = tau x at hx
        change sigma y = tau y at hy
        change sigma (x * y) = tau (x * y)
        rw [map_mul, map_mul, hx, hy]
      algebraMap_mem' := by
        intro x
        exact sigma.commutes x |>.trans (tau.commutes x).symm
      inv_mem' := by
        intro x hx
        change sigma x = tau x at hx
        change sigma x⁻¹ = tau x⁻¹
        rw [map_inv₀, map_inv₀, hx] }
  apply AlgEquiv.ext
  intro x
  have hLQ : L ≤ Q := fun y hy ↦ hL ⟨y, hy⟩
  have hMQ : M ≤ Q := fun y hy ↦ hM ⟨y, hy⟩
  have htop : (⊤ : IntermediateField K E) ≤ Q := by
    rw [← hLM]
    exact sup_le hLQ hMQ
  exact htop trivial

/-- Agreement on every field in a family implies agreement on their
compositum. -/
theorem alg_i_sup
    {I : Type*} (L : I → IntermediateField K E)
    (sigma tau : E ≃ₐ[K] E)
    (hL : ∀ i (x : L i), sigma (x : E) = tau (x : E))
    (x : ↑(iSup L)) :
    sigma (x : E) = tau (x : E) := by
  let Q : IntermediateField K E :=
    { carrier := {y | sigma y = tau y}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := by
        intro y z hy hz
        change sigma y = tau y at hy
        change sigma z = tau z at hz
        change sigma (y + z) = tau (y + z)
        rw [map_add, map_add, hy, hz]
      mul_mem' := by
        intro y z hy hz
        change sigma y = tau y at hy
        change sigma z = tau z at hz
        change sigma (y * z) = tau (y * z)
        rw [map_mul, map_mul, hy, hz]
      algebraMap_mem' := by
        intro y
        exact sigma.commutes y |>.trans (tau.commutes y).symm
      inv_mem' := by
        intro y hy
        change sigma y = tau y at hy
        change sigma y⁻¹ = tau y⁻¹
        rw [map_inv₀, map_inv₀, hy] }
  have hsup : (⨆ i, L i) ≤ Q := by
    refine iSup_le fun i y hy ↦ ?_
    exact hL i ⟨y, hy⟩
  exact hsup x.property

section LocalField

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  (E : Type v) [Field E] [Algebra K E]

/-- Claim I.1.14.  The family `KpiLevel pi n` represents the fields
`K_{π,n}` inside the common target `K'`.  The hypotheses are precisely the
three facts invoked in the text: these levels and the unramified field
generate `K'`, both maps fix every Lubin--Tate level, and both maps have the
same Frobenius action on the unramified field. -/
theorem ext_valuative_rel
    (KpiLevel : Kˣ → ℕ → IntermediateField K E)
    (Kun : IntermediateField K E)
    (phi phi' : Kˣ →* (E ≃ₐ[K] E))
    (hcomposite : ∀ pi : Kˣ, LocalPrimeElement K pi →
      (⨆ n, KpiLevel pi n) ⊔ Kun = ⊤)
    (hphiLT : ∀ (pi : Kˣ), LocalPrimeElement K pi →
      ∀ n (x : KpiLevel pi n), phi pi (x : E) = x)
    (hphi'LT : ∀ (pi : Kˣ), LocalPrimeElement K pi →
      ∀ n (x : KpiLevel pi n), phi' pi (x : E) = x)
    (hun : ∀ (pi : Kˣ), LocalPrimeElement K pi →
      ∀ x : Kun, phi pi (x : E) = phi' pi (x : E)) :
    phi = phi' := by
  apply monoid_hom_elements K phi phi'
  intro pi hpi
  apply alg_intermediate_sup
    (⨆ n, KpiLevel pi n) Kun (hcomposite pi hpi)
  · intro x
    apply alg_i_sup (KpiLevel pi) (phi pi) (phi' pi)
    intro n y
    exact (hphiLT pi hpi n y).trans (hphi'LT pi hpi n y).symm
  · exact hun pi hpi

end LocalField

section CanonicalValuation

variable (F : Type u) [NontriviallyNormedField F]
  [IsUltrametricDist F]
  (Omega : Type v) [Field Omega] [Algebra F Omega]

/-- Hypothesis-minimal statement of Claim I.1.14. -/
def LubinArtinUniqueness : Prop :=
  letI : ValuativeRel F :=
    ValuativeRel.ofValuation (NormedField.valuation (K := F))
  ∀ [IsNonarchimedeanLocalField F],
    ∀ (KpiLevel : Fˣ → ℕ → IntermediateField F Omega)
      (Kun : IntermediateField F Omega)
      (phi phi' : Fˣ →* (Omega ≃ₐ[F] Omega)),
    (∀ pi : Fˣ, LocalPrimeElement F pi →
      (⨆ n, KpiLevel pi n) ⊔ Kun = ⊤) →
    (∀ (pi : Fˣ), LocalPrimeElement F pi →
      ∀ n (x : KpiLevel pi n), phi pi (x : Omega) = x) →
    (∀ (pi : Fˣ), LocalPrimeElement F pi →
      ∀ n (x : KpiLevel pi n), phi' pi (x : Omega) = x) →
    (∀ (pi : Fˣ), LocalPrimeElement F pi →
      ∀ x : Kun, phi pi (x : Omega) = phi' pi (x : Omega)) →
    phi = phi'

/-- Claim I.1.14 with the canonical valuation, so its statement has no
auxiliary valuative-relation hypothesis. -/
theorem lubinArtinUniqueness : LubinArtinUniqueness F Omega := by
  letI : ValuativeRel F :=
    ValuativeRel.ofValuation (NormedField.valuation (K := F))
  dsimp only [LubinArtinUniqueness]
  intro _ KpiLevel Kun phi phi' hcomposite hphiLT hphi'LT hun
  apply ext_valuative_rel F Omega KpiLevel Kun phi phi'
  · intro pi hpi
    exact hcomposite pi hpi
  · intro pi hpi
    exact hphiLT pi hpi
  · intro pi hpi
    exact hphi'LT pi hpi
  · intro pi hpi
    exact hun pi hpi

end CanonicalValuation

end

end Towers.CField.NCorr
