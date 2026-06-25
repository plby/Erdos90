import Submission.ClassField.TateCohomology.AddEquivAbelianization
import Submission.ClassField.Shifting.ZeroResTop

/-!
# Milne, Class Field Theory, Example II.3.14

For a local Galois extension, later chapters supply `C = Lˣ`, Hilbert 90,
and the canonical fundamental class.  The group-cohomological content needed
here is independent of local-field topology: Tate's degree-minus-two shift
identifies the abelianization of `G` with `H_T⁰(G,C)`.  Its inverse is the
abstract Artin map.
-/

namespace Submission.CField.Shifting

open AddSubgroup CategoryTheory.Limits Rep

noncomputable section

variable {G : Type} [Group G] [Fintype G]

/-- The fundamental-class isomorphism from the additive group underlying
`Gᵃᵇ` to degree-zero Tate cohomology.  In Example II.3.14, `C = Lˣ` and
`gamma = u_{L/K}`. -/
noncomputable def fundamentalAbelianizationEquiv
    (C : Rep ℤ G) (gamma : groupCohomology C 2)
    (hgamma : ∀ x : groupCohomology C 2, x ∈ zmultiples gamma)
    (hcardG : Nat.card (groupCohomology C 2) = Nat.card G)
    (hC1 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype C) 1))
    (hcardH : ∀ H : Subgroup G,
      Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H) :
    Additive (Abelianization G) ≃+ tateCohomologyZero C :=
  (TCohomo.homology1Abelianization G).symm.trans
    (cohomologyResTop C gamma hgamma hcardG hC1 hcardH).negTwo

/-- **Example II.3.14.** The abstract Artin map is the inverse of the
fundamental-class isomorphism.  For local fields, degree-zero Tate cohomology
is `Kˣ / Nm(Lˣ)`, so this becomes the usual local Artin map. -/
noncomputable def abstractArtinMap
    (C : Rep ℤ G) (gamma : groupCohomology C 2)
    (hgamma : ∀ x : groupCohomology C 2, x ∈ zmultiples gamma)
    (hcardG : Nat.card (groupCohomology C 2) = Nat.card G)
    (hC1 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype C) 1))
    (hcardH : ∀ H : Subgroup G,
      Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H) :
    tateCohomologyZero C ≃+ Additive (Abelianization G) :=
  (fundamentalAbelianizationEquiv C gamma hgamma hcardG hC1 hcardH).symm

@[simp]
theorem abstract_fundamental_abelianization
    (C : Rep ℤ G) (gamma : groupCohomology C 2)
    (hgamma : ∀ x : groupCohomology C 2, x ∈ zmultiples gamma)
    (hcardG : Nat.card (groupCohomology C 2) = Nat.card G)
    (hC1 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype C) 1))
    (hcardH : ∀ H : Subgroup G,
      Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (g : Additive (Abelianization G)) :
    abstractArtinMap C gamma hgamma hcardG hC1 hcardH
        (fundamentalAbelianizationEquiv C gamma hgamma hcardG hC1 hcardH g) = g :=
  (fundamentalAbelianizationEquiv C gamma hgamma hcardG hC1 hcardH).left_inv g

end

end Submission.CField.Shifting
