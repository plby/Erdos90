import Mathlib.GroupTheory.QuotientGroup.Basic
import Towers.ClassField.Ideles.Ideles

/-!
# Chapter V, Section 5: the algebraic form of reciprocity

The construction of the global Artin map and the proofs of the reciprocity
and existence theorems are not currently available in the imported local and
global class-field-theory development.  This file records the exact algebraic
consequences used in Theorem 5.3 once such a map has been constructed:

* triviality on principal ideles is equivalent to containment of the
  principal-idele subgroup in the kernel;
* such a map descends to the idele class group; and
* a surjective map with kernel `K^x * N` induces the claimed quotient
  isomorphism.

No existence assumption is installed as an axiom or typeclass.
-/

noncomputable section

namespace Towers.CField.Recip

open Towers.CField.Ideles

variable (R K G : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [Group G]

/-- A homomorphism on ideles satisfies the principal-idele clause of the
global reciprocity law. -/
def TrivialPrincipalIdeles (phi : IdeleGroup R K →* G) : Prop :=
  ∀ x : Kˣ, phi (principalIdele R K x) = 1

/-- **Theorem V.5.3(a), algebraic form.** Triviality on every diagonal idele
is exactly containment of the principal-idele subgroup in the kernel. -/
theorem trivial_principal_ideles
    (phi : IdeleGroup R K →* G) :
    TrivialPrincipalIdeles R K G phi ↔
      principalIdeles R K ≤ phi.ker := by
  constructor
  · intro h y hy
    rcases hy with ⟨x, rfl⟩
    exact h x
  · intro h x
    exact h ⟨x, rfl⟩

/-- A homomorphism satisfying reciprocity on principal ideles descends to the
idele class group. -/
def ideleClassMap (phi : IdeleGroup R K →* G)
    (hphi : TrivialPrincipalIdeles R K G phi) :
    IdeleClassGroup R K →* G :=
  QuotientGroup.lift (principalIdeles R K) phi
    ((trivial_principal_ideles R K G phi).mp hphi)

@[simp]
theorem idele_mk (phi : IdeleGroup R K →* G)
    (hphi : TrivialPrincipalIdeles R K G phi)
    (x : IdeleGroup R K) :
    ideleClassMap R K G phi hphi (QuotientGroup.mk' (principalIdeles R K) x) =
      phi x :=
  QuotientGroup.lift_mk' _ _ _

/-- The group-theoretic hypotheses in Theorem V.5.3(b), with `N` standing
for the image of the idele norm from a finite abelian extension. -/
def FiniteReciprocityLaw (phi : IdeleGroup R K →* G)
    (N : Subgroup (IdeleGroup R K)) : Prop :=
  Function.Surjective phi ∧ principalIdeles R K ⊔ N = phi.ker

/-- **Theorem V.5.3(b), algebraic quotient step.** A surjective homomorphism
whose kernel is `K^x * N` induces an isomorphism from the corresponding idele
quotient.  The arithmetic theorem is the assertion that the global Artin map
satisfies `FiniteReciprocityLaw` for the idele norm subgroup. -/
def finiteReciprocityEquiv (phi : IdeleGroup R K →* G)
    (N : Subgroup (IdeleGroup R K))
    (hphi : FiniteReciprocityLaw R K G phi N) :
    IdeleGroup R K ⧸ (principalIdeles R K ⊔ N) ≃* G :=
  QuotientGroup.liftEquiv (principalIdeles R K ⊔ N) hphi.1 hphi.2

@[simp]
theorem finite_reciprocity_mk (phi : IdeleGroup R K →* G)
    (N : Subgroup (IdeleGroup R K))
    (hphi : FiniteReciprocityLaw R K G phi N)
    (x : IdeleGroup R K) :
    finiteReciprocityEquiv R K G phi N hphi
        (QuotientGroup.mk' (principalIdeles R K ⊔ N) x) = phi x :=
  QuotientGroup.liftEquiv_mk _ hphi.1 hphi.2 x

end Towers.CField.Recip
