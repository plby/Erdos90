import Submission.FieldTheory.QuotientKoch.LayerObstructionPersistence


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open ONCompar

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The actual initial Koch candidate-kernel image is covered at the canonical tame
Koch relation-word radius in every canonical Zassenhaus layer through `depth`.
-/
def RadiusVerifiedThrough
    (D : KRData)
    (depth : ℕ) :
    Prop :=
  ∀ n : ℕ, n ≤ depth → D.ImageCoveredRadius n

/--
The same finite verification prefix, indexed by the finite type of depths at
most `depth`.
-/
def RadiusVerifiedPrefix
    (D : KRData)
    (depth : ℕ) :
    Prop :=
  ∀ n : Fin (depth + 1), D.ImageCoveredRadius n

/--
The natural-number and finite-index presentations of a finite Zassenhaus
verification prefix are equivalent.
-/
lemma radius_verified_prefix
    (D : KRData)
    (depth : ℕ) :
    D.RadiusVerifiedThrough depth ↔
      D.RadiusVerifiedPrefix depth := by
  constructor
  · intro h n
    exact h n (Nat.lt_succ_iff.mp n.isLt)
  · intro h n hn
    exact h ⟨n, Nat.lt_succ_iff.mpr hn⟩

/--
Verification of a deeper Zassenhaus prefix implies verification of every
shallower prefix.
-/
lemma relation_verified_through
    (D : KRData)
    {lower upper : ℕ}
    (hlowerUpper : lower ≤ upper)
    (hupper : D.RadiusVerifiedThrough upper) :
    D.RadiusVerifiedThrough lower := by
  intro n hn
  exact hupper n (hn.trans hlowerUpper)

/--
The concrete finite quotient Koch theorem is equivalent to verification of every
finite canonical Zassenhaus relation-word-radius prefix.
-/
lemma radius_verified_through
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ depth : ℕ, D.RadiusVerifiedThrough depth := by
  rw [D.fin_factorization_radius]
  constructor
  · intro h depth n hn
    exact h n
  · intro h n
    exact h n n le_rfl

/--
A finite Zassenhaus verification prefix fails exactly when one depth inside the
prefix has a canonical-radius tame Koch relation-word obstruction.
-/
lemma radius_image_obstruction
    (D : KRData)
    (depth : ℕ) :
    ¬ D.RadiusVerifiedThrough depth ↔
      ∃ n : ℕ, n ≤ depth ∧ D.RadiusImageObstruction n := by
  constructor
  · intro hnot
    rw [RadiusVerifiedThrough] at hnot
    rcases not_forall.mp hnot with ⟨n, hn⟩
    rcases Classical.not_imp.mp hn with ⟨hndepth, hnotcover⟩
    letI : Finite (ONCompar.OpenNormalLayer
        (zassenhausOpenSubgroup n)) :=
      pro_p_open (zassenhausOpenSubgroup n)
    exact ⟨n, hndepth,
      (radius_image_not
        initialKochQuotient
        (initialTameRelator D.frobeniusLift)
        (zassenhausOpenSubgroup n)).mpr hnotcover⟩
  · rintro ⟨n, hndepth, hobs⟩ hverified
    letI : Finite (ONCompar.OpenNormalLayer
        (zassenhausOpenSubgroup n)) :=
      pro_p_open (zassenhausOpenSubgroup n)
    exact (radius_image_not
      initialKochQuotient
      (initialTameRelator D.frobeniusLift)
      (zassenhausOpenSubgroup n)).mp hobs (hverified n hndepth)

/--
If a finite Zassenhaus verification prefix fails, every longer prefix fails too.
-/
lemma not_verified_through
    (D : KRData)
    {lower upper : ℕ}
    (hlowerUpper : lower ≤ upper)
    (hlower : ¬ D.RadiusVerifiedThrough lower) :
    ¬ D.RadiusVerifiedThrough upper := by
  intro hupper
  exact hlower (D.relation_verified_through hlowerUpper hupper)

/--
The concrete finite quotient Koch theorem fails exactly when one finite
canonical Zassenhaus relation-word-radius verification prefix fails.
-/
lemma not_radius_verified
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ depth : ℕ, ¬ D.RadiusVerifiedThrough depth := by
  constructor
  · intro hnot
    rcases (D.not_radius_obstruction).mp
      hnot with ⟨n, hobs⟩
    exact ⟨n,
      (D.radius_image_obstruction
        n).mpr ⟨n, le_rfl, hobs⟩⟩
  · rintro ⟨depth, hdepth⟩
    rw [D.radius_verified_through]
    exact not_forall.mpr ⟨depth, hdepth⟩

/--
For fixed finite Zassenhaus prefix, verification at the canonical tame Koch
relation-word radii is a finite decidable search problem.
-/
def radiusVerifiedDecidable
    (D : KRData)
    (depth : ℕ) :
    Decidable (D.RadiusVerifiedThrough depth) := by
  letI : DecidablePred
      (fun n : Fin (depth + 1) =>
        D.ImageCoveredRadius n) :=
    fun n => D.imageCoveredDecidable n
  letI : Decidable (D.RadiusVerifiedPrefix depth) :=
    Fintype.decidableForallFintype
  exact decidable_of_iff'
    (D.RadiusVerifiedPrefix depth)
    (D.radius_verified_prefix depth)

end KRData

end TBluepr
end Submission
