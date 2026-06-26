import Mathlib.GroupTheory.Rank
import Towers.ClassField.ArtinReciprocity.Chebotarev

/-!
# Chapter VIII, Section 7: density theorems

Theorem 7.1 is the analytic nonvanishing statement `L(1, chi) != 0`, and
Theorem 7.2 deduces the prime-ideal theorem for ray classes from it.  The
analytic continuation and nonvanishing theory needed for those statements is
not presently available in Mathlib.

Theorems 7.3 and 7.4 are the abelian and general Chebotarev density theorems.
The Milne layer states the exact Chebotarev property and develops its natural
density consequences.  The wrappers below give the source-numbered forms used
in this section.  Natural density is stronger than the Dirichlet density stated
in the source; the missing work is the analytic proof of the supplied
Chebotarev hypothesis, not a finite-group calculation.
-/

namespace Towers.CField.CDensit

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- **Corollary 7.3, conditional natural-density form.** In an abelian
extension every Frobenius element has density `1 / |G|`. -/
theorem density_abelian_frobenius
    {G : Type*} [CommGroup G] [Finite G]
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) (sigma : G) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk sigma))
      (1 / Nat.card G) :=
  abelian_density_chebotarev K hcheb sigma

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The exact arithmetic Frobenius statement of Theorem 7.4. -/
abbrev DensityStatement : Prop := ChebotarevDensityTheorem K L

/-- **Theorem 7.4 (Chebotarev), conditional natural-density form.** The
primes with Frobenius in a conjugacy class have density `|C| / |G|`. -/
theorem frobenius_conjugacy_density
    (hcheb : DensityStatement K L) (C : ConjClasses Gal(L/K)) :
    PNDensit K
      {p | arithmeticFrobeniusClass K L p = C}
      ((C.carrier.ncard : ℝ) / Nat.card Gal(L/K)) :=
  natural_density_frobenius K L hcheb C

/-- The finite-group count used in the proof of Theorem 7.4: the size of a
conjugacy class times the size of the centralizer is the order of the group. -/
theorem conjugacy_card_centralizer
    {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier *
        Nat.card (Subgroup.centralizer ({g} : Set G)) = Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (ConjClasses.mk g).carrier := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer (ConjAct G) g) := Fintype.ofFinite _
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, ConjClasses.card_carrier,
    Nat.div_mul_cancel]
  have hdvd := (MulAction.stabilizer (ConjAct G) g).card_subgroup_dvd_card
  rw [Nat.card_congr (ConjAct.toConjAct (G := G)).toEquiv.symm] at hdvd
  simpa only [Nat.card_eq_fintype_card] using hdvd

end

end Towers.CField.CDensit
