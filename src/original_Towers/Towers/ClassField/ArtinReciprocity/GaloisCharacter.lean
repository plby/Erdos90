import Towers.ClassField.ArtinReciprocity.Statements
import Towers.NumberTheory.Ramification.RamificationDiscriminant
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Chapter V, Section 3: Theorem 3.27

This file states Milne's conductor--discriminant product formula literally:
`disc(L/K) = ∏ χ, f₀(χ ∘ ψ_{L/K})`

and

`f(L/K) = lcm χ, f(χ ∘ ψ_{L/K})`.

The relative discriminant ideal already exists in the repository.  What is
not yet present is a global Weber-character type, together with the conductor
of a character composed with the Artin map.  `ACData` isolates
exactly that interface while retaining the actual Artin map and the actual
finite and infinite parts of every conductor.

The first displayed equality is reduced to its prime-by-prime exponent
formula; the reconstruction of the ideal is proved here.  The second is
reduced to the corresponding finite-prime maximum and real-prime union
formulas; the reconstruction of the modulus is also proved here.  These are
the genuinely local conductor inputs absent from the current library.
-/

namespace Towers.CField.ARecip

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open RCGroups
open scoped nonZeroDivisors BigOperators

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The character group `G∨ = Hom(G, ℂˣ)` in Theorem V.3.27. -/
abbrev GaloisCharacter (L : ANExt K) :=
  Gal(L.carrier/K) →* ℂˣ

/-- The least common multiple of finitely many number-field moduli: maximum
at each finite prime and union at the real infinite primes. -/
def modulusLcm {ι : Type*} (s : Finset ι) (f : ι → Modulus K) : Modulus K := by
  classical
  exact {
    finite := s.sup fun i ↦ (f i).finite
    infinite := s.biUnion fun i ↦ (f i).infinite }

/-- The missing conductor interface for `χ ∘ ψ_{L/K}`.

`characterConductor χ` denotes `f(χ ∘ ψ_{L/K})`, while
`extensionConductor` denotes `f(L/K)`.  The Artin map itself and its defining
property are retained, so the character being assigned a conductor is the
literal composite occurring in the source. -/
structure ACData (L : ANExt K) where
  modulus : Modulus K
  artinMap :
    IdealsPrimeTo (𝓞 K) K modulus.finiteSupport →* Gal(L.carrier/K)
  isArtinMap : IsArtinMap L modulus.finiteSupport artinMap
  characterConductor : GaloisCharacter L → Modulus K
  extensionConductor : Modulus K

namespace ACData

variable {L : ANExt K}
    (D : ACData L)

/-- The literal composite `χ ∘ ψ_{L/K}` at the defining modulus stored in
`D`. -/
def composedArtinCharacter (χ : GaloisCharacter L) :
    IdealsPrimeTo (𝓞 K) K D.modulus.finiteSupport →* ℂˣ :=
  χ.comp D.artinMap

end ACData

/-- The finite part of the conductor product in Theorem V.3.27. -/
def characterConductorProduct
    {L : ANExt K}
    (D : ACData L) : Ideal (𝓞 K) := by
  letI : Fintype (GaloisCharacter L) := Fintype.ofFinite _
  exact ∏ χ : GaloisCharacter L, (D.characterConductor χ).finiteIdeal

/-- The lcm of the conductors `f(χ ∘ ψ_{L/K})`. -/
def characterConductorLcm
    {L : ANExt K}
    (D : ACData L) : Modulus K := by
  letI : Fintype (GaloisCharacter L) := Fintype.ofFinite _
  exact modulusLcm Finset.univ D.characterConductor

/-- The exact local input for the conductor--discriminant product formula:
at every finite prime, the discriminant exponent is the sum of the conductor
exponents of all characters. -/
def ConductorDiscriminantFormula
    {L : ANExt K}
    (D : ACData L) : Prop := by
  letI : Fintype (GaloisCharacter L) := Fintype.ofFinite _
  exact ∀ p : HeightOneSpectrum (𝓞 K),
    FractionalIdeal.count K p
        (relativeDiscriminantIdeal (𝓞 K) (𝓞 L.carrier) :
          FractionalIdeal (𝓞 K)⁰ K) =
      ∑ χ : GaloisCharacter L,
        ((D.characterConductor χ).finite p : ℤ)

/-- The exact local input for the lcm formula: finite exponents are maxima,
and a real prime occurs precisely when it occurs in at least one character
conductor. -/
def ConductorMaximumFormula
    {L : ANExt K}
    (D : ACData L) : Prop := by
  letI : Fintype (GaloisCharacter L) := Fintype.ofFinite _
  exact
    (∀ p : HeightOneSpectrum (𝓞 K),
      D.extensionConductor.finite p =
        Finset.univ.sup fun χ : GaloisCharacter L ↦
          (D.characterConductor χ).finite p) ∧
    ∀ w : RealInfinitePlace K,
      w ∈ D.extensionConductor.infinite ↔
        ∃ χ : GaloisCharacter L,
          w ∈ (D.characterConductor χ).infinite

/-- The exponent of the integral ideal represented by the finite part of a
modulus is its stored exponent. -/
theorem count_finiteIdeal (m : Modulus K)
    (p : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K p
        (m.finiteIdeal : FractionalIdeal (𝓞 K)⁰ K) =
      (m.finite p : ℤ) := by
  classical
  rw [Modulus.finiteIdeal, Finsupp.prod]
  change FractionalIdeal.count K p
      (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K
        (∏ q ∈ m.finite.support, q.asIdeal ^ m.finite q)) = _
  rw [map_prod]
  simp_rw [map_pow]
  rw [FractionalIdeal.count_prod]
  · (simp [FractionalIdeal.count_pow, FractionalIdeal.count_maximal] ; omega)
  · intro q hq
    exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr q.ne_bot)

omit [NumberField K] in
/-- The finite ideal of every modulus is nonzero. -/
theorem ideal_ne_bot (m : Modulus K) :
    m.finiteIdeal ≠ (0 : Ideal (𝓞 K)) := by
  classical
  rw [Modulus.finiteIdeal, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun p _ ↦ pow_ne_zero _ p.ne_bot

/-- The relative discriminant ideal is nonzero. -/
theorem relative_discriminant_bot
    (L : ANExt K) :
    relativeDiscriminantIdeal (𝓞 K) (𝓞 L.carrier) ≠
      (0 : Ideal (𝓞 K)) := by
  have hdifferent : differentIdeal (𝓞 K) (𝓞 L.carrier) ≠
      (0 : Ideal (𝓞 L.carrier)) := by
    rw [ne_eq, ← FractionalIdeal.coeIdeal_inj (K := L.carrier),
      coeIdeal_differentIdeal (K := K)]
    simp
  unfold relativeDiscriminantIdeal
  intro h
  exact hdifferent (Ideal.relNorm_eq_bot_iff.mp h)

/-- Evaluation commutes with a finite supremum of finitely supported
functions. -/
private theorem finsupp_finset_sup
    {ι α : Type*}
    (s : Finset ι) (f : ι → α →₀ ℕ) (a : α) :
    (s.sup f) a = s.sup fun i ↦ f i a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sup_empty, Finset.sup_empty, bot_eq_zero,
        Finsupp.zero_apply]
      rfl
  | @insert i s hi ih =>
      rw [Finset.sup_insert, Finset.sup_insert, Finsupp.sup_apply, ih]

/-- Prime-by-prime conductor exponents reconstruct the first displayed
ideal equality in Theorem V.3.27. -/
theorem discriminant_character_conductor
    (L : ANExt K)
    (D : ACData L)
    (hlocal : ConductorDiscriminantFormula D) :
    relativeDiscriminantIdeal (𝓞 K) (𝓞 L.carrier) =
      characterConductorProduct D := by
  classical
  letI : Fintype (GaloisCharacter L) := Fintype.ofFinite _
  unfold characterConductorProduct
  apply FractionalIdeal.coeIdeal_injective (K := K)
  let disc : FractionalIdeal (𝓞 K)⁰ K :=
    relativeDiscriminantIdeal (𝓞 K) (𝓞 L.carrier)
  let conductorIdeal : GaloisCharacter L → FractionalIdeal (𝓞 K)⁰ K :=
    fun χ ↦ (D.characterConductor χ).finiteIdeal
  have hdisc : disc ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr
      (relative_discriminant_bot L)
  have hconductor (χ : GaloisCharacter L) : conductorIdeal χ ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr
      (ideal_ne_bot (D.characterConductor χ))
  have hproduct : (∏ χ, conductorIdeal χ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun χ _ ↦ hconductor χ
  change FractionalIdeal.coeIdealHom (𝓞 K)⁰ K
      (relativeDiscriminantIdeal (𝓞 K) (𝓞 L.carrier)) =
    FractionalIdeal.coeIdealHom (𝓞 K)⁰ K
      (∏ χ : GaloisCharacter L,
        (D.characterConductor χ).finiteIdeal)
  rw [map_prod]
  change disc = ∏ χ, conductorIdeal χ
  calc
    disc = ∏ᶠ p : HeightOneSpectrum (𝓞 K),
        (p.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          FractionalIdeal.count K p disc :=
      (FractionalIdeal.finprod_heightOneSpectrum_factorization'
        (K := K) hdisc).symm
    _ = ∏ᶠ p : HeightOneSpectrum (𝓞 K),
        (p.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          FractionalIdeal.count K p (∏ χ, conductorIdeal χ) := by
      apply finprod_congr
      intro p
      congr 1
      rw [FractionalIdeal.count_prod]
      · change FractionalIdeal.count K p disc =
          ∑ χ : GaloisCharacter L,
            FractionalIdeal.count K p
              ((D.characterConductor χ).finiteIdeal :
                FractionalIdeal (𝓞 K)⁰ K)
        rw [hlocal p]
        apply Finset.sum_congr rfl
        intro χ hχ
        exact (count_finiteIdeal
          (D.characterConductor χ) p).symm
      · intro χ hχ
        exact hconductor χ
    _ = ∏ χ, conductorIdeal χ :=
      FractionalIdeal.finprod_heightOneSpectrum_factorization'
        (K := K) hproduct

/-- The local maximum/union statement reconstructs the lcm equality of
moduli. -/
theorem extension_conductor_lcm
    {L : ANExt K}
    (D : ACData L)
    (hlocal : ConductorMaximumFormula D) :
    D.extensionConductor = characterConductorLcm D := by
  classical
  letI : Fintype (GaloisCharacter L) := Fintype.ofFinite _
  have hfinite : D.extensionConductor.finite =
      (characterConductorLcm D).finite := by
    apply Finsupp.ext
    intro p
    rw [hlocal.1 p]
    exact (finsupp_finset_sup
      Finset.univ (fun χ : GaloisCharacter L ↦
        (D.characterConductor χ).finite) p).symm
  have hinfinite : D.extensionConductor.infinite =
      (characterConductorLcm D).infinite := by
    ext w
    simpa [characterConductorLcm, modulusLcm] using hlocal.2 w
  cases hE : D.extensionConductor with
  | mk ef ei =>
      cases hC : characterConductorLcm D with
      | mk cf ci =>
          rw [hE, hC] at hfinite hinfinite
          cases hfinite
          cases hinfinite
          rfl

/-- Complex characters separate the elements of the finite abelian Galois
group.  This is the group-theoretic fact cited immediately after the second
formula in the source. -/
theorem i_inf_character
    (L : ANExt K) :
    (⨅ χ : GaloisCharacter L, χ.ker) = ⊥ := by
  letI : CommGroup Gal(L.carrier/K) :=
    { (inferInstance : Group Gal(L.carrier/K)) with mul_comm := mul_comm' }
  apply le_antisymm
  · intro σ hσ
    rw [Subgroup.mem_bot]
    by_contra hσ1
    obtain ⟨χ, hχ⟩ :=
      CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
        Gal(L.carrier/K) ℂ hσ1
    exact hχ (MonoidHom.mem_ker.mp (Subgroup.mem_iInf.mp hσ χ))
  · exact bot_le

/-- Sharp reduction of the full Theorem V.3.27 to its two genuinely local
conductor formulas. -/
theorem local_conductor_formulas
    (L : ANExt K)
    (D : ACData L)
    (hdiscriminant : ConductorDiscriminantFormula D)
    (hconductor : ConductorMaximumFormula D) :
    relativeDiscriminantIdeal (𝓞 K) (𝓞 L.carrier) =
      characterConductorProduct D ∧
    D.extensionConductor = characterConductorLcm D
  := by
  exact ⟨
    discriminant_character_conductor L D hdiscriminant,
    extension_conductor_lcm D hconductor⟩

end

end Towers.CField.ARecip
