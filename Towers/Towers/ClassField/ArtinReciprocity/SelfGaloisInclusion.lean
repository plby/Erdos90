import Towers.ClassField.ArtinReciprocity.Statements

/-!
# Chapter V, Section 3, Corollary 3.4

The source states that for every finite abelian extension `L/K`, the image
`Nm_{L/K}(I_L^S)` is contained in the kernel of the Artin map.  Its proof is
to take the intermediate field `K' = L` in Proposition 3.3: the Artin map for
`L/L` has values in the trivial group `Gal(L/L)`.

The tracked files prove Proposition 3.3 on every prime generator and define
`idealNormSubgroup`, but Mathlib still has no compatible literal norm
homomorphism on the groups of fractional ideals prime to `S`.  The theorem
below therefore takes exactly the two missing transport facts as premises:

* the range of the supplied norm homomorphism is `idealNormSubgroup`; and
* its Artin square is the square from Proposition 3.3.

No reciprocity theorem is used, and no stronger kernel hypothesis is assumed.
-/

namespace Towers.CField.ARecip

open IsDedekindDomain NumberField
open RCGroups

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The right vertical map in Proposition 3.3 when the intermediate field
is `L`: an `L`-automorphism is in particular a `K`-automorphism. -/
def selfGaloisInclusion (L : ANExt K) :
    Gal(L.carrier/L.carrier) →* Gal(L.carrier/K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Pure group-theoretic content of the proof: in a commutative square, if
the upper-right group is trivial, the lower map kills the norm range. -/
theorem commutative_square_subsingleton
    {I' I G' G : Type*} [Group I'] [Group I] [Group G'] [Group G]
    [Subsingleton G']
    (norm : I' →* I) (ψ' : I' →* G') (ψ : I →* G) (embed : G' →* G)
    (hsquare : ψ.comp norm = embed.comp ψ') :
    norm.range ≤ ψ.ker := by
  rintro y ⟨x, rfl⟩
  change ψ (norm x) = 1
  have hx := DFunLike.congr_fun hsquare x
  simpa only [MonoidHom.comp_apply, Subsingleton.elim (ψ' x) 1,
    map_one] using hx

/-- Corollary V.3.4 from the literal ideal-level instance of Proposition
3.3.  `I_L^S` is left abstract because this is exactly the fractional-ideal
transport object absent from the current library.

The equality `hnormRange` says that `norm` realizes the already defined
`idealNormSubgroup`; `hsquare` is precisely Proposition 3.3 for this norm and
the two Artin maps. -/
theorem ideal_norm_bridge
    (L : ANExt K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ψ : IdealsPrimeTo (𝓞 K) K S →* Gal(L.carrier/K))
    {I_L_S : Type u} [Group I_L_S]
    (norm : I_L_S →* IdealsPrimeTo (𝓞 K) K S)
    (ψtop : I_L_S →* Gal(L.carrier/L.carrier))
    (hnormRange : norm.range = L.idealNormSubgroup S)
    (hsquare : ψ.comp norm = (selfGaloisInclusion L).comp ψtop) :
    (L.RamifiedPrimes ⊆ (S : Set (HeightOneSpectrum (𝓞 K))) →
          IsArtinMap L S ψ → L.idealNormSubgroup S ≤ ψ.ker) := by
  intro _hS _hψ
  rw [← hnormRange]
  exact commutative_square_subsingleton
    norm ψtop ψ (selfGaloisInclusion L) hsquare

/-- The homomorphism on the quotient displayed immediately after Corollary
V.3.4 in the source. -/
def quotientArtinMap
    (L : ANExt K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ψ : IdealsPrimeTo (𝓞 K) K S →* Gal(L.carrier/K))
    (hS : L.RamifiedPrimes ⊆ (S : Set (HeightOneSpectrum (𝓞 K))))
    (hψ : IsArtinMap L S ψ)
    (hcor : (L.RamifiedPrimes ⊆ (S : Set (HeightOneSpectrum (𝓞 K))) →
          IsArtinMap L S ψ → L.idealNormSubgroup S ≤ ψ.ker)) :
    (IdealsPrimeTo (𝓞 K) K S ⧸ L.idealNormSubgroup S) →*
      Gal(L.carrier/K) :=
  QuotientGroup.lift (L.idealNormSubgroup S) ψ (hcor hS hψ)

@[simp]
theorem quotient_artin_mk
    (L : ANExt K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ψ : IdealsPrimeTo (𝓞 K) K S →* Gal(L.carrier/K))
    (hS : L.RamifiedPrimes ⊆ (S : Set (HeightOneSpectrum (𝓞 K))))
    (hψ : IsArtinMap L S ψ)
    (hcor : (L.RamifiedPrimes ⊆ (S : Set (HeightOneSpectrum (𝓞 K))) →
          IsArtinMap L S ψ → L.idealNormSubgroup S ≤ ψ.ker))
    (I : IdealsPrimeTo (𝓞 K) K S) :
    quotientArtinMap L S ψ hS hψ hcor
        (QuotientGroup.mk' (L.idealNormSubgroup S) I) = ψ I :=
  QuotientGroup.lift_mk' _ _ _

end

end Towers.CField.ARecip
