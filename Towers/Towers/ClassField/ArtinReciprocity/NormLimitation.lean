import Towers.ClassField.LocalReciprocity.FiniteIndexCore
import Towers.ClassField.ArtinReciprocity.Statements

/-!
# Chapter V, Section 3, Theorem 3.16: Norm Limitation

Milne's literal statement allows an arbitrary finite extension `L/K`.  If
`L'/K` is its maximal abelian subextension and `m` is any defining modulus
for `L'/K`, then

`i(K_{m,1}) Nm_{L/K}(I_L^m) = i(K_{m,1}) Nm_{L'/K}(I_{L'}^m)`.

The tracked Chapter V ideal API only bundles *abelian* finite extensions.
This file supplies the same prime-generator definition of the ideal norm
subgroup for an arbitrary finite number-field extension, without adding a
Galois or separability assumption.  It then reduces the equality to the two
standard inputs of norm limitation:
* norm transitivity gives containment in the norm subgroup of `L'`; and
* the norm-index formula says that the left subgroup has index `[L' : K]`.

The defining-modulus isomorphism proves the same index formula for the right
subgroup, so the existing finite-index group lemma finishes the equality.
The genuinely unavailable global theorem is isolated as the left norm-index
formula; no reciprocity or norm-limitation assertion is hidden in the other
definitions.
-/

namespace Towers.CField.ARecip

open IsDedekindDomain NumberField
open RCGroups
open scoped nonZeroDivisors

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- An arbitrary finite extension of a number field.  Unlike the existing
`ANExt`, this imposes no Galois or commutativity
hypothesis. -/
structure NFExt (K : Type u) [Field K] [NumberField K] where
  carrier : Type u
  [field : Field carrier]
  [numberField : NumberField carrier]
  [algebra : Algebra K carrier]
  [finiteDimensional : FiniteDimensional K carrier]

attribute [instance]
  NFExt.field
  NFExt.numberField
  NFExt.algebra
  NFExt.finiteDimensional

namespace NFExt

/-- A prime of an arbitrary finite extension together with the prime below
it. -/
structure PAbove (L : NFExt K) where
  downstairs : HeightOneSpectrum (𝓞 K)
  upstairs : HeightOneSpectrum (𝓞 L.carrier)
  liesOver : upstairs.asIdeal.LiesOver downstairs.asIdeal

/-- The norm of a prime generator, using `N(P) = p ^ f(P/p)`. -/
def PAbove.normGenerator (L : NFExt K)
    (P : L.PAbove) : (FractionalIdeal (𝓞 K)⁰ K)ˣ := by
  letI : P.upstairs.asIdeal.LiesOver P.downstairs.asIdeal := P.liesOver
  exact ANExt.primeFractionalIdeal P.downstairs ^
    P.downstairs.asIdeal.inertiaDeg P.upstairs.asIdeal

/-- Image of the ideal norm on fractional ideals, presented by its prime
generators.  This definition does not require the extension to be abelian. -/
def totalIdealSubgroup (L : NFExt K) :
    Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Subgroup.closure (Set.range fun P : L.PAbove ↦ P.normGenerator L)

/-- The norm subgroup inside the ideals prime to `S`. -/
def idealNormSubgroup (L : NFExt K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (IdealsPrimeTo (𝓞 K) K S) :=
  L.totalIdealSubgroup.comap (IdealsPrimeTo (𝓞 K) K S).subtype

end NFExt

/-- Forget that a finite abelian extension is abelian. -/
def ANExt.toFinite
    (L : ANExt K) : NFExt K where
  carrier := L.carrier

/-- The arbitrary-extension and abelian-extension prime-above structures
agree after forgetting abelianity. -/
def abelianAboveEquiv (L : ANExt K) :
    L.toFinite.PAbove ≃ L.PAbove where
  toFun P := ⟨P.downstairs, P.upstairs, P.liesOver⟩
  invFun P := ⟨P.downstairs, P.upstairs, P.liesOver⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

@[simp]
theorem generator_abelian_above
    (L : ANExt K) (P : L.toFinite.PAbove) :
    P.normGenerator L.toFinite =
      (abelianAboveEquiv L P).normGenerator L := by
  rfl

/-- On abelian extensions, the arbitrary-extension total norm subgroup is
the tracked total norm subgroup. -/
theorem total_ideal_norm
    (L : ANExt K) :
    L.toFinite.totalIdealSubgroup = L.totalIdealSubgroup := by
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨abelianAboveEquiv L P, by simp⟩
  · rintro ⟨P, rfl⟩
    exact ⟨(abelianAboveEquiv L).symm P, by simp⟩

/-- Hence the prime-to-`S` norm subgroups also agree. -/
theorem ideal_norm_subgroup
    (L : ANExt K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    L.toFinite.idealNormSubgroup S = L.idealNormSubgroup S := by
  unfold NFExt.idealNormSubgroup
    ANExt.idealNormSubgroup
  rw [total_ideal_norm]

/-- A chosen model `L'` is the maximal abelian subextension of `L` when it
embeds in `L` and every finite abelian extension embedded in `L` factors
through that embedding. -/
def MaximalSubextension
    (L : NFExt K)
    (L' : ANExt K) : Prop :=
  ∃ inclusion : L'.carrier →ₐ[K] L.carrier,
    ∀ (F : ANExt K)
      (j : F.carrier →ₐ[K] L.carrier),
      ∃ factor : F.carrier →ₐ[K] L'.carrier,
        inclusion.comp factor = j

/-- The source subgroup `i(K_{m,1}) Nm(I_L^m)` for an arbitrary finite
extension. -/
def extensionRaySubgroup
    (L : NFExt K) (m : Modulus K) :
    Subgroup (IdealsPrimeTo (𝓞 K) K m.finiteSupport) :=
  rayPrincipalSubgroup K m ⊔ L.idealNormSubgroup m.finiteSupport

/-- The arbitrary-extension ray norm subgroup specializes to the tracked
one for abelian extensions. -/
theorem extension_ray_subgroup
    (L : ANExt K) (m : Modulus K) :
    extensionRaySubgroup L.toFinite m = rayNormSubgroup L m := by
  unfold extensionRaySubgroup rayNormSubgroup
  rw [ideal_norm_subgroup]

/-- A defining modulus for the finite abelian extension `L'/K`, expressed
with the existing Artin-map API and the arbitrary-extension norm subgroup
above. -/
def IsDefiningModulus
    (L' : ANExt K) (m : Modulus K) : Prop :=
  L'.ExactRamificationSupport m ∧
    ∃ ψ : IdealsPrimeTo (𝓞 K) K m.finiteSupport →* Gal(L'.carrier/K),
      IsArtinMap L' m.finiteSupport ψ ∧
        ∃ e :
            (IdealsPrimeTo (𝓞 K) K m.finiteSupport ⧸
              rayNormSubgroup L' m) ≃*
                Gal(L'.carrier/K),
          ∀ I : IdealsPrimeTo (𝓞 K) K m.finiteSupport,
            e (QuotientGroup.mk'
              (rayNormSubgroup L' m) I) = ψ I

/-- Norm transitivity in exactly the subgroup form needed for the easy
inclusion in Theorem V.3.16.  Establishing this from a literal fractional
ideal norm map is one of the ideal-transport gaps documented in
`ArtinMap.lean`. -/
def IdealNormTransitivity
    (L : NFExt K)
    (L' : ANExt K) (m : Modulus K) : Prop :=
  L.idealNormSubgroup m.finiteSupport ≤
    L'.toFinite.idealNormSubgroup m.finiteSupport

/-- Exact prime-level adapter needed to derive ideal norm transitivity from
the tower formula for residue degrees.  For an actual tower `L/L'/K`, the
exponent is `f(P/Q)` and the equality is
`N_{L/K}(P) = N_{L'/K}(Q) ^ f(P/Q)`.

The current library has the numerical inertia-degree tower formula, but does
not transport primes and ring-of-integers ideals along an arbitrary chosen
embedding `L' →ₐ[K] L`; this is the genuinely missing algebraic adapter. -/
def PrimeTransitivityBridge
    (L : NFExt K)
    (L' : ANExt K) : Prop :=
  ∀ P : L.PAbove,
    ∃ (Q : L'.toFinite.PAbove) (f : ℕ),
      P.normGenerator L = (Q.normGenerator L'.toFinite) ^ f

/-- The prime-level tower adapter implies containment of total norm
subgroups. -/
theorem total_mono_bridge
    (L : NFExt K)
    (L' : ANExt K)
    (hbridge : PrimeTransitivityBridge L L') :
    L.totalIdealSubgroup ≤ L'.toFinite.totalIdealSubgroup := by
  rw [NFExt.totalIdealSubgroup, Subgroup.closure_le]
  rintro x ⟨P, rfl⟩
  obtain ⟨Q, f, hQ⟩ := hbridge P
  change P.normGenerator L ∈ L'.toFinite.totalIdealSubgroup
  rw [hQ]
  exact (L'.toFinite.totalIdealSubgroup.pow_mem
    (Subgroup.subset_closure (Set.mem_range_self Q)) f)

/-- Consequently the same bridge proves norm transitivity in every
prime-to-`S` ideal group. -/
theorem ideal_transitivity_bridge
    (L : NFExt K)
    (L' : ANExt K) (m : Modulus K)
    (hbridge : PrimeTransitivityBridge L L') :
    IdealNormTransitivity L L' m := by
  exact Subgroup.comap_mono
    (total_mono_bridge L L' hbridge)

/-- The genuinely deep global norm-index input: after adjoining ray
principal ideals, the norm subgroup of arbitrary `L` has index equal to the
degree of its maximal abelian subextension. -/
def LimitationIndexFormula
    (L : NFExt K)
    (L' : ANExt K) (m : Modulus K) : Prop :=
  (extensionRaySubgroup L m).index =
    Nat.card Gal(L'.carrier/K)

/-- A defining modulus computes the index of the right-hand subgroup in the
Norm Limitation Theorem. -/
theorem defining_modulus_index
    (L' : ANExt K) (m : Modulus K)
    (hdef : IsDefiningModulus L' m) :
    (rayNormSubgroup L' m).index =
      Nat.card Gal(L'.carrier/K) := by
  rcases hdef.2 with ⟨ψ, hψ, e, he⟩
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr e.toEquiv

/-- Norm transitivity supplies the forward subgroup containment, including
the common ray-principal factor. -/
theorem ray_mono_transitivity
    (L : NFExt K)
    (L' : ANExt K) (m : Modulus K)
    (htrans : IdealNormTransitivity L L' m) :
    extensionRaySubgroup L m ≤
      rayNormSubgroup L' m := by
  rw [← extension_ray_subgroup]
  exact sup_le_sup le_rfl htrans

/-- With norm transitivity fixed, the literal equality is equivalent to the
deep reverse containment. -/
theorem limitation_reverse_inclusion
    (L : NFExt K)
    (L' : ANExt K) (m : Modulus K)
    (htrans : IdealNormTransitivity L L' m) :
    extensionRaySubgroup L m =
        rayNormSubgroup L' m ↔
      rayNormSubgroup L' m ≤
        extensionRaySubgroup L m := by
  constructor
  · intro h
    exact h.ge
  · intro hreverse
    exact le_antisymm
      (ray_mono_transitivity L L' m htrans)
      hreverse

/-- Faithful reduction of Theorem V.3.16 to norm transitivity and the one
missing global norm-index formula.  The maximality and defining-modulus
hypotheses are exactly those in the source statement. -/
theorem prime_transitivity_index
    (L : NFExt K)
    (L' : ANExt K)
    (hprime : PrimeTransitivityBridge L L')
    (hindex : ∀ m : Modulus K, IsDefiningModulus L' m →
      LimitationIndexFormula L L' m) :
    MaximalSubextension L L' →
    ∀ m : Modulus K, IsDefiningModulus L' m →
      extensionRaySubgroup L m =
        rayNormSubgroup L' m
  := by
  intro hmax m hdef
  let NL := extensionRaySubgroup L m
  let NE := rayNormSubgroup L' m
  have hcontain : NL ≤ NE :=
    ray_mono_transitivity
      L L' m (ideal_transitivity_bridge L L' m hprime)
  have hNLindex : NL.index = Nat.card Gal(L'.carrier/K) := hindex m hdef
  have hNEindex : NE.index = Nat.card Gal(L'.carrier/K) :=
    defining_modulus_index L' m hdef
  letI : NL.FiniteIndex := Subgroup.finiteIndex_iff.mpr (by
    rw [hNLindex]
    exact Nat.card_pos.ne')
  exact Towers.CField.LRecip.subgroup_index
    hcontain (hNLindex.trans hNEindex.symm)

end

end Towers.CField.ARecip
