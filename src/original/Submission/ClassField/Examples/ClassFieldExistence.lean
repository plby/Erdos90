import Submission.ClassField.RayClassGroups.CountFiniteIdeal
import Submission.ClassField.ArtinReciprocity.Statements

/-!
# Class Field Theory, Introduction, Theorems 0.4 and 0.5

This file states the existence clauses of Furtwaengler's unramified class
field theorem and Takagi's ray class field theorem using the actual ray class
groups developed in Chapter V.

A subgroup of the quotient ray class group is pulled back to the group of
ideals prime to the modulus.  The main result below proves that Takagi's
existence clause in this quotient formulation is *equivalent* to the ideal
existence theorem `GlobalExistenceTheorem`; in particular, no extra
finiteness, openness, or compatibility hypothesis is added to the source
statement.  The unramified existence clause of Theorem 0.4 is then the
special case of the trivial modulus.
-/

namespace Submission.CField.Examples

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.RCGroups
open Submission.CField.ARecip
open scoped nonZeroDivisors

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The inverse image in `I^S` of a subgroup of the ray class group
`C_m = I^S / i(K_{m,1})`.  This is the subgroup denoted `H tilde` in
the introduction. -/
def rayClassPreimage (m : Modulus K)
    (H : Subgroup (RayClassGroup K m)) :
    Subgroup (IdealsPrimeTo (𝓞 K) K m.finiteSupport) :=
  H.comap (QuotientGroup.mk' (rayPrincipalSubgroup K m))

/-- The inverse image of a ray class subgroup is a congruence subgroup. -/
theorem ray_principal_preimage
    (m : Modulus K) (H : Subgroup (RayClassGroup K m)) :
    rayPrincipalSubgroup K m ≤ rayClassPreimage K m H := by
  intro I hI
  change QuotientGroup.mk' (rayPrincipalSubgroup K m) I ∈ H
  have hclass :
      QuotientGroup.mk' (rayPrincipalSubgroup K m) I = 1 :=
    (QuotientGroup.eq_one_iff I).2 hI
  rw [hclass]
  exact H.one_mem

/-- The extension data supplied by the existence clause of Theorem 0.5 for
a subgroup `H ≤ C_m`.  Equality of the ray norm subgroup with the
inverse image of `H` is the ideal-theoretic class-field condition. -/
structure RayClassCandidate (m : Modulus K)
    (H : Subgroup (RayClassGroup K m)) where
  extension : ANExt K
  unramifiedOutside : extension.IsUnramifiedOutside m
  normGroup_eq :
    rayNormSubgroup extension m = rayClassPreimage K m H

/-- **Theorem 0.5 (Takagi), existence clause.** Every subgroup of every ray
class group has a finite abelian class-field candidate. -/
def RayClassExistence : Prop :=
  ∀ (m : Modulus K) (H : Subgroup (RayClassGroup K m)),
    Nonempty (RayClassCandidate K m H)

/-- Takagi's ray-class-subgroup formulation of existence follows from the
ideal existence theorem of Chapter V. -/
theorem ray_existence_global
    (hExistence : GlobalExistenceTheorem K) :
    RayClassExistence K := by
  intro m H
  obtain ⟨L, hunramified, hnorm⟩ := hExistence m
    (rayClassPreimage K m H)
    (ray_principal_preimage K m H)
  exact ⟨{
    extension := L
    unramifiedOutside := hunramified
    normGroup_eq := hnorm.symm }⟩

/-- Pulling back the image of a congruence subgroup recovers that subgroup.
This is the group-theoretic passage from a subgroup containing
`i(K_{m,1})` to a subgroup of `C_m` and back. -/
theorem ray_class_preimage
    (m : Modulus K)
    (H : Subgroup (IdealsPrimeTo (𝓞 K) K m.finiteSupport))
    (hH : rayPrincipalSubgroup K m ≤ H) :
    rayClassPreimage K m
        (H.map (QuotientGroup.mk' (rayPrincipalSubgroup K m))) = H := by
  apply Subgroup.comap_map_eq_self
  simpa only [QuotientGroup.ker_mk'] using hH

/-- Conversely, the quotient formulation of Takagi's existence clause
implies the ideal existence theorem. -/
theorem global_existence_clause
    (h05 : RayClassExistence K) :
    GlobalExistenceTheorem K := by
  intro m H hH
  let Hbar : Subgroup (RayClassGroup K m) :=
    H.map (QuotientGroup.mk' (rayPrincipalSubgroup K m))
  obtain ⟨C⟩ := h05 m Hbar
  refine ⟨C.extension, C.unramifiedOutside, ?_⟩
  have hpre : rayClassPreimage K m Hbar = H := by
    simpa only [Hbar] using ray_class_preimage K m H hH
  exact (C.normGroup_eq.trans hpre).symm

/-- Thus the source-faithful ray-class-subgroup existence clause is exactly
the ideal existence theorem, rather than a strengthening of it with hidden
hypotheses. -/
theorem existence_clause_ideal :
    RayClassExistence K ↔ GlobalExistenceTheorem K :=
  ⟨global_existence_clause K,
    ray_existence_global K⟩

/-- A finite abelian extension is everywhere unramified when all finite
primes are unramified and every real prime remains real. -/
def IsEverywhereUnramified
    (L : ANExt K) : Prop :=
  (∀ P : L.PAbove,
    Algebra.IsUnramifiedAt (𝓞 K) P.upstairs.asIdeal) ∧
  ∀ w : RealInfinitePlace K, w.1.IsUnramifiedIn L.carrier

/-- Being unramified outside the trivial modulus is exactly being
everywhere unramified, including at the real infinite primes. -/
theorem unramified_outside_everywhere
    (L : ANExt K) :
    L.IsUnramifiedOutside (1 : Modulus K) ↔
      IsEverywhereUnramified K L := by
  simp [ANExt.IsUnramifiedOutside,
    IsEverywhereUnramified,
    Modulus.finiteSupport]

/-- The extension data in the existence clause of Theorem 0.4.  The ray
class group at the trivial modulus is the ordinary ideal class group model
used by the Chapter V API. -/
structure UnramifiedClassCandidate
    (H : Subgroup (RayClassGroup K (1 : Modulus K))) where
  extension : ANExt K
  unramified : IsEverywhereUnramified K extension
  normGroup_eq :
    rayNormSubgroup extension (1 : Modulus K) =
      rayClassPreimage K (1 : Modulus K) H

/-- **Theorem 0.4 (Furtwaengler), existence clause.** Every subgroup of the
class group has an everywhere-unramified finite abelian class-field
candidate. -/
def UnramifiedClassExistence : Prop :=
  ∀ H : Subgroup (RayClassGroup K (1 : Modulus K)),
    Nonempty (UnramifiedClassCandidate K H)

/-- Furtwaengler's unramified existence clause is the trivial-modulus case
of Takagi's theorem. -/
theorem existence_clause_global
    (h05 : RayClassExistence K) :
    UnramifiedClassExistence K := by
  intro H
  obtain ⟨C⟩ := h05 (1 : Modulus K) H
  exact ⟨{
    extension := C.extension
    unramified :=
      (unramified_outside_everywhere K C.extension).mp
        C.unramifiedOutside
    normGroup_eq := C.normGroup_eq }⟩

/-- The ideal existence theorem therefore implies the existence clause of
Furtwaengler's theorem without an additional hypothesis on the subgroup. -/
theorem unramified_existence_global
    (hExistence : GlobalExistenceTheorem K) :
    UnramifiedClassExistence K :=
  existence_clause_global K
    (ray_existence_global K hExistence)

/-- The subgroup of the ray class group attached to an extension at a
modulus: the image of its ray norm subgroup in the quotient. -/
def rayClassExtension
    (L : ANExt K) (m : Modulus K) :
    Subgroup (RayClassGroup K m) :=
  (rayNormSubgroup L m).map
    (QuotientGroup.mk' (rayPrincipalSubgroup K m))

/-- The ray norm subgroup contains the ray principal subgroup. -/
theorem ray_principal_norm
    (L : ANExt K) (m : Modulus K) :
    rayPrincipalSubgroup K m ≤ rayNormSubgroup L m :=
  le_sup_left

/-- Pulling the associated ray class subgroup back to the ideal group
recovers the ray norm subgroup. -/
theorem ray_preimage_extension
    (L : ANExt K) (m : Modulus K) :
    rayClassPreimage K m (rayClassExtension K L m) =
      rayNormSubgroup L m := by
  exact ray_class_preimage K m (rayNormSubgroup L m)
    (ray_principal_norm K L m)

/-- Noether's third isomorphism theorem identifies the quotient of the ray
class group by the subgroup attached to L with the ideal quotient by the
ray norm subgroup. -/
noncomputable def rayClassNorm
    (L : ANExt K) (m : Modulus K) :
    (RayClassGroup K m ⧸ rayClassExtension K L m) ≃*
      (IdealsPrimeTo (𝓞 K) K m.finiteSupport ⧸ rayNormSubgroup L m) :=
  QuotientGroup.quotientQuotientEquivQuotient
    (rayPrincipalSubgroup K m) (rayNormSubgroup L m)
    (ray_principal_norm K L m)

/-- A ray-class description of a fixed finite abelian extension.  It records
the exact ramification support, the Artin map, the quotient isomorphism in
Theorem 0.5, and its compatibility with ideal classes. -/
structure RCDescri (L : ANExt K) where
  modulus : Modulus K
  artinMap :
    IdealsPrimeTo (𝓞 K) K modulus.finiteSupport →* Gal(L.carrier/K)
  exactRamification : L.ExactRamificationSupport modulus
  isArtinMap : IsArtinMap L modulus.finiteSupport artinMap
  artinEquiv :
    (RayClassGroup K modulus ⧸
      rayClassExtension K L modulus) ≃* Gal(L.carrier/K)
  artinEquiv_apply :
    ∀ I : IdealsPrimeTo (𝓞 K) K modulus.finiteSupport,
      artinEquiv
          (QuotientGroup.mk'
            (rayClassExtension K L modulus)
            (QuotientGroup.mk' (rayPrincipalSubgroup K modulus) I)) =
        artinMap I

/-- The global ideal reciprocity law supplies the every-finite-abelian-
extension-arises clause of Theorem 0.5, together with its specified Artin
isomorphism. -/
theorem ray_description_reciprocity
    (hReciprocity : IdealReciprocityLaw K)
    (L : ANExt K) :
    Nonempty (RCDescri K L) := by
  obtain ⟨m, ψ, hramified, hArtin, e, he⟩ := hReciprocity L
  let e' :
      (RayClassGroup K m ⧸ rayClassExtension K L m) ≃*
        Gal(L.carrier/K) :=
    (rayClassNorm K L m).trans e
  refine ⟨{
    modulus := m
    artinMap := ψ
    exactRamification := hramified
    isArtinMap := hArtin
    artinEquiv := e'
    artinEquiv_apply := ?_ }⟩
  intro I
  simpa only [e', MulEquiv.trans_apply,
    QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk] using he I

/-- The order assertion in Theorems 0.4 and 0.5: under an Artin map, the
order of the class of an unramified prime is its residue degree.  The
representative I is bundled because the ideal-prime-to-modulus API is a
subgroup of fractional ideals. -/
theorem order_residue_degree
    {L : ANExt K}
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    {ψ : IdealsPrimeTo (𝓞 K) K S →* Gal(L.carrier/K)}
    (hArtin : IsArtinMap L S ψ)
    (P : L.PAbove) (hP : P.downstairs ∉ S)
    (hunramified : Algebra.IsUnramifiedAt (𝓞 K) P.upstairs.asIdeal) :
    ∃ I : IdealsPrimeTo (𝓞 K) K S,
      (I.1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
          ANExt.primeFractionalIdeal P.downstairs ∧
        orderOf (ψ I) =
          P.downstairs.asIdeal.inertiaDeg P.upstairs.asIdeal := by
  obtain ⟨I, hI, hψ⟩ := hArtin P hP hunramified
  refine ⟨I, hI, ?_⟩
  rw [hψ]
  letI : P.upstairs.asIdeal.LiesOver P.downstairs.asIdeal := P.liesOver
  letI : Algebra.IsUnramifiedAt (𝓞 K) P.upstairs.asIdeal := hunramified
  letI : MulSemiringAction Gal(L.carrier/K) (𝓞 L.carrier) :=
    IsIntegralClosure.MulSemiringAction
      (𝓞 K) K L.carrier (𝓞 L.carrier)
  letI : IsGaloisGroup Gal(L.carrier/K) (𝓞 K) (𝓞 L.carrier) :=
    IsGaloisGroup.of_isFractionRing Gal(L.carrier/K)
      (𝓞 K) (𝓞 L.carrier) K L.carrier
  unfold ANExt.PAbove.arithmeticFrobenius
  simpa only [Ideal.over_def (P := P.upstairs.asIdeal)
    (p := P.downstairs.asIdeal)] using
      (frob_inertia_deg
        (R := 𝓞 K) (G := Gal(L.carrier/K)) P.upstairs.asIdeal)

end

end Submission.CField.Examples
