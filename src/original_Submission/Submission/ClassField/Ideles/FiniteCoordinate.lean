import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Submission.ClassField.RayClassGroups.CountFiniteIdeal
import Submission.ClassField.Ideles.IdeleIdealMap

/-!
# Chapter V, Section 4, Proposition 4.7

Milne's proposition identifies finite ideal characters admitting a modulus
with continuous idèle characters trivial on the principal idèles.  This file
states that result literally and proves all of its quotient-group and density
bookkeeping.

Two genuinely global inputs are kept as named interfaces:

* `RayExtensionBridge` is the map from Proposition 4.6, including its
  continuity and compatibility with the idèle-to-ideal map;
* `RayFactorizationProperty` is the open-kernel/conductor assertion used
  in the converse.

The remaining uniqueness input is stated exactly as the weak-approximation
density assertion used in the printed proof.  No continuity, principal-idèle,
or agreement hypothesis is added to the statement of Proposition 4.7.
-/

namespace Submission.CField.Ideles

open IsDedekindDomain NumberField
open Submission.CField.RCGroups
open Submission.CField.ARecip
open scoped RestrictedProduct nonZeroDivisors

noncomputable section

universe u v

variable (K : Type u) [Field K] [NumberField K]

/-- The integral model used by Proposition V.4.7.  This abbreviation is
public because it occurs in the types exported by `RayExtensionBridge`. -/
abbrev O := NumberField.RingOfIntegers K

/-- The finite coordinate of an idèle at a finite prime. -/
private abbrev finiteCoordinate (a : IdeleGroup (O K) K)
    (w : HeightOneSpectrum (O K)) : (w.adicCompletion K)ˣ :=
  (show Πʳ v : HeightOneSpectrum (O K),
      [(v.adicCompletion K)ˣ, IdeleUnitSubgroup (O K) K v] from a.2) w

/-- The infinite coordinate of an idèle at an infinite prime. -/
private abbrev infiniteCoordinate (a : IdeleGroup (O K) K)
    (w : InfinitePlace K) : w.Completionˣ :=
  MulEquiv.piUnits a.1 w

/-- Milne's `ℐ^S`, where `S` is represented by its finite part and all
infinite primes are understood to belong to `S`.  Thus an element is `1` at
every finite prime in `S` and at every infinite prime. -/
def IdelesAwayFrom
    (S : Finset (HeightOneSpectrum (O K))) : Subgroup (IdeleGroup (O K) K) where
  carrier := {a |
    (∀ w ∈ S, finiteCoordinate K a w = 1) ∧
      ∀ w : InfinitePlace K, infiniteCoordinate K a w = 1}
  one_mem' := by
    constructor
    · intro w hw
      rfl
    · intro w
      exact congrFun (map_one (MulEquiv.piUnits :
        (InfiniteAdeleRing K)ˣ ≃* ((w : InfinitePlace K) → w.Completionˣ))) w
  mul_mem' := by
    intro a b ha hb
    constructor
    · intro w hw
      change finiteCoordinate K a w * finiteCoordinate K b w = 1
      rw [ha.1 w hw, hb.1 w hw, one_mul]
    · intro w
      change infiniteCoordinate K a w * infiniteCoordinate K b w = 1
      rw [ha.2 w, hb.2 w, one_mul]
  inv_mem' := by
    intro a ha
    constructor
    · intro w hw
      change (finiteCoordinate K a w)⁻¹ = 1
      rw [ha.1 w hw, inv_one]
    · intro w
      change (infiniteCoordinate K a w)⁻¹ = 1
      rw [ha.2 w, inv_one]

@[simp]
theorem ideles_away
    (S : Finset (HeightOneSpectrum (O K))) (a : IdeleGroup (O K) K) :
    a ∈ IdelesAwayFrom K S ↔
      (∀ w ∈ S, finiteCoordinate K a w = 1) ∧
        ∀ w : InfinitePlace K, infiniteCoordinate K a w = 1 :=
  Iff.rfl

/-- The currently missing restriction of Statement 4.1's idèle-to-ideal map
to `ℐ^S → I^S`.  The compatibility field says that this is literally the
canonical ideal attached to the idèle, rather than an arbitrary map. -/
structure IdeleAwayData
    (S : Finset (HeightOneSpectrum (O K))) where
  toIdeal :
    IdelesAwayFrom K S →* IdealsPrimeTo (O K) K S
  agrees_idele_ideal : ∀ a : IdelesAwayFrom K S,
    ((toIdeal a).1 : (FractionalIdeal (O K)⁰ K)ˣ) =
      ideleIdealMap (O K) K a.1

/-- The ray class group used in Proposition 4.7. -/
abbrev CoordinateRayGroup (m : Modulus K) :=
  IdealsPrimeTo (O K) K m.finiteSupport ⧸ rayPrincipalSubgroup K m

/-- Transport ideals prime to one finite set across equality of that set.
This is used only to express that a modulus has the same finite support as
the originally specified `S`. -/
def idealsPrimeCongr
    {S T : Finset (HeightOneSpectrum (O K))} (h : S = T) :
    IdealsPrimeTo (O K) K S ≃* IdealsPrimeTo (O K) K T := by
  subst T
  exact MulEquiv.refl _

/-- A character of `I^S` admits a modulus.  Since our `S` records only the
finite primes (all infinite primes are implicit), its finite support can be
taken to be exactly `S`: a modulus supported in `S` may be enlarged by putting
positive exponent at the unused finite primes without changing triviality on
the smaller ray-principal subgroup. -/
def CharacterAdmitsModulus
    {G : Type v} [Group G]
    (S : Finset (HeightOneSpectrum (O K)))
    (ψ : IdealsPrimeTo (O K) K S →* G) : Prop :=
  ∃ m : Modulus K,
    ∃ h : m.finiteSupport = S,
      rayPrincipalSubgroup K m ≤
        (ψ.comp (idealsPrimeCongr K h).toMonoidHom).ker

/-- Conditions (a), (b), and (c) in Proposition 4.7. -/
def IsIdeleExtension
    {G : Type v} [Group G] [TopologicalSpace G]
    (S : Finset (HeightOneSpectrum (O K)))
    (idealMap : IdeleAwayData K S)
    (ψ : IdealsPrimeTo (O K) K S →* G)
    (φ : IdeleGroup (O K) K →* G) : Prop :=
  Continuous φ ∧
    principalIdeles (O K) K ≤ φ.ker ∧
      ∀ a : IdelesAwayFrom K S, φ a.1 = ψ (idealMap.toIdeal a)

/-- The exact Proposition 4.6 bridge needed for a fixed modulus: a ray-class
character pulls back continuously to the idèles, kills principal idèles, and
agrees with the ideal map on `ℐ^S`. -/
structure RayExtensionBridge
    {G : Type v} [CommGroup G] [TopologicalSpace G]
    (m : Modulus K)
    (idealMap : IdeleAwayData K m.finiteSupport) where
  extend :
    (CoordinateRayGroup K m →* G) →
      (IdeleGroup (O K) K →* G)
  continuous_extend : ∀ χ, Continuous (extend χ)
  principal_le_ker : ∀ χ,
    principalIdeles (O K) K ≤ (extend χ).ker
  agrees_ideles_away : ∀ χ (a : IdelesAwayFrom K m.finiteSupport),
    extend χ a.1 =
      χ (QuotientGroup.mk' (rayPrincipalSubgroup K m)
        (idealMap.toIdeal a))

/-- The weak-approximation assertion used in the uniqueness paragraph of the
printed proof: `ℐ^S Kˣ` is dense in the idèles. -/
def WeakApproximationDensity
    (S : Finset (HeightOneSpectrum (O K))) : Prop :=
  Dense {x : IdeleGroup (O K) K |
    ∃ (a : IdelesAwayFrom K S) (b : Kˣ),
      x = a.1 * principalIdele (O K) K b}

/-- Quotient-group construction of the unique extension.  All algebraic
factorization and the density uniqueness argument are proved here; only the
two named global bridge inputs remain. -/
theorem forward_ray_bridge
    {G : Type v} [CommGroup G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G]
    (idealMaps : ∀ S : Finset (HeightOneSpectrum (O K)),
      IdeleAwayData K S)
    (bridges : ∀ m : Modulus K,
      RayExtensionBridge (G := G) K m (idealMaps m.finiteSupport))
    (hweak : ∀ S : Finset (HeightOneSpectrum (O K)),
      WeakApproximationDensity K S) :
    (∀ (S : Finset (HeightOneSpectrum (O K)))
          (ψ : IdealsPrimeTo (O K) K S →* G),
          CharacterAdmitsModulus K S ψ →
            ∃! φ : IdeleGroup (O K) K →* G,
              IsIdeleExtension K S (idealMaps S) ψ φ) := by
  intro S ψ hψ
  obtain ⟨m, hm, hker⟩ := hψ
  subst S
  have hker' : rayPrincipalSubgroup K m ≤ ψ.ker := by
    simpa [idealsPrimeCongr] using hker
  let χ : CoordinateRayGroup K m →* G :=
    QuotientGroup.lift (rayPrincipalSubgroup K m) ψ hker'
  let φ : IdeleGroup (O K) K →* G := (bridges m).extend χ
  have hφ : IsIdeleExtension K m.finiteSupport
      (idealMaps m.finiteSupport) ψ φ := by
    refine ⟨(bridges m).continuous_extend χ,
      (bridges m).principal_le_ker χ, ?_⟩
    intro a
    rw [(bridges m).agrees_ideles_away χ a]
    exact QuotientGroup.lift_mk' _ _ _
  refine ⟨φ, hφ, ?_⟩
  intro φ' hφ'
  apply MonoidHom.ext
  have heq : (φ : IdeleGroup (O K) K → G) = φ' :=
    Continuous.ext_on (hweak m.finiteSupport)
      hφ.1 hφ'.1 (by
        intro x hx
        obtain ⟨a, b, rfl⟩ := hx
        rw [map_mul, map_mul, hφ.2.2 a, hφ'.2.2 a]
        have hb : principalIdele (O K) K b ∈ principalIdeles (O K) K :=
          ⟨b, rfl⟩
        rw [show φ (principalIdele (O K) K b) = 1 from hφ.2.1 hb,
          show φ' (principalIdele (O K) K b) = 1 from hφ'.2.1 hb])
  exact fun x ↦ (congrFun heq x).symm

/-- The precise conductor input in the converse: every continuous idèle
character trivial on principal idèles factors through the ray-class pullback
for some modulus.  Analytically, this is the assertion that its open kernel
contains some `W_m`, together with Proposition 4.6. -/
def RayFactorizationProperty
    {G : Type v} [CommGroup G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G]
    (idealMaps : ∀ S : Finset (HeightOneSpectrum (O K)),
      IdeleAwayData K S)
    (bridges : ∀ m : Modulus K,
      RayExtensionBridge (G := G) K m
        (idealMaps m.finiteSupport)) : Prop :=
  ∀ φ : IdeleGroup (O K) K →* G,
    Continuous φ →
    principalIdeles (O K) K ≤ φ.ker →
      ∃ (m : Modulus K)
        (χ : CoordinateRayGroup K m →* G),
        φ = (bridges m).extend χ

/-- The converse is formal once the exact open-kernel/ray-factorization
interface is supplied. -/
theorem converse_ray_factorization
    {G : Type v} [CommGroup G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G]
    (idealMaps : ∀ S : Finset (HeightOneSpectrum (O K)),
      IdeleAwayData K S)
    (bridges : ∀ m : Modulus K,
      RayExtensionBridge (G := G) K m (idealMaps m.finiteSupport))
    (hfactor : RayFactorizationProperty (G := G) K idealMaps bridges) :
    (∀ φ : IdeleGroup (O K) K →* G,
          Continuous φ →
          principalIdeles (O K) K ≤ φ.ker →
            ∃ (S : Finset (HeightOneSpectrum (O K)))
              (ψ : IdealsPrimeTo (O K) K S →* G),
              CharacterAdmitsModulus K S ψ ∧
                IsIdeleExtension K S (idealMaps S) ψ φ) := by
  intro φ hcontinuous hprincipal
  obtain ⟨m, χ, hφ⟩ := hfactor φ hcontinuous hprincipal
  let ψ : IdealsPrimeTo (O K) K m.finiteSupport →* G :=
    χ.comp (QuotientGroup.mk' (rayPrincipalSubgroup K m))
  refine ⟨m.finiteSupport, ψ, ?_, ?_⟩
  · refine ⟨m, rfl, ?_⟩
    intro I hI
    change χ (QuotientGroup.mk' (rayPrincipalSubgroup K m) I) = 1
    rw [show QuotientGroup.mk' (rayPrincipalSubgroup K m) I = 1 by
      exact (QuotientGroup.eq_one_iff I).mpr hI, map_one]
  · refine ⟨hcontinuous, hprincipal, ?_⟩
    intro a
    rw [hφ, (bridges m).agrees_ideles_away χ a]
    rfl

/-- Proposition 4.7 follows from precisely the three global ingredients
identified in its printed proof: Proposition 4.6, weak approximation, and
the open-kernel conductor factorization. -/
theorem of_global_bridges
    {G : Type v} [CommGroup G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G]
    (idealMaps : ∀ S : Finset (HeightOneSpectrum (O K)),
      IdeleAwayData K S)
    (bridges : ∀ m : Modulus K,
      RayExtensionBridge (G := G) K m (idealMaps m.finiteSupport))
    (hweak : ∀ S : Finset (HeightOneSpectrum (O K)),
      WeakApproximationDensity K S)
    (hfactor : RayFactorizationProperty (G := G) K idealMaps bridges) :
    ((
        ∀ (S : Finset (HeightOneSpectrum (O K)))
            (ψ : IdealsPrimeTo (O K) K S →* G),
            CharacterAdmitsModulus K S ψ →
              ∃! φ : IdeleGroup (O K) K →* G,
                IsIdeleExtension K S (idealMaps S) ψ φ
      ) ∧
          (
            ∀ φ : IdeleGroup (O K) K →* G,
                Continuous φ →
                principalIdeles (O K) K ≤ φ.ker →
                  ∃ (S : Finset (HeightOneSpectrum (O K)))
                    (ψ : IdealsPrimeTo (O K) K S →* G),
                    CharacterAdmitsModulus K S ψ ∧
                      IsIdeleExtension K S (idealMaps S) ψ φ
          )) :=
  ⟨forward_ray_bridge (G := G) K idealMaps bridges hweak,
    converse_ray_factorization (G := G) K idealMaps bridges hfactor⟩

end

end Submission.CField.Ideles
