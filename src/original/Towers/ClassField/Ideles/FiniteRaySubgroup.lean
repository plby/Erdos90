import Towers.ClassField.RayClassGroups.CountFiniteIdeal
import Towers.ClassField.Ideles.IdeleIdealMap
import Towers.Group.Edmonton.HallCommutatorIdentities

/-!
# Chapter V, Section 4, Proposition 4.6

For a modulus `m`, Milne writes `I_m` for the ideles satisfying the local
ray conditions at the places in `m`, and `W_m` for those elements of `I_m`
which are units at every finite place.  Proposition 4.6 identifies

`I_m / (K_{m,1} W_m)` with the ray class group, and
`I_m / K_{m,1}` with the idele class group.

This file defines the source's local subgroups literally.  The quotient-group
arguments are proved in full.  The arithmetic interfaces which are not yet
packaged by the finite-adele API are isolated in
`IdealMapBridge`; its fields say exactly that the ideal map
lands in and surjects onto the ideals prime to `m`, and that principal ideles
give precisely the ray-principal subgroup.  The sole input isolated for part
(b), `WeakApproximation`, is the exact surjectivity consequence
of weak approximation used in Milne's proof.
-/

namespace Towers.CField.Ideles

open IsDedekindDomain NumberField
open Towers.CField.RCGroups
open Towers.CField.ARecip
open scoped nonZeroDivisors RestrictedProduct

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

local notation "𝑜K" => NumberField.RingOfIntegers K

/-- The local subgroup `1 + p^n` inside the multiplicative group of the
completion at `v`.  It is obtained from the `n`th power of the maximal ideal
of the completed valuation ring. -/
def rayLocalSubgroup (v : HeightOneSpectrum 𝑜K) (n : ℕ) :
    Subgroup (v.adicCompletion K)ˣ :=
  let A := v.adicCompletionIntegers K
  (Edmonton.idealUnitSubgroup (IsLocalRing.maximalIdeal A) n).map
    (A.unitGroup.subtype.comp A.unitGroupMulEquiv.symm.toMonoidHom)

/-- The positive component of the multiplicative group at a real infinite
place. -/
def positiveRealSubgroup (w : RealInfinitePlace K) :
    Subgroup w.1.Completionˣ :=
  (Units.posSubgroup ℝ).comap <|
    Units.map
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal w.property).toMonoidHom

/-- The subgroup `I_m` of ideles satisfying the local ray conditions at all
places dividing `m`.  Outside the support of `m` there is no additional
condition beyond being an idele. -/
def modulusIdeles (m : Modulus K) : Subgroup (IdeleGroup 𝑜K K) where
  carrier := {a |
    (∀ v ∈ m.finiteSupport,
      a.2.1 v ∈ rayLocalSubgroup (K := K) v (m.finite v)) ∧
    (∀ w ∈ m.infinite,
      (MulEquiv.piUnits a.1) w.1 ∈ positiveRealSubgroup w)}
  one_mem' := by
    constructor
    · intro v hv
      exact (rayLocalSubgroup (K := K) v (m.finite v)).one_mem
    · intro w hw
      change (MulEquiv.piUnits (1 : (InfiniteAdeleRing K)ˣ)) w.1 ∈
        positiveRealSubgroup w
      have h := congrFun (map_one (MulEquiv.piUnits :
        (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) → v.Completionˣ))) w.1
      exact h.symm ▸ (positiveRealSubgroup w).one_mem
  mul_mem' := by
    intro a b ha hb
    constructor
    · intro v hv
      exact (rayLocalSubgroup (K := K) v (m.finite v)).mul_mem
        (ha.1 v hv) (hb.1 v hv)
    · intro w hw
      have h := congrFun (map_mul (MulEquiv.piUnits :
        (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) → v.Completionˣ)) a.1 b.1) w.1
      change (MulEquiv.piUnits (a.1 * b.1)) w.1 ∈ positiveRealSubgroup w
      exact h.symm ▸
        (positiveRealSubgroup w).mul_mem (ha.2 w hw) (hb.2 w hw)
  inv_mem' := by
    intro a ha
    constructor
    · intro v hv
      exact (rayLocalSubgroup (K := K) v (m.finite v)).inv_mem (ha.1 v hv)
    · intro w hw
      have h := congrFun (map_inv (MulEquiv.piUnits :
        (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) → v.Completionˣ)) a.1) w.1
      change (MulEquiv.piUnits a.1⁻¹) w.1 ∈ positiveRealSubgroup w
      exact h.symm ▸ (positiveRealSubgroup w).inv_mem (ha.2 w hw)

/-- The source identity `K_{m,1} = K× ∩ I_m`, expressed as a subgroup
of `I_m`. -/
def modulusPrincipalIdeles (m : Modulus K) : Subgroup (modulusIdeles m) :=
  (principalIdeles 𝑜K K).comap (modulusIdeles m).subtype

/-- The subgroup `W_m`: elements of `I_m` which are units at every finite
place. -/
def modulusUnitIdeles (m : Modulus K) : Subgroup (modulusIdeles m) :=
  (idelesEveryPlace 𝑜K K).comap (modulusIdeles m).subtype

/-- The assertion that the ideal attached to an element of `I_m` is prime to
the finite support of `m`.  This is the local-valuation compatibility needed
to type Milne's map `id : I_m → I^{S(m)}`. -/
def ModulusLandsPrime (m : Modulus K) : Prop :=
  ∀ a : modulusIdeles m,
    ideleIdealMap 𝑜K K a.1 ∈ IdealsPrimeTo 𝑜K K m.finiteSupport

/-- Milne's map `id : I_m → I^{S(m)}`, once the local-valuation
compatibility has been supplied. -/
def modulusIdeleIdeal (m : Modulus K)
    (hlands : ModulusLandsPrime m) :
    modulusIdeles m →* IdealsPrimeTo 𝑜K K m.finiteSupport where
  toFun a := ⟨ideleIdealMap 𝑜K K a.1, hlands a⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (ideleIdealMap 𝑜K K)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (ideleIdealMap 𝑜K K) a.1 b.1

/-- The kernel of the restricted ideal map is exactly `W_m`.  This part of
Milne's proof follows directly from Statement 4.1. -/
theorem modulus_ideal_ker (m : Modulus K)
    (hlands : ModulusLandsPrime m) :
    (modulusIdeleIdeal m hlands).ker = modulusUnitIdeles m := by
  ext a
  rw [MonoidHom.mem_ker]
  change (⟨ideleIdealMap 𝑜K K a.1, hlands a⟩ :
      IdealsPrimeTo 𝑜K K m.finiteSupport) = 1 ↔
    a.1 ∈ idelesEveryPlace 𝑜K K
  rw [Subtype.ext_iff]
  change ideleIdealMap 𝑜K K a.1 = 1 ↔
    a.1 ∈ idelesEveryPlace 𝑜K K
  rw [← MonoidHom.mem_ker, idele_ker]

/-- The three precise ideal-theoretic/local compatibility facts needed for
part (a).  No quotient-group assertion is included here. -/
structure IdealMapBridge (m : Modulus K) where
  /-- Local ray conditions force the associated ideal to be prime to `m`. -/
  landsPrimeTo : ModulusLandsPrime m
  /-- Every fractional ideal prime to `m` has an idele representative in
  `I_m`. -/
  idealMap_surjective :
    Function.Surjective (modulusIdeleIdeal m landsPrimeTo)
  /-- Principal ideles in `I_m` map to precisely `i(K_{m,1})`. -/
  principal_image :
    Subgroup.map (modulusIdeleIdeal m landsPrimeTo)
        (modulusPrincipalIdeles m) =
      rayPrincipalSubgroup K m

/-- The map from `I_m` to the ray class group induced by the ideal map. -/
def modulusIdeleRay (m : Modulus K)
    (B : IdealMapBridge m) :
    modulusIdeles m →* RayClassGroup K m :=
  (QuotientGroup.mk' (rayPrincipalSubgroup K m)).comp
    (modulusIdeleIdeal m B.landsPrimeTo)

theorem modulus_ray_surjective (m : Modulus K)
    (B : IdealMapBridge m) :
    Function.Surjective (modulusIdeleRay m B) :=
  (QuotientGroup.mk'_surjective (rayPrincipalSubgroup K m)).comp
    B.idealMap_surjective

/-- The kernel calculation underlying Proposition 4.6(a). -/
theorem modulus_ray_ker (m : Modulus K)
    (B : IdealMapBridge m) :
    (modulusIdeleRay m B).ker =
      modulusPrincipalIdeles m ⊔ modulusUnitIdeles m := by
  let f := modulusIdeleIdeal m B.landsPrimeTo
  rw [modulusIdeleRay]
  change Subgroup.comap f
    (QuotientGroup.mk' (rayPrincipalSubgroup K m)).ker = _
  rw [QuotientGroup.ker_mk', ← B.principal_image, Subgroup.comap_map_eq,
    modulus_ideal_ker m B.landsPrimeTo]

/-- The canonical isomorphism in Proposition 4.6(a). -/
noncomputable def rayClassEquiv (m : Modulus K)
    (B : IdealMapBridge m) :
    (modulusIdeles m ⧸
      (modulusPrincipalIdeles m ⊔ modulusUnitIdeles m)) ≃*
        RayClassGroup K m :=
  (QuotientGroup.quotientMulEquivOfEq
      (modulus_ray_ker m B).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (modulusIdeleRay m B)
      (modulus_ray_surjective m B))

/-- Literal source-level assertion of Proposition 4.6(a), including that the
displayed isomorphism is induced by the ideal map. -/
def ModulusRayClass (m : Modulus K) : Prop :=
  ∃ (hlands : ModulusLandsPrime m)
    (e : (modulusIdeles m ⧸
      (modulusPrincipalIdeles m ⊔ modulusUnitIdeles m)) ≃*
        RayClassGroup K m),
    ∀ a : modulusIdeles m,
      e (QuotientGroup.mk' _ a) =
        QuotientGroup.mk' (rayPrincipalSubgroup K m)
          (modulusIdeleIdeal m hlands a)

/-- Proposition 4.6(a), reduced only to the sharply isolated local/ideal
bridge. -/
theorem ideal_bridge (m : Modulus K)
    (B : IdealMapBridge m) :
    ModulusRayClass m := by
  refine ⟨B.landsPrimeTo, rayClassEquiv m B, ?_⟩
  intro a
  rfl

/-- The map induced by `I_m → I → I/K×`. -/
def modulusIdeleHom (m : Modulus K) :
    modulusIdeles m →* IdeleClassGroup 𝑜K K :=
  (QuotientGroup.mk' (principalIdeles 𝑜K K)).comp
    (modulusIdeles m).subtype

/-- Its kernel is `K× ∩ I_m = K_{m,1}`. -/
theorem modulus_idele_ker (m : Modulus K) :
    (modulusIdeleHom m).ker = modulusPrincipalIdeles m := by
  rw [modulusIdeleHom]
  change Subgroup.comap (modulusIdeles m).subtype
    (QuotientGroup.mk' (principalIdeles 𝑜K K)).ker = _
  rw [QuotientGroup.ker_mk']
  rfl

/-- The exact weak-approximation consequence in Milne's proof of part (b):
every idele class has a representative satisfying the local ray conditions
at the finitely many places in the modulus. -/
def WeakApproximation (m : Modulus K) : Prop :=
  Function.Surjective (modulusIdeleHom m)

/-- The canonical isomorphism in Proposition 4.6(b), conditional only on the
literal weak-approximation surjectivity above. -/
noncomputable def modulusIdeleEquiv (m : Modulus K)
    (hWA : WeakApproximation m) :
    (modulusIdeles m ⧸ modulusPrincipalIdeles m) ≃*
      IdeleClassGroup 𝑜K K :=
  (QuotientGroup.quotientMulEquivOfEq
      (modulus_idele_ker m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (modulusIdeleHom m) hWA)

/-- Literal source-level assertion of Proposition 4.6(b), including that the
displayed isomorphism is induced by inclusion into the full idele group. -/
def ModulusIdeleEquiv (m : Modulus K) : Prop :=
  ∃ e : (modulusIdeles m ⧸ modulusPrincipalIdeles m) ≃*
      IdeleClassGroup 𝑜K K,
    ∀ a : modulusIdeles m,
      e (QuotientGroup.mk' _ a) =
        QuotientGroup.mk' (principalIdeles 𝑜K K) a.1

/-- Proposition 4.6(b), reduced exactly to weak approximation. -/
theorem of_weakApproximation (m : Modulus K)
    (hWA : WeakApproximation m) :
    ModulusIdeleEquiv m := by
  refine ⟨modulusIdeleEquiv m hWA, ?_⟩
  intro a
  rfl

/-- The literal conjunction of both clauses of Proposition 4.6. -/
def RayLocalDecomposition (m : Modulus K) : Prop :=
  ModulusRayClass m ∧ ModulusIdeleEquiv m

/-- All formal group-theoretic content of Proposition 4.6, with only the
local ideal-map bridge and weak approximation exposed. -/
theorem of_bridges (m : Modulus K)
    (B : IdealMapBridge m)
    (hWA : WeakApproximation m) :
    RayLocalDecomposition m :=
  ⟨ideal_bridge m B,
    of_weakApproximation m hWA⟩

end

end Towers.CField.Ideles
