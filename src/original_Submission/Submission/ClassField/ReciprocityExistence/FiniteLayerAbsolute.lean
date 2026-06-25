import Submission.ClassField.Ideles.IdeleClassNorm
import Submission.ClassField.Reciprocity.RestrictedFactorFamily
import Submission.ClassField.NormIndex.IdeleTowerFinite
import Submission.ClassField.ReciprocityExistence.GaloisRestriction
import Submission.ClassField.ReciprocityExistence.Functoriality

/-!
# Chapter VII, Section 8, Lemma 8.4

The two functoriality steps for principal-idèle reciprocity are recorded with
the actual idèle maps.  Passing to a finite abelian layer is postcomposition
with the genuine restriction map.  Under base change, the vertical map on
idèles is the genuine idèle norm; its effect on principal idèles is already
proved in Chapter V, Section 4.
-/

namespace Submission.CField.RExist

open Function Set
open NumberField IsDedekindDomain
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.Ideles
open Submission.CField.Recip
open Submission.CField.NIndex
open scoped RestrictedProduct IsMulCommutative

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- **Lemma VII.8.4(a), finite-layer form.**  If the absolute global Artin
map is trivial on principal idèles, so is its restriction to every finite
abelian subextension. -/
theorem finite_layer_absolute
    (K : Type u) [Field K] [NumberField K]
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (hphi : TrivialPrincipalIdeles
      (NumberField.RingOfIntegers K) K
      (AbsoluteAbelianGalois K) phi)
    (L : FASubext K) :
    TrivialPrincipalIdeles
      (NumberField.RingOfIntegers K) K Gal(L.1/K)
      ((localAbelianRestriction L).comp phi) := by
  intro x
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  rw [hphi x, map_one]

/-! ### Products of local Artin symbols -/

/-- A finite product can be regrouped over finite fibers.  This is the
algebraic reindexing used below for the finite-place Artin factors. -/
private theorem finprod_fiberwise
    {I J M : Type*} [CommMonoid M]
    (p : J → I) (f : J → M) (hf : Function.HasFiniteMulSupport f)
    [∀ i, Fintype {j : J // p j = i}] :
    (∏ᶠ j, f j) = ∏ᶠ i, ∏ j : {j : J // p j = i}, f j := by
  classical
  let S : Finset J := hf.toFinset
  let T : Finset I := S.image p
  have hinner (i : I) :
      (∏ j : {j : J // p j = i}, f j) =
        ∏ j ∈ S.filter (fun j ↦ p j = i), f j := by
    calc
      (∏ j : {j : J // p j = i}, f j) =
          ∏ j ∈ (Finset.univ : Finset {j : J // p j = i}), f j := by
            simp
      _ = ∏ j ∈ (Finset.univ : Finset {j : J // p j = i}).filter
          (fun j : {j : J // p j = i} ↦ j.1 ∈ S), f j := by
        symm
        apply Finset.prod_subset
        · exact Finset.filter_subset _ _
        · intro j _ hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          apply not_ne_iff.mp
          intro hne
          exact hj (hf.mem_toFinset.mpr hne)
      _ = ∏ j ∈ S.filter (fun j ↦ p j = i), f j := by
        apply Finset.prod_bij (fun j _ ↦ j.1)
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact Finset.mem_filter.mpr ⟨hj, j.2⟩
        · intro j₁ _ j₂ _ h
          exact Subtype.ext h
        · intro j hj
          refine ⟨⟨j, (Finset.mem_filter.mp hj).2⟩, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (Finset.mem_filter.mp hj).1
        · intro _ _
          rfl
  have houter_subset : mulSupport
      (fun i ↦ ∏ j : {j : J // p j = i}, f j) ⊆ T := by
    intro i hi
    by_contra hiT
    apply hi
    change (∏ j : {j : J // p j = i}, f j) = 1
    rw [hinner i]
    apply Finset.prod_eq_one
    intro j hj
    have hjS : j ∈ S := (Finset.mem_filter.mp hj).1
    have hjpi : p j = i := (Finset.mem_filter.mp hj).2
    exact (hiT (Finset.mem_image.mpr ⟨j, hjS, hjpi⟩)).elim
  have houter : Function.HasFiniteMulSupport
      (fun i ↦ ∏ j : {j : J // p j = i}, f j) :=
    T.finite_toSet.subset houter_subset
  rw [finprod_eq_prod f hf]
  rw [finprod_eq_prod _ houter]
  calc
    ∏ j ∈ S, f j =
        ∏ i ∈ T, ∏ j ∈ S.filter (fun j ↦ p j = i), f j := by
      exact (Finset.prod_fiberwise_of_maps_to
        (fun j hj ↦ Finset.mem_image.mpr ⟨j, hj, rfl⟩) f).symm
    _ = ∏ i ∈ T, ∏ j : {j : J // p j = i}, f j := by
      apply Finset.prod_congr rfl
      intro i _
      exact (hinner i).symm
    _ = ∏ i ∈ houter.toFinset, ∏ j : {j : J // p j = i}, f j := by
      symm
      apply Finset.prod_subset
      · intro i hi
        exact houter_subset (houter.mem_toFinset.mp hi)
      · intro i _ hi
        exact not_ne_iff.mp (fun hne ↦ hi (houter.mem_toFinset.mpr hne))

/-- The global Artin homomorphism obtained by multiplying specified local
Artin symbols.  At finite places the usual almost-everywhere unit condition
makes the `finprod` finite; the set of infinite places is finite. -/
structure FAProduc
    (K G : Type u) [Field K] [NumberField K] [CommGroup G] where
  finite : RLFam (A := G)
    (fun P : HeightOneSpectrum (OK K) ↦ IdeleUnitSubgroup (OK K) K P)
  infinite : ∀ v : InfinitePlace K, v.1.Completionˣ →* G

namespace FAProduc

variable {K G : Type u} [Field K] [NumberField K] [CommGroup G]

/-- Product of the archimedean local Artin symbols. -/
noncomputable def infiniteHom (D : FAProduc K G) :
    (InfiniteAdeleRing K)ˣ →* G where
  toFun x := ∏ v : InfinitePlace K, D.infinite v (MulEquiv.piUnits x v)
  map_one' := by
    apply Finset.prod_eq_one
    intro v _
    rw [show MulEquiv.piUnits (1 : (InfiniteAdeleRing K)ˣ) v = 1 by
      exact congrFun (map_one (MulEquiv.piUnits :
        MulEquiv (InfiniteAdeleRing K)ˣ
          ((v : InfinitePlace K) → v.1.Completionˣ))) v]
    exact map_one (D.infinite v)
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v _
    rw [show MulEquiv.piUnits (x * y) v =
        MulEquiv.piUnits x v * MulEquiv.piUnits y v by
      exact congrFun (map_mul (MulEquiv.piUnits :
        MulEquiv (InfiniteAdeleRing K)ˣ
          ((v : InfinitePlace K) → v.1.Completionˣ)) x y) v]
    exact map_mul (D.infinite v) _ _

set_option synthInstance.maxHeartbeats 100000 in
-- The restricted-product group structure is dependent on every finite place.
/-- The actual global product of all specified local Artin symbols. -/
noncomputable def artin (D : FAProduc K G) :
    IdeleGroup (OK K) K →* G where
  toFun x := D.infiniteHom x.1 * D.finite.restrictedProductHom _ x.2
  map_one' := by
    change D.infiniteHom 1 * D.finite.restrictedProductHom _ 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' x y := by
    change D.infiniteHom (x.1 * y.1) *
        D.finite.restrictedProductHom _ (x.2 * y.2) = _
    rw [map_mul D.infiniteHom]
    calc
      (D.infiniteHom x.1 * D.infiniteHom y.1) *
          D.finite.restrictedProductHom _ (x.2 * y.2) =
        (D.infiniteHom x.1 * D.infiniteHom y.1) *
          (D.finite.restrictedProductHom _ x.2 *
            D.finite.restrictedProductHom _ y.2) := by
              exact congrArg (fun z ↦
                (D.infiniteHom x.1 * D.infiniteHom y.1) * z)
                ((D.finite.restrictedProductHom _).map_mul x.2 y.2)
      _ = _ := by ac_rfl

@[simp]
theorem artin_apply (D : FAProduc K G) (x : IdeleGroup (OK K) K) :
    D.artin x =
      (∏ v : InfinitePlace K, D.infinite v (MulEquiv.piUnits x.1 v)) *
        (∏ᶠ P : HeightOneSpectrum (OK K),
          D.finite.localHom P (x.2.1 P)) := by
  rfl

end FAProduc

/-- The local input for the base-change Artin square.  Unlike the old
`Lemma84BaseChangeArtinSquare`, this contains no global commutativity
assumption: it records only the already-local norm/Artin compatibilities. -/
structure BCData
    (K L G G' : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [CommGroup G] [CommGroup G'] where
  lower : FAProduc K G
  upper : FAProduc L G'
  targetMap : G' →* G
  targetMap_injective : Function.Injective targetMap
  finite_commutes : ∀ (P : HeightOneSpectrum (OK K))
      (Q : PlacesAbovePrime K L P) (z : (Q.1.adicCompletion L)ˣ),
    targetMap (upper.finite.localHom Q.1 z) =
      lower.finite.localHom P
        (completionNormLiteral (K := K) (L := L) P Q z)
  infinite_commutes : ∀ (v : InfinitePlace K)
      (w : InfinitePlacesAbove (K := K) (L := L) v)
      (z : w.1.1.Completionˣ),
    targetMap (upper.infinite w.1 z) =
      lower.infinite v (infiniteCompletionNorm (K := K) (L := L) v w z)

namespace BCData

variable {K L G G' : Type u}
    [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    [CommGroup G] [CommGroup G']

private theorem finite_commutes_global
    (D : BCData K L G G')
    (x : FiniteIdeles (OK L) L) :
    D.targetMap (D.upper.finite.restrictedProductHom _ x) =
      D.lower.finite.restrictedProductHom _
        (finiteIdeleNorm (K := K) (L := L) x) := by
  classical
  let p : HeightOneSpectrum (OK L) → HeightOneSpectrum (OK K) :=
    fun Q ↦ Q.under (OK K)
  let f : HeightOneSpectrum (OK L) → G :=
    fun Q ↦ D.targetMap (D.upper.finite.localHom Q (x.1 Q))
  have hfUpper := D.upper.finite.finite_mulSupport _ x
  have hf : Function.HasFiniteMulSupport f :=
    hfUpper.subset (mulSupport_comp_subset D.targetMap.map_one _)
  change D.targetMap
      (∏ᶠ Q, D.upper.finite.localHom Q (x.1 Q)) =
    ∏ᶠ P, D.lower.finite.localHom P
      ((finiteIdeleNorm (K := K) (L := L) x).1 P)
  rw [D.targetMap.map_finprod_of_injective D.targetMap_injective]
  change (∏ᶠ Q, f Q) = _
  rw [finprod_fiberwise p f hf]
  apply finprod_congr
  intro P
  change (∏ Q : PlacesAbovePrime K L P,
      D.targetMap (D.upper.finite.localHom Q.1 (x.1 Q.1))) =
    D.lower.finite.localHom P
      ((finiteIdeleNorm (K := K) (L := L) x).1 P)
  rw [finite_idele_norm,
    idele_norm_literal (K := K) (L := L)]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro Q _
  exact D.finite_commutes P Q (x.1 Q.1)

private theorem infinite_commutes_global
    (D : BCData K L G G')
    (x : (InfiniteAdeleRing L)ˣ) :
    D.targetMap (D.upper.infiniteHom x) =
      D.lower.infiniteHom (infiniteIdeleNorm (K := K) (L := L) x) := by
  classical
  letI (v : InfinitePlace K) :
      Fintype (InfinitePlacesAbove (K := K) (L := L) v) :=
    infiniteCor84ExtensionsFintype v
  change D.targetMap
      (∏ w : InfinitePlace L,
        D.upper.infinite w (MulEquiv.piUnits x w)) =
    ∏ v : InfinitePlace K, D.lower.infinite v
      (infiniteNorm (K := K) (L := L) v x)
  rw [map_prod]
  simp_rw [infinite_norm]
  let e : Equiv (Σ v : InfinitePlace K,
      InfinitePlacesAbove (K := K) (L := L) v) (InfinitePlace L) :=
    { toFun := fun w ↦ w.2.1
      invFun := fun w ↦
        Sigma.mk (w.comap (algebraMap K L))
          (show InfinitePlacesAbove (K := K) (L := L)
            (w.comap (algebraMap K L)) from ⟨w, rfl⟩)
      left_inv := by
        rintro ⟨v, ⟨w, hw⟩⟩
        cases hw
        rfl
      right_inv := by
        intro w
        rfl }
  rw [← e.prod_comp]
  rw [Fintype.prod_sigma]
  apply Fintype.prod_congr
  intro v
  rw [map_prod]
  apply Fintype.prod_congr
  intro w
  exact D.infinite_commutes v w (MulEquiv.piUnits x w.1)

/-- Combining all local norm/Artin squares proves the global idèle Artin
square; it is no longer supplied as an assumption. -/
theorem commutes (D : BCData K L G G') :
    D.targetMap.comp D.upper.artin =
      D.lower.artin.comp (ideleNorm (K := K) (L := L)) := by
  ext x
  change D.targetMap (D.upper.infiniteHom x.1 *
      D.upper.finite.restrictedProductHom _ x.2) =
    D.lower.infiniteHom (infiniteIdeleNorm (K := K) (L := L) x.1) *
      D.lower.finite.restrictedProductHom _
        (finiteIdeleNorm (K := K) (L := L) x.2)
  rw [map_mul]
  rw [D.infinite_commutes_global x.1, D.finite_commutes_global x.2]

end BCData

/-! ### The concrete compositum Galois map -/

section Compositum

/-- Concrete data for VII.8.4(b).  Here `M` is literally the compositum of
the normal abelian field `E` and `K'`; the two global Artin maps are defined
as products of their local symbols.  Only the local norm/Artin squares are
fields of the structure. -/
structure CADataa
    (K K' M : Type u)
    [Field K] [NumberField K] [Field K'] [NumberField K'] [Field M]
    [Algebra K K'] [FiniteDimensional K K']
    [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    (E : IntermediateField K M)
    [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K' M] [IsGalois K' M]
    [IsMulCommutative Gal(E/K)] [IsMulCommutative Gal(M/K')] where
  lower : FAProduc K Gal(E/K)
  upper : FAProduc K' Gal(M/K')
  hcompositum : E ⊔ IntermediateField.adjoin K
    (Set.range (algebraMap K' M)) = ⊤
  finite_commutes : ∀ (P : HeightOneSpectrum (OK K))
      (Q : PlacesAbovePrime K K' P) (z : (Q.1.adicCompletion K')ˣ),
    compositumGaloisRestriction (K := K) (K' := K') (M := M) E
        (upper.finite.localHom Q.1 z) =
      lower.finite.localHom P
        (completionNormLiteral (K := K) (L := K') P Q z)
  infinite_commutes : ∀ (v : InfinitePlace K)
      (w : InfinitePlacesAbove (K := K) (L := K') v)
      (z : w.1.1.Completionˣ),
    compositumGaloisRestriction (K := K) (K' := K') (M := M) E
        (upper.infinite w.1 z) =
      lower.infinite v (infiniteCompletionNorm (K := K) (L := K') v w z)

namespace CADataa

variable {K K' M : Type u}
    [Field K] [NumberField K] [Field K'] [NumberField K'] [Field M]
    [Algebra K K'] [FiniteDimensional K K']
    [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    {E : IntermediateField K M}
    [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K' M] [IsGalois K' M]
    [IsMulCommutative Gal(E/K)] [IsMulCommutative Gal(M/K')]

private def toLocalData (D : CADataa K K' M E) :
    BCData K K' Gal(E/K) Gal(M/K') where
  lower := D.lower
  upper := D.upper
  targetMap := compositumGaloisRestriction
    (K := K) (K' := K') (M := M) E
  targetMap_injective :=
    compositum_restriction_injective E D.hcompositum
  finite_commutes := D.finite_commutes
  infinite_commutes := D.infinite_commutes

/-- The concrete global Artin square for the compositum, derived from its
local squares. -/
theorem commutes (D : CADataa K K' M E) :
    (compositumGaloisRestriction
      (K := K) (K' := K') (M := M) E).comp D.upper.artin =
      D.lower.artin.comp (ideleNorm (K := K) (L := K')) :=
  D.toLocalData.commutes

/-- **Lemma VII.8.4(b).**  If product reciprocity holds for `E/K`, it holds
after base change for the literal compositum `M = EK'` over `K'`.  The proof
uses the derived Artin square and the already-proved principal-idèle norm
compatibility. -/
theorem baseChange
    (D : CADataa K K' M E)
    (hreciprocity : TrivialPrincipalIdeles
      (OK K) K Gal(E/K) D.lower.artin) :
    TrivialPrincipalIdeles
      (OK K') K' Gal(M/K') D.upper.artin := by
  intro x
  apply compositum_restriction_injective E D.hcompositum
  rw [map_one]
  have hcomm := DFunLike.congr_fun D.commutes
    (principalIdele (OK K') K' x)
  change compositumGaloisRestriction E
      (D.upper.artin (principalIdele (OK K') K' x)) =
    D.lower.artin (ideleNorm (K := K) (L := K')
      (principalIdele (OK K') K' x)) at hcomm
  rw [hcomm, principalNormCompatibility (K := K) (L := K'),
    hreciprocity]

end CADataa

end Compositum

end

end Submission.CField.RExist
