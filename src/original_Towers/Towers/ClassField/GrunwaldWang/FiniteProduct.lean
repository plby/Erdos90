import Towers.NumberTheory.Density.PrimeIdealNatural
import Towers.ClassField.Ideles.IdeleClassNorm
import Towers.ClassField.Ideles.IdeleIdealMap
import Towers.ClassField.Ideles.LocalPlaceEmbeddings
import Towers.ClassField.GrunwaldWang.FamilySubgroupExtension
import Towers.ClassField.GrunwaldWang.GrunwaldWangStatement

/-!
# The finite product of local multiplicative groups in the idele class group

This file formalizes the first assertion in the paragraph preceding Theorem
VIII.2.3: the product of finitely many canonical one-place maps injects into
the idele class group.  The proof uses a finite prime outside the prescribed
set.  At that prime a supported idele has coordinate `1`; if it is principal,
injectivity of the completion map forces the principal element itself to be
`1`.
-/

namespace Towers.CField.GWang

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles

open scoped BigOperators

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

private abbrev OK := NumberField.RingOfIntegers K
private abbrev IK := IdeleGroup (OK K) K
private abbrev CK := IdeleClassGroup (OK K) K

/-- The canonical map from one local multiplicative group to the ideles. -/
def placeHom (v : Place K) :
    LocalMultiplicativeGroup K v →* IK K := by
  cases v with
  | inl P => exact finitePlaceEmbedding (OK K) K P
  | inr v => exact infinitePlaceEmbedding (OK K) K v

/-- The canonical map from one local multiplicative group to the idele class
group. -/
def placeClassHom (v : Place K) :
    LocalMultiplicativeGroup K v →* CK K :=
  (QuotientGroup.mk' (principalIdeles (OK K) K)).comp
    (placeHom K v)

theorem continuous_place_idele (v : Place K) :
    Continuous (placeHom K v) := by
  cases v with
  | inl P => exact continuous_finite_embedding P
  | inr v => exact continuous_place_embedding v

theorem continuous_place_hom (v : Place K) :
    Continuous (placeClassHom K v) :=
  continuous_quotient_mk'.comp (continuous_place_idele K v)

/-- Put a finite family of local elements into their corresponding idele
coordinates. -/
def productIdeleHom (S : Finset (Place K)) :
    ((v : S) → LocalMultiplicativeGroup K v.1) →* IK K :=
  finiteFamilyHom (fun v : S => LocalMultiplicativeGroup K v.1)
    (IK K) (fun v => placeHom K v.1)

@[simp]
theorem product_idele_hom
    (S : Finset (Place K))
    (x : (v : S) → LocalMultiplicativeGroup K v.1) :
    productIdeleHom K S x =
      ∏ v : S, placeHom K v.1 (x v) := by
  classical
  simp [productIdeleHom, finiteFamilyHom,
    Pi.monoidHomMulEquiv]

/-- The composite finite-product map into the idele class group. -/
def placeIdeleHom (S : Finset (Place K)) :
    ((v : S) → LocalMultiplicativeGroup K v.1) →* CK K :=
  finiteFamilyHom (fun v : S => LocalMultiplicativeGroup K v.1)
    (CK K) (fun v => placeClassHom K v.1)

theorem continuous_idele_hom
    (S : Finset (Place K)) :
    Continuous (placeIdeleHom K S) :=
  continuous_family_hom
    (fun v : S => LocalMultiplicativeGroup K v.1) (CK K)
    (fun v => placeClassHom K v.1)
    (fun v => continuous_place_hom K v.1)

theorem place_idele_comp (S : Finset (Place K)) :
    placeIdeleHom K S =
      (QuotientGroup.mk' (principalIdeles (OK K) K)).comp
        (productIdeleHom K S) := by
  classical
  apply (Pi.monoidHomMulEquiv
    (fun v : S => LocalMultiplicativeGroup K v.1) (CK K)).injective
  funext v
  ext x
  change placeIdeleHom K S (Pi.mulSingle v x) =
    QuotientGroup.mk' (principalIdeles (OK K) K)
      (productIdeleHom K S (Pi.mulSingle v x))
  unfold placeIdeleHom productIdeleHom
  rw [family_hom_single, family_hom_single]
  rfl

private def ideleCoordinateHom
    (P : HeightOneSpectrum (OK K)) : IK K →* (P.adicCompletion K)ˣ where
  toFun a := a.2.1 P
  map_one' := rfl
  map_mul' _ _ := rfl

private def infiniteIdeleHom
    (v : InfinitePlace K) : IK K →* v.Completionˣ where
  toFun a := MulEquiv.piUnits a.1 v
  map_one' := by
    exact congrFun (map_one (MulEquiv.piUnits :
      (InfiniteAdeleRing K)ˣ ≃* ((w : InfinitePlace K) → w.Completionˣ))) v
  map_mul' a b := by
    exact congrFun (map_mul (MulEquiv.piUnits :
      (InfiniteAdeleRing K)ˣ ≃* ((w : InfinitePlace K) → w.Completionˣ)) a.1 b.1) v

private theorem place_idele_one
    (S : Finset (Place K)) (P : HeightOneSpectrum (OK K))
    (hP : (Sum.inl P : Place K) ∉ S) (v : S)
    (x : LocalMultiplicativeGroup K v.1) :
    ideleCoordinateHom K P (placeHom K v.1 x) = 1 := by
  classical
  rcases v with ⟨v, hv⟩
  cases v with
  | inl Q =>
      have hQP : Q ≠ P := by
        intro h
        subst Q
        exact hP hv
      change RestrictedProduct.mulSingle
        (IdeleUnitSubgroup (OK K) K) Q x P = 1
      exact RestrictedProduct.mulSingle_eq_of_ne
        (IdeleUnitSubgroup (OK K) K) x hQP.symm
  | inr w =>
      rfl

private theorem coordinate_place_idele
    (S : Finset (Place K)) (P : HeightOneSpectrum (OK K))
    (hP : (Sum.inl P : Place K) ∉ S)
    (x : (v : S) → LocalMultiplicativeGroup K v.1) :
    ideleCoordinateHom K P
      (productIdeleHom K S x) = 1 := by
  classical
  rw [product_idele_hom]
  rw [map_prod]
  exact Finset.prod_eq_one fun v hv =>
    place_idele_one K S P hP v (x v)

private theorem place_idele_hom
    (S : Finset (Place K)) (P : HeightOneSpectrum (OK K))
    (hP : (Sum.inl P : Place K) ∈ S)
    (x : (v : S) → LocalMultiplicativeGroup K v.1) :
    ideleCoordinateHom K P
      (productIdeleHom K S x) =
        x ⟨Sum.inl P, hP⟩ := by
  classical
  let i : S := ⟨Sum.inl P, hP⟩
  rw [product_idele_hom]
  rw [map_prod, Finset.prod_eq_single i]
  · change RestrictedProduct.mulSingle
      (IdeleUnitSubgroup (OK K) K) P (x i) P = x i
    exact RestrictedProduct.mulSingle_eq_same (IdeleUnitSubgroup (OK K) K) P (x i)
  · intro v _ hvi
    rcases v with ⟨v, hv⟩
    cases v with
    | inl Q =>
        have hQP : Q ≠ P := by
          intro h
          apply hvi
          apply Subtype.ext
          simpa [i] using
            congrArg (fun Q => (Sum.inl Q : Place K)) h
        change RestrictedProduct.mulSingle
          (IdeleUnitSubgroup (OK K) K) Q (x ⟨Sum.inl Q, hv⟩) P = 1
        exact RestrictedProduct.mulSingle_eq_of_ne
          (IdeleUnitSubgroup (OK K) K) _ hQP.symm
    | inr w => rfl
  · simp

private theorem infinite_idele_hom
    (S : Finset (Place K)) (w : InfinitePlace K)
    (hw : (Sum.inr w : Place K) ∈ S)
    (x : (v : S) → LocalMultiplicativeGroup K v.1) :
    infiniteIdeleHom K w
      (productIdeleHom K S x) =
        x ⟨Sum.inr w, hw⟩ := by
  classical
  let i : S := ⟨Sum.inr w, hw⟩
  rw [product_idele_hom]
  rw [map_prod, Finset.prod_eq_single i]
  · dsimp [i]
    change MulEquiv.piUnits
      (MulEquiv.piUnits.symm
        (Pi.mulSingle (M := fun z : InfinitePlace K => z.Completionˣ)
          w (x ⟨Sum.inr w, hw⟩))) w = x ⟨Sum.inr w, hw⟩
    rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_same]
  · intro v _ hvi
    rcases v with ⟨v, hv⟩
    cases v with
    | inl P => rfl
    | inr z =>
        have hzw : z ≠ w := by
          intro h
          apply hvi
          apply Subtype.ext
          simpa [i] using
            congrArg (fun z => (Sum.inr z : Place K)) h
        change MulEquiv.piUnits
          (MulEquiv.piUnits.symm
            (Pi.mulSingle (M := fun z : InfinitePlace K => z.Completionˣ)
              z (x ⟨Sum.inr z, hv⟩))) w = 1
        rw [MulEquiv.apply_symm_apply, Pi.mulSingle_eq_of_ne' hzw]
  · simp

/-- The supported map from a finite product of local multiplicative groups
to the ideles is injective. -/
theorem idele_hom_injective (S : Finset (Place K)) :
    Function.Injective (productIdeleHom K S) := by
  apply (injective_iff_map_eq_one (productIdeleHom K S)).2
  intro x hx
  funext v
  rcases v with ⟨v, hv⟩
  cases v with
  | inl P =>
      have hcoord := congrArg (ideleCoordinateHom K P) hx
      rw [map_one, place_idele_hom K S P hv] at hcoord
      exact hcoord
  | inr w =>
      have hcoord := congrArg (infiniteIdeleHom K w) hx
      rw [map_one, infinite_idele_hom K S w hv] at hcoord
      exact hcoord

/-- A finite set of places omits some finite prime. -/
private theorem finite_place_not (S : Finset (Place K)) :
    ∃ P : HeightOneSpectrum (OK K), (Sum.inl P : Place K) ∉ S := by
  letI : Infinite (HeightOneSpectrum (OK K)) :=
    Towers.NumberTheory.Milne.infinite_primeIdeals K
  have hrange :
      (Set.range (Sum.inl : HeightOneSpectrum (OK K) → Place K)).Infinite :=
    Set.infinite_range_of_injective Sum.inl_injective
  have hdiff := hrange.diff S.finite_toSet
  obtain ⟨v, ⟨P, rfl⟩, hP⟩ := hdiff.nonempty
  exact ⟨P, hP⟩

/-- The canonical product map from finitely many local multiplicative groups
to the idele class group is injective.  This is the first assertion in the
paragraph preceding Theorem VIII.2.3. -/
theorem place_idele_injective
    (S : Finset (Place K)) :
    Function.Injective (placeIdeleHom K S) := by
  classical
  apply (injective_iff_map_eq_one
    (placeIdeleHom K S)).2
  intro x hx
  rw [place_idele_comp] at hx
  have hprincipal : productIdeleHom K S x ∈
      principalIdeles (OK K) K :=
    (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨a, ha⟩ := hprincipal
  obtain ⟨P, hP⟩ := finite_place_not K S
  have hcoord : Units.map
      (algebraMap K (P.adicCompletion K)).toMonoidHom a = 1 := by
    have hcoord' := congrArg (ideleCoordinateHom K P) ha
    change (principalIdele (OK K) K a).2.1 P =
      ideleCoordinateHom K P
        (productIdeleHom K S x) at hcoord'
    rw [principal_idele_finite,
      coordinate_place_idele K S P hP x]
      at hcoord'
    exact hcoord'
  have haone : a = 1 := by
    exact Units.map_injective
      (algebraMap K (P.adicCompletion K)).injective hcoord
  apply idele_hom_injective K S
  simpa only [haone, map_one] using ha.symm

end

end Towers.CField.GWang
