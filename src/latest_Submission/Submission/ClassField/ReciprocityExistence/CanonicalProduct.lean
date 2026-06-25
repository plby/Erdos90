import Submission.ClassField.Ideles.LocalPlaceEmbeddings
import Submission.ClassField.Reciprocity.FiniteProductContinuity
import Submission.ClassField.ReciprocityExistence.FiniteLayerAbsolute

/-!
# A continuous idèle homomorphism as a product of its local coordinates

A continuous homomorphism from the idèles to a discrete group depends on
only finitely many coordinates of the product of the local unit subgroups.
This gives the almost-everywhere unit condition and reconstructs the
homomorphism as the finite product of its local coordinate maps.
-/

namespace Submission.CField.RExist

open Filter Set
open NumberField IsDedekindDomain
open Submission.CField.Ideles
open Submission.CField.Recip
open scoped RestrictedProduct

noncomputable section

universe u v

section RestrictedProduct

variable {ι : Type u} {G : ι → Type v} [∀ i, CommGroup (G i)]
variable (U : ∀ i, Subgroup (G i))
variable {A : Type v} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable [∀ i, TopologicalSpace (G i)]

/-- Continuity into a discrete group gives a finite set of unit coordinates
which controls a restricted-product homomorphism on the full unit product. -/
theorem continuous_restricted_control
    (f : (Πʳ i, [G i, U i]) →* A) (hf : Continuous f) :
    ∃ I : Finset ι, ∀ x : ∀ i, U i,
      (∀ i ∈ I, x i = 1) →
        f (RestrictedProduct.structureMap G (fun i => (U i : Set (G i)))
          cofinite x) = 1 := by
  let includeUnits : (∀ i, U i) →*
      (Πʳ i, [G i, U i]) :=
    { toFun := RestrictedProduct.structureMap G
        (fun i => (U i : Set (G i))) cofinite
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let h : (∀ i, U i) →* A := f.comp includeUnits
  have hh : Continuous h :=
    hf.comp RestrictedProduct.isEmbedding_structureMap.continuous
  have hopen : IsOpen {x : ∀ i, U i | h x = 1} := by
    exact (isOpen_discrete {1}).preimage hh
  have hone : (1 : ∀ i, U i) ∈ {x : ∀ i, U i | h x = 1} := by
    exact map_one h
  obtain ⟨I, V, hV, hsub⟩ := (isOpen_pi_iff.mp hopen) 1 hone
  refine ⟨I, fun x hx => ?_⟩
  change f (includeUnits x) = 1
  apply hsub
  intro i hi
  rw [hx i (Finset.mem_coe.mp hi)]
  exact (hV i (Finset.mem_coe.mpr (Finset.mem_coe.mp hi))).2

/-- A continuous homomorphism from a restricted product to a discrete group
is the `finprod` of its one-coordinate homomorphisms. -/
theorem restricted_family_continuous
    [DecidableEq ι]
    (f : (Πʳ i, [G i, U i]) →* A) (hf : Continuous f) :
    ∃ D : RLFam (A := A) U,
      D.restrictedProductHom U = f ∧
        ∀ i x, D.localHom i x = f (RestrictedProduct.mulSingle U i x) := by
  classical
  obtain ⟨I, hI⟩ :=
    continuous_restricted_control U f hf
  let localHom : ∀ i, G i →* A := fun i =>
    f.comp
      { toFun := RestrictedProduct.mulSingle U i
        map_one' := RestrictedProduct.mulSingle_one U i
        map_mul' := RestrictedProduct.mulSingle_mul U i }
  have hlocalOutside (i : ι) (hiI : i ∉ I)
      (x : G i) (hx : x ∈ U i) : localHom i x = 1 := by
    let xu : U i := ⟨x, hx⟩
    let z : ∀ j, U j := Pi.mulSingle i xu
    have hzI : ∀ j ∈ I, z j = 1 := by
      intro j hj
      change (Pi.mulSingle i xu : ∀ k, U k) j = 1
      rw [Pi.mulSingle_eq_of_ne]
      exact fun hji => hiI (hji ▸ hj)
    have hz := hI z hzI
    change f (RestrictedProduct.mulSingle U i x) = 1
    have hzsingle : RestrictedProduct.structureMap G
        (fun j => (U j : Set (G j))) cofinite z =
        RestrictedProduct.mulSingle U i x := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [z, xu]
      · simp [z, xu, hji]
    rwa [hzsingle] at hz
  have heventually : ∀ᶠ i in cofinite,
      ∀ x : G i, x ∈ U i → localHom i x = 1 := by
    filter_upwards [I.finite_toSet.compl_mem_cofinite] with i hiI
    exact hlocalOutside i (by simpa using hiI)
  let D : RLFam (A := A) U :=
    { localHom := localHom
      eventually_units := heventually }
  refine ⟨D, ?_, fun _ _ => rfl⟩
  apply MonoidHom.ext
  intro x
  let bad : Set ι := {i | x i ∉ U i}
  have hbad : bad.Finite := by
    simpa [bad] using (mem_cofinite.mp x.2)
  let J : Finset ι := hbad.toFinset
  let H : Finset ι := I ∪ J
  let tail : ∀ i, U i := fun i =>
    if hi : i ∈ H then 1 else
      ⟨x i, by
        have hiJ : i ∉ J := fun h => hi (Finset.mem_union_right I h)
        have hibad : i ∉ bad := by simpa [J] using hiJ
        simpa [bad] using hibad⟩
  have htailI : ∀ i ∈ I, tail i = 1 := by
    intro i hi
    simp [tail, H, hi]
  have htail : f (RestrictedProduct.structureMap G
      (fun i => (U i : Set (G i))) cofinite tail) = 1 :=
    hI tail htailI
  have hDtail : D.restrictedProductHom U
      (RestrictedProduct.structureMap G
        (fun i => (U i : Set (G i))) cofinite tail) = 1 := by
    change (∏ᶠ i, localHom i (tail i)) = 1
    apply finprod_eq_one_of_forall_eq_one
    intro i
    by_cases hi : i ∈ I
    · rw [htailI i hi]
      exact map_one (localHom i)
    · exact hlocalOutside i hi (tail i) (tail i).2
  have hprod (i : ι) :
      (∏ j ∈ H, RestrictedProduct.mulSingle U j (x j)) i =
        if i ∈ H then x i else 1 := by
    change RestrictedProduct.evalMonoidHom G i
      (∏ j ∈ H, RestrictedProduct.mulSingle U j (x j)) = _
    rw [map_prod]
    by_cases hi : i ∈ H
    · rw [if_pos hi]
      rw [Finset.prod_eq_single i]
      · exact RestrictedProduct.mulSingle_eq_same
          (A := U) (i := i) (x i)
      · intro j hj hji
        exact RestrictedProduct.mulSingle_eq_of_ne U (x j) hji.symm
      · intro hnot
        exact (hnot hi).elim
    · rw [if_neg hi]
      apply Finset.prod_eq_one
      intro j hj
      exact RestrictedProduct.mulSingle_eq_of_ne U (x j)
        (fun hji => hi (hji ▸ hj))
  have hxdecomp :
      x = (∏ i ∈ H, RestrictedProduct.mulSingle U i (x i)) *
        RestrictedProduct.structureMap G
          (fun i => (U i : Set (G i))) cofinite tail := by
    ext i
    change x i =
      (∏ j ∈ H, RestrictedProduct.mulSingle U j (x j)) i *
        (tail i : G i)
    by_cases hi : i ∈ H
    · rw [hprod i, if_pos hi]
      simp [tail, hi]
    · rw [hprod i, if_neg hi]
      simp [tail, hi]
  change D.restrictedProductHom U x = f x
  rw [hxdecomp, map_mul, map_mul, htail, hDtail, mul_one]
  rw [map_prod, map_prod]
  simp only [mul_one]
  apply Finset.prod_congr rfl
  intro i _
  exact D.restricted_product_single U i (x i)

end RestrictedProduct

section IdeleGroup

variable {K A : Type u} [Field K] [NumberField K]
  [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- Every continuous idèle homomorphism to a discrete commutative group is
canonically reconstructed as the product of its one-place restrictions. -/
theorem artin_product_continuous
    (f : IdeleGroup (RingOfIntegers K) K →* A) (hf : Continuous f) :
    ∃ D : FAProduc K A,
      D.artin = f ∧
      (∀ P x, D.finite.localHom P x =
        f (finitePlaceEmbedding (RingOfIntegers K) K P x)) ∧
      ∀ v x, D.infinite v x =
        f (infinitePlaceEmbedding (RingOfIntegers K) K v x) := by
  classical
  let finiteInclusion : FiniteIdeles (RingOfIntegers K) K →*
      IdeleGroup (RingOfIntegers K) K :=
    { toFun := fun x => (1, x)
      map_one' := rfl
      map_mul' := by
        intro x y
        apply Prod.ext
        · change (1 : (InfiniteAdeleRing K)ˣ) = 1 * 1
          simp
        · rfl }
  let ffinite : FiniteIdeles (RingOfIntegers K) K →* A :=
    f.comp finiteInclusion
  have hffinite : Continuous ffinite := by
    exact hf.comp (continuous_const.prodMk continuous_id)
  letI : DecidableEq (HeightOneSpectrum (RingOfIntegers K)) :=
    Classical.decEq _
  obtain ⟨finite, hfinite, hfinite_coord⟩ :=
    restricted_family_continuous
      (fun P : HeightOneSpectrum (RingOfIntegers K) =>
        IdeleUnitSubgroup (RingOfIntegers K) K P)
      ffinite hffinite
  let D : FAProduc K A :=
    { finite := finite
      infinite := fun v =>
        f.comp (infinitePlaceEmbedding (RingOfIntegers K) K v) }
  refine ⟨D, ?_, ?_, fun _ _ => rfl⟩
  · apply MonoidHom.ext
    intro a
    rw [D.artin_apply]
    have hfin := DFunLike.congr_fun hfinite a.2
    change (∏ᶠ P, finite.localHom P (a.2.1 P)) = ffinite a.2 at hfin
    rw [hfin]
    have hinfinite :
        (∏ v : InfinitePlace K,
          f (infinitePlaceEmbedding (RingOfIntegers K) K v
            (MulEquiv.piUnits a.1 v))) = f (a.1, 1) := by
      have hidele :
          (∏ v : InfinitePlace K,
            infinitePlaceEmbedding (RingOfIntegers K) K v
              (MulEquiv.piUnits a.1 v)) = (a.1, 1) := by
        apply Prod.ext
        · change (MonoidHom.fst
              (InfiniteAdeleRing K)ˣ
              (FiniteIdeles (RingOfIntegers K) K))
              (∏ v : InfinitePlace K,
                infinitePlaceEmbedding (RingOfIntegers K) K v
                  (MulEquiv.piUnits a.1 v)) = a.1
          rw [map_prod]
          change (∏ v : InfinitePlace K,
              MulEquiv.piUnits.symm
                (Pi.mulSingle v (MulEquiv.piUnits a.1 v))) = a.1
          rw [← map_prod]
          rw [Finset.univ_prod_mulSingle]
          exact MulEquiv.symm_apply_apply _ _
        · change (MonoidHom.snd
              (InfiniteAdeleRing K)ˣ
              (FiniteIdeles (RingOfIntegers K) K))
              (∏ v : InfinitePlace K,
                infinitePlaceEmbedding (RingOfIntegers K) K v
                  (MulEquiv.piUnits a.1 v)) = 1
          rw [map_prod]
          change (∏ _v : InfinitePlace K,
              (1 : FiniteIdeles (RingOfIntegers K) K)) = 1
          simp
      calc
        _ = f (∏ v : InfinitePlace K,
            infinitePlaceEmbedding (RingOfIntegers K) K v
              (MulEquiv.piUnits a.1 v)) := by
          exact (map_prod f (fun v : InfinitePlace K =>
            infinitePlaceEmbedding (RingOfIntegers K) K v
              (MulEquiv.piUnits a.1 v)) Finset.univ).symm
        _ = f (a.1, 1) := congrArg f hidele
    change (∏ v : InfinitePlace K,
        f (infinitePlaceEmbedding (RingOfIntegers K) K v
          (MulEquiv.piUnits a.1 v))) * f (1, a.2) = f a
    rw [hinfinite]
    rw [← map_mul]
    apply congrArg f
    apply Prod.ext
    · change a.1 * 1 = a.1
      simp
    · change 1 * a.2 = a.2
      simp
  · intro P x
    change finite.localHom P x = f _
    rw [hfinite_coord P x]
    rfl

end IdeleGroup

end

end Submission.CField.RExist
