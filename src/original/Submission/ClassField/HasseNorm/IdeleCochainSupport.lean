import Submission.ClassField.HasseNorm.IdeleDecomposition
import Submission.ClassField.IdeleCohomology.NormInvariants
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Finite support of idèle-valued cochains

An idèle is a local unit at all but finitely many finite places.  Since the
Galois group of a finite extension is finite, every finite-degree cochain has
one common finite set of base places outside which all of its values are local
units.  This is the first restricted-product step in Proposition VII.2.5(b).
-/

namespace Submission.CField.HNorm

open CategoryTheory Representation
open Filter IsDedekindDomain NumberField
open Submission.CField.Ideles
open Submission.CField.ICohomo
open groupCohomology
open scoped RestrictedProduct

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A finite family of idèles is contained in one `I_{L,T}`: there is a
finite set of base places outside which every finite coordinate of every
member of the family is a local unit. -/
theorem ideles_places_family
    {D : Type u} [Finite D]
    (f : D → IdeleGroup (NumberField.RingOfIntegers L) L) :
    ∃ S : Finset (NumberFieldPlace K),
      ∀ d : D, f d ∈ idelesAtPlaces (K := K) (L := L) S := by
  classical
  let bad : Set (HeightOneSpectrum (NumberField.RingOfIntegers L)) :=
    {Q | ∃ d : D,
      (f d).2.1 Q ∉ IdeleUnitSubgroup
        (NumberField.RingOfIntegers L) L Q}
  have hgood : ∀ᶠ Q in cofinite, ∀ d : D,
      (f d).2.1 Q ∈ IdeleUnitSubgroup
        (NumberField.RingOfIntegers L) L Q := by
    rw [Filter.eventually_all]
    exact fun d => (f d).2.2
  have hbad : bad.Finite := by
    have hfinite := Filter.eventually_cofinite.mp hgood
    refine hfinite.subset ?_
    intro Q hQ
    change ∃ d : D,
      (f d).2.1 Q ∉ IdeleUnitSubgroup
        (NumberField.RingOfIntegers L) L Q at hQ
    change ¬∀ d : D,
      (f d).2.1 Q ∈ IdeleUnitSubgroup
        (NumberField.RingOfIntegers L) L Q
    simpa only [not_forall] using hQ
  let badBase : Set (NumberFieldPlace K) :=
    (fun Q : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
      (Sum.inl (Q.under (NumberField.RingOfIntegers K)) : NumberFieldPlace K)) '' bad
  have hbadBase : badBase.Finite := hbad.image _
  let S : Finset (NumberFieldPlace K) := hbadBase.toFinset
  refine ⟨S, ?_⟩
  intro d Q hQ
  by_contra hnotUnit
  apply hQ
  change (Sum.inl (Q.under (NumberField.RingOfIntegers K)) : NumberFieldPlace K) ∈ S
  rw [Set.Finite.mem_toFinset]
  exact ⟨Q, ⟨d, hnotUnit⟩, rfl⟩

/-- The resized representation on Milne's subgroup `I_{L,T}`. -/
noncomputable def resizedPlacesRepresentation
    (S : Finset (NumberFieldPlace K)) : Rep (ULift.{u} ℤ) Gal(L/K) :=
  uliftIntegralRepresentation
    (idelesRepresentation (K := K) (L := L) S)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Enlarging the exceptional set enlarges Milne's subgroup `I_{L,T}`. -/
theorem ideles_places_mono
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    idelesAtPlaces (K := K) (L := L) S ≤
      idelesAtPlaces (K := K) (L := L) T := by
  intro x hx Q hQT
  apply hx Q
  exact fun hQS => hQT (hST hQS)

/-- The equivariant inclusion between two finite-support idèle stages. -/
noncomputable def idelesPlacesIntegral
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    idelesRepresentation (K := K) (L := L) S ⟶
      idelesRepresentation (K := K) (L := L) T := by
  apply Rep.ofHom
  let inclusion : idelesAtPlaces (K := K) (L := L) S →*
      idelesAtPlaces (K := K) (L := L) T :=
    { toFun := fun x => ⟨x.1, ideles_places_mono hST x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine
    { toLinearMap := (MonoidHom.toAdditive inclusion).toIntLinearMap
      isIntertwining' := ?_ }
  intro sigma
  ext x
  rfl

/-- The resized transition map between finite-support idèle stages. -/
noncomputable def resizedIdeles
    {S T : Finset (NumberFieldPlace K)} (hST : S ⊆ T) :
    resizedPlacesRepresentation (K := K) (L := L) S ⟶
      resizedPlacesRepresentation (K := K) (L := L) T :=
  uliftIntegralHom (idelesPlacesIntegral
    (K := K) (L := L) hST)

/-- Inclusion of `I_{L,T}` into the concrete idèle representation. -/
noncomputable def idelesInclusionIntegral
    (S : Finset (NumberFieldPlace K)) :
    idelesRepresentation (K := K) (L := L) S ⟶
      (concreteActionData (K := K) (L := L)).representation := by
  apply Rep.ofHom
  refine
    { toLinearMap :=
        (MonoidHom.toAdditive
          (idelesAtPlaces (K := K) (L := L) S).subtype).toIntLinearMap
      isIntertwining' := ?_ }
  intro sigma
  ext x
  rfl

/-- The resized equivariant inclusion of `I_{L,T}` into the idèles. -/
noncomputable def resizedInclusion
    (S : Finset (NumberFieldPlace K)) :
    resizedPlacesRepresentation (K := K) (L := L) S ⟶
      resizedConcreteRepresentation K L :=
  uliftIntegralHom (idelesInclusionIntegral
    (K := K) (L := L) S)

/-- A cochain with values in `I_{L,T}`, viewed as a cochain with values in
the full idèle group, is unchanged on underlying idèles. -/
@[simp]
theorem resized_inclusion
    (S : Finset (NumberFieldPlace K))
    (x : resizedPlacesRepresentation (K := K) (L := L) S) :
    (resizedInclusion (K := K) (L := L) S).hom x =
      Additive.ofMul
        (((show Additive (idelesAtPlaces (K := K) (L := L) S) from x).toMul :
            idelesAtPlaces (K := K) (L := L) S) :
          IdeleGroup (NumberField.RingOfIntegers L) L) :=
  rfl

/-- Every idèle-valued one-cochain has a common finite base support. -/
theorem ideles_places_cochain
    (f : Gal(L/K) → resizedConcreteRepresentation K L) :
    ∃ S : Finset (NumberFieldPlace K),
      ∀ sigma : Gal(L/K),
        (f sigma).toMul ∈ idelesAtPlaces (K := K) (L := L) S := by
  exact ideles_places_family
    (K := K) (L := L) (fun sigma => (f sigma).toMul)

/-- Lift a supported idèle-valued one-cochain to a finite idèle stage. -/
noncomputable def liftResizedCochain
    (S : Finset (NumberFieldPlace K))
    (f : Gal(L/K) → resizedConcreteRepresentation K L)
    (hf : ∀ sigma, (f sigma).toMul ∈
      idelesAtPlaces (K := K) (L := L) S) :
    Gal(L/K) → resizedPlacesRepresentation (K := K) (L := L) S :=
  fun sigma => Additive.ofMul ⟨(f sigma).toMul, hf sigma⟩

@[simp]
theorem resized_inclusion_cochain
    (S : Finset (NumberFieldPlace K))
    (f : Gal(L/K) → resizedConcreteRepresentation K L)
    (hf : ∀ sigma, (f sigma).toMul ∈
      idelesAtPlaces (K := K) (L := L) S)
    (sigma : Gal(L/K)) :
    (resizedInclusion (K := K) (L := L) S).hom
      (liftResizedCochain S f hf sigma) = f sigma :=
  rfl

/-- Every idèle-valued two-cochain, hence every degree-two cocycle, has a
common finite base support. -/
theorem ideles_resized_cochain
    (f : Gal(L/K) × Gal(L/K) → resizedConcreteRepresentation K L) :
    ∃ S : Finset (NumberFieldPlace K),
      ∀ gh : Gal(L/K) × Gal(L/K),
        (f gh).toMul ∈ idelesAtPlaces (K := K) (L := L) S := by
  exact ideles_places_family
    (K := K) (L := L) (fun gh => (f gh).toMul)

/-- Lift a supported idèle-valued two-cochain to the corresponding
`I_{L,T}` representation. -/
noncomputable def liftIdeleCochain
    (S : Finset (NumberFieldPlace K))
    (f : Gal(L/K) × Gal(L/K) → resizedConcreteRepresentation K L)
    (hf : ∀ gh, (f gh).toMul ∈ idelesAtPlaces (K := K) (L := L) S) :
    Gal(L/K) × Gal(L/K) →
      resizedPlacesRepresentation (K := K) (L := L) S :=
  fun gh => Additive.ofMul ⟨(f gh).toMul, hf gh⟩

@[simp]
theorem ideles_inclusion_cochain
    (S : Finset (NumberFieldPlace K))
    (f : Gal(L/K) × Gal(L/K) → resizedConcreteRepresentation K L)
    (hf : ∀ gh, (f gh).toMul ∈ idelesAtPlaces (K := K) (L := L) S)
    (gh : Gal(L/K) × Gal(L/K)) :
    (resizedInclusion (K := K) (L := L) S).hom
      (liftIdeleCochain S f hf gh) = f gh :=
  rfl

/-- Inclusion of `I_{L,T}` remains injective after universe resizing. -/
theorem resized_inclusion_injective
    (S : Finset (NumberFieldPlace K)) :
    Function.Injective
      (resizedInclusion (K := K) (L := L) S).hom := by
  intro x y hxy
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg Additive.toMul hxy

/-- A supported idèle cocycle is already a cocycle in the corresponding
`I_{L,T}` representation. -/
theorem lift_cochain_cocycles₂
    (S : Finset (NumberFieldPlace K))
    (x : cocycles₂ (resizedConcreteRepresentation K L))
    (hx : ∀ gh, (x gh).toMul ∈ idelesAtPlaces (K := K) (L := L) S) :
    liftIdeleCochain S x hx ∈
      cocycles₂ (resizedPlacesRepresentation
        (K := K) (L := L) S) := by
  apply (mem_cocycles₂_iff _).2
  intro g h j
  apply resized_inclusion_injective (K := K) (L := L) S
  simpa only [map_add,
      ideles_inclusion_cochain,
      Rep.hom_comm_apply] using
    ((mem_cocycles₂_iff x).1 x.2 g h j)

/-- Lift a supported degree-two cocycle to `I_{L,T}`. -/
noncomputable def liftResizedCocycle₂
    (S : Finset (NumberFieldPlace K))
    (x : cocycles₂ (resizedConcreteRepresentation K L))
    (hx : ∀ gh, (x gh).toMul ∈ idelesAtPlaces (K := K) (L := L) S) :
    cocycles₂ (resizedPlacesRepresentation (K := K) (L := L) S) :=
  ⟨liftIdeleCochain S x hx,
    lift_cochain_cocycles₂ S x hx⟩

/-- Mapping the lifted cocycle back to the full idèle representation recovers
the original cocycle. -/
theorem mapCocycles₂_liftResizedIdeleCocycle₂
    (S : Finset (NumberFieldPlace K))
    (x : cocycles₂ (resizedConcreteRepresentation K L))
    (hx : ∀ gh, (x gh).toMul ∈ idelesAtPlaces (K := K) (L := L) S) :
    mapCocycles₂ (MonoidHom.id Gal(L/K))
        (resizedInclusion (K := K) (L := L) S)
        (liftResizedCocycle₂ S x hx) = x := by
  apply cocycles₂_ext
  intro g h
  rfl

/-- Every degree-two idèle cohomology class comes from `H²(G,I_{L,T})`
for some finite set `T` of base places.  This is the cohomological finite-
support half of the restricted-product colimit argument. -/
theorem ideles_h_preimage
    (q : H2 (resizedConcreteRepresentation K L)) :
    ∃ (S : Finset (NumberFieldPlace K))
      (qS : H2 (resizedPlacesRepresentation (K := K) (L := L) S)),
      groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedInclusion (K := K) (L := L) S) 2 qS = q := by
  induction q using H2_induction_on with
  | h x =>
      obtain ⟨S, hx⟩ :=
        ideles_resized_cochain
          (K := K) (L := L) x
      refine ⟨S, H2π _ (liftResizedCocycle₂ S x hx), ?_⟩
      rw [H2π_comp_map_apply]
      rw [mapCocycles₂_liftResizedIdeleCocycle₂]

/-- If a class at one finite idèle stage becomes zero in the full idèles,
then it is already zero after enlarging the finite exceptional set.  The
enlargement only has to contain the finitely many places occurring in a
one-cochain witnessing that the mapped cocycle is a coboundary. -/
theorem ideles_places_h
    (S : Finset (NumberFieldPlace K))
    (qS : H2 (resizedPlacesRepresentation (K := K) (L := L) S))
    (hq : groupCohomology.map (MonoidHom.id Gal(L/K))
        (resizedInclusion (K := K) (L := L) S) 2 qS = 0) :
    ∃ (T : Finset (NumberFieldPlace K)) (hST : S ⊆ T),
      groupCohomology.map (MonoidHom.id Gal(L/K))
          (resizedIdeles (K := K) (L := L) hST) 2 qS = 0 := by
  classical
  induction qS using H2_induction_on with
  | h x =>
      have hmapped : H2π (resizedConcreteRepresentation K L)
          (mapCocycles₂ (MonoidHom.id Gal(L/K))
            (resizedInclusion (K := K) (L := L) S) x) = 0 := by
        rw [← H2π_comp_map_apply]
        exact hq
      have hb := (H2π_eq_zero_iff _).1 hmapped
      rcases hb with ⟨a, ha⟩
      obtain ⟨T₀, haT₀⟩ :=
        ideles_places_cochain
          (K := K) (L := L) a
      let T := S ∪ T₀
      have hST : S ⊆ T := Finset.subset_union_left
      have hT₀T : T₀ ⊆ T := Finset.subset_union_right
      have haT : ∀ sigma, (a sigma).toMul ∈
          idelesAtPlaces (K := K) (L := L) T := fun sigma =>
        ideles_places_mono (K := K) (L := L) hT₀T (haT₀ sigma)
      let aT := liftResizedCochain T a haT
      let xT := mapCocycles₂ (MonoidHom.id Gal(L/K))
        (resizedIdeles (K := K) (L := L) hST) x
      have hxT : (xT : Gal(L/K) × Gal(L/K) →
          resizedPlacesRepresentation (K := K) (L := L) T) ∈
          coboundaries₂ (resizedPlacesRepresentation
            (K := K) (L := L) T) := by
        refine ⟨aT, ?_⟩
        funext gh
        apply resized_inclusion_injective
          (K := K) (L := L) T
        change (resizedInclusion (K := K) (L := L) T).hom
              ((resizedPlacesRepresentation
                (K := K) (L := L) T).ρ gh.1 (aT gh.2) -
                aT (gh.1 * gh.2) + aT gh.1) =
            (resizedInclusion (K := K) (L := L) T).hom
              (xT gh)
        simp only [map_add, map_sub, Rep.hom_comm_apply]
        exact congrFun ha gh
      refine ⟨T, hST, ?_⟩
      rw [H2π_comp_map_apply]
      exact (H2π_eq_zero_iff xT).2 hxT

end

end Submission.CField.HNorm
