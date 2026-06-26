import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Milne, Class Field Theory, Proposition II.1.24

The additive Galois module of a finite Galois extension is coinduced from the
trivial subgroup.  The normal basis theorem identifies it with the regular
representation, and Shapiro's lemma then gives the vanishing of its positive
degree group cohomology.
-/

namespace Towers.CField.COps

open CategoryTheory

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The `K`-linear representation of the Galois group on the additive group of `L`. -/
noncomputable abbrev additiveGaloisRepresentation : Rep K Gal(L/K) :=
  Rep.ofDistribMulAction K Gal(L/K) L

section NormalBasis

variable [FiniteDimensional K L] [IsGalois K L]

/-- A normal basis identifies the regular representation with the additive Galois module. -/
noncomputable def isoAdditiveRepresentation :
    Rep.leftRegular K Gal(L/K) ≅ additiveGaloisRepresentation K L := by
  let b := IsGalois.normalBasis K L
  exact Rep.mkIso (.mk b.repr.symm fun g ↦ by
    apply Finsupp.lhom_ext'
    intro h
    apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply,
      Representation.ofMulAction_single,
      Representation.ofDistribMulAction_apply_apply]
    change b.repr.symm (Finsupp.single (g * h) r) =
      g (b.repr.symm (Finsupp.single h r))
    rw [b.repr_symm_single, b.repr_symm_single]
    rw [map_smul]
    congr 1
    change b (g * h) = g (b h)
    rw [show b (g * h) = (g * h) (b 1) from IsGalois.normalBasis_apply (g * h),
      show b h = h (b 1) from IsGalois.normalBasis_apply h]
    rfl)

end NormalBasis

section RegularCoinduced

variable {G : Type u} [Group G] [Finite G]

private noncomputable def regularTrivialCoind :
    Rep.leftRegular K G →ₗ[K]
      Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial K (⊥ : Subgroup G) K) where
  toFun x := ⟨fun g ↦ x g⁻¹, by
    intro s g
    have hs : s = (1 : (⊥ : Subgroup G)) :=
      Subtype.ext (Subgroup.mem_bot.mp s.property)
    subst hs
    simp⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

private theorem regular_coind_bijective :
    Function.Bijective (regularTrivialCoind K (G := G)) := by
  constructor
  · intro x y hxy
    apply Finsupp.ext
    intro g
    have := congrArg (fun f ↦ f.1 g⁻¹) hxy
    change x ((g⁻¹)⁻¹) = y ((g⁻¹)⁻¹) at this
    simpa using this
  · intro f
    let x : G →₀ K := Finsupp.equivFunOnFinite.symm fun g ↦ f.1 g⁻¹
    refine ⟨x, Subtype.ext ?_⟩
    funext g
    simp [regularTrivialCoind, x]

/-- The regular representation is coinduced from the trivial subgroup. -/
noncomputable def isoTrivialCoind :
    Rep.leftRegular K G ≅ Rep.coind (⊥ : Subgroup G).subtype
      (Rep.trivial K (⊥ : Subgroup G) K) :=
  Rep.mkIso (.mk
    (LinearEquiv.ofBijective (regularTrivialCoind K (G := G))
      (regular_coind_bijective K))
    (by
      intro g
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      funext h
      change (Representation.ofMulAction K G G g x) h⁻¹ = x (h * g)⁻¹
      rw [Representation.ofMulAction_apply]
      simp))

end RegularCoinduced

section Cohomology

variable [FiniteDimensional K L] [IsGalois K L]

/-- **Proposition II.1.24.** Positive-degree group cohomology of the additive
Galois module of a finite Galois extension vanishes. -/
theorem cohomology_representation_succ (n : ℕ) :
    Limits.IsZero (groupCohomology (additiveGaloisRepresentation K L) (n + 1)) := by
  let G := Gal(L/K)
  let A : Rep K (⊥ : Subgroup G) := Rep.trivial K (⊥ : Subgroup G) K
  let e : additiveGaloisRepresentation K L ≅ Rep.coind (⊥ : Subgroup G).subtype A :=
    (isoAdditiveRepresentation K L).symm ≪≫
      isoTrivialCoind K
  have hA : Limits.IsZero (groupCohomology A (n + 1)) :=
    isZero_groupCohomology_succ_of_subsingleton A n
  have hcoind : Limits.IsZero
      (groupCohomology (Rep.coind (⊥ : Subgroup G).subtype A) (n + 1)) :=
    Limits.IsZero.of_iso hA (groupCohomology.coindIso A (n + 1))
  exact Limits.IsZero.of_iso hcoind
    ((groupCohomology.functor K G (n + 1)).mapIso e)

/-- The positive-degree formulation of Proposition II.1.24. -/
theorem cohomology_additive_representation
    (r : ℕ) (hr : 0 < r) :
    Limits.IsZero (groupCohomology (additiveGaloisRepresentation K L) r) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  exact cohomology_representation_succ K L n

end Cohomology

end Towers.CField.COps
