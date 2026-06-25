import Submission.ClassField.BrauerGroups.RelativeBrauerGroup
import Submission.ClassField.CrossedProducts.CohomologyClass
import Submission.ClassField.CrossedProducts.CohomologousProducts
import Submission.ClassField.CrossedProducts.BimoduleInfrastructure
import Submission.ClassField.CrossedProducts.Injectivity
import Submission.ClassField.CrossedProducts.FixedDimensionInjectivity

/-!
# Chapter IV, Section 3, Theorem 3.14: the cohomology-to-Brauer map

Crossed products descend from normalized cocycles to multiplicative `H²` and
land in the relative Brauer group.  Theorem 3.11 gives injectivity, Theorem
3.6 gives surjectivity, and Lemma 3.15 gives multiplicativity.  Together these
produce Milne's isomorphism of abelian groups.
-/

namespace Submission.CField.CProduca

noncomputable section

universe u

attribute [local instance] Units.mulDistribMulActionRight

namespace CProduc

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]

/-- The relative Brauer class represented by a normalized crossed product. -/
def relativeBrauerClass
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ)) :
    BGroups.relativeBrauerGroup k L :=
  ⟨brauerClass k L c,
    (BGroups.brauer_relative_split
      k L (centralSimpleCSA k L c)).2 (isSplitBy k L c)⟩

/-- Cohomologous normalized cocycles determine the same relative Brauer
class. -/
theorem relative_brauer_cohomologous
    {c d : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ)}
    (h : MHTwo.IsCohomologous c d) :
    relativeBrauerClass k L c = relativeBrauerClass k L d := by
  apply Subtype.ext
  change BGroups.brauerClass k (centralSimpleCSA k L c) =
    BGroups.brauerClass k (centralSimpleCSA k L d)
  rw [BGroups.brauer_class]
  exact BGroups.brauer_equivalent_alg k _ _
    (algMulCoboundary₂ k L c d h)

/-- Equality of crossed-product Brauer classes forces an algebra isomorphism,
because all crossed products for `L/k` have the same dimension. -/
theorem nonempty_relative_brauer
    {c d : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ)}
    (h : relativeBrauerClass k L c = relativeBrauerClass k L d) :
    Nonempty (CProduc c ≃ₐ[k] CProduc d) := by
  have hBrauer : IsBrauerEquivalent (centralSimpleCSA k L c)
      (centralSimpleCSA k L d) := by
    rw [← BGroups.brauer_class]
    exact congrArg Subtype.val h
  apply nonempty_equivalent_finrank
    k (CProduc c) (CProduc d) hBrauer
  rw [finrank_over_base, finrank_over_base]

/-- The crossed-product map from multiplicative `H²(L/k)` to the relative
Brauer group `Br(L/k)`. -/
def h2Relative :
    MHTwo (Gal(L/k)) Lˣ →
      BGroups.relativeBrauerGroup k L :=
  Quotient.lift (relativeBrauerClass k L)
    (fun _ _ h ↦ relative_brauer_cohomologous k L h)

@[simp]
theorem h_brauer_mk
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ)) :
    h2Relative k L (MHTwo.mk c) =
      relativeBrauerClass k L c :=
  rfl

/-- Lemma 3.15 is exactly the assertion needed for the crossed-product map to
preserve multiplication on a pair of represented cohomology classes. -/
theorem h_tensor_compatibility
    (c d : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (h : TensorCompatibility k L c d) :
    h2Relative k L (MHTwo.mk c * MHTwo.mk d) =
      h2Relative k L (MHTwo.mk c) *
        h2Relative k L (MHTwo.mk d) := by
  rw [← MHTwo.mk_mul, h_brauer_mk,
    h_brauer_mk, h_brauer_mk]
  apply Subtype.ext
  change BGroups.brauerClass k
      (centralSimpleCSA k L (NMCocycl₂.mul c d)) =
    BGroups.brauerClass k (tensorSimpleCSA k L c d)
  rw [BGroups.brauer_class]
  exact h

/-- If Lemma 3.15 holds for every pair of normalized cocycles, the
crossed-product map preserves multiplication on arbitrary cohomology
classes. -/
theorem brauer_tensor_compatibility
    (hcompat : ∀ c d : NMCocycl₂
      (G := Gal(L/k)) (M := Lˣ), TensorCompatibility k L c d)
    (x y : MHTwo (Gal(L/k)) Lˣ) :
    h2Relative k L (x * y) =
      h2Relative k L x * h2Relative k L y := by
  induction x using Quotient.inductionOn with
  | _ c =>
      induction y using Quotient.inductionOn with
      | _ d =>
          exact h_tensor_compatibility
            k L c d (hcompat c d)

/-- The crossed-product map as a monoid homomorphism, conditional only on
the tensor-product calculation of Lemma 3.15. -/
def hBrauerMonoid
    (hcompat : ∀ c d : NMCocycl₂
      (G := Gal(L/k)) (M := Lˣ), TensorCompatibility k L c d) :
    MHTwo (Gal(L/k)) Lˣ →*
      BGroups.relativeBrauerGroup k L where
  toFun := h2Relative k L
  map_one' := by
    have h := brauer_tensor_compatibility
      k L hcompat (1 : MHTwo (Gal(L/k)) Lˣ) 1
    simp only [one_mul] at h
    apply mul_left_cancel (a := h2Relative k L 1)
    simpa using h.symm
  map_mul' := brauer_tensor_compatibility k L hcompat

/-- Every relative Brauer class is represented by a crossed product.  This is
the surjectivity part of Theorem IV.3.14. -/
theorem h_brauer_surjective :
    Function.Surjective (h2Relative k L) := by
  intro x
  obtain ⟨A, hA⟩ := Quotient.exists_rep x.1
  change BGroups.brauerClass k A = x.1 at hA
  have hmem : BGroups.brauerClass k A ∈
      BGroups.relativeBrauerGroup k L := by
    rw [hA]
    exact x.2
  have hsplit : BGroups.ISBy k L A :=
    (BGroups.brauer_relative_split
      k L A).1 hmem
  obtain ⟨c, hc⟩ :=
    crossed_brauer_split k A L hsplit
  refine ⟨MHTwo.mk c, ?_⟩
  apply Subtype.ext
  exact hc.trans hA

/-- Distinct multiplicative cohomology classes determine distinct relative
Brauer classes.  This is the injectivity part of Theorem IV.3.14. -/
theorem h_brauer_injective :
    Function.Injective (h2Relative k L) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ c =>
      induction y using Quotient.inductionOn with
      | _ d =>
          apply Quotient.sound
          have hclass : relativeBrauerClass k L c = relativeBrauerClass k L d :=
            hxy
          obtain ⟨e⟩ := nonempty_relative_brauer k L hclass
          exact cohomologous_alg_equiv k L c d e

/-- The crossed-product construction is a bijection from multiplicative
`H²(L/k)` to the relative Brauer group. -/
theorem h_brauer_bijective :
    Function.Bijective (h2Relative k L) :=
  ⟨h_brauer_injective k L, h_brauer_surjective k L⟩

/-- The set-level equivalence underlying Milne's Theorem IV.3.14.  Lemma
3.15 upgrades this equivalence to an isomorphism of abelian groups. -/
def h2Brauer :
    MHTwo (Gal(L/k)) Lˣ ≃
      BGroups.relativeBrauerGroup k L :=
  Equiv.ofBijective (h2Relative k L) (h_brauer_bijective k L)

/-- The group isomorphism in Theorem IV.3.14, with Lemma 3.15 exposed as
its sole remaining algebraic input. -/
def hTensorCompatibility
    (hcompat : ∀ c d : NMCocycl₂
      (G := Gal(L/k)) (M := Lˣ), TensorCompatibility k L c d) :
    MHTwo (Gal(L/k)) Lˣ ≃*
      BGroups.relativeBrauerGroup k L :=
  MulEquiv.ofBijective (hBrauerMonoid k L hcompat)
    (h_brauer_bijective k L)

/-- The crossed-product map preserves multiplication.  This is Theorem
IV.3.14's group-law assertion, supplied by Lemma IV.3.15. -/
theorem h_brauer_mul
    (x y : MHTwo (Gal(L/k)) Lˣ) :
    h2Relative k L (x * y) =
      h2Relative k L x * h2Relative k L y :=
  brauer_tensor_compatibility k L
    (fun c d ↦ tensorCompatibility k L c d) x y

/-- The crossed-product construction as a homomorphism of abelian groups. -/
def hBrauerHom :
    MHTwo (Gal(L/k)) Lˣ →*
      BGroups.relativeBrauerGroup k L :=
  hBrauerMonoid k L
    (fun c d ↦ tensorCompatibility k L c d)

@[simp]
theorem h_brauer_hom
    (x : MHTwo (Gal(L/k)) Lˣ) :
    hBrauerHom k L x = h2Relative k L x :=
  rfl

/-- **Theorem IV.3.14.** For a finite Galois extension `L/k`, crossed
products give an isomorphism of abelian groups from multiplicative
`H²(Gal(L/k), Lˣ)` to the relative Brauer group `Br(L/k)`. -/
def hRelativeBrauer :
    MHTwo (Gal(L/k)) Lˣ ≃*
      BGroups.relativeBrauerGroup k L :=
  hTensorCompatibility k L
    (fun c d ↦ tensorCompatibility k L c d)

@[simp]
theorem h_relative_brauer
    (x : MHTwo (Gal(L/k)) Lˣ) :
    hRelativeBrauer k L x = h2Relative k L x :=
  rfl

end CProduc

end

end Submission.CField.CProduca
