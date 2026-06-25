import Mathlib.Algebra.Colimit.DirectLimit
import Submission.ClassField.CrossedProducts.TensorRightCongr
import Submission.ClassField.CrossedProducts.Cohomology

/-!
# Chapter IV, Section 3, Corollary 3.16

Milne obtains `Br(k) ≃ H²(k^al/k)` by passing the finite-Galois
classification of Theorem 3.14 to a direct limit.  We construct the transition
maps by transporting inclusions of relative Brauer groups through Theorem
3.14, and identify the resulting direct limit with the absolute Brauer group.
-/

namespace Submission.CField.CProduca

noncomputable section

universe u

open BGroups

set_option synthInstance.maxHeartbeats 500000 in
-- The nested subtype fields make the scalar-tower instance search unusually deep.
/-- Relative Brauer groups increase when the splitting field increases. -/
theorem relative_brauer_mono
    (k : Type u) [Field k]
    {L E : FiniteGaloisIntermediateField k (SeparableClosure k)}
    (hLE : L ≤ E) :
    relativeBrauerGroup k L ≤ relativeBrauerGroup k E := by
  intro x hx
  obtain ⟨A, hA⟩ := Quotient.exists_rep x
  subst x
  have hsplitL : ISBy k L A :=
    (brauer_relative_split k L A).1 hx
  letI : Algebra (↑L.toIntermediateField) (↑E.toIntermediateField) :=
    (IntermediateField.inclusion
      (E := L.toIntermediateField) (F := E.toIntermediateField) hLE).toAlgebra
  haveI : IsScalarTower k L E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact (brauer_relative_split k E A).2
    (ISBy.tower k L E A hsplitL)

/-- Inclusion of relative Brauer groups along an inclusion of splitting
fields. -/
def relativeBrauerInclusion
    (k : Type u) [Field k]
    {L E : FiniteGaloisIntermediateField k (SeparableClosure k)}
    (hLE : L ≤ E) :
    relativeBrauerGroup k L →* relativeBrauerGroup k E :=
  Subgroup.inclusion (relative_brauer_mono k hLE)

@[simp]
theorem relative_brauer_inclusion
    (k : Type u) [Field k]
    {L E : FiniteGaloisIntermediateField k (SeparableClosure k)}
    (hLE : L ≤ E) (x : relativeBrauerGroup k L) :
    (relativeBrauerInclusion k hLE x : BrauerGroup k) = x :=
  rfl

/-- Inflation between finite-level multiplicative second cohomology groups.
It is characterized canonically by the inclusion `Br(L/k) ≤ Br(E/k)`. -/
def inflationHom
    (k : Type u) [Field k]
    {L E : FiniteGaloisIntermediateField k (SeparableClosure k)}
    (hLE : L ≤ E) :
    MHTwo (Gal(L/k)) Lˣ →*
      MHTwo (Gal(E/k)) Eˣ :=
  (CProduc.hRelativeBrauer k E).symm.toMonoidHom.comp
    ((relativeBrauerInclusion k hLE).comp
      (CProduc.hRelativeBrauer k L).toMonoidHom)

/-- The defining commutative square for inflation and relative Brauer-group
inclusion. -/
theorem relative_brauer_inflation
    (k : Type u) [Field k]
    {L E : FiniteGaloisIntermediateField k (SeparableClosure k)}
    (hLE : L ≤ E) (x : MHTwo (Gal(L/k)) Lˣ) :
    CProduc.hRelativeBrauer k E (inflationHom k hLE x) =
      relativeBrauerInclusion k hLE
        (CProduc.hRelativeBrauer k L x) := by
  simp [inflationHom]

@[simp]
theorem inflationHom_refl
    (k : Type u) [Field k]
    (L : FiniteGaloisIntermediateField k (SeparableClosure k))
    (x : MHTwo (Gal(L/k)) Lˣ) :
    inflationHom k (le_refl L) x = x := by
  apply (CProduc.hRelativeBrauer k L).injective
  rw [relative_brauer_inflation]
  rfl

@[simp]
theorem inflationHom_trans
    (k : Type u) [Field k]
    {L E F : FiniteGaloisIntermediateField k (SeparableClosure k)}
    (hLE : L ≤ E) (hEF : E ≤ F)
    (x : MHTwo (Gal(L/k)) Lˣ) :
    inflationHom k hEF (inflationHom k hLE x) =
      inflationHom k (hLE.trans hEF) x := by
  apply (CProduc.hRelativeBrauer k F).injective
  rw [relative_brauer_inflation,
    relative_brauer_inflation,
    relative_brauer_inflation]
  rfl

/-- Inflation is injective, since on relative Brauer groups it is an
inclusion. -/
theorem inflationHom_injective
    (k : Type u) [Field k]
    {L E : FiniteGaloisIntermediateField k (SeparableClosure k)}
    (hLE : L ≤ E) : Function.Injective (inflationHom k hLE) := by
  intro x y hxy
  apply (CProduc.hRelativeBrauer k L).injective
  apply Subtype.ext
  have this := congrArg
    (CProduc.hRelativeBrauer k E) hxy
  rw [relative_brauer_inflation,
    relative_brauer_inflation] at this
  exact congrArg
    (fun z : relativeBrauerGroup k E => (z : BrauerGroup k)) this

/-- The family of finite-level multiplicative cohomology groups. -/
abbrev multiplicativeHFamily
    (k : Type u) [Field k]
    (L : FiniteGaloisIntermediateField k (SeparableClosure k)) :=
  MHTwo (Gal(L/k)) Lˣ

/-- The transition map of the finite-level cohomology system. -/
def inflationSystemMap
    (k : Type u) [Field k]
    (L E : FiniteGaloisIntermediateField k (SeparableClosure k))
    (hLE : L ≤ E) :
    multiplicativeHFamily k L →*
      multiplicativeHFamily k E :=
  inflationHom k hLE

/-- The finite-level cohomology groups form a directed system under
inflation. -/
instance inflationDirectedSystem (k : Type u) [Field k] :
    DirectedSystem
      (multiplicativeHFamily k)
      (fun {_ _} h => inflationSystemMap k _ _ h) where
  map_self := by
    intro L x
    exact inflationHom_refl k L x
  map_map := by
    intro F E L hLE hEF x
    exact inflationHom_trans k (hLE := hLE) (hEF := hEF) x

/-- Milne's absolute multiplicative `H²`: the direct limit over finite Galois
subextensions of a fixed separable closure. -/
abbrev absoluteMultiplicativeH (k : Type u) [Field k] :=
  DirectLimit (multiplicativeHFamily k) (inflationSystemMap k)

/-- The canonical finite-level map into absolute multiplicative `H²`. -/
def absoluteMultiplicative2
    (k : Type u) [Field k]
    (L : FiniteGaloisIntermediateField k (SeparableClosure k)) :
    MHTwo (Gal(L/k)) Lˣ →*
      absoluteMultiplicativeH k where
  toFun x := ⟦⟨L, x⟩⟧
  map_one' := (DirectLimit.one_def L).symm
  map_mul' _ _ := (DirectLimit.mul_def L _ _).symm

set_option maxHeartbeats 800000 in
-- Unfolding equality in the dependent direct system needs a larger elaboration budget.
@[simp]
theorem absolute_multiplicative_inflation
    (k : Type u) [Field k]
    {L E : FiniteGaloisIntermediateField k (SeparableClosure k)}
    (hLE : L ≤ E) (x : MHTwo (Gal(L/k)) Lˣ) :
    absoluteMultiplicative2 k E (inflationHom k hLE x) =
      absoluteMultiplicative2 k L x := by
  change (⟦⟨E, inflationSystemMap k L E hLE x⟩⟧ :
    absoluteMultiplicativeH k) = ⟦⟨L, x⟩⟧
  exact (DirectLimit.eq_of_le (f := inflationSystemMap k) ⟨L, x⟩ E hLE).symm

/-- The finite relative Brauer class represented by a finite-level
cohomology class, viewed in the absolute Brauer group. -/
def finiteHBrauer
    (k : Type u) [Field k]
    (L : FiniteGaloisIntermediateField k (SeparableClosure k)) :
    MHTwo (Gal(L/k)) Lˣ →* BrauerGroup k :=
  (relativeBrauerGroup k L).subtype.comp
    (CProduc.hRelativeBrauer k L).toMonoidHom

theorem h_2_inflation
    (k : Type u) [Field k]
    {L E : FiniteGaloisIntermediateField k (SeparableClosure k)}
    (hLE : L ≤ E) (x : MHTwo (Gal(L/k)) Lˣ) :
    finiteHBrauer k E (inflationHom k hLE x) =
      finiteHBrauer k L x := by
  change ((CProduc.hRelativeBrauer k E
    (inflationHom k hLE x) : relativeBrauerGroup k E) : BrauerGroup k) = _
  rw [relative_brauer_inflation]
  rfl

set_option maxHeartbeats 1600000 in
-- Building the bundled homomorphism unfolds the dependent direct-limit operations.
/-- The canonical homomorphism from absolute multiplicative `H²` to the
Brauer group. -/
def absoluteHBrauer (k : Type u) [Field k] :
    absoluteMultiplicativeH k →* BrauerGroup k where
  toFun := DirectLimit.lift (inflationSystemMap k)
    (fun L => finiteHBrauer k L)
    (fun L E h x => (h_2_inflation k h x).symm)
  map_one' := by
    rw [DirectLimit.one_def (⊥ :
      FiniteGaloisIntermediateField k (SeparableClosure k))]
    exact map_one (finiteHBrauer k ⊥)
  map_mul' := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ L x y =>
        rw [DirectLimit.mul_def, DirectLimit.lift_def,
          DirectLimit.lift_def, DirectLimit.lift_def, map_mul]

@[simp]
theorem absolute_brauer_multiplicative
    (k : Type u) [Field k]
    (L : FiniteGaloisIntermediateField k (SeparableClosure k))
    (x : MHTwo (Gal(L/k)) Lˣ) :
    absoluteHBrauer k (absoluteMultiplicative2 k L x) =
      finiteHBrauer k L x :=
  rfl

/-- The absolute cohomology-to-Brauer map is injective. -/
theorem absolute_brauer_injective (k : Type u) [Field k] :
    Function.Injective (absoluteHBrauer k) := by
  intro x y hxy
  induction x, y using DirectLimit.induction₂ with
  | _ L x y =>
      apply congrArg (fun z : multiplicativeHFamily k L =>
        (⟦⟨L, z⟩⟧ : absoluteMultiplicativeH k))
      apply (CProduc.hRelativeBrauer k L).injective
      apply Subtype.ext
      exact hxy

/-- The absolute cohomology-to-Brauer map is surjective. -/
theorem absolute_brauer_surjective (k : Type u) [Field k] :
    Function.Surjective (absoluteHBrauer k) := by
  intro x
  have hx : x ∈ ⋃ L : FiniteGaloisIntermediateField k (SeparableClosure k),
      relativeBrauerClasses k L := by
    rw [← brauer_i_classes k]
    trivial
  obtain ⟨L, hxL⟩ := Set.mem_iUnion.1 hx
  let y : relativeBrauerGroup k L := ⟨x, hxL⟩
  let z := (CProduc.hRelativeBrauer k L).symm y
  exact ⟨absoluteMultiplicative2 k L z, by
    change ((CProduc.hRelativeBrauer k L z :
      relativeBrauerGroup k L) : BrauerGroup k) = x
    simp [z, y]⟩

/-- **Corollary IV.3.16.** The Brauer group is canonically isomorphic to
absolute multiplicative second Galois cohomology. -/
def brauerAbsoluteMultiplicative
    (k : Type u) [Field k] :
    BrauerGroup k ≃* absoluteMultiplicativeH k :=
  (MulEquiv.ofBijective (absoluteHBrauer k)
    ⟨absolute_brauer_injective k,
      absolute_brauer_surjective k⟩).symm

/-- The Brauer-side filtered-union assertion used in Milne's proof of
Corollary IV.3.16. -/
theorem i_union_classes
    (k : Type u) [Field k] :
    (Set.univ : Set (BrauerGroup.{u, u} k)) =
      ⋃ L : FiniteGaloisIntermediateField k (SeparableClosure k),
        relativeBrauerClasses k L :=
  brauer_i_classes k

end

end Submission.CField.CProduca
