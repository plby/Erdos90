import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Quotients by open ideals and dense subrings

This is the topological algebra mechanism in Milne's Lemma 7.25: a dense
subring and its completion have the same quotient by an open ideal, once the
ideal in the subring is identified with the pullback.
-/

namespace Submission.NumberTheory.Milne

open Set
open scoped Pointwise

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B]
  [TopologicalSpace B] [IsTopologicalRing B]

/-- The homomorphism induced on quotients by a ring homomorphism and the
pullback of an ideal. -/
def denseQuotientMap (f : A →+* B) (J : Ideal B) :
    A ⧸ J.comap f →+* B ⧸ J :=
  Ideal.quotientMap J f le_rfl

/-- If the original homomorphism has dense range and the target ideal is open,
then the induced quotient homomorphism is bijective. -/
theorem dense_quotient_bijective
    (f : A →+* B) (hf : DenseRange f) (J : Ideal B)
    (hJ : IsOpen (J : Set B)) :
    Function.Bijective (denseQuotientMap f J) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [denseQuotientMap, Ideal.quotientMap_mk, Ideal.quotientMap_mk,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hxy
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simpa only [Ideal.mem_comap, map_sub] using hxy
  · intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hopen : IsOpen ({b} + (J : Set B)) :=
      IsOpen.add_left (s := {b}) hJ
    have hnonempty : ({b} + (J : Set B)).Nonempty := by
      exact ⟨b, by simp⟩
    obtain ⟨a, ha⟩ := hf.exists_mem_open hopen hnonempty
    refine ⟨Ideal.Quotient.mk (J.comap f) a, ?_⟩
    rw [denseQuotientMap, Ideal.quotientMap_mk,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    rcases ha with ⟨x, hx, j, hj, haj⟩
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [← haj]
    simpa using hj

/-- A dense ring homomorphism induces an isomorphism from the quotient by the
pullback of any open ideal onto the corresponding quotient of the target. -/
def denseRangeOpen
    (f : A →+* B) (hf : DenseRange f) (J : Ideal B)
    (hJ : IsOpen (J : Set B)) :
    A ⧸ J.comap f ≃+* B ⧸ J :=
  RingEquiv.ofBijective (denseQuotientMap f J)
    (dense_quotient_bijective f hf J hJ)

@[simp]
theorem range_open_mk
    (f : A →+* B) (hf : DenseRange f) (J : Ideal B)
    (hJ : IsOpen (J : Set B)) (a : A) :
    denseRangeOpen f hf J hJ
        (Ideal.Quotient.mk (J.comap f) a) =
      Ideal.Quotient.mk J (f a) :=
  by
    rw [denseRangeOpen, RingEquiv.ofBijective_apply]
    exact Ideal.quotientMap_mk

end

end Submission.NumberTheory.Milne
