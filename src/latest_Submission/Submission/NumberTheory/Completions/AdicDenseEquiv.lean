import Mathlib.Algebra.Group.Translate
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Adic completions of dense subrings

A dense ring homomorphism induces an equivalence on adic completions when
the target ideal powers are open and contract to the corresponding source
ideal powers.  This packages the quotient-by-quotient argument used for a
local Dedekind ring inside its completed valuation ring.
-/

namespace Submission.NumberTheory.Milne

open scoped Pointwise Topology

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B]
  [TopologicalSpace B] [IsTopologicalRing B]

private theorem surjective_dense_range
    (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hf : DenseRange f) (hJ : IsOpen (J : Set B))
    (hcomap : J.comap f = I) :
    Function.Surjective
      (Ideal.quotientMap J f (le_of_eq hcomap.symm)) := by
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hopen : IsOpen (b +ᵥ (J : Set B)) := hJ.left_addCoset b
  have hnonempty : (b +ᵥ (J : Set B)).Nonempty := by
    refine ⟨b, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp
  obtain ⟨a, ha⟩ := hf.exists_mem_open hopen hnonempty
  refine ⟨Ideal.Quotient.mk I a, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  rw [Set.mem_vadd_set_iff_neg_vadd_mem] at ha
  simpa [sub_eq_add_neg, add_comm] using ha

omit [TopologicalSpace B] [IsTopologicalRing B] in
private theorem injective_comap
    (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hcomap : J.comap f = I) :
    Function.Injective
      (Ideal.quotientMap J f (le_of_eq hcomap.symm)) := by
  unfold Ideal.quotientMap
  rw [Ideal.injective_lift_iff]
  ext a
  simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem]
  change a ∈ J.comap f ↔ a ∈ I
  rw [hcomap]

private noncomputable def denseRingEquiv
    (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hf : DenseRange f) (hJ : IsOpen (J : Set B))
    (hcomap : J.comap f = I) :
    (A ⧸ I) ≃+* (B ⧸ J) :=
  RingEquiv.ofBijective
    (Ideal.quotientMap J f (le_of_eq hcomap.symm))
    ⟨injective_comap f I J hcomap,
      surjective_dense_range f I J hf hJ hcomap⟩

private theorem dense_ring_mk
    (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hf : DenseRange f) (hJ : IsOpen (J : Set B))
    (hcomap : J.comap f = I) (a : A) :
    denseRingEquiv f I J hf hJ hcomap
        (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J (f a) := by
  exact Ideal.quotientMap_mk (H := le_of_eq hcomap.symm)

variable (f : A →+* B) (I : Ideal A) (J : Ideal B)
  (hf : DenseRange f)
  (hopen : ∀ n : ℕ, IsOpen (((J ^ n : Ideal B)) : Set B))
  (hcomap : ∀ n : ℕ, (J ^ n).comap f = I ^ n)

private noncomputable def adicQuotientRing (n : ℕ) :
    (A ⧸ (I ^ n • (⊤ : Submodule A A))) ≃+*
      (B ⧸ (J ^ n • (⊤ : Submodule B B))) :=
  (Ideal.quotEquivOfEq (by simp)).trans <|
    (denseRingEquiv f (I ^ n) (J ^ n) hf (hopen n)
      (hcomap n)).trans <|
      Ideal.quotEquivOfEq (by simp)

@[simp]
private theorem adic_ring_mk (n : ℕ) (a : A) :
    adicQuotientRing f I J hf hopen hcomap n
        (Submodule.mkQ (I ^ n • (⊤ : Submodule A A)) a) =
      Submodule.mkQ (J ^ n • (⊤ : Submodule B B)) (f a) := by
  rfl

private theorem adic_quotient_transition
    {m n : ℕ} (hmn : m ≤ n)
    (x : A ⧸ (I ^ n • (⊤ : Submodule A A))) :
    AdicCompletion.transitionMap J B hmn
        (adicQuotientRing f I J hf hopen hcomap n x) =
      adicQuotientRing f I J hf hopen hcomap m
        (AdicCompletion.transitionMap I A hmn x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
      change AdicCompletion.transitionMap J B hmn
          (adicQuotientRing f I J hf hopen hcomap n
            (Submodule.mkQ (I ^ n • (⊤ : Submodule A A)) a)) =
        adicQuotientRing f I J hf hopen hcomap m
          (AdicCompletion.transitionMap I A hmn
            (Submodule.mkQ (I ^ n • (⊤ : Submodule A A)) a))
      rw [adic_ring_mk]
      change Submodule.factor _ (Submodule.mkQ _ (f a)) = _
      rw [Submodule.factor_mk, Submodule.factor_mk]
      rw [adic_ring_mk]

private theorem adic_ring_transition
    {m n : ℕ} (hmn : m ≤ n)
    (x : B ⧸ (J ^ n • (⊤ : Submodule B B))) :
    AdicCompletion.transitionMap I A hmn
        ((adicQuotientRing f I J hf hopen hcomap n).symm x) =
      (adicQuotientRing f I J hf hopen hcomap m).symm
        (AdicCompletion.transitionMap J B hmn x) := by
  apply (adicQuotientRing f I J hf hopen hcomap m).injective
  rw [RingEquiv.apply_symm_apply]
  rw [← adic_quotient_transition]
  rw [RingEquiv.apply_symm_apply]

private noncomputable def adicRingHom :
    AdicCompletion I A →+* AdicCompletion J B where
  toFun x := ⟨fun n =>
      adicQuotientRing f I J hf hopen hcomap n (x.val n),
    fun hmn => by
      rw [adic_quotient_transition, x.property hmn]⟩
  map_zero' := by
    apply AdicCompletion.ext
    intro n
    exact map_zero (adicQuotientRing f I J hf hopen hcomap n)
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    exact map_add (adicQuotientRing f I J hf hopen hcomap n)
      (x.val n) (y.val n)
  map_one' := by
    apply AdicCompletion.ext
    intro n
    exact map_one (adicQuotientRing f I J hf hopen hcomap n)
  map_mul' x y := by
    apply AdicCompletion.ext
    intro n
    exact map_mul (adicQuotientRing f I J hf hopen hcomap n)
      (x.val n) (y.val n)

private noncomputable def adicDenseInv
    (x : AdicCompletion J B) : AdicCompletion I A :=
  ⟨fun n => (adicQuotientRing f I J hf hopen hcomap n).symm (x.val n),
    fun hmn => by
      rw [adic_ring_transition, x.property hmn]⟩

/-- A dense ring map which identifies all powers of the source ideal with
the contractions of open powers of the target ideal induces an equivalence
of adic completions. -/
noncomputable def adicDenseRing :
    AdicCompletion I A ≃+* AdicCompletion J B where
  __ := adicRingHom f I J hf hopen hcomap
  invFun := adicDenseInv f I J hf hopen hcomap
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (adicQuotientRing f I J hf hopen hcomap n).symm_apply_apply
      (x.val n)
  right_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (adicQuotientRing f I J hf hopen hcomap n).apply_symm_apply
      (x.val n)

@[simp]
theorem adic_dense_ring (a : A) :
    adicDenseRing f I J hf hopen hcomap
        (AdicCompletion.of I A a) =
      AdicCompletion.of J B (f a) := by
  apply AdicCompletion.ext
  intro n
  rfl

end

end Submission.NumberTheory.Milne
