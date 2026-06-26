import Submission.NumberTheory.Dedekind.DVRQuotientAnnihilator
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Card

/-!
# Class Field Theory, Chapter I, Lemma 3.3

The exact kernel tower, cardinality argument, compatible cyclic generators,
and quotient classification used in Milne's Lemma 3.3.
-/

namespace Submission.CField.LTate

noncomputable section

variable {A M : Type*} [CommRing A]
  [AddCommGroup M] [Module A M]

/-- Elements of an `A`-module killed by `pi ^ n`. -/
def torsionKernel (pi : A) (n : ℕ) : Submodule A M :=
  LinearMap.ker (LinearMap.lsmul A M (pi ^ n))

@[simp]
theorem mem_torsionKernel {pi : A} {n : ℕ} {x : M} :
    x ∈ torsionKernel (M := M) pi n ↔ pi ^ n • x = 0 := by
  rfl

@[simp]
theorem torsionKernel_zero (pi : A) :
    torsionKernel (M := M) pi 0 = ⊥ := by
  ext x
  simp [torsionKernel]

/-- Multiplication by `pi` maps the `(n+1)`-st kernel to the `n`-th kernel. -/
def torsionKernelTransition (pi : A) (n : ℕ) :
    torsionKernel (M := M) pi (n + 1) →ₗ[A]
      torsionKernel (M := M) pi n :=
  (LinearMap.lsmul A M pi).domRestrict (torsionKernel pi (n + 1)) |>.codRestrict
    (torsionKernel pi n) (by
      rintro ⟨x, hx⟩
      apply mem_torsionKernel.mpr
      change pi ^ n • (pi • x) = 0
      rw [← mul_smul, ← pow_succ]
      exact mem_torsionKernel.mp hx)

@[simp]
theorem torsion_kernel_transition (pi : A) (n : ℕ)
    (x : torsionKernel (M := M) pi (n + 1)) :
    (torsionKernelTransition pi n x : M) = pi • (x : M) := rfl

/-- Surjectivity of multiplication by `pi` descends to every transition in
the torsion-kernel tower. -/
theorem torsion_transition_surjective {pi : A}
    (hpi : Function.Surjective fun x : M ↦ pi • x) (n : ℕ) :
    Function.Surjective (torsionKernelTransition (M := M) pi n) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hpi y
  change pi • x = y at hx
  refine ⟨⟨x, ?_⟩, ?_⟩
  · apply mem_torsionKernel.mpr
    rw [pow_succ, mul_smul, hx]
    exact mem_torsionKernel.mp hy
  · ext
    exact hx

/-- The kernel of `M_{n+1} → M_n` is canonically the first torsion kernel
`M_1`. -/
def torsionTransitionKer (pi : A) (n : ℕ) :
    LinearMap.ker (torsionKernelTransition (M := M) pi n) ≃ₗ[A]
      torsionKernel (M := M) pi 1 where
  toFun x := ⟨x.1.1, by
    apply mem_torsionKernel.mpr
    simp only [pow_one]
    have hx : (torsionKernelTransition pi n x.1 : M) = 0 :=
      congrArg Subtype.val x.2
    rw [torsion_kernel_transition] at hx
    exact hx⟩
  invFun x := ⟨⟨x.1, by
    apply mem_torsionKernel.mpr
    rw [pow_succ, mul_smul]
    have hx : pi • (x.1 : M) = 0 := by
      simpa only [pow_one] using mem_torsionKernel.mp x.2
    rw [hx, smul_zero]⟩, by
      ext
      have hx : pi • (x.1 : M) = 0 := by
        simpa only [pow_one] using mem_torsionKernel.mp x.2
      exact hx⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_add' x y := by ext; rfl
  map_smul' a x := by ext; rfl

/-- Cardinal recurrence from the short exact sequence
`0 → M_1 → M_{n+1} → M_n → 0`. -/
theorem torsion_card_succ {pi : A}
    (hpi : Function.Surjective fun x : M ↦ pi • x) (n : ℕ) :
    Nat.card (torsionKernel (M := M) pi (n + 1)) =
      Nat.card (torsionKernel (M := M) pi n) *
        Nat.card (torsionKernel (M := M) pi 1) := by
  let f := torsionKernelTransition (M := M) pi n
  have hf : Function.Surjective f := torsion_transition_surjective hpi n
  calc
    Nat.card (torsionKernel (M := M) pi (n + 1)) =
        Nat.card ((torsionKernel (M := M) pi (n + 1)) ⧸ LinearMap.ker f) *
          Nat.card (LinearMap.ker f) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (LinearMap.ker f).toAddSubgroup
    _ = Nat.card (torsionKernel (M := M) pi n) *
          Nat.card (torsionKernel (M := M) pi 1) := by
      rw [Nat.card_congr (f.quotKerEquivOfSurjective hf).toEquiv,
        Nat.card_congr (torsionTransitionKer pi n).toEquiv]

/-- Lemma 3.3's cardinality conclusion: if `M_1` has `q` elements and
multiplication by `pi` is surjective, then `M_n` has `q^n` elements. -/
theorem torsionKernel_card {pi : A}
    (hpi : Function.Surjective fun x : M ↦ pi • x)
    (q : ℕ) (hcard : Nat.card (torsionKernel (M := M) pi 1) = q) (n : ℕ) :
    Nat.card (torsionKernel (M := M) pi n) = q ^ n := by
  induction n with
  | zero => simp [torsionKernel_zero]
  | succ n ih =>
      rw [torsion_card_succ hpi n, ih, hcard, pow_succ]

/-- A generator of the first torsion kernel can be lifted compatibly to a
generator of every higher torsion kernel.  This is the cyclicity argument in
Lemma 3.3, separated from the DVR calculation of the annihilator. -/
theorem torsion_generator {pi : A}
    (hpi : Function.Surjective fun x : M ↦ pi • x)
    (x : torsionKernel (M := M) pi 1)
    (hx : A ∙ (x : M) = torsionKernel pi 1) (n : ℕ) :
    ∃ y : torsionKernel (M := M) pi (n + 1),
      pi ^ n • (y : M) = x ∧ A ∙ (y : M) = torsionKernel pi (n + 1) := by
  induction n with
  | zero =>
      refine ⟨x, ?_, hx⟩
      simp
  | succ n ih =>
      obtain ⟨z, hzcompat, hzspan⟩ := ih
      obtain ⟨y, hy⟩ := torsion_transition_surjective hpi (n + 1) z
      have hy' : pi • (y : M) = (z : M) := by
        simpa only [torsion_kernel_transition] using congrArg Subtype.val hy
      have hycompat : pi ^ (n + 1) • (y : M) = (x : M) := by
        calc
          pi ^ (n + 1) • (y : M) = pi ^ n • (pi • (y : M)) := by
            rw [pow_succ, mul_smul]
          _ = pi ^ n • (z : M) := by rw [hy']
          _ = (x : M) := hzcompat
      refine ⟨y, hycompat, ?_⟩
      apply le_antisymm
      · rw [Submodule.span_singleton_le_iff_mem]
        exact y.2
      · intro w hw
        have hpw : pi • w ∈ torsionKernel (M := M) pi (n + 1) := by
          apply mem_torsionKernel.mpr
          simpa only [pow_succ, mul_smul] using mem_torsionKernel.mp hw
        rw [← hzspan, Submodule.mem_span_singleton] at hpw
        obtain ⟨a, ha⟩ := hpw
        have hdiff : w - a • (y : M) ∈ torsionKernel (M := M) pi 1 := by
          apply mem_torsionKernel.mpr
          simp only [pow_one, smul_sub, smul_smul]
          rw [← ha, ← hy']
          simp [smul_smul, mul_comm]
        rw [← hx, Submodule.mem_span_singleton] at hdiff
        obtain ⟨b, hb⟩ := hdiff
        rw [show (w : M) = (a + b * pi ^ (n + 1)) • (y : M) by
          rw [add_smul, mul_smul, hycompat, hb]
          abel]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- A compatible generator of `M_{n+1}` has annihilator `(pi^(n+1))`.
The proof uses the DVR classification of nonzero ideals by powers of an
irreducible element. -/
theorem torsion_kernel_generator
    [IsDomain A] [IsDiscreteValuationRing A]
    {pi : A} (hpi : Irreducible pi)
    (x : torsionKernel (M := M) pi 1) (hx : (x : M) ≠ 0) (n : ℕ)
    (y : torsionKernel (M := M) pi (n + 1))
    (hy : pi ^ n • (y : M) = x) :
    Ideal.torsionOf A M (y : M) = Ideal.span {pi ^ (n + 1)} := by
  have hpow_mem : pi ^ (n + 1) ∈ Ideal.torsionOf A M (y : M) := by
    rw [Ideal.mem_torsionOf_iff]
    exact mem_torsionKernel.mp y.2
  have htors_ne : Ideal.torsionOf A M (y : M) ≠ ⊥ := by
    intro htors
    rw [htors, Ideal.mem_bot] at hpow_mem
    exact pow_ne_zero (n + 1) hpi.ne_zero hpow_mem
  obtain ⟨k, hk⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible htors_ne hpi
  have hspan_le : Ideal.span {pi ^ (n + 1)} ≤ Ideal.torsionOf A M (y : M) := by
    rw [Ideal.span_le]
    exact Set.singleton_subset_iff.mpr hpow_mem
  have hk_le : k ≤ n + 1 := by
    have hmem : pi ^ (n + 1) ∈ Ideal.span {pi ^ k} := by
      rw [← hk]
      exact hspan_le (Ideal.mem_span_singleton_self _)
    exact (pow_dvd_pow_iff hpi.ne_zero hpi.not_isUnit).mp
      (Ideal.mem_span_singleton.mp hmem)
  have hn_lt : n < k := by
    by_contra hnk
    have hk_n : k ≤ n := Nat.le_of_not_gt hnk
    have hkill : pi ^ k • (y : M) = 0 := by
      rw [← Ideal.mem_torsionOf_iff, hk]
      exact Ideal.mem_span_singleton_self _
    apply hx
    calc
      (x : M) = pi ^ n • (y : M) := hy.symm
      _ = pi ^ (n - k) • (pi ^ k • (y : M)) := by
        rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hk_n]
      _ = 0 := by rw [hkill, smul_zero]
  have : k = n + 1 := by omega
  rw [hk, this]

/-- If the annihilator of `y` is a specified ideal `I`, the usual cyclic
module equivalence identifies `A / I` with the span of `y`. -/
noncomputable def spanSingletonTorsion
    {I : Ideal A} (y : M) (hy : Ideal.torsionOf A M y = I) :
    (A ⧸ I) ≃ₗ[A] A ∙ y := by
  subst I
  exact Ideal.quotTorsionOfEquivSpanSingleton A M y

@[simp]
theorem singleton_torsion_mk
    {I : Ideal A} (y : M) (hy : Ideal.torsionOf A M y = I) (a : A) :
    spanSingletonTorsion y hy
        (Ideal.Quotient.mk I a) =
      a • ⟨y, Submodule.mem_span_singleton_self y⟩ := by
  subst I
  rfl

/-- Units of `A / I` act faithfully on a point whose annihilator is exactly
`I`.  The image is the unit orbit of the cyclic generator `y`. -/
noncomputable def orbitEmbeddingTorsion
    {I : Ideal A} (y : M) (hy : Ideal.torsionOf A M y = I) :
    (A ⧸ I)ˣ ↪ M where
  toFun u :=
    (spanSingletonTorsion y hy (u : A ⧸ I) : M)
  inj' u v huv := by
    apply Units.ext
    apply (spanSingletonTorsion y hy).injective
    apply Subtype.ext
    exact huv

@[simp]
theorem orbit_embedding_torsion
    {I : Ideal A} (y : M) (hy : Ideal.torsionOf A M y = I)
    (u : (A ⧸ I)ˣ) :
    orbitEmbeddingTorsion y hy u =
      (spanSingletonTorsion y hy (u : A ⧸ I) : M) :=
  rfl

@[simp]
theorem embedding_torsion_one
    {I : Ideal A} (y : M) (hy : Ideal.torsionOf A M y = I) :
    orbitEmbeddingTorsion y hy 1 = y := by
  change (spanSingletonTorsion y hy
    (1 : A ⧸ I) : M) = y
  rw [← map_one (Ideal.Quotient.mk I),
    singleton_torsion_mk, one_smul]

/-- Multiplication in the quotient-unit orbit is computed by any lift to the
coefficient ring.  If `a` represents `v`, then scalar multiplication by `a`
sends the orbit point indexed by `u` to the point indexed by `v * u`. -/
theorem smul_embedding_torsion
    {I : Ideal A} (y : M) (hy : Ideal.torsionOf A M y = I)
    (a : A) (u v : (A ⧸ I)ˣ)
    (ha : Ideal.Quotient.mk I a = (v : A ⧸ I)) :
    a • orbitEmbeddingTorsion y hy u =
      orbitEmbeddingTorsion y hy (v * u) := by
  let e := spanSingletonTorsion y hy
  have hquot : a • (u : A ⧸ I) = ((v * u : (A ⧸ I)ˣ) : A ⧸ I) := by
    rw [Algebra.smul_def]
    change Ideal.Quotient.mk I a * (u : A ⧸ I) = _
    rw [ha]
    rfl
  change a • (e (u : A ⧸ I) : M) =
    (e ((v * u : (A ⧸ I)ˣ) : A ⧸ I) : M)
  calc
    a • (e (u : A ⧸ I) : M) = (e (a • (u : A ⧸ I)) : M) := by
      exact congrArg Subtype.val (e.map_smul a (u : A ⧸ I)).symm
    _ = (e ((v * u : (A ⧸ I)ˣ) : A ⧸ I) : M) := by rw [hquot]

/-- Every point in the quotient-unit orbit has the same exact annihilator as
the cyclic generator. -/
theorem torsion_orbit_embedding
    {I : Ideal A} (y : M) (hy : Ideal.torsionOf A M y = I)
    (u : (A ⧸ I)ˣ) :
    Ideal.torsionOf A M
        (orbitEmbeddingTorsion y hy u) = I := by
  ext a
  rw [Ideal.mem_torsionOf_iff]
  let e := spanSingletonTorsion y hy
  change a • (e (u : A ⧸ I) : M) = 0 ↔ a ∈ I
  constructor
  · intro ha
    have hsmul : e (a • (u : A ⧸ I)) = 0 := by
      rw [e.map_smul]
      apply Subtype.ext
      exact ha
    have hquot : a • (u : A ⧸ I) = 0 := by
      apply e.injective
      exact hsmul.trans e.map_zero.symm
    have hmul : (Ideal.Quotient.mk I a) * (u : A ⧸ I) = 0 := by
      simpa [Algebra.smul_def] using hquot
    have hmk : Ideal.Quotient.mk I a = 0 := by
      apply IsUnit.mul_right_cancel u.isUnit
      simpa using hmul
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
  · intro ha
    have hmk : Ideal.Quotient.mk I a = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    have hsmul : a • (u : A ⧸ I) = 0 := by
      change (Ideal.Quotient.mk I a) * (u : A ⧸ I) = 0
      rw [hmk, zero_mul]
    calc
      a • (e (u : A ⧸ I) : M) = (e (a • (u : A ⧸ I)) : M) :=
        congrArg Subtype.val (e.map_smul a _).symm
      _ = 0 := by rw [hsmul, map_zero]; rfl

/-- The cyclic generator identifies the higher torsion kernel with the
expected quotient by `pi^(n+1)`. -/
def torsionKernelGenerator
    [IsDomain A] [IsDiscreteValuationRing A]
    {pi : A} (hpi : Irreducible pi)
    (x : torsionKernel (M := M) pi 1) (hx : (x : M) ≠ 0) (n : ℕ)
    (y : torsionKernel (M := M) pi (n + 1))
    (hycompat : pi ^ n • (y : M) = x)
    (hyspan : A ∙ (y : M) = torsionKernel pi (n + 1)) :
    torsionKernel (M := M) pi (n + 1) ≃ₗ[A]
      A ⧸ Ideal.span {pi ^ (n + 1)} :=
  ((Submodule.quotEquivOfEq _ _
      (torsion_kernel_generator hpi x hx n y hycompat).symm).trans
    ((Ideal.quotTorsionOfEquivSpanSingleton A M (y : M)).trans
      (LinearEquiv.ofEq _ _ hyspan))).symm

/-- If the first torsion kernel and the residue quotient have the same finite
cardinality, every nonzero element of the first kernel is a generator. -/
theorem torsion_one_generator
    [IsDomain A] [IsDiscreteValuationRing A]
    {pi : A} (hpi : Irreducible pi) [Finite (A ⧸ Ideal.span {pi})]
    (hcard : Nat.card (torsionKernel (M := M) pi 1) =
      Nat.card (A ⧸ Ideal.span {pi})) :
    ∃ x : torsionKernel (M := M) pi 1,
      (x : M) ≠ 0 ∧ A ∙ (x : M) = torsionKernel pi 1 := by
  classical
  have hproper : Ideal.span {pi} ≠ (⊤ : Ideal A) :=
    mt Ideal.span_singleton_eq_top.mp hpi.not_isUnit
  letI : Nontrivial (A ⧸ Ideal.span {pi}) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  have hquot_card : 1 < Nat.card (A ⧸ Ideal.span {pi}) :=
    Finite.one_lt_card
  letI : Finite (torsionKernel (M := M) pi 1) :=
    Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial (torsionKernel (M := M) pi 1) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx0⟩ := exists_ne (0 : torsionKernel (M := M) pi 1)
  have hx0' : (x : M) ≠ 0 := by
    simpa only [Ne, Subtype.ext_iff, ZeroMemClass.coe_zero] using hx0
  have hspan_le : A ∙ (x : M) ≤ torsionKernel pi 1 := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact x.2
  have htors_le : Ideal.span {pi} ≤ Ideal.torsionOf A M (x : M) := by
    rw [Ideal.span_le]
    refine Set.singleton_subset_iff.mpr ?_
    change pi • (x : M) = 0
    simpa only [pow_one] using mem_torsionKernel.mp x.2
  have htors_ne_top : Ideal.torsionOf A M (x : M) ≠ ⊤ := by
    intro htop
    exact hx0' ((Ideal.torsionOf_eq_top_iff A (x : M)).mp htop)
  have htors : Ideal.torsionOf A M (x : M) = Ideal.span {pi} :=
    (PrincipalIdealRing.isMaximal_of_irreducible hpi).eq_of_le
      htors_ne_top htors_le |>.symm
  have hspan_card : Nat.card (A ∙ (x : M)) =
      Nat.card (A ⧸ Ideal.span {pi}) := by
    rw [← htors]
    exact (Nat.card_congr
      (Ideal.quotTorsionOfEquivSpanSingleton A M (x : M)).toEquiv).symm
  have hspan : A ∙ (x : M) = torsionKernel pi 1 := by
    apply SetLike.coe_injective
    apply Set.Finite.eq_of_subset_of_card_le (Set.toFinite _)
    · exact hspan_le
    · simpa only [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] using
        (hcard.trans hspan_card.symm).le
  exact ⟨x, hx0', hspan⟩

/-- Lemma 3.3: under its finiteness and surjectivity hypotheses, the `n`-th
torsion kernel is the cyclic quotient `A/(pi^n)`. -/
theorem torsion_nonempty_quotient
    [IsDomain A] [IsDiscreteValuationRing A]
    {pi : A} (hpi : Irreducible pi) [Finite (A ⧸ Ideal.span {pi})]
    (hsurj : Function.Surjective fun x : M ↦ pi • x)
    (hcard : Nat.card (torsionKernel (M := M) pi 1) =
      Nat.card (A ⧸ Ideal.span {pi})) (n : ℕ) :
    Nonempty (torsionKernel (M := M) pi n ≃ₗ[A]
      A ⧸ Ideal.span {pi ^ n}) := by
  cases n with
  | zero =>
      rw [torsionKernel_zero, pow_zero, Ideal.span_singleton_one]
      exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  | succ n =>
      obtain ⟨x, hx0, hxspan⟩ :=
        torsion_one_generator hpi hcard
      obtain ⟨y, hycompat, hyspan⟩ :=
        torsion_generator hsurj x hxspan n
      exact ⟨torsionKernelGenerator
        hpi x hx0 n y hycompat hyspan⟩

end

end Submission.CField.LTate
