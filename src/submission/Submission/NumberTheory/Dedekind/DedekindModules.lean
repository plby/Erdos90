import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Module.DedekindDomain
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.RingTheory.PicardGroup

/-!
# Milne, Algebraic Number Theory, modules over Dedekind domains

We formalize the projectivity claims used in Milne's proof sketch for Theorem 3.31.
-/

namespace Submission.NumberTheory.Milne

open scoped DirectSum nonZeroDivisors
open CommRing

/-- A central claim in the proof sketch following Theorem 3.32: every finitely generated
torsion-free module over a Dedekind domain is projective. -/
theorem torsion_module_projective
    (A M : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M] :
    Module.Projective A M := by
  letI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  exact Module.Flat.projective_of_finitePresentation

/-- The finite form of the direct-summand characterization used in the proof of Theorem 3.31:
a finitely generated projective module is a direct summand of a finite free module. -/
theorem projective_split_fin
    (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] :
    ∃ (n : ℕ) (i : M →ₗ[A] Fin n → A) (s : (Fin n → A) →ₗ[A] M),
      s.comp i = LinearMap.id := by
  obtain ⟨n, generators, hgenerators⟩ :=
    @Module.Finite.exists_fin A M _ _ _ _
  let s : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A generators
  have hs : LinearMap.range s = ⊤ := by
    simpa [s, Fintype.range_linearCombination] using hgenerators
  obtain ⟨i, hi⟩ := s.exists_rightInverse_of_surjective hs
  exact ⟨n, i, s, hi⟩

/-- The ideal-summand step in Milne's proof of Theorem 3.31(a): a nonzero finite projective
module admits a nonzero map to the base ring whose ideal-valued range is a split quotient. -/
theorem projective_split_range
    (A M : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] [Nontrivial M] :
    ∃ (f : M →ₗ[A] A), f ≠ 0 ∧
      ∃ r : LinearMap.range f →ₗ[A] M,
        f.rangeRestrict.comp r = LinearMap.id := by
  obtain ⟨n, i, s, hi⟩ := projective_split_fin A M
  have hi_injective : Function.Injective i := by
    intro x y hxy
    have h := congrArg s hxy
    simpa only [← LinearMap.comp_apply, hi, LinearMap.id_apply] using h
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have hix : i x ≠ 0 := by
    intro h
    apply hx
    apply hi_injective
    simpa using h
  obtain ⟨j, hj⟩ : ∃ j : Fin n, i x j ≠ 0 := by
    by_contra h
    push Not at h
    apply hix
    ext j
    exact h j
  let f : M →ₗ[A] A := (LinearMap.proj j).comp i
  have hf : f ≠ 0 := by
    intro h
    apply hj
    have hfx : f x = 0 := by rw [h]; rfl
    simpa [f] using hfx
  letI : Module.Finite A (LinearMap.range f) :=
    Module.Finite.of_fg (IsNoetherian.noetherian _)
  letI : Module.Projective A (LinearMap.range f) :=
    torsion_module_projective A (LinearMap.range f)
  obtain ⟨r, hr⟩ := Module.projective_lifting_property
    f.rangeRestrict LinearMap.id f.surjective_rangeRestrict
  exact ⟨f, hf, r, hr⟩

/-- The corresponding one-step decomposition from the proof of Theorem 3.31(a).  The second
factor is an ideal of `A`, since ideals are implemented as submodules of the regular module. -/
theorem projective_ker_range
    (A M : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] [Nontrivial M] :
    ∃ (f : M →ₗ[A] A), f ≠ 0 ∧
      Nonempty (M ≃ₗ[A] LinearMap.ker f × LinearMap.range f) := by
  obtain ⟨f, hf, r, hr⟩ := projective_split_range A M
  refine ⟨f, hf, ⟨?_⟩⟩
  exact (lequivProdOfRightSplitExact
    (j := (LinearMap.ker f).subtype) (g := f.rangeRestrict) (f := r)
    (LinearMap.ker f).injective_subtype (by
      rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict]) hr).symm

/-- The induction step for Theorem 3.31(a), under Milne's original hypotheses: a nonzero
finitely generated torsion-free module splits as a module times a nonzero integral ideal. -/
theorem torsion_split_nonzero
    (A M : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M] [Nontrivial M] :
    ∃ (I : Ideal A) (_ : I ≠ ⊥) (N : Submodule A M),
      Nonempty (M ≃ₗ[A] N × I) := by
  letI : Module.Projective A M := torsion_module_projective A M
  obtain ⟨f, hf, he⟩ := projective_ker_range A M
  have hrange : LinearMap.range f ≠ ⊥ := by
    intro h
    exact hf (LinearMap.range_eq_bot.mp h)
  exact ⟨LinearMap.range f, hrange, LinearMap.ker f, he⟩

private theorem ideal_finrank_one
    (A : Type*) [CommRing A] [IsDomain A]
    (I : Ideal A) [Module.Finite A I] (hI : I ≠ ⊥) :
    Module.finrank A I = 1 := by
  apply Nat.le_antisymm
  · simpa using LinearMap.finrank_le_finrank_of_injective I.injective_subtype
  · exact (Submodule.one_le_finrank_iff).2 hI

/-- Theorem 3.31(a): every finitely generated torsion-free module over a Dedekind domain is
isomorphic to a finite direct sum of ideals, and therefore to a direct sum of fractional ideals. -/
theorem torsion_direct_ideals
    (A M : Type u) [CommRing A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M] :
    ∃ (n : ℕ) (I : Fin n → Ideal A), Nonempty (M ≃ₗ[A] ⨁ i, I i) := by
  classical
  induction h : Module.finrank A M using Nat.strong_induction_on generalizing M with
  | h n ih =>
      cases subsingleton_or_nontrivial M with
      | inl hM =>
          letI : Subsingleton M := hM
          refine ⟨0, Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
      | inr hM =>
          letI : Nontrivial M := hM
          letI : Module.Projective A M := torsion_module_projective A M
          obtain ⟨f, hf, ⟨e⟩⟩ := projective_ker_range A M
          let I : Ideal A := LinearMap.range f
          let N : Submodule A M := LinearMap.ker f
          have hI : I ≠ ⊥ := by
            intro hI
            exact hf (LinearMap.range_eq_bot.mp hI)
          letI : Module.Finite A N :=
            Module.Finite.of_fg (IsNoetherian.noetherian N)
          have hfinI : Module.finrank A I = 1 := ideal_finrank_one A I hI
          have hfinQuotient : Module.finrank A (M ⧸ N) = 1 := by
            calc
              Module.finrank A (M ⧸ N) = Module.finrank A I :=
                f.quotKerEquivRange.finrank_eq
              _ = 1 := hfinI
          have hfin : Module.finrank A N + 1 = n := by
            have hsum := N.finrank_quotient_add_finrank
            omega
          have hlt : Module.finrank A N < n := by omega
          obtain ⟨d, J, ⟨eN⟩⟩ := ih (Module.finrank A N) hlt N rfl
          let K : Option (Fin d) → Ideal A := fun
            | none => I
            | some i => J i
          refine ⟨d + 1, fun i => K (finSuccEquiv d i), ⟨?_⟩⟩
          exact e ≪≫ₗ (eN.prodCongr (LinearEquiv.refl A I)) ≪≫ₗ
            LinearEquiv.prodComm A _ _ ≪≫ₗ
            (DirectSum.lequivProdDirectSum
              (R := A) (ι := Fin d) (α := fun o => ↑(K o))).symm ≪≫ₗ
            DirectSum.lequivCongrLeft
              (M := fun o => ↑(K o)) A (finSuccEquiv d).symm

/-- The fractional-ideal case used in the proof sketch for Theorem 3.31: every fractional
ideal of a Dedekind domain is projective as a module over the domain. -/
theorem fractionalIdeal_projective
    (A K : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (I : FractionalIdeal (nonZeroDivisors A) K) :
    Module.Projective A I := by
  letI : Module.Finite A I :=
    Module.Finite.of_fg (FractionalIdeal.fg_of_isNoetherianRing le_rfl I)
  exact torsion_module_projective A I

/-- A fractional ideal over a Dedekind domain is finitely generated as a module. -/
theorem fractionalIdeal_fg
    (A K : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (I : FractionalIdeal (nonZeroDivisors A) K) :
    I.coeToSubmodule.FG := by
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl I

/-- The forward implication in the last assertion of Theorem 3.31: fractional ideals
representing the same class are isomorphic as modules. The equivalence is multiplication by
the nonzero fraction relating their representatives. -/
noncomputable def fractional_linear_group
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {I J : (FractionalIdeal (nonZeroDivisors A) (FractionRing A))ˣ}
    (h : ClassGroup.mk (FractionRing A) I = ClassGroup.mk (FractionRing A) J) :
    (I : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) ≃ₗ[A]
      (J : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) := by
  let x := Classical.choose (ClassGroup.mk_eq_mk.mp h)
  have hx := Classical.choose_spec (ClassGroup.mk_eq_mk.mp h)
  have hIJ :
      (J : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) =
        FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : FractionRing A) *
          (I : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) := by
    simpa [mul_comm] using congrArg Units.val hx.symm
  let f :
      (I : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) →ₗ[A]
        (J : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) :=
    { toFun := fun y ↦
        ⟨(x : FractionRing A) * y, by
          rw [hIJ]
          exact FractionalIdeal.mul_mem_mul
            (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors A) (x : FractionRing A))
            y.property⟩
      map_add' := fun y z ↦ by
        apply Subtype.ext
        exact mul_add _ _ _
      map_smul' := fun a y ↦ by
        apply Subtype.ext
        simp only [SetLike.val_smul, RingHom.id_apply]
        rw [Algebra.smul_def, Algebra.smul_def]
        exact mul_left_comm _ _ _ }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro y z hyz
    apply Subtype.ext
    apply mul_left_cancel₀ x.ne_zero
    exact congrArg Subtype.val hyz
  · intro z
    have hz :
        (z : FractionRing A) ∈
          FractionalIdeal.spanSingleton (nonZeroDivisors A) (x : FractionRing A) *
            (I : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) := by
      rw [← hIJ]
      exact z.property
    rcases FractionalIdeal.mem_singleton_mul.mp hz with ⟨y, hy, hyz⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact hyz.symm

/-- The class-group/Picard-group comparison sends a fractional ideal class to the Picard
class of its underlying invertible submodule. -/
theorem class_pic_mk
    (A : Type*) [CommRing A] [IsDomain A]
    (I : (FractionalIdeal (nonZeroDivisors A) (FractionRing A))ˣ) :
    (ClassGroup.equivPic A) (ClassGroup.mk (FractionRing A) I) =
      CommRing.Pic.mk A (FractionalIdeal.unitsMulEquivSubmodule I) := by
  rw [ClassGroup.mk_def]
  have hcanon :
      Units.map (FractionalIdeal.canonicalEquiv
        (nonZeroDivisors A) (FractionRing A) (FractionRing A)) I = I := by
    ext
    simp
  let I' : (Submodule A (FractionRing A))ˣ :=
    FractionalIdeal.unitsMulEquivSubmodule I
  have h1 :
      (ClassGroup.mulEquivUnitsSubmoduleQuotRange A)
          ((QuotientGroup.mk' (toPrincipalIdeal A (FractionRing A)).range) I) =
        (QuotientGroup.mk' (Units.map (Submodule.spanSingleton A).toMonoidHom).range) I' := by
    simpa [ClassGroup.mulEquivUnitsSubmoduleQuotRange, I'] using
      QuotientGroup.congr_mk'
        (toPrincipalIdeal A (FractionRing A)).range
        (Units.map (Submodule.spanSingleton A).toMonoidHom).range
        FractionalIdeal.unitsMulEquivSubmodule
        (by simp_rw [MonoidHom.range_eq_map, Subgroup.map_map]; congr; ext;
            simp [FractionalIdeal.unitsMulEquivSubmodule]) I
  rw [hcanon]
  simp only [ClassGroup.equivPic, MulEquiv.trans_apply]
  rw [h1]
  simp only [Submodule.unitsQuotEquivRelPic, MulEquiv.trans_apply]
  rw [QuotientGroup.congr_mk']
  rfl

/-- The tensor-product remark following Theorem 3.31: under the class-group/Picard-group
identification, multiplication of fractional-ideal classes is tensor product of their
underlying invertible modules. -/
theorem corresponds_tensor_product
    (A : Type*) [CommRing A] [IsDomain A]
    (I J : (FractionalIdeal (nonZeroDivisors A) (FractionRing A))ˣ) :
    (ClassGroup.equivPic A)
        (ClassGroup.mk (FractionRing A) I * ClassGroup.mk (FractionRing A) J) =
      CommRing.Pic.mk A
        (TensorProduct A
          ↥(FractionalIdeal.unitsMulEquivSubmodule I :
            Submodule A (FractionRing A))
          ↥(FractionalIdeal.unitsMulEquivSubmodule J :
            Submodule A (FractionRing A))) := by
  rw [map_mul, class_pic_mk A I, class_pic_mk A J]
  exact CommRing.Pic.mk_tensor.symm

/-- The converse implication in the rank-one assertion of Theorem 3.31(b). -/
theorem class_fractional_linear
    (A : Type*) [CommRing A] [IsDomain A]
    {I J : (FractionalIdeal (nonZeroDivisors A) (FractionRing A))ˣ}
    (e :
      (I : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) ≃ₗ[A]
        (J : FractionalIdeal (nonZeroDivisors A) (FractionRing A))) :
    ClassGroup.mk (FractionRing A) I = ClassGroup.mk (FractionRing A) J := by
  apply (ClassGroup.equivPic A).injective
  rw [class_pic_mk A I, class_pic_mk A J]
  exact CommRing.Pic.mk_eq_mk_iff.mpr ⟨e⟩

/-- The rank-one assertion of Theorem 3.31(b): two nonzero fractional ideals are linearly
equivalent exactly when they determine the same ideal class. -/
theorem fractional_nonempty_linear
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {I J : (FractionalIdeal (nonZeroDivisors A) (FractionRing A))ˣ} :
    Nonempty
        ((I : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) ≃ₗ[A]
          (J : FractionalIdeal (nonZeroDivisors A) (FractionRing A))) ↔
      ClassGroup.mk (FractionRing A) I = ClassGroup.mk (FractionRing A) J := by
  constructor
  · rintro ⟨e⟩
    exact class_fractional_linear A e
  · intro h
    exact ⟨fractional_linear_group A h⟩

/-- For two fractional ideals whose sum is the unit ideal, multiplication realizes their
intersection. -/
theorem fractional_inf_add
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (a b : FractionalIdeal (nonZeroDivisors A) (FractionRing A))
    (h : a + b = 1) : a * b = a ⊓ b := by
  apply le_antisymm
  · apply le_inf
    · calc
        a * b ≤ a * 1 := mul_le_mul_right (le_add_self.trans_eq h) a
        _ = a := mul_one a
    · calc
        a * b ≤ 1 * b := mul_le_mul_left (le_self_add.trans_eq h) b
        _ = b := one_mul b
  · intro z hz
    have hone : (1 : FractionRing A) ∈ a + b := by
      rw [h]
      exact FractionalIdeal.one_mem_one (nonZeroDivisors A)
    rcases (FractionalIdeal.mem_add a b 1).mp hone with ⟨x, hx, y, hy, hxy⟩
    have hzx : z * x ∈ a * b := by
      simpa [mul_comm] using FractionalIdeal.mul_mem_mul hz.2 hx
    have hzy : z * y ∈ a * b :=
      FractionalIdeal.mul_mem_mul hz.1 hy
    convert (a * b).val.add_mem hzx hzy using 1
    rw [← mul_add, hxy, mul_one]

private noncomputable def fractionalIdealSup
    (A : Type*) [CommRing A]
    (a b : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) :
    (↑a × ↑b) →ₗ[A] ↑(a + b) :=
  ((a : Submodule A (FractionRing A)).subtype.coprod
    (b : Submodule A (FractionRing A)).subtype).codRestrict
      (a + b : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) fun z =>
        (FractionalIdeal.mem_add a b _).mpr
          ⟨z.1, z.1.property, z.2, z.2.property, rfl⟩

private theorem fractional_sup_surjective
    (A : Type*) [CommRing A]
    (a b : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) :
    Function.Surjective (fractionalIdealSup A a b) := by
  intro z
  rcases (FractionalIdeal.mem_add a b z).mp z.property with ⟨x, hx, y, hy, hxy⟩
  exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy⟩

private noncomputable def fractionalInfSup
    (A : Type*) [CommRing A]
    (a b : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) :
    ↑(a ⊓ b) ≃ₗ[A] LinearMap.ker (fractionalIdealSup A a b) := by
  let f : ↑(a ⊓ b) →ₗ[A] LinearMap.ker (fractionalIdealSup A a b) :=
    { toFun := fun z => ⟨(⟨z, z.property.1⟩, ⟨-z, b.val.neg_mem z.property.2⟩), by
          apply Subtype.ext
          change (z : FractionRing A) + -z = 0
          simp⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          change -(x + y : FractionRing A) = -x + -y
          ring
      map_smul' := by
        intro r x
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          simp only [Prod.smul_snd, SetLike.val_smul, RingHom.id_apply,
            Algebra.smul_def]
          ring }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z => ((z : LinearMap.ker (fractionalIdealSup A a b)) : ↑a × ↑b).1.1) hxy
  · intro z
    have hzsum : (z.1.1 : FractionRing A) + z.1.2 = 0 := by
      exact congrArg Subtype.val z.property
    have hxb : (z.1.1 : FractionRing A) ∈ b := by
      rw [eq_neg_of_add_eq_zero_left hzsum]
      exact b.val.neg_mem z.1.2.property
    refine ⟨⟨z.1.1, z.1.1.property, hxb⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact (eq_neg_of_add_eq_zero_right hzsum).symm

private noncomputable def fractionalSumInf
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (a b : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) :
    (↑a × ↑b) ≃ₗ[A] (↑(a + b) × ↑(a ⊓ b)) := by
  let g := fractionalIdealSup A a b
  letI : Module.Finite A ↑(a + b) :=
    Module.Finite.of_fg (FractionalIdeal.fg_of_isNoetherianRing le_rfl (a + b))
  letI : Module.Projective A ↑(a + b) :=
    torsion_module_projective A ↑(a + b)
  let hex := g.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (fractional_sup_surjective A a b))
  let s := Classical.choose hex
  have hs := Classical.choose_spec hex
  exact (lequivProdOfRightSplitExact
      (j := (LinearMap.ker g).subtype) (g := g) (f := s)
      (LinearMap.ker g).injective_subtype (Submodule.range_subtype _) hs).symm ≪≫ₗ
    ((fractionalInfSup A a b).symm.prodCongr
      (LinearEquiv.refl A ↑(a + b))) ≪≫ₗ
    LinearEquiv.prodComm A _ _

/-- The split exact-sequence form of the two-ideal Steinitz relation in the coprime case. -/
noncomputable def fractional_prod_add
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (a b : FractionalIdeal (nonZeroDivisors A) (FractionRing A))
    (h : a + b = 1) :
    (↑a × ↑b) ≃ₗ[A]
      (↑(1 : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) × ↑(a * b)) :=
  fractionalSumInf A a b ≪≫ₗ
    ((LinearEquiv.ofEq _ _ (congrArg FractionalIdeal.coeToSubmodule h)).prodCongr
      (LinearEquiv.ofEq _ _ (congrArg FractionalIdeal.coeToSubmodule
        (fractional_inf_add A a b h).symm)))

/-- Principal rescaling reduces the two-ideal Steinitz relation to the coprime case. -/
noncomputable def fractional_prod_mul
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (a b : FractionalIdeal (nonZeroDivisors A) (FractionRing A))
    (ha_le : a ≤ 1) (ha : a ≠ 0) (hb : b ≠ 0) :
    (↑a × ↑b) ≃ₗ[A]
      (↑(1 : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) × ↑(a * b)) := by
  by_cases ha_one : a = 1
  · subst a
    exact (LinearEquiv.refl A
        ↑(1 : FractionalIdeal (nonZeroDivisors A) (FractionRing A))).prodCongr
      (LinearEquiv.ofEq _ _ (congrArg FractionalIdeal.coeToSubmodule
        (one_mul b).symm))
  · let x := Classical.choose
        (IsDedekindDomain.exists_add_spanSingleton_mul_eq ha_le ha hb)
    have hxadd := Classical.choose_spec
      (IsDedekindDomain.exists_add_spanSingleton_mul_eq ha_le ha hb)
    let b' := FractionalIdeal.spanSingleton (nonZeroDivisors A) x * b
    have hb' : b' ≠ 0 := by
      intro hb'zero
      apply ha_one
      change a + b' = 1 at hxadd
      calc
        a = a + b' := by rw [hb'zero, add_zero]
        _ = 1 := hxadd
    have hx : x ≠ 0 := by
      intro hxzero
      apply hb'
      simp [b', hxzero]
    let ub : (FractionalIdeal (nonZeroDivisors A) (FractionRing A))ˣ := Units.mk0 b hb
    let ub' : (FractionalIdeal (nonZeroDivisors A) (FractionRing A))ˣ := Units.mk0 b' hb'
    let ux : (FractionRing A)ˣ := Units.mk0 x hx
    have hbclass :
        ClassGroup.mk (FractionRing A) ub = ClassGroup.mk (FractionRing A) ub' := by
      apply ClassGroup.mk_eq_mk.mpr
      refine ⟨ux, ?_⟩
      apply Units.ext
      simp only [Units.val_mul, coe_toPrincipalIdeal]
      change b * FractionalIdeal.spanSingleton (nonZeroDivisors A) x = b'
      simp only [b']
      rw [mul_comm]
    let uab : (FractionalIdeal (nonZeroDivisors A) (FractionRing A))ˣ :=
      Units.mk0 (a * b) (mul_ne_zero ha hb)
    let uab' : (FractionalIdeal (nonZeroDivisors A) (FractionRing A))ˣ :=
      Units.mk0 (a * b') (mul_ne_zero ha hb')
    have habclass :
        ClassGroup.mk (FractionRing A) uab = ClassGroup.mk (FractionRing A) uab' := by
      apply ClassGroup.mk_eq_mk.mpr
      refine ⟨ux, ?_⟩
      apply Units.ext
      simp only [Units.val_mul, coe_toPrincipalIdeal]
      change (a * b) * FractionalIdeal.spanSingleton (nonZeroDivisors A) x = a * b'
      simp only [b']
      ac_rfl
    exact (LinearEquiv.refl A ↑a).prodCongr
        (fractional_linear_group A hbclass) ≪≫ₗ
      fractional_prod_add A a b' hxadd ≪≫ₗ
      (LinearEquiv.refl A
        ↑(1 : FractionalIdeal (nonZeroDivisors A) (FractionRing A))).prodCongr
        (fractional_linear_group A habclass).symm

/-- An integral ideal and its associated fractional ideal are linearly equivalent. -/
noncomputable def idealCoeFractional
    (A : Type*) [CommRing A] [IsDomain A] (I : Ideal A) :
    ↑I ≃ₗ[A]
      ↑(I : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) := by
  let f : ↑I →ₗ[A]
      ↑(I : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) :=
    { toFun := fun x =>
        ⟨algebraMap A (FractionRing A) x,
          FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors A) x.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add _ _ _
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp only [SetLike.val_smul, RingHom.id_apply, Algebra.smul_def, map_mul,
          Algebra.algebraMap_self_apply] }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply FaithfulSMul.algebraMap_injective A (FractionRing A)
    exact congrArg Subtype.val hxy
  · intro y
    rcases (FractionalIdeal.mem_coeIdeal (nonZeroDivisors A)).mp y.property with
      ⟨x, hx, hxy⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

private noncomputable def fractionalLinearEquiv
    (A : Type*) [CommRing A] [IsDomain A] :
    ↑(1 : FractionalIdeal (nonZeroDivisors A) (FractionRing A)) ≃ₗ[A] A :=
  (LinearEquiv.ofEq _ _ (congrArg FractionalIdeal.coeToSubmodule
      (FractionalIdeal.coeIdeal_top
        (S := nonZeroDivisors A) (P := FractionRing A)).symm) ≪≫ₗ
      (idealCoeFractional A (⊤ : Ideal A)).symm) ≪≫ₗ
    Submodule.topEquiv

/-- The key two-ideal relation in Theorem 3.31(b): `I ⊕ J ≃ A ⊕ IJ`. -/
noncomputable def idealProdMul
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (I J : Ideal A) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    (↑I × ↑J) ≃ₗ[A] (A × ↑(I * J)) :=
  (idealCoeFractional A I).prodCongr
      (idealCoeFractional A J) ≪≫ₗ
    fractional_prod_mul A
      (I : FractionalIdeal (nonZeroDivisors A) (FractionRing A))
      (J : FractionalIdeal (nonZeroDivisors A) (FractionRing A))
      FractionalIdeal.coeIdeal_le_one
      (FractionalIdeal.coeIdeal_ne_zero.mpr hI)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hJ) ≪≫ₗ
    (fractionalLinearEquiv A).prodCongr
      ((LinearEquiv.ofEq _ _ (congrArg FractionalIdeal.coeToSubmodule
        (FractionalIdeal.coeIdeal_mul
          (S := nonZeroDivisors A) (P := FractionRing A) I J))).symm ≪≫ₗ
        (idealCoeFractional A (I * J)).symm)

private noncomputable def freeDirectSucc
    (A : Type*) [CommRing A] (n : ℕ) :
    ((⨁ _ : Fin n, A) × A) ≃ₗ[A] (⨁ _ : Fin (n + 1), A) :=
  LinearEquiv.prodComm A _ _ ≪≫ₗ
    (DirectSum.lequivProdDirectSum
      (R := A) (ι := Fin n) (α := fun _ : Option (Fin n) => A)).symm ≪≫ₗ
    DirectSum.lequivCongrLeft
      (M := fun _ : Option (Fin n) => A) A (finSuccEquiv n).symm

/-- The normal form in Theorem 3.31(b): a direct sum of `n + 1` nonzero ideals is
equivalent to `n` free summands together with the product of all the ideals. -/
theorem ideals_direct_prod
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (n : ℕ) (I : Fin (n + 1) → Ideal A) (hI : ∀ i, I i ≠ ⊥) :
    Nonempty ((⨁ i, I i) ≃ₗ[A]
      ((⨁ _ : Fin n, A) × ↑(∏ i, I i))) := by
  induction n with
  | zero =>
      let K : Option (Fin 0) → Ideal A := fun o => I ((finSuccEquiv 0).symm o)
      let e : (⨁ i, I i) ≃ₗ[A] (K none × (⨁ i : Fin 0, K (some i))) :=
        DirectSum.lequivCongrLeft
            (M := fun i => ↑(I i)) A (finSuccEquiv 0) ≪≫ₗ
          DirectSum.lequivProdDirectSum A
      refine ⟨e ≪≫ₗ LinearEquiv.prodUnique ≪≫ₗ ?_⟩
      exact LinearEquiv.uniqueProd.symm ≪≫ₗ
        (LinearEquiv.refl A (⨁ _ : Fin 0, A)).prodCongr
          (LinearEquiv.ofEq _ _ (by simp [K]))
  | succ n ih =>
      let K : Option (Fin (n + 1)) → Ideal A := fun o =>
        I ((finSuccEquiv (n + 1)).symm o)
      let J : Fin (n + 1) → Ideal A := fun i => K (some i)
      have hK : K none ≠ ⊥ := by simpa [K] using hI 0
      have hJ : ∀ i, J i ≠ ⊥ := by
        intro i
        simpa [J, K] using hI i.succ
      obtain ⟨eJ⟩ := ih J hJ
      have hprodJ : (∏ i, J i) ≠ (⊥ : Ideal A) :=
        Finset.prod_ne_zero_iff.mpr fun i _ => hJ i
      let ePair := idealProdMul A (K none) (∏ i, J i) hK hprodJ
      let eSplit : (⨁ i, I i) ≃ₗ[A] (↑(K none) × (⨁ i, J i)) :=
        DirectSum.lequivCongrLeft
            (M := fun i => ↑(I i)) A (finSuccEquiv (n + 1)) ≪≫ₗ
          DirectSum.lequivProdDirectSum A
      refine ⟨eSplit ≪≫ₗ
        (LinearEquiv.refl A ↑(K none)).prodCongr eJ ≪≫ₗ
        (LinearEquiv.prodAssoc A _ _ _).symm ≪≫ₗ
        ((LinearEquiv.prodComm A ↑(K none) (⨁ _ : Fin n, A)).prodCongr
          (LinearEquiv.refl A ↑(∏ i, J i))) ≪≫ₗ
        LinearEquiv.prodAssoc A _ _ _ ≪≫ₗ
        (LinearEquiv.refl A (⨁ _ : Fin n, A)).prodCongr ePair ≪≫ₗ
        (LinearEquiv.prodAssoc A _ _ _).symm ≪≫ₗ
        (freeDirectSucc A n).prodCongr
          (LinearEquiv.ofEq _ _ (by
            simp [K, J, Fin.prod_univ_succ]))⟩

/-- The sufficient direction of the ideal-class criterion in Theorem 3.31(b): equality of
the product classes gives an equivalence of the two direct sums. -/
theorem ideals_direct_linear
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (n : ℕ) (I J : Fin (n + 1) → Ideal A)
    (hI : ∀ i, I i ≠ ⊥) (hJ : ∀ i, J i ≠ ⊥)
    (hclass :
      ClassGroup.mk0 ⟨∏ i, I i, mem_nonZeroDivisors_iff_ne_zero.mpr
          (Finset.prod_ne_zero_iff.mpr fun i _ => hI i)⟩ =
        ClassGroup.mk0 ⟨∏ i, J i, mem_nonZeroDivisors_iff_ne_zero.mpr
          (Finset.prod_ne_zero_iff.mpr fun i _ => hJ i)⟩) :
    Nonempty ((⨁ i, I i) ≃ₗ[A] (⨁ i, J i)) := by
  obtain ⟨eI⟩ := ideals_direct_prod A n I hI
  obtain ⟨eJ⟩ := ideals_direct_prod A n J hJ
  let pI : (Ideal A)⁰ :=
    ⟨∏ i, I i, mem_nonZeroDivisors_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun i _ => hI i)⟩
  let pJ : (Ideal A)⁰ :=
    ⟨∏ i, J i, mem_nonZeroDivisors_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun i _ => hJ i)⟩
  have hclass' :
      ClassGroup.mk (FractionRing A) (FractionalIdeal.mk0 (FractionRing A) pI) =
        ClassGroup.mk (FractionRing A) (FractionalIdeal.mk0 (FractionRing A) pJ) := by
    simpa [pI, pJ] using hclass
  let eFrac := fractional_linear_group A hclass'
  let eProd : ↑(∏ i, I i) ≃ₗ[A] ↑(∏ i, J i) :=
    idealCoeFractional A (∏ i, I i) ≪≫ₗ
      LinearEquiv.ofEq _ _ (by simp [pI]) ≪≫ₗ
      eFrac ≪≫ₗ
      (LinearEquiv.ofEq _ _ (by simp [pJ])).symm ≪≫ₗ
      (idealCoeFractional A (∏ i, J i)).symm
  exact ⟨eI ≪≫ₗ
    (LinearEquiv.refl A (⨁ _ : Fin n, A)).prodCongr eProd ≪≫ₗ
    eJ.symm⟩

/-- The rank assertion used in Theorem 3.31(b): a direct sum of `n` nonzero ideals has
rank `n`.  The proof embeds it both into and around the free module of rank `n`. -/
theorem ideals_direct_finrank
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (n : ℕ) (I : Fin n → Ideal A) (hI : ∀ i, I i ≠ ⊥) :
    Module.finrank A (⨁ (i : Fin n), I i) = n := by
  classical
  choose y hyI hy using fun i => (I i).ne_bot_iff.mp (hI i)
  let x : ∀ i, I i := fun i => ⟨y i, hyI i⟩
  have hx : ∀ i, x i ≠ 0 := by
    intro i hxi
    apply hy i
    exact congrArg Subtype.val hxi
  let f : ∀ i, A →ₗ[A] I i := fun i =>
    { toFun := fun a => a • x i
      map_add' := fun a b => by simp [add_smul]
      map_smul' := fun a b => by simp [mul_smul] }
  have hf : ∀ i, Function.Injective (f i) := by
    intro i a b hab
    apply mul_right_cancel₀ (show (x i : A) ≠ 0 by
      intro h
      apply hx i
      exact Subtype.ext h)
    simpa [f, Algebra.smul_def] using congrArg Subtype.val hab
  let g : ∀ i, I i →ₗ[A] A := fun i => (I i).subtype
  have hg : ∀ i, Function.Injective (g i) := fun i => (I i).injective_subtype
  have hle : Module.finrank A (⨁ (i : Fin n), A) ≤
      Module.finrank A (⨁ (i : Fin n), I i) :=
    LinearMap.finrank_le_finrank_of_injective
      ((DirectSum.lmap_injective f).mpr hf)
  have hge : Module.finrank A (⨁ (i : Fin n), I i) ≤
      Module.finrank A (⨁ (i : Fin n), A) :=
    LinearMap.finrank_le_finrank_of_injective
      ((DirectSum.lmap_injective g).mpr hg)
  have hfree : Module.finrank A (⨁ (_ : Fin n), A) = n := by simp
  omega

/-- The rank-necessity half of Theorem 3.31(b): equivalent direct sums of nonzero ideals
have the same number of summands. -/
theorem ideals_direct_imp
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (m n : ℕ) (I : Fin m → Ideal A) (J : Fin n → Ideal A)
    (hI : ∀ i, I i ≠ ⊥) (hJ : ∀ j, J j ≠ ⊥)
    (e : (⨁ (i : Fin m), I i) ≃ₗ[A] (⨁ (j : Fin n), J j)) :
    m = n := by
  rw [← ideals_direct_finrank A m I hI,
    ← ideals_direct_finrank A n J hJ]
  exact e.finrank_eq

/-- A same-rank inclusion has torsion quotient, and hence the prime-power primary decomposition
which is the packaged part of the consequence of Theorem 3.32. -/
theorem quotient_decomposition_finrank
    (A M : Type*) [CommRing A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Submodule A M)
    (h : Module.finrank A N = Module.finrank A M) :
    ∃ (P : Finset (Ideal A)) (_ : DecidableEq P)
      (_ : ∀ p ∈ P, Prime p) (e : P → ℕ),
      DirectSum.IsInternal fun p : P ↦
        Submodule.torsionBySet A (M ⧸ N) (p ^ e p : Ideal A) := by
  apply Submodule.exists_isInternal_prime_power_torsion
  rw [← Module.finrank_eq_zero_iff_isTorsion]
  rw [N.finrank_quotient, h, Nat.sub_self]

/-- The consequence of Theorem 3.32 stated by Milne: a finitely generated torsion module
over a Dedekind domain is an internal direct sum of prime-power torsion submodules. -/
theorem torsion_prime_decomposition
    (A M : Type*) [CommRing A] [IsDedekindDomain A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : Module.IsTorsion A M) :
    ∃ (P : Finset (Ideal A)) (_ : DecidableEq P)
      (_ : ∀ p ∈ P, Prime p) (e : P → ℕ),
      DirectSum.IsInternal fun p : P =>
        Submodule.torsionBySet A M (p ^ e p : Ideal A) := by
  exact Submodule.exists_isInternal_prime_power_torsion hM

end Submission.NumberTheory.Milne
