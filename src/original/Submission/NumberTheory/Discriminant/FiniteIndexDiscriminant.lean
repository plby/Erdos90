import Submission.NumberTheory.Discriminant.DiscriminantBasisCriterion

/-!
# Milne, Algebraic Number Theory, Remark 2.25

For a full-rank sublattice of a finite free `ℤ`-algebra, the discriminant is the square of
the additive index times the discriminant of the ambient algebra.
-/

namespace Submission.NumberTheory.Milne

open scoped Matrix
open Module NumberField

/-- Let `b` be an integral basis of `B`, and let `bN` be a basis of a full-rank
`ℤ`-submodule `N`. The discriminant of `bN`, viewed as a family in `B`, is the square of
the additive index of `N` times the discriminant of `b`. -/
theorem discr_submodule_sq
    {B ι : Type*} [CommRing B]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ B) (N : Submodule ℤ B) (bN : Module.Basis ι ℤ N) :
    Algebra.discr ℤ (fun i ↦ (bN i : B)) =
      (N.toAddSubgroup.index : ℤ) ^ 2 * Algebra.discr ℤ b := by
  let P : Matrix ι ι ℤ := b.toMatrix fun i ↦ (bN i : B)
  have hfamily :
      b ᵥ* P.map (algebraMap ℤ B) = fun i ↦ (bN i : B) := by
    exact b.toMatrix_map_vecMul fun i ↦ (bN i : B)
  have hindex : N.toAddSubgroup.index = P.det.natAbs := by
    rw [AddSubgroup.index_eq_natAbs_det b N.toAddSubgroup bN]
    rfl
  rw [← hfamily, Algebra.discr_of_matrix_vecMul, hindex]
  norm_num [Int.natCast_natAbs]

/-- A full-rank submodule whose basis has squarefree discriminant is the whole module.
This is the squarefree-discriminant criterion used in Examples 2.36 and 2.37. -/
theorem submodule_squarefree_discr
    {B ι : Type*} [CommRing B]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ B) (N : Submodule ℤ B) (bN : Module.Basis ι ℤ N)
    (hsq : Squarefree (Algebra.discr ℤ (fun i ↦ (bN i : B)))) :
    N = ⊤ := by
  have hdiscr := discr_submodule_sq b N bN
  have hdiv :
      ((N.toAddSubgroup.index : ℤ) * (N.toAddSubgroup.index : ℤ)) ∣
        Algebra.discr ℤ (fun i ↦ (bN i : B)) := by
    refine ⟨Algebra.discr ℤ b, ?_⟩
    simpa [pow_two] using hdiscr
  have hunit : IsUnit (N.toAddSubgroup.index : ℤ) :=
    hsq _ hdiv
  have hindex : N.toAddSubgroup.index = 1 := by
    rw [Int.isUnit_iff] at hunit
    rcases hunit with hunit | hunit <;> omega
  apply Submodule.toAddSubgroup_eq_top.mp
  exact AddSubgroup.index_eq_one.mp hindex

/-- The discriminant of a basis of integral elements is an integer square
times the number-field discriminant.  This is formula (8) in Remark 2.25. -/
theorem sq_discr_basis
    (K : Type*) [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i)) :
    ∃ d : ℤ,
      Algebra.discr ℚ b = (d : ℚ) ^ 2 * (NumberField.discr K : ℚ) := by
  classical
  let bInt := NumberField.integralBasis K
  let e := bInt.indexEquiv b
  let bInt' := bInt.reindex e
  have hcoeff : ∀ i j, IsIntegral ℤ (bInt'.toMatrix b i j) := by
    intro i j
    obtain ⟨x, hx⟩ :=
      (IsIntegralClosure.isIntegral_iff (A := NumberField.RingOfIntegers K)).mp
        (hb j)
    change IsIntegral ℤ (bInt'.repr (b j) i)
    rw [← hx]
    simpa [bInt', bInt] using
      (isIntegral_algebraMap : IsIntegral ℤ
        (algebraMap ℤ ℚ
          ((NumberField.RingOfIntegers.basis K).repr x (e.symm i))))
  have hdet : IsIntegral ℤ (bInt'.toMatrix b).det :=
    IsIntegral.det hcoeff
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdet
  refine ⟨d, ?_⟩
  rw [← bInt'.toMatrix_map_vecMul b, Algebra.discr_of_matrix_vecMul, ← hd]
  simp [bInt', bInt, NumberField.coe_discr]

/-- Discriminants of integer-ring families commute with passage from `ℤ` to
`ℚ`. -/
theorem discr_coe_integers
    {K ι : Type*} [Field K] [NumberField K]
    [Fintype ι] [DecidableEq ι]
    (v : ι → NumberField.RingOfIntegers K) :
    ((Algebra.discr ℤ v : ℤ) : ℚ) =
      Algebra.discr ℚ
        (fun i => ((v i : NumberField.RingOfIntegers K) : K)) := by
  change algebraMap ℤ ℚ (Algebra.discr ℤ v) = _
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  simpa only [map_mul] using Algebra.coe_trace_int (v i * v j)

/-- If an integral generator gives a rational power basis with squarefree
integral discriminant, its powers already form an integral basis of the full
ring of integers.  This is the index-one step used in Examples 2.36 and 2.37. -/
theorem integers_discr_squarefree
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (d : ℤ)
    (hdiscr : Algebra.discr ℚ B.basis = (d : ℚ))
    (hsquarefree : Squarefree d) :
    ∃ PB : PowerBasis ℤ (NumberField.RingOfIntegers K),
      PB.gen = alpha ∧ PB.dim = B.dim := by
  classical
  have hIntegral : ∀ i, IsIntegral ℤ (B.basis i) := by
    intro i
    rw [PowerBasis.coe_basis, hgen]
    exact alpha.isIntegral_coe.pow i
  obtain ⟨m, hm⟩ :=
    sq_discr_basis
      K B.basis hIntegral
  have hmZ : d = m ^ 2 * NumberField.discr K := by
    have hm' := hm
    rw [hdiscr] at hm'
    exact_mod_cast hm'
  have hmunit : IsUnit m := by
    apply hsquarefree m
    refine ⟨NumberField.discr K, ?_⟩
    simpa [pow_two] using hmZ
  have hfieldDiscr : NumberField.discr K = d := by
    rcases Int.isUnit_eq_one_or hmunit with hm1 | hm1
    · rw [hm1] at hmZ
      norm_num at hmZ
      exact hmZ.symm
    · rw [hm1] at hmZ
      norm_num at hmZ
      exact hmZ.symm
  let v : Fin B.dim → NumberField.RingOfIntegers K :=
    fun i => alpha ^ (i : ℕ)
  have hvQ :
      (fun i => ((v i : NumberField.RingOfIntegers K) : K)) = B.basis := by
    funext i
    rw [PowerBasis.basis_eq_pow]
    simp only [v, map_pow]
    rw [hgen]
  have hvZdiscr : Algebra.discr ℤ v = d := by
    apply Rat.intCast_injective
    rw [discr_coe_integers, hvQ, hdiscr]
  let eInt : Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃
      Fin B.dim :=
    Fintype.equivOfCardEq (by
      rw [← finrank_eq_card_chooseBasisIndex,
        NumberField.RingOfIntegers.rank]
      simpa using B.finrank)
  let bInt : Basis (Fin B.dim) ℤ (NumberField.RingOfIntegers K) :=
    (NumberField.RingOfIntegers.basis K).reindex eInt
  have hbIntDiscr : Algebra.discr ℤ bInt = d := by
    rw [NumberField.discr_eq_discr K bInt]
    exact hfieldDiscr
  have hbIntDiscr_ne : Algebra.discr ℤ bInt ≠ 0 := by
    rw [hbIntDiscr, ← hfieldDiscr]
    exact NumberField.discr_ne_zero K
  have hspan : Ideal.span ({Algebra.discr ℤ v} : Set ℤ) =
      Ideal.span ({Algebra.discr ℤ bInt} : Set ℤ) := by
    rw [hvZdiscr, hbIntDiscr]
  obtain ⟨bZ, hbZ⟩ :=
    (basis_span_discr bInt v hbIntDiscr_ne).mpr hspan
  let PB : PowerBasis ℤ (NumberField.RingOfIntegers K) :=
    { gen := alpha
      dim := B.dim
      basis := bZ
      basis_eq_pow := fun i => by rw [congr_fun hbZ i] }
  exact ⟨PB, rfl, rfl⟩

/-- Squarefree power-basis discriminant criterion in the usual order form:
the ring of integers is generated over `ℤ` by `alpha`. -/
theorem adjoin_discr_squarefree
    {K : Type*} [Field K] [NumberField K]
    (alpha : NumberField.RingOfIntegers K)
    (B : PowerBasis ℚ K)
    (hgen : B.gen = (alpha : K))
    (d : ℤ)
    (hdiscr : Algebra.discr ℚ B.basis = (d : ℚ))
    (hsquarefree : Squarefree d) :
    Algebra.adjoin ℤ ({alpha} : Set (NumberField.RingOfIntegers K)) = ⊤ := by
  obtain ⟨PB, hPBgen, _⟩ :=
    integers_discr_squarefree
      alpha B hgen d hdiscr hsquarefree
  simpa [hPBgen] using PB.adjoin_gen_eq_top

end Submission.NumberTheory.Milne
