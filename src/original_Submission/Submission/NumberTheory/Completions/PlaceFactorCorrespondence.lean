import Submission.NumberTheory.Locals.CompleteDiscreteExtension
import Submission.NumberTheory.Locals.CompletionUniversal
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.RingTheory.Adjoin.Field
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace


/-!
# Milne, Chapter 8, Proposition 8.1: places and completed factors

Let `L = K[α]`, let `v` be an absolute value on `K`, and factor the minimal
polynomial of `α` over the completion of `K`.  Every monic irreducible factor
defines a finite extension of the completed field.  Sending `α` to the root of
that factor embeds `L` into this extension, whose unique absolute value pulls
back to an absolute value on `L` lying over `v`.

Conversely, an absolute value on `L` lying over `v` gives an embedding between
the two completions.  The minimal polynomial of the image of `α` in the
second completion is an irreducible factor over the first.  The file proves
that converting a place to this factor and then back recovers the place.
-/

namespace Submission.NumberTheory.Milne

open AbsoluteValue Polynomial

noncomputable section

variable {K L Khat : Type*} [Field K] [Field L] [Field Khat]
  [Algebra K L] [Algebra K Khat] [FiniteDimensional K L]

/-- If `g` divides the minimal polynomial of a primitive element after scalar
extension, the root of `g` determines a `K`-algebra map from the primitive
extension to `AdjoinRoot g`. -/
def primitiveAdjoinRoot
    (α : L) (hα : Algebra.adjoin K {α} = ⊤) (g : Khat[X])
    (hg : g ∣ (minpoly K α).map (algebraMap K Khat)) :
    L →ₐ[K] AdjoinRoot g := by
  let pb : PowerBasis K L :=
    PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral α) hα
  apply pb.lift (AdjoinRoot.root g)
  rw [show pb.gen = α by
    exact PowerBasis.ofAdjoinEqTop_gen (Algebra.IsIntegral.isIntegral α) hα]
  rw [← aeval_map_algebraMap Khat]
  rcases hg with ⟨q, hq⟩
  rw [hq, aeval_def, eval₂_mul, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.eval₂_root, zero_mul]


section ComplexArchimedean

variable [Algebra.IsSeparable K L]

/-- Ring embeddings of `L` into `ℂ` extending a fixed embedding of `K`.
For a complex archimedean place, these are its extensions to `L`. -/
abbrev ComplexEmbeddingExtension
    (ψ : K →+* ℂ) :=
  {φ : L →+* ℂ // φ.comp (algebraMap K L) = ψ}

/-- The monic irreducible factors over `ℂ` of the minimal polynomial of a
primitive element after applying a fixed complex embedding of the base
field. -/
abbrev ComplexCompletedMinpoly
    (ψ : K →+* ℂ) (α : L) :=
  {g : ℂ[X] // Irreducible g ∧ g.Monic ∧ g ∣ (minpoly K α).map ψ}

/-- Over an algebraically closed field, roots of a nonzero polynomial are
equivalent to its monic irreducible factors. -/
private noncomputable def monicIrreducibleFactors
    {F A : Type*} [Field F] [Field A] [Algebra F A] [IsAlgClosed A]
    (p : F[X]) (hp : p ≠ 0) :
    p.rootSet A ≃
      {g : A[X] // Irreducible g ∧ g.Monic ∧
        g ∣ p.map (algebraMap F A)} where
  toFun x := ⟨X - C x.1, irreducible_X_sub_C x.1, monic_X_sub_C x.1, by
    rw [dvd_iff_isRoot, IsRoot, eval_map_algebraMap]
    exact (mem_rootSet_of_ne hp).mp x.2⟩
  invFun g := ⟨-g.1.coeff 0, by
    have hlinear : g.1 = X - C (-g.1.coeff 0) := by
      simpa [g.2.2.1.leadingCoeff] using
        eq_X_add_C_of_degree_eq_one
          (IsAlgClosed.degree_eq_one_of_irreducible A g.2.1)
    have hroot : (p.map (algebraMap F A)).IsRoot (-g.1.coeff 0) := by
      rw [← dvd_iff_isRoot, ← hlinear]
      exact g.2.2.2
    rw [mem_rootSet_of_ne hp]
    simpa [aeval_def, IsRoot] using hroot⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv g := by
    apply Subtype.ext
    simpa [g.2.2.1.leadingCoeff] using
      (eq_X_add_C_of_degree_eq_one
        (IsAlgClosed.degree_eq_one_of_irreducible A g.2.1)).symm

/-- The archimedean embedding form of Milne, Proposition 8.1: extensions of
a fixed complex embedding are naturally parametrized by the roots of the
mapped minimal polynomial. -/
noncomputable def complexEmbeddingSet
    (ψ : K →+* ℂ) (α : L) (hα : Algebra.adjoin K {α} = ⊤) :
    ComplexEmbeddingExtension (K := K) (L := L) ψ ≃
      ((minpoly K α).map ψ).rootSet ℂ := by
  letI : Algebra K ℂ := ψ.toAlgebra
  let toAlgHom
      (φ : ComplexEmbeddingExtension (K := K) (L := L) ψ) : L →ₐ[K] ℂ :=
    { toRingHom := φ.1
      commutes' := fun x ↦ RingHom.congr_fun φ.2 x }
  let evalRoot : ComplexEmbeddingExtension (K := K) (L := L) ψ →
      ((minpoly K α).map ψ).rootSet ℂ :=
    fun φ ↦ ⟨φ.1 α, by
      rw [mem_rootSet_of_ne
        ((minpoly.monic (Algebra.IsIntegral.isIntegral α)).map ψ).ne_zero]
      simpa [aeval_def, eval_map] using
        congrArg (toAlgHom φ) (minpoly.aeval K α)⟩
  apply Equiv.ofBijective evalRoot
  constructor
  · intro φ χ h
    apply Subtype.ext
    have heval : toAlgHom φ α = toAlgHom χ α :=
      congrArg Subtype.val h
    have hinjective : Function.Injective fun f : L →ₐ[K] ℂ ↦ f α :=
      (Field.primitive_element_iff_algHom_eq_of_eval'
        K ℂ (fun _ ↦ IsAlgClosed.splits _) α).mp
          (IntermediateField.adjoin_eq_top_of_algebra
            (F := K) (E := L) (S := ({α} : Set L)) hα)
    exact congrArg AlgHom.toRingHom (hinjective heval)
  · intro z
    have hz : z.1 ∈ (minpoly K α).rootSet ℂ := by
      rw [mem_rootSet_of_ne (minpoly.ne_zero (Algebra.IsIntegral.isIntegral α))]
      have hzMapped := z.2
      rw [mem_rootSet_of_ne
        ((minpoly.monic (Algebra.IsIntegral.isIntegral α)).map ψ).ne_zero] at hzMapped
      simpa [aeval_def, eval_map] using hzMapped
    have hrange : z.1 ∈ Set.range fun f : L →ₐ[K] ℂ ↦ f α := by
      rw [Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ α]
      exact hz
    rcases hrange with ⟨f, hf⟩
    let φ : ComplexEmbeddingExtension (K := K) (L := L) ψ :=
      ⟨f.toRingHom, by
        ext x
        exact f.commutes x⟩
    refine ⟨φ, ?_⟩
    apply Subtype.ext
    exact hf

/-- Milne, Proposition 8.1 for a complex archimedean base place.  A fixed
embedding `K → ℂ` has one extension for each monic irreducible factor over
its complete field `ℂ` of the mapped minimal polynomial. -/
noncomputable def complexEmbeddingMinpoly
    (ψ : K →+* ℂ) (α : L) (hα : Algebra.adjoin K {α} = ⊤) :
    ComplexEmbeddingExtension (K := K) (L := L) ψ ≃
      ComplexCompletedMinpoly (K := K) ψ α := by
  letI : Algebra K ℂ := ψ.toAlgebra
  simpa using (complexEmbeddingSet ψ α hα).trans
    (monicIrreducibleFactors
      (F := ℂ) (A := ℂ) ((minpoly K α).map ψ)
        ((minpoly.monic (Algebra.IsIntegral.isIntegral α)).map ψ).ne_zero)

end ComplexArchimedean


section Nonarchimedean

variable (v : AbsoluteValue K ℝ) [IsUltrametricDist v.Completion]

omit [IsUltrametricDist v.Completion] in
/-- A nontrivial absolute value gives its completion a nontrivial normed
field structure. -/
@[reducible] noncomputable def absoluteNontriviallyNormed
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial] :
    NontriviallyNormedField v.Completion :=
  NontriviallyNormedField.ofNormNeOne <| by
    rcases (Fact.out : v.IsNontrivial) with ⟨x, hx0, hx1⟩
    refine ⟨completionEmbedding v x, ?_, ?_⟩
    · intro hx
      apply hx0
      apply RingHom.injective (completionEmbedding v)
      rw [map_zero]
      exact hx
    · rwa [norm_completionEmbedding]

omit [IsUltrametricDist v.Completion] in
/-- The completion of a nonarchimedean absolute value is ultrametric. -/
@[reducible] def absoluteUltrametricDist
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) :
    IsUltrametricDist v.Completion := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one
  intro n
  rw [← map_natCast (completionEmbedding v) n, norm_completionEmbedding]
  exact hv.apply_natCast_le_one

/-- A monic irreducible factor over the completion of the minimal polynomial
of `α`. -/
abbrev CompletedMinpolyFactor (α : L) :=
  {g : v.Completion[X] //
    Irreducible g ∧ g.Monic ∧
      g ∣ (minpoly K α).map (completionEmbedding v)}

private noncomputable local instance completionNontriviallyNormedField
    [Fact v.IsNontrivial] :
    NontriviallyNormedField v.Completion :=
  NontriviallyNormedField.ofNormNeOne <| by
    rcases (Fact.out : v.IsNontrivial) with ⟨x, hx0, hx1⟩
    refine ⟨completionEmbedding v x, ?_, ?_⟩
    · intro hx
      apply hx0
      apply RingHom.injective (completionEmbedding v)
      rw [map_zero]
      exact hx
    · rwa [norm_completionEmbedding]

/-- The absolute value on `L` obtained from an irreducible factor of the
minimal polynomial over the completion of `K`. -/
def absoluteExtensionFactor
    [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤) (g : v.Completion[X])
    (hmonic : g.Monic) (hirr : Irreducible g)
    (hg : g ∣ (minpoly K α).map (completionEmbedding v)) :
    AbsoluteValue L ℝ := by
  letI : Algebra K v.Completion := (completionEmbedding v).toAlgebra
  letI : Fact (Irreducible g) := ⟨hirr⟩
  letI : Module.Finite v.Completion (AdjoinRoot g) := hmonic.finite_adjoinRoot
  let φ : L →ₐ[K] AdjoinRoot g :=
    primitiveAdjoinRoot α hα g hg
  exact (completeAbsoluteValue v.Completion (AdjoinRoot g)).comp
    φ.toRingHom.injective

/-- The absolute value obtained from a factor restricts to the original
absolute value on `K`. -/
@[simp]
theorem absolute_extension_algebra
    [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤) (g : v.Completion[X])
    (hmonic : g.Monic) (hirr : Irreducible g)
    (hg : g ∣ (minpoly K α).map (completionEmbedding v)) (x : K) :
    absoluteExtensionFactor v α hα g hmonic hirr hg
        (algebraMap K L x) = v x := by
  letI : Algebra K v.Completion := (completionEmbedding v).toAlgebra
  letI : Fact (Irreducible g) := ⟨hirr⟩
  letI : Module.Finite v.Completion (AdjoinRoot g) := hmonic.finite_adjoinRoot
  change completeAbsoluteValue v.Completion (AdjoinRoot g)
      (primitiveAdjoinRoot α hα g hg (algebraMap K L x)) = v x
  rw [AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply K v.Completion (AdjoinRoot g)]
  rw [complete_absolute_algebra]
  change ‖completionEmbedding v x‖ = v x
  exact norm_completionEmbedding v x

/-- The factor construction really gives an extension of `v` in the sense of
`AbsoluteValue.LiesOver`. -/
theorem absolute_extension_lies
    [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤) (g : v.Completion[X])
    (hmonic : g.Monic) (hirr : Irreducible g)
    (hg : g ∣ (minpoly K α).map (completionEmbedding v)) :
    AbsoluteValue.LiesOver
      (absoluteExtensionFactor v α hα g hmonic hirr hg) v := by
  constructor
  ext x
  exact absolute_extension_algebra v α hα g hmonic hirr hg x

/-- The factor-to-place map in the converse direction of Milne's
Proposition 8.1. -/
def completedMinpolyExtension
    [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤) :
    CompletedMinpolyFactor v α →
      {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v} :=
  fun g =>
    ⟨absoluteExtensionFactor v α hα g g.2.2.1 g.2.1 g.2.2.2,
      absolute_extension_lies v α hα g g.2.2.1 g.2.1 g.2.2.2⟩

/-- Every nontrivial nonarchimedean absolute value extends to a finite
separable field extension. -/
theorem absolute_value_extension
    [Algebra.IsSeparable K L] [Fact v.IsNontrivial] :
    Nonempty {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v} := by
  let α := (Field.exists_primitive_element K L).choose
  have hα : Algebra.adjoin K {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α)]
    exact congrArg IntermediateField.toSubalgebra
      (Field.exists_primitive_element K L).choose_spec
  let p : v.Completion[X] :=
    (minpoly K α).map (completionEmbedding v)
  have hpDegree : 0 < p.natDegree := by
    rw [Polynomial.Monic.natDegree_map
      (minpoly.monic (Algebra.IsIntegral.isIntegral α))]
    exact minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral α)
  have hpUnit : ¬ IsUnit p := by
    intro hp
    exact (not_lt_of_ge (Polynomial.natDegree_eq_zero_of_isUnit hp).le) hpDegree
  obtain ⟨g, hmonic, hirr, hdiv⟩ :=
    Polynomial.exists_monic_irreducible_factor p hpUnit
  let G : CompletedMinpolyFactor v α :=
    ⟨g, hirr, hmonic, hdiv⟩
  exact ⟨completedMinpolyExtension v α hα G⟩

omit [FiniteDimensional K L] [IsUltrametricDist v.Completion] in
/-- An absolute value lying over a nontrivial absolute value is nontrivial. -/
theorem absolute_extension_nontrivial
    [Fact v.IsNontrivial]
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    w.1.IsNontrivial := by
  obtain ⟨x, hx0, hx1⟩ := (Fact.out : v.IsNontrivial)
  refine ⟨algebraMap K L x, ?_, ?_⟩
  · simpa only [map_zero] using (algebraMap K L).injective.ne hx0
  · have heq := DFunLike.congr_fun w.2.comp_eq x
    exact fun h => hx1 (heq.symm.trans h)

omit [FiniteDimensional K L] [IsUltrametricDist v.Completion] in
/-- Two equivalent absolute values which have the same nontrivial
normalization on the base field are equal. -/
theorem absolute_value_lies
    [Fact v.IsNontrivial]
    (w₁ w₂ : AbsoluteValue L ℝ)
    (hw₁ : AbsoluteValue.LiesOver w₁ v)
    (hw₂ : AbsoluteValue.LiesOver w₂ v)
    (hequiv : w₁.IsEquiv w₂) : w₁ = w₂ := by
  obtain ⟨c, hc, hpow⟩ :=
    AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  obtain ⟨x, hx0, hx1⟩ := (Fact.out : v.IsNontrivial)
  have hvx : 0 < v x := v.pos hx0
  have hw₁x := DFunLike.congr_fun hw₁.comp_eq x
  have hw₂x := DFunLike.congr_fun hw₂.comp_eq x
  change w₁ (algebraMap K L x) = v x at hw₁x
  change w₂ (algebraMap K L x) = v x at hw₂x
  have hbase : v x ^ c = v x ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    calc
      v x ^ c = w₁ (algebraMap K L x) ^ c := by
        exact congrArg (fun r : ℝ => r ^ c) hw₁x.symm
      _ = w₂ (algebraMap K L x) := congrFun hpow _
      _ = v x := hw₂x
  have hc1 : c = 1 :=
    (Real.rpow_right_inj hvx hx1).mp hbase
  apply AbsoluteValue.ext
  intro y
  have hy := congrFun hpow y
  simpa [hc1] using hy

omit [FiniteDimensional K L] [IsUltrametricDist v.Completion] in
/-- The embedding of `K` into the completion belonging to an extension `w`
of `v` preserves the absolute value `v`. -/
private theorem embedding_preserves_lies
    (w : AbsoluteValue L ℝ) (hwv : AbsoluteValue.LiesOver w v) (x : K) :
    ‖completionEmbedding w (algebraMap K L x)‖ = v x := by
  rw [norm_completionEmbedding]
  exact DFunLike.congr_fun hwv.comp_eq x

/-- An extension `w` of `v` induces the canonical embedding from the
`v`-completion of `K` into the `w`-completion of `L`. -/
def completionLies
    (w : AbsoluteValue L ℝ) (hwv : AbsoluteValue.LiesOver w v) :
    v.Completion →+* w.Completion :=
  (completion_universal v
    ((completionEmbedding w).comp (algebraMap K L))
    (embedding_preserves_lies v w hwv)).choose

omit [FiniteDimensional K L] [IsUltrametricDist v.Completion] in
/-- The induced map between completions extends the original embedding
`K → L`. -/
theorem completion_lies_comp
    (w : AbsoluteValue L ℝ) (hwv : AbsoluteValue.LiesOver w v) :
    (completionLies v w hwv).comp (completionEmbedding v) =
      (completionEmbedding w).comp (algebraMap K L) :=
  (completion_universal v
    ((completionEmbedding w).comp (algebraMap K L))
    (embedding_preserves_lies v w hwv)).choose_spec.1.2

omit [FiniteDimensional K L] [IsUltrametricDist v.Completion] in
/-- The induced map between completions is an isometry. -/
theorem completion_lies_isometry
    (w : AbsoluteValue L ℝ) (hwv : AbsoluteValue.LiesOver w v) :
    Isometry (completionLies v w hwv) :=
  (completion_universal v
    ((completionEmbedding w).comp (algebraMap K L))
    (embedding_preserves_lies v w hwv)).choose_spec.1.1

omit [FiniteDimensional K L] [IsUltrametricDist v.Completion] in
/-- Completion embeddings are transitive in a tower of extending absolute
values. -/
theorem completion_lies_trans
    {D : Type*} [Field D] [Algebra K D] [Algebra D L]
    [IsScalarTower K D L]
    (u : AbsoluteValue D ℝ) (w : AbsoluteValue L ℝ)
    (huv : AbsoluteValue.LiesOver u v)
    (hwu : AbsoluteValue.LiesOver w u)
    (hwv : AbsoluteValue.LiesOver w v) :
    (completionLies u w hwu).comp
        (completionLies v u huv) =
      completionLies v w hwv := by
  apply DFunLike.ext _ _
  intro y
  exact congrFun ((dense_range_embedding v).equalizer
    ((completion_lies_isometry u w hwu).continuous.comp
      (completion_lies_isometry v u huv).continuous)
    (completion_lies_isometry v w hwv).continuous
    (funext fun x => by
      have huvx := RingHom.congr_fun
        (completion_lies_comp v u huv) x
      have hwux := RingHom.congr_fun
        (completion_lies_comp u w hwu) (algebraMap K D x)
      have hwvx := RingHom.congr_fun
        (completion_lies_comp v w hwv) x
      change completionLies v u huv (completionEmbedding v x) =
        completionEmbedding u (algebraMap K D x) at huvx
      change completionLies u w hwu
          (completionEmbedding u (algebraMap K D x)) =
        completionEmbedding w (algebraMap D L (algebraMap K D x)) at hwux
      change completionLies v w hwv (completionEmbedding v x) =
        completionEmbedding w (algebraMap K L x) at hwvx
      calc
        completionLies u w hwu
            (completionLies v u huv (completionEmbedding v x)) =
            completionLies u w hwu
              (completionEmbedding u (algebraMap K D x)) := by rw [huvx]
        _ = completionEmbedding w
            (algebraMap D L (algebraMap K D x)) := hwux
        _ = completionEmbedding w (algebraMap K L x) := by
          rw [IsScalarTower.algebraMap_apply K D L]
        _ = completionLies v w hwv
            (completionEmbedding v x) := hwvx.symm)) y

omit [FiniteDimensional K L] [IsUltrametricDist v.Completion] in
/-- The image of `α` in the completion belonging to `w` is a root of the
minimal polynomial of `α` after extension to the completion of `K`. -/
theorem mapped_minpoly_eval₂
    (w : AbsoluteValue L ℝ) (hwv : AbsoluteValue.LiesOver w v) (α : L) :
    eval₂ (completionLies v w hwv) (completionEmbedding w α)
      ((minpoly K α).map (completionEmbedding v)) = 0 := by
  rw [eval₂_map, completion_lies_comp v w hwv]
  rw [← Polynomial.hom_eval₂]
  change completionEmbedding w (aeval α (minpoly K α)) = 0
  rw [minpoly.aeval, map_zero]

omit [IsUltrametricDist v.Completion] in
/-- The place-to-factor map in Milne's Proposition 8.1: the minimal
polynomial of the image of `α` in the `w`-completion is an irreducible factor
of the minimal polynomial of `α` over the `v`-completion. -/
def absoluteMinpolyFactor
    (α : L) (w : AbsoluteValue L ℝ)
    (hwv : AbsoluteValue.LiesOver w v) :
    CompletedMinpolyFactor v α := by
  let ι : v.Completion →+* w.Completion := completionLies v w hwv
  letI : Algebra v.Completion w.Completion := ι.toAlgebra
  let β : w.Completion := completionEmbedding w α
  let p : v.Completion[X] := (minpoly K α).map (completionEmbedding v)
  have hpmonic : p.Monic :=
    (minpoly.monic (Algebra.IsIntegral.isIntegral α)).map (completionEmbedding v)
  have hpeval : eval₂ ι β p = 0 := mapped_minpoly_eval₂ v w hwv α
  have hp_aeval : aeval β p = 0 := by
    rw [aeval_def]
    exact hpeval
  have hβint : IsIntegral v.Completion β := ⟨p, hpmonic, hp_aeval⟩
  refine ⟨minpoly v.Completion β, ?_, ?_, ?_⟩
  · exact minpoly.irreducible hβint
  · exact minpoly.monic hβint
  · exact minpoly.dvd v.Completion β hp_aeval

omit [IsUltrametricDist v.Completion] in
/-- The bundled place-to-factor map in Milne's Proposition 8.1. -/
def absoluteCompletedMinpoly
    (α : L) :
    {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v} →
      CompletedMinpolyFactor v α :=
  fun w => absoluteMinpolyFactor v α w w.2

set_option maxHeartbeats 800000 in
-- Unfolding both constructions creates several nested completion and adjoin-root terms.
/-- Passing from an extension `w` to its completed minimal-polynomial factor
and then back to an absolute value recovers `w`.  This is one inverse law in
Milne's place-factor correspondence. -/
theorem absolute_extension_roundtrip
    [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤)
    (w : AbsoluteValue L ℝ) (hwv : AbsoluteValue.LiesOver w v) :
    let G := absoluteMinpolyFactor v α w hwv
    absoluteExtensionFactor v α hα G G.2.2.1 G.2.1 G.2.2.2 = w := by
  let ι : v.Completion →+* w.Completion := completionLies v w hwv
  letI : Algebra v.Completion w.Completion := ι.toAlgebra
  let β : w.Completion := completionEmbedding w α
  let g : v.Completion[X] := minpoly v.Completion β
  have hβint : IsIntegral v.Completion β := by
    let p : v.Completion[X] := (minpoly K α).map (completionEmbedding v)
    have hpmonic : p.Monic :=
      (minpoly.monic (Algebra.IsIntegral.isIntegral α)).map (completionEmbedding v)
    have hp_aeval : aeval β p = 0 := by
      rw [aeval_def]
      exact mapped_minpoly_eval₂ v w hwv α
    exact ⟨p, hpmonic, hp_aeval⟩
  have hgβ : aeval β g = 0 := minpoly.aeval v.Completion β
  have hgβ' : eval₂ (Algebra.ofId v.Completion w.Completion) β g = 0 := by
    simpa [aeval_def] using hgβ
  letI : Fact (Irreducible g) := ⟨minpoly.irreducible hβint⟩
  letI : Module.Finite v.Completion (AdjoinRoot g) :=
    (minpoly.monic hβint).finite_adjoinRoot
  let ψ : AdjoinRoot g →ₐ[v.Completion] w.Completion :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId v.Completion w.Completion) β hgβ'
  let pulled : AbsoluteValue (AdjoinRoot g) ℝ :=
    (NormedField.toAbsoluteValue w.Completion).comp ψ.toRingHom.injective
  have hpulled : pulled = completeAbsoluteValue v.Completion (AdjoinRoot g) := by
    apply complete_absolute_unique
    intro x
    change ‖ψ (algebraMap v.Completion (AdjoinRoot g) x)‖ = ‖x‖
    rw [ψ.commutes]
    simpa only [dist_zero_right, map_zero] using
      (completion_lies_isometry v w hwv).dist_eq x 0
  letI : Algebra K v.Completion := (completionEmbedding v).toAlgebra
  let φ : L →ₐ[K] AdjoinRoot g := by
    apply primitiveAdjoinRoot α hα g
    exact minpoly.dvd v.Completion β (by
      rw [aeval_def]
      exact mapped_minpoly_eval₂ v w hwv α)
  let algKw : Algebra K w.Completion :=
    ((completionEmbedding w).comp (algebraMap K L)).toAlgebra
  letI : Algebra K w.Completion := algKw
  let ψφ : L →ₐ[K] w.Completion :=
    { toRingHom := ψ.toRingHom.comp φ.toRingHom
      commutes' := fun x => by
        change ψ (φ (algebraMap K L x)) =
          completionEmbedding w (algebraMap K L x)
        rw [φ.commutes]
        rw [IsScalarTower.algebraMap_apply K v.Completion (AdjoinRoot g)]
        rw [ψ.commutes]
        exact RingHom.congr_fun (completion_lies_comp v w hwv) x }
  let jw : L →ₐ[K] w.Completion :=
    { toRingHom := completionEmbedding w
      commutes' := fun x => rfl }
  have hψφ : ψφ = jw := by
    let pb : PowerBasis K L :=
      PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral α) hα
    apply pb.algHom_ext
    rw [show pb.gen = α by
      exact PowerBasis.ofAdjoinEqTop_gen (Algebra.IsIntegral.isIntegral α) hα]
    change ψ (φ α) = completionEmbedding w α
    have hφα : φ α = AdjoinRoot.root g := by
      unfold φ primitiveAdjoinRoot
      simpa only [PowerBasis.ofAdjoinEqTop_gen] using
        (PowerBasis.lift_gen
          (PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral α) hα)
          (AdjoinRoot.root g) _)
    rw [hφα]
    change ψ (AdjoinRoot.root g) = β
    exact AdjoinRoot.liftAlgHom_root g
      (Algebra.ofId v.Completion w.Completion) β hgβ'
  ext x
  change completeAbsoluteValue v.Completion (AdjoinRoot g) (φ x) = w x
  rw [← hpulled]
  change ‖ψ (φ x)‖ = w x
  have hx := DFunLike.congr_fun hψφ x
  change ψ (φ x) = completionEmbedding w x at hx
  rw [hx, norm_completionEmbedding]

set_option synthInstance.maxHeartbeats 100000 in
-- Inferring the isometry of the scalar map unfolds the spectral norm instances.
set_option maxHeartbeats 800000 in
-- The proof compares two completion maps by continuity on a dense subfield.
/-- Passing from a completed irreducible factor to its absolute value and
then back to a completed factor recovers the original factor.  This is the
other inverse law in Milne's place-factor correspondence. -/
theorem minpoly_place_roundtrip
    [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤)
    (G : CompletedMinpolyFactor v α) :
    absoluteMinpolyFactor v α
      (completedMinpolyExtension v α hα G).1
      (completedMinpolyExtension v α hα G).2 = G := by
  apply Subtype.ext
  let g : v.Completion[X] := G.1
  have hmonic : g.Monic := G.2.2.1
  have hirr : Irreducible g := G.2.1
  have hg : g ∣ (minpoly K α).map (completionEmbedding v) := G.2.2.2
  letI : Algebra K v.Completion := (completionEmbedding v).toAlgebra
  letI : Fact (Irreducible g) := ⟨hirr⟩
  letI : Module.Finite v.Completion (AdjoinRoot g) := hmonic.finite_adjoinRoot
  let φ : L →ₐ[K] AdjoinRoot g :=
    primitiveAdjoinRoot α hα g hg
  let eAbs : AbsoluteValue (AdjoinRoot g) ℝ :=
    completeAbsoluteValue v.Completion (AdjoinRoot g)
  let w : AbsoluteValue L ℝ :=
    absoluteExtensionFactor v α hα g hmonic hirr hg
  letI : NormedField (AdjoinRoot g) :=
    spectralNorm.normedField v.Completion (AdjoinRoot g)
  letI : CompleteSpace (AdjoinRoot g) :=
    spectralNorm.completeSpace v.Completion (AdjoinRoot g)
  have hφnorm (x : L) : ‖φ x‖ = w x := by
    change eAbs (φ x) = w x
    rfl
  let F : w.Completion →+* AdjoinRoot g :=
    (completion_universal w φ.toRingHom hφnorm).choose
  have hFcomp : F.comp (completionEmbedding w) = φ.toRingHom :=
    (completion_universal w φ.toRingHom hφnorm).choose_spec.1.2
  have hFinj : Function.Injective F :=
    (completion_universal w φ.toRingHom hφnorm).choose_spec.1.1.injective
  let hwv : AbsoluteValue.LiesOver w v :=
    absolute_extension_lies v α hα g hmonic hirr hg
  let ι : v.Completion →+* w.Completion := completionLies v w hwv
  have hFι : F.comp ι = algebraMap v.Completion (AdjoinRoot g) := by
    have hFiso : Isometry F :=
      (completion_universal w φ.toRingHom hφnorm).choose_spec.1.1
    have hFιiso : Isometry (F.comp ι) :=
      hFiso.comp (completion_lies_isometry v w hwv)
    have hAiso : Isometry (algebraMap v.Completion (AdjoinRoot g)) := by
      exact AddMonoidHomClass.isometry_of_norm
        (algebraMap v.Completion (AdjoinRoot g)) (fun x ↦ by
          change eAbs (algebraMap v.Completion (AdjoinRoot g) x) = ‖x‖
          exact complete_absolute_algebra
            v.Completion (AdjoinRoot g) x)
    apply DFunLike.ext _ _
    exact congrFun ((dense_range_embedding v).equalizer
      hFιiso.continuous hAiso.continuous (by
        apply _root_.funext
        intro x
        have hιx := RingHom.congr_fun (completion_lies_comp v w hwv) x
        have hFx := RingHom.congr_fun hFcomp (algebraMap K L x)
        have hιx' : ι (completionEmbedding v x) =
            completionEmbedding w (algebraMap K L x) := by
          simpa [ι] using hιx
        have hFx' : F (completionEmbedding w (algebraMap K L x)) =
            φ (algebraMap K L x) := by
          simpa using hFx
        change F (ι (completionEmbedding v x)) =
          algebraMap v.Completion (AdjoinRoot g) (completionEmbedding v x)
        rw [hιx', hFx']
        rw [φ.commutes]
        rfl))
  let β : w.Completion := completionEmbedding w α
  have hFβ : F β = AdjoinRoot.root g := by
    have h := RingHom.congr_fun hFcomp α
    calc
      F β = φ α := h
      _ = AdjoinRoot.root g := by
        unfold φ primitiveAdjoinRoot
        simpa only [PowerBasis.ofAdjoinEqTop_gen] using
          (PowerBasis.lift_gen
            (PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral α) hα)
            (AdjoinRoot.root g) _)
  have hgeval : eval₂ ι β g = 0 := by
    apply hFinj
    rw [map_zero]
    rw [Polynomial.hom_eval₂]
    simpa only [hFι, hFβ] using AdjoinRoot.eval₂_root g
  letI : Algebra v.Completion w.Completion := ι.toAlgebra
  have hgdvd : minpoly v.Completion β ∣ g := by
    apply minpoly.dvd
    rw [aeval_def]
    exact hgeval
  have hminirr : Irreducible (minpoly v.Completion β) :=
    (absoluteMinpolyFactor v α w hwv).2.1
  have hminmonic : (minpoly v.Completion β).Monic :=
    (absoluteMinpolyFactor v α w hwv).2.2.1
  exact eq_of_monic_of_associated hminmonic hmonic
    (hminirr.associated_of_dvd hirr hgdvd)

/-- Constructional form of Milne's place-factor correspondence: the
place-to-factor map is a right inverse of the factor-to-place map. -/
theorem completed_minpoly_inverse
    [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤) :
    Function.RightInverse
      (absoluteCompletedMinpoly v α)
      (completedMinpolyExtension v α hα) := by
  intro w
  apply Subtype.ext
  exact absolute_extension_roundtrip v α hα w w.2

/-- Milne, Proposition 8.1: monic irreducible factors of the completed
minimal polynomial are naturally equivalent to the absolute values on `L`
extending `v`. -/
def completedMinpolyExtensions
    [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤) :
    CompletedMinpolyFactor v α ≃
      {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v} where
  toFun := completedMinpolyExtension v α hα
  invFun := absoluteCompletedMinpoly v α
  left_inv := minpoly_place_roundtrip v α hα
  right_inv := fun w => completed_minpoly_inverse v α hα w

/-- Every absolute value extending a nontrivial nonarchimedean absolute
value through a finite separable extension is nonarchimedean. -/
theorem absolute_extension_nonarchimedean
    [Algebra.IsSeparable K L] [Fact v.IsNontrivial]
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v}) :
    IsNonarchimedean w.1 := by
  let α := (Field.exists_primitive_element K L).choose
  have hα : Algebra.adjoin K {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α)]
    exact congrArg IntermediateField.toSubalgebra
      (Field.exists_primitive_element K L).choose_spec
  let e := completedMinpolyExtensions v α hα
  let G : CompletedMinpolyFactor v α := e.symm w
  have hw : w = e G := (e.apply_symm_apply w).symm
  letI : Algebra K v.Completion := (completionEmbedding v).toAlgebra
  letI : Fact (Irreducible G.1) := ⟨G.2.1⟩
  letI : Module.Finite v.Completion (AdjoinRoot G.1) :=
    G.2.2.1.finite_adjoinRoot
  rw [hw]
  intro x y
  change completeAbsoluteValue v.Completion (AdjoinRoot G.1)
      (primitiveAdjoinRoot α hα G.1 G.2.2.2 (x + y)) ≤ _
  rw [map_add]
  exact complete_absolute_nonarchimedean
    v.Completion (AdjoinRoot G.1) _ _

/-- A nonarchimedean extension of a nontrivial nonarchimedean absolute
value can be chosen explicitly. -/
theorem nonarchimedean_absolute_extension
    [Algebra.IsSeparable K L] [Fact v.IsNontrivial] :
    ∃ w : AbsoluteValue L ℝ,
      AbsoluteValue.LiesOver w v ∧ IsNonarchimedean w := by
  obtain ⟨w⟩ := absolute_value_extension (K := K) (L := L) v
  exact ⟨w.1, w.2, absolute_extension_nonarchimedean v w⟩

omit [IsUltrametricDist v.Completion] in
/-- There are only finitely many monic irreducible factors of the completed
minimal polynomial. -/
theorem completed_minpoly_factor (α : L) :
    Finite (CompletedMinpolyFactor v α) := by
  let p : v.Completion[X] :=
    (minpoly K α).map (completionEmbedding v)
  have hpmonic : p.Monic :=
    (minpoly.monic (Algebra.IsIntegral.isIntegral α)).map (completionEmbedding v)
  letI : Fintype {g : v.Completion[X] // g.Monic ∧ g ∣ p} :=
    Polynomial.fintypeSubtypeMonicDvd p hpmonic.ne_zero
  let toFactors : CompletedMinpolyFactor v α →
      {g : v.Completion[X] // g.Monic ∧ g ∣ p} :=
    fun g => ⟨g, g.2.2⟩
  exact Finite.of_injective toFactors fun a b h =>
    Subtype.ext (congrArg
      (fun x : {g : v.Completion[X] // g.Monic ∧ g ∣ p} => x.1) h)

/-- The finiteness assertion in Milne's Proposition 8.2, for a chosen
primitive element. -/
theorem absolute_value_extensions
    [Fact v.IsNontrivial]
    (α : L) (hα : Algebra.adjoin K {α} = ⊤) :
    Finite {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v} := by
  letI : Finite (CompletedMinpolyFactor v α) :=
    completed_minpoly_factor v α
  exact Finite.of_injective
    (absoluteCompletedMinpoly v α)
    (completed_minpoly_inverse v α hα).injective

/-- Milne, Proposition 8.2 (finiteness clause): a finite separable extension
has only finitely many extensions of a fixed nonarchimedean absolute value. -/
theorem absolute_extensions_separable
    [Fact v.IsNontrivial] [Algebra.IsSeparable K L] :
    Finite {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v} := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  have hα' : Algebra.adjoin K {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α)]
    exact congrArg IntermediateField.toSubalgebra hα
  exact absolute_value_extensions v α hα'

end Nonarchimedean

section Archimedean

open NumberField

variable [Algebra.IsSeparable K L]

/-- The monic irreducible factors over `ℝ` obtained from a fixed real
embedding of the base field. -/
abbrev RealCompletedMinpoly
    (psi : K →+* ℝ) (alpha : L) :=
  {g : ℝ[X] // Irreducible g ∧ g.Monic ∧ g ∣ (minpoly K alpha).map psi}

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- An infinite place of `L` above `v` is, in particular, an extension of
the absolute value underlying `v`. -/
theorem infinite_lies_comap
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hwv : w.comap (algebraMap K L) = v) :
    AbsoluteValue.LiesOver w.1 v.1 := by
  constructor
  ext x
  exact InfinitePlace.comp_of_comap_eq hwv x

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- Above a real infinite place, the chosen embedding of an overlying place
restricts to the chosen embedding of the base place, rather than merely to
one of its two conjugates. -/
theorem infinite_embedding_real
    (v : InfinitePlace K) (hv : v.IsReal) (w : InfinitePlace L)
    (hwv : w.comap (algebraMap K L) = v) :
    w.embedding.comp (algebraMap K L) = v.embedding := by
  letI : AbsoluteValue.LiesOver w.1 v.1 :=
    infinite_lies_comap v w hwv
  rcases
      InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq
        w v with h | h
  · exact h
  · ext x
    have hx := RingHom.congr_fun h x
    change starRingEnd ℂ (w.embedding (algebraMap K L x)) =
      v.embedding x at hx
    calc
      w.embedding (algebraMap K L x) =
          starRingEnd ℂ (starRingEnd ℂ
            (w.embedding (algebraMap K L x))) :=
        (star_star _).symm
      _ = starRingEnd ℂ (v.embedding x) := congrArg (starRingEnd ℂ) hx
      _ = v.embedding x := by
        exact RingHom.congr_fun
          (InfinitePlace.conjugate_embedding_eq_of_isReal hv) x

/-- Two complex embeddings extending the chosen representative of `v` are
identified when they define the same infinite place of `L`. -/
abbrev ComplexEmbeddingSetoid (v : InfinitePlace K) :
    Setoid (ComplexEmbeddingExtension (K := K) (L := L) v.embedding) :=
  Setoid.ker fun phi => InfinitePlace.mk phi.1

/-- Infinite places of `L` above `v` are the complex embeddings extending the
chosen representative of `v`, modulo the equivalence relation of defining the
same infinite place.  For a real base place this quotient pairs conjugate
embeddings; for a complex base place the relation is trivial. -/
noncomputable def complexClassesAbove
    (v : InfinitePlace K) :
    Quotient (ComplexEmbeddingSetoid (K := K) (L := L) v) ≃
      {w : InfinitePlace L // w.comap (algebraMap K L) = v} := by
  let toPlace : ComplexEmbeddingExtension (K := K) (L := L) v.embedding →
      {w : InfinitePlace L // w.comap (algebraMap K L) = v} :=
    fun phi => ⟨InfinitePlace.mk phi.1, by
      rw [InfinitePlace.comap_mk, phi.2, InfinitePlace.mk_embedding]⟩
  let quotientToPlace :
      Quotient (ComplexEmbeddingSetoid (K := K) (L := L) v) →
        {w : InfinitePlace L // w.comap (algebraMap K L) = v} :=
    Quotient.lift toPlace fun _ _ h => Subtype.ext h
  apply Equiv.ofBijective quotientToPlace
  constructor
  · intro a b h
    induction a using Quotient.inductionOn with
    | _ phi =>
      induction b using Quotient.inductionOn with
      | _ chi =>
        apply Quotient.sound
        exact congrArg Subtype.val h
  · intro w
    letI : AbsoluteValue.LiesOver w.1.1 v.1 :=
      infinite_lies_comap v w.1 w.2
    rcases
        InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq
          w.1 v with h | h
    · refine ⟨Quotient.mk _ ⟨w.1.embedding, h⟩, ?_⟩
      apply Subtype.ext
      exact InfinitePlace.mk_embedding w.1
    · refine
        ⟨Quotient.mk _
          ⟨NumberField.ComplexEmbedding.conjugate w.1.embedding, h⟩, ?_⟩
      apply Subtype.ext
      exact (InfinitePlace.mk_conjugate_eq w.1.embedding).trans
        (InfinitePlace.mk_embedding w.1)

/-- If the base infinite place is complex, passing from an embedding extending
the chosen representative of the base place to its associated infinite place
loses no information.  Complex conjugation cannot identify two such embeddings,
because it would also fix the nonreal base embedding. -/
noncomputable def complexExtensionsAbove
    (v : InfinitePlace K) (hv : v.IsComplex) :
    ComplexEmbeddingExtension (K := K) (L := L) v.embedding ≃
      {w : InfinitePlace L // w.comap (algebraMap K L) = v} := by
  let toPlace : ComplexEmbeddingExtension (K := K) (L := L) v.embedding →
      {w : InfinitePlace L // w.comap (algebraMap K L) = v} :=
    fun phi => ⟨InfinitePlace.mk phi.1, by
      rw [InfinitePlace.comap_mk, phi.2, InfinitePlace.mk_embedding]⟩
  apply Equiv.ofBijective toPlace
  constructor
  · intro phi chi h
    apply Subtype.ext
    have hm : InfinitePlace.mk phi.1 = InfinitePlace.mk chi.1 :=
      congrArg Subtype.val h
    rcases InfinitePlace.mk_eq_iff.mp hm with hEq | hConj
    · exact hEq
    · exfalso
      have hbase : NumberField.ComplexEmbedding.conjugate v.embedding =
          v.embedding := by
        calc
          NumberField.ComplexEmbedding.conjugate v.embedding =
              (NumberField.ComplexEmbedding.conjugate phi.1).comp
                (algebraMap K L) := by
            simpa only [NumberField.ComplexEmbedding.conjugate_comp] using
              congrArg NumberField.ComplexEmbedding.conjugate phi.2.symm
          _ = chi.1.comp (algebraMap K L) := by rw [hConj]
          _ = v.embedding := chi.2
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr hv)
        (InfinitePlace.isReal_iff.mpr
          (NumberField.ComplexEmbedding.isReal_iff.mpr hbase))
  · intro w
    letI : AbsoluteValue.LiesOver w.1.1 v.1 :=
      infinite_lies_comap v w.1 w.2
    rcases
        InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq
          w.1 v with h | h
    · refine ⟨⟨w.1.embedding, h⟩, ?_⟩
      apply Subtype.ext
      exact InfinitePlace.mk_embedding w.1
    · refine
        ⟨⟨NumberField.ComplexEmbedding.conjugate w.1.embedding, h⟩, ?_⟩
      apply Subtype.ext
      exact (InfinitePlace.mk_conjugate_eq w.1.embedding).trans
        (InfinitePlace.mk_embedding w.1)

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
private theorem completion_complex_minpoly
    (v : InfinitePlace K) (hv : v.IsComplex) (alpha : L) :
    ((minpoly K alpha).map (completionEmbedding v.1)).map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).toRingHom =
      (minpoly K alpha).map v.embedding := by
  rw [Polynomial.map_map]
  congr 1
  ext x
  change InfinitePlace.Completion.extensionEmbedding v
      (completionEmbedding v.1 x) = v.embedding x
  rw [completionEmbedding_apply]
  exact InfinitePlace.Completion.extensionEmbedding_coe v
    ((WithAbs.equiv v.1).symm x)

set_option maxHeartbeats 800000 in
-- Transporting all three subtype predicates through a polynomial ring
-- equivalence takes more elaboration than the default heartbeat allowance.
/-- For a complex infinite place, its completion is canonically isomorphic to
`ℂ`; this equivalence transports the completed irreducible factors to the
factors obtained by applying the chosen complex embedding coefficientwise. -/
noncomputable def completedMinpolyComplex
    (v : InfinitePlace K) (hv : v.IsComplex) (alpha : L) :
    CompletedMinpolyFactor v.1 alpha ≃
      ComplexCompletedMinpoly (K := K) v.embedding alpha := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
  let pe : v.1.Completion[X] ≃+* ℂ[X] := Polynomial.mapEquiv e
  apply Equiv.subtypeEquiv pe
  intro g
  change (Irreducible g ∧ g.Monic ∧
      g ∣ (minpoly K alpha).map (completionEmbedding v.1)) ↔
    (Irreducible (pe g) ∧ (pe g).Monic ∧
      pe g ∣ (minpoly K alpha).map v.embedding)
  rw [← completion_complex_minpoly v hv alpha]
  constructor
  · rintro ⟨hirr, hmonic, hdvd⟩
    exact ⟨hirr.map pe,
      by
        simpa [pe, Polynomial.mapEquiv_apply] using
          hmonic.map e.toRingHom,
      map_dvd pe hdvd⟩
  · rintro ⟨hirr, hmonic, hdvd⟩
    have hirr' : Irreducible (pe.symm (pe g)) := hirr.map pe.symm
    have hmonic' : (pe.symm (pe g)).Monic := by
      simpa [pe, Polynomial.mapEquiv_apply] using
        hmonic.map e.symm.toRingHom
    have hdvd' : pe.symm (pe g) ∣
        pe.symm (pe ((minpoly K alpha).map (completionEmbedding v.1))) :=
      map_dvd pe.symm hdvd
    simpa using And.intro hirr' (And.intro hmonic' hdvd')

omit [FiniteDimensional K L] [Algebra.IsSeparable K L] in
private theorem completion_real_minpoly
    (v : InfinitePlace K) (hv : v.IsReal) (alpha : L) :
    ((minpoly K alpha).map (completionEmbedding v.1)).map
        (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toRingHom =
      (minpoly K alpha).map (InfinitePlace.embedding_of_isReal hv) := by
  rw [Polynomial.map_map]
  congr 1
  ext x
  change InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
      (completionEmbedding v.1 x) =
    InfinitePlace.embedding_of_isReal hv x
  rw [completionEmbedding_apply]
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv
    ((WithAbs.equiv v.1).symm x)

set_option maxHeartbeats 800000 in
-- As in the complex case, transporting all subtype predicates through the
-- polynomial-ring equivalence requires a larger elaboration budget.
/-- For a real infinite place, its completion is canonically isomorphic to
`ℝ`; this transports completed factors to factors obtained from the
associated real embedding. -/
noncomputable def completedMinpolyReal
    (v : InfinitePlace K) (hv : v.IsReal) (alpha : L) :
    CompletedMinpolyFactor v.1 alpha ≃
      RealCompletedMinpoly (K := K)
        (InfinitePlace.embedding_of_isReal hv) alpha := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  let pe : v.1.Completion[X] ≃+* ℝ[X] := Polynomial.mapEquiv e
  apply Equiv.subtypeEquiv pe
  intro g
  change (Irreducible g ∧ g.Monic ∧
      g ∣ (minpoly K alpha).map (completionEmbedding v.1)) ↔
    (Irreducible (pe g) ∧ (pe g).Monic ∧
      pe g ∣ (minpoly K alpha).map
        (InfinitePlace.embedding_of_isReal hv))
  rw [← completion_real_minpoly v hv alpha]
  constructor
  · rintro ⟨hirr, hmonic, hdvd⟩
    exact ⟨hirr.map pe,
      by
        simpa [pe, Polynomial.mapEquiv_apply] using
          hmonic.map e.toRingHom,
      map_dvd pe hdvd⟩
  · rintro ⟨hirr, hmonic, hdvd⟩
    have hirr' : Irreducible (pe.symm (pe g)) := hirr.map pe.symm
    have hmonic' : (pe.symm (pe g)).Monic := by
      simpa [pe, Polynomial.mapEquiv_apply] using
        hmonic.map e.symm.toRingHom
    have hdvd' : pe.symm (pe g) ∣
        pe.symm (pe ((minpoly K alpha).map (completionEmbedding v.1))) :=
      map_dvd pe.symm hdvd
    simpa using And.intro hirr' (And.intro hmonic' hdvd')

/-- A place above a real infinite place determines the real minimal
polynomial of the image of the primitive element. -/
noncomputable def realInfiniteFactor
    (v : InfinitePlace K) (hv : v.IsReal) (alpha : L) :
    {w : InfinitePlace L // w.comap (algebraMap K L) = v} →
      RealCompletedMinpoly (K := K)
        (InfinitePlace.embedding_of_isReal hv) alpha := by
  intro W
  let z : ℂ := W.1.embedding alpha
  have hcomp : W.1.embedding.comp (algebraMap K L) = v.embedding :=
    infinite_embedding_real v hv W.1 W.2
  have hpEval : aeval z
      ((minpoly K alpha).map (InfinitePlace.embedding_of_isReal hv)) = 0 := by
    rw [aeval_def, eval₂_map]
    have hscalar :
        (algebraMap ℝ ℂ).comp (InfinitePlace.embedding_of_isReal hv) =
          W.1.embedding.comp (algebraMap K L) := by
      ext x
      rw [hcomp]
      exact InfinitePlace.embedding_of_isReal_apply hv x
    rw [hscalar, ← Polynomial.hom_eval₂]
    change W.1.embedding (aeval alpha (minpoly K alpha)) = 0
    rw [minpoly.aeval, map_zero]
  have hzIntegral : IsIntegral ℝ z := Algebra.IsIntegral.isIntegral z
  exact ⟨minpoly ℝ z, minpoly.irreducible hzIntegral,
    minpoly.monic hzIntegral, minpoly.dvd ℝ z hpEval⟩

/-- The real place-to-factor map is injective for a primitive element.  Equal
real minimal polynomials identify the two complex values by either the
identity or complex conjugation, which define the same infinite place. -/
theorem real_infinite_injective
    (v : InfinitePlace K) (hv : v.IsReal) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤) :
    Function.Injective (realInfiniteFactor v hv alpha) := by
  intro W₁ W₂ hfactor
  let z₁ : ℂ := W₁.1.embedding alpha
  let z₂ : ℂ := W₂.1.embedding alpha
  have hmin : minpoly ℝ z₁ = minpoly ℝ z₂ :=
    congrArg Subtype.val hfactor
  have hz₁root : z₁ ∈ (minpoly ℝ z₂).rootSet ℂ := by
    rw [mem_rootSet_of_ne
      (minpoly.ne_zero (Algebra.IsIntegral.isIntegral z₂)), ← hmin]
    exact minpoly.aeval ℝ z₁
  have hz₁range : z₁ ∈ Set.range fun sigma : ℂ →ₐ[ℝ] ℂ ↦ sigma z₂ := by
    rw [Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ z₂]
    exact hz₁root
  rcases hz₁range with ⟨sigma, hsigma⟩
  letI : Algebra K ℂ := v.embedding.toAlgebra
  have hcomp₁ : W₁.1.embedding.comp (algebraMap K L) = v.embedding :=
    infinite_embedding_real v hv W₁.1 W₁.2
  have hcomp₂ : W₂.1.embedding.comp (algebraMap K L) = v.embedding :=
    infinite_embedding_real v hv W₂.1 W₂.2
  let f₁ : L →ₐ[K] ℂ :=
    { toRingHom := W₁.1.embedding
      commutes' := fun x ↦ RingHom.congr_fun hcomp₁ x }
  let f₂ : L →ₐ[K] ℂ :=
    { toRingHom := W₂.1.embedding
      commutes' := fun x ↦ RingHom.congr_fun hcomp₂ x }
  have hevalInjective : Function.Injective fun f : L →ₐ[K] ℂ ↦ f alpha :=
    (Field.primitive_element_iff_algHom_eq_of_eval'
      K ℂ (fun _ ↦ IsAlgClosed.splits _) alpha).mp
        (IntermediateField.adjoin_eq_top_of_algebra
          (F := K) (E := L) (S := ({alpha} : Set L)) halpha)
  rcases Complex.real_algHom_eq_id_or_conj sigma with hid | hconj
  · have hz : z₂ = z₁ := by
      have hsigmaApply := DFunLike.congr_fun hid z₂
      exact hsigmaApply.symm.trans hsigma
    have hf : f₁ = f₂ := by
      apply hevalInjective
      exact hz.symm
    apply Subtype.ext
    apply InfinitePlace.embedding_injective L
    exact congrArg AlgHom.toRingHom hf
  · let f₂c : L →ₐ[K] ℂ :=
      { toRingHom := NumberField.ComplexEmbedding.conjugate W₂.1.embedding
        commutes' := fun x ↦ by
          change starRingEnd ℂ (W₂.1.embedding (algebraMap K L x)) =
            v.embedding x
          have hx := RingHom.congr_fun hcomp₂ x
          change W₂.1.embedding (algebraMap K L x) = v.embedding x at hx
          rw [hx]
          exact RingHom.congr_fun
            (InfinitePlace.conjugate_embedding_eq_of_isReal hv) x }
    have hz : f₂c alpha = f₁ alpha := by
      change starRingEnd ℂ z₂ = z₁
      have hsigmaApply := DFunLike.congr_fun hconj z₂
      exact hsigmaApply.symm.trans hsigma
    have hf : f₁ = f₂c := hevalInjective hz.symm
    apply Subtype.ext
    apply InfinitePlace.eq_of_embedding_eq_conjugate
    exact congrArg AlgHom.toRingHom hf

/-- Every real irreducible factor is obtained from an infinite place above
the real base place. -/
theorem real_infinite_surjective
    (v : InfinitePlace K) (hv : v.IsReal) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤) :
    Function.Surjective (realInfiniteFactor v hv alpha) := by
  intro G
  let p : ℝ[X] :=
    (minpoly K alpha).map (InfinitePlace.embedding_of_isReal hv)
  obtain ⟨z, hz⟩ : ∃ z : ℂ, aeval z G.1 = 0 :=
    IsAlgClosed.exists_aeval_eq_zero ℂ G.1
      (degree_pos_of_irreducible G.2.1).ne'
  have hzP : aeval z p = 0 := by
    rw [aeval_def] at hz ⊢
    exact eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
      (algebraMap ℝ ℂ) z G.2.2.2 hz
  have hmap : p.map (algebraMap ℝ ℂ) =
      (minpoly K alpha).map v.embedding := by
    rw [Polynomial.map_map]
    congr 1
    ext x
    exact InfinitePlace.embedding_of_isReal_apply hv x
  have hzComplex : z ∈ ((minpoly K alpha).map v.embedding).rootSet ℂ := by
    rw [← hmap]
    apply (mem_rootSet_of_ne
      (((minpoly.monic (Algebra.IsIntegral.isIntegral alpha)).map
        (InfinitePlace.embedding_of_isReal hv)).map
          (algebraMap ℝ ℂ)).ne_zero).2
    simpa [aeval_def, eval_map] using hzP
  let root : ((minpoly K alpha).map v.embedding).rootSet ℂ :=
    ⟨z, hzComplex⟩
  let E := complexEmbeddingSet v.embedding alpha halpha
  let phi : ComplexEmbeddingExtension (K := K) (L := L) v.embedding :=
    E.symm root
  have hphiAlpha : phi.1 alpha = z := by
    have h := congrArg Subtype.val (E.apply_symm_apply root)
    exact h
  let W : {w : InfinitePlace L // w.comap (algebraMap K L) = v} :=
    ⟨InfinitePlace.mk phi.1, by
      rw [InfinitePlace.comap_mk, phi.2, InfinitePlace.mk_embedding]⟩
  have hGmin : G.1 = minpoly ℝ z := by
    exact minpoly.eq_of_irreducible_of_monic G.2.1 hz G.2.2.1
  refine ⟨W, ?_⟩
  apply Subtype.ext
  change minpoly ℝ (W.1.embedding alpha) = G.1
  have hwEmbedding : W.1.embedding = phi.1 ∨
      W.1.embedding = NumberField.ComplexEmbedding.conjugate phi.1 := by
    exact InfinitePlace.embedding_mk_eq phi.1
  rcases hwEmbedding with h | h
  · rw [h, hphiAlpha]
    exact hGmin.symm
  · rw [h, NumberField.ComplexEmbedding.conjugate_coe_eq, hphiAlpha]
    exact (minpoly.algEquiv_eq Complex.conjAe z).trans hGmin.symm

/-- Milne, Proposition 8.1 for a real infinite base place, expressed first
over the canonically identified completion `ℝ`. -/
noncomputable def realPlacesAbove
    (v : InfinitePlace K) (hv : v.IsReal) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤) :
    {w : InfinitePlace L // w.comap (algebraMap K L) = v} ≃
      RealCompletedMinpoly (K := K)
        (InfinitePlace.embedding_of_isReal hv) alpha :=
  Equiv.ofBijective (realInfiniteFactor v hv alpha)
    ⟨real_infinite_injective v hv alpha halpha,
      real_infinite_surjective v hv alpha halpha⟩

/-- Milne, Proposition 8.1 for a real infinite base place: infinite places
above `v` are equivalent to the irreducible factors over its completion. -/
noncomputable def realCompletedMinpoly
    (v : InfinitePlace K) (hv : v.IsReal) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤) :
    {w : InfinitePlace L // w.comap (algebraMap K L) = v} ≃
      CompletedMinpolyFactor v.1 alpha :=
  (realPlacesAbove v hv alpha halpha).trans
    (completedMinpolyReal v hv alpha).symm

/-- Milne, Proposition 8.1 for a complex infinite base place: infinite places
of `L` above `v` are naturally in bijection with the monic irreducible factors
over the completion of `v` of the mapped minimal polynomial of a primitive
element. -/
noncomputable def complexCompletedMinpoly
    (v : InfinitePlace K) (hv : v.IsComplex) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤) :
    {w : InfinitePlace L // w.comap (algebraMap K L) = v} ≃
      CompletedMinpolyFactor v.1 alpha :=
  (complexExtensionsAbove v hv).symm.trans <|
    (complexEmbeddingMinpoly
      v.embedding alpha halpha).trans <|
        (completedMinpolyComplex v hv alpha).symm

/-- Milne, Proposition 8.1 for all infinite places.  The real case identifies
the completion with `ℝ`, while the complex case identifies it with `ℂ`. -/
noncomputable def placesAboveMinpoly
    (v : InfinitePlace K) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤) :
    {w : InfinitePlace L // w.comap (algebraMap K L) = v} ≃
      CompletedMinpolyFactor v.1 alpha := by
  classical
  by_cases hv : v.IsReal
  · exact realCompletedMinpoly
      v hv alpha halpha
  · exact complexCompletedMinpoly
      v (InfinitePlace.not_isReal_iff_isComplex.mp hv) alpha halpha

/-- The archimedean place-to-factor direction of Milne's Proposition 8.1.
Every infinite place above `v` determines the irreducible completed factor
given by the minimal polynomial of the image of the primitive element in the
corresponding completion. -/
def infiniteCompletedMinpoly
    (v : InfinitePlace K) (alpha : L) :
    {w : InfinitePlace L // w.comap (algebraMap K L) = v} →
      CompletedMinpolyFactor v.1 alpha :=
  fun w => absoluteMinpolyFactor v.1 alpha w.1.1
    (infinite_lies_comap v w.1 w.2)

/-- The factor-to-place construction for the archimedean half of
Proposition 8.1.  A completed factor acquires a root in `ℂ`; composing the
corresponding map out of `AdjoinRoot` with the primitive-element map produces
an infinite place of `L` above `v`. -/
noncomputable def completedMinpolyPlace
    (v : InfinitePlace K) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤) :
    CompletedMinpolyFactor v.1 alpha →
      {w : InfinitePlace L // w.comap (algebraMap K L) = v} := by
  intro G
  let e : v.1.Completion →+* ℂ := InfinitePlace.Completion.extensionEmbedding v
  let rootExists := IsAlgClosed.exists_eval₂_eq_zero e G.1
    (degree_pos_of_irreducible G.2.1).ne'
  let z : ℂ := Classical.choose rootExists
  have hz : eval₂ e z G.1 = 0 := Classical.choose_spec rootExists
  let rootMap : AdjoinRoot G.1 →+* ℂ := AdjoinRoot.lift e z hz
  let phi : L →ₐ[K] AdjoinRoot G.1 :=
    primitiveAdjoinRoot alpha halpha G.1 G.2.2.2
  let psi : L →+* ℂ := rootMap.comp phi.toRingHom
  refine ⟨InfinitePlace.mk psi, ?_⟩
  rw [InfinitePlace.comap_mk]
  have hpsi : psi.comp (algebraMap K L) = v.embedding := by
    ext x
    change rootMap (phi (algebraMap K L x)) = v.embedding x
    rw [AlgHom.commutes]
    change rootMap (algebraMap v.1.Completion (AdjoinRoot G.1)
      (completionEmbedding v.1 x)) = v.embedding x
    change (AdjoinRoot.lift e z hz)
      (AdjoinRoot.of G.1 (completionEmbedding v.1 x)) = v.embedding x
    rw [AdjoinRoot.lift_of hz]
    rw [completionEmbedding_apply]
    simp [e]
  rw [hpsi, InfinitePlace.mk_embedding]

set_option maxHeartbeats 800000 in
-- Comparing the two completion embeddings inside `ℂ` requires substantial
-- elaboration through nested `AdjoinRoot` and completion constructions.
/-- For a real infinite base place, converting a completed factor to an
infinite place and back recovers the factor.  The chosen complex root may be
replaced by its conjugate when passing to an infinite place, but the
coefficients coming from the real completion are fixed by conjugation. -/
theorem minpoly_roundtrip_real
    (v : InfinitePlace K) (hv : v.IsReal) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤)
    (G : CompletedMinpolyFactor v.1 alpha) :
    infiniteCompletedMinpoly v alpha
        (completedMinpolyPlace v alpha halpha G) = G := by
  apply Subtype.ext
  let e : v.1.Completion →+* ℂ :=
    InfinitePlace.Completion.extensionEmbedding v
  let rootExists := IsAlgClosed.exists_eval₂_eq_zero e G.1
    (degree_pos_of_irreducible G.2.1).ne'
  let z : ℂ := Classical.choose rootExists
  have hz : eval₂ e z G.1 = 0 := Classical.choose_spec rootExists
  let rootMap : AdjoinRoot G.1 →+* ℂ := AdjoinRoot.lift e z hz
  let phi : L →ₐ[K] AdjoinRoot G.1 :=
    primitiveAdjoinRoot alpha halpha G.1 G.2.2.2
  let psi : L →+* ℂ := rootMap.comp phi.toRingHom
  let W := completedMinpolyPlace v alpha halpha G
  let w : InfinitePlace L := W.1
  have hwv : w.comap (algebraMap K L) = v := W.2
  let hwvAbs : AbsoluteValue.LiesOver w.1 v.1 :=
    infinite_lies_comap v w hwv
  let iota : v.1.Completion →+* w.1.Completion :=
    completionLies v.1 w.1 hwvAbs
  letI : Algebra v.1.Completion w.1.Completion := iota.toAlgebra
  let beta : w.1.Completion := completionEmbedding w.1 alpha
  have heReal : NumberField.ComplexEmbedding.conjugate e = e := by
    ext x
    change starRingEnd ℂ (e x) = e x
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
    exact Complex.conj_ofReal _
  have heReal' : (starRingEnd ℂ).comp e = e := heReal
  have hpsiAlpha : psi alpha = z := by
    change rootMap (phi alpha) = z
    have hphiAlpha : phi alpha = AdjoinRoot.root G.1 := by
      unfold phi primitiveAdjoinRoot
      simpa only [PowerBasis.ofAdjoinEqTop_gen] using
        (PowerBasis.lift_gen
          (PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral alpha) halpha)
          (AdjoinRoot.root G.1) _)
    rw [hphiAlpha]
    exact AdjoinRoot.lift_root hz
  have hw_eq : w = InfinitePlace.mk psi := by
    rfl
  have hwEmbedding : w.embedding = psi ∨
      w.embedding = NumberField.ComplexEmbedding.conjugate psi := by
    rw [hw_eq]
    exact InfinitePlace.embedding_mk_eq psi
  have hroot : eval₂ e (InfinitePlace.Completion.extensionEmbedding w beta) G.1 = 0 := by
    change eval₂ e
      (InfinitePlace.Completion.extensionEmbedding w
        (completionEmbedding w.1 alpha)) G.1 = 0
    rw [completionEmbedding_apply,
      InfinitePlace.Completion.extensionEmbedding_coe]
    change eval₂ e (w.embedding alpha) G.1 = 0
    rcases hwEmbedding with h | h
    · rw [h, hpsiAlpha]
      exact hz
    · rw [h, NumberField.ComplexEmbedding.conjugate_coe_eq, hpsiAlpha]
      have hzConj := congrArg (starRingEnd ℂ) hz
      simpa only [map_zero, Polynomial.hom_eval₂, heReal'] using hzConj
  have hwEmbeddingOver :
      w.embedding.comp (algebraMap K L) = v.embedding := by
    letI : AbsoluteValue.LiesOver w.1 v.1 := hwvAbs
    rcases
        InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq
          w v with h | h
    · exact h
    · ext x
      have hx := RingHom.congr_fun h x
      change starRingEnd ℂ (w.embedding (algebraMap K L x)) =
        v.embedding x at hx
      calc
        w.embedding (algebraMap K L x) =
            starRingEnd ℂ (starRingEnd ℂ
              (w.embedding (algebraMap K L x))) :=
          (star_star _).symm
        _ = starRingEnd ℂ (v.embedding x) := congrArg (starRingEnd ℂ) hx
        _ = v.embedding x := by
          exact RingHom.congr_fun
            (InfinitePlace.conjugate_embedding_eq_of_isReal hv) x
  have hiota :
      (InfinitePlace.Completion.extensionEmbedding w).comp iota = e := by
    apply DFunLike.ext _ _
    exact congrFun ((dense_range_embedding v.1).equalizer
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
        (completion_lies_isometry v.1 w.1 hwvAbs).continuous)
      (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous
      (funext fun x ↦ by
        change InfinitePlace.Completion.extensionEmbedding w
            (iota (completionEmbedding v.1 x)) =
          InfinitePlace.Completion.extensionEmbedding v
            (completionEmbedding v.1 x)
        rw [show iota (completionEmbedding v.1 x) =
            completionEmbedding w.1 (algebraMap K L x) by
          exact RingHom.congr_fun
            (completion_lies_comp v.1 w.1 hwvAbs) x]
        rw [completionEmbedding_apply, completionEmbedding_apply]
        simpa using RingHom.congr_fun hwEmbeddingOver x))
  have hGeval : eval₂ iota beta G.1 = 0 := by
    apply (InfinitePlace.Completion.extensionEmbedding w).injective
    rw [map_zero, Polynomial.hom_eval₂]
    change eval₂
      ((InfinitePlace.Completion.extensionEmbedding w).comp iota)
      (InfinitePlace.Completion.extensionEmbedding w beta) G.1 = 0
    rw [hiota]
    exact hroot
  have hGdvd : minpoly v.1.Completion beta ∣ G.1 := by
    apply minpoly.dvd
    rw [aeval_def]
    exact hGeval
  have hminIrreducible : Irreducible (minpoly v.1.Completion beta) :=
    (infiniteCompletedMinpoly v alpha W).2.1
  have hminMonic : (minpoly v.1.Completion beta).Monic :=
    (infiniteCompletedMinpoly v alpha W).2.2.1
  change minpoly v.1.Completion beta = G.1
  exact eq_of_monic_of_associated hminMonic G.2.2.1
    (hminIrreducible.associated_of_dvd G.2.1 hGdvd)

set_option maxHeartbeats 1200000 in
-- Comparing the two completion embeddings inside `ℂ` requires substantial
-- elaboration through nested `AdjoinRoot` and completion constructions.
/-- Converting a completed factor to an infinite place and back recovers the
factor.  The proof compares the two possible complex embeddings representing
the resulting infinite place. -/
theorem completed_minpoly_roundtrip
    (v : InfinitePlace K) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤)
    (G : CompletedMinpolyFactor v.1 alpha) :
    infiniteCompletedMinpoly v alpha
        (completedMinpolyPlace v alpha halpha G) = G := by
  apply Subtype.ext
  let e : v.1.Completion →+* ℂ := InfinitePlace.Completion.extensionEmbedding v
  let rootExists := IsAlgClosed.exists_eval₂_eq_zero e G.1
    (degree_pos_of_irreducible G.2.1).ne'
  let z : ℂ := Classical.choose rootExists
  have hz : eval₂ e z G.1 = 0 := Classical.choose_spec rootExists
  let rootMap : AdjoinRoot G.1 →+* ℂ := AdjoinRoot.lift e z hz
  let phi : L →ₐ[K] AdjoinRoot G.1 :=
    primitiveAdjoinRoot alpha halpha G.1 G.2.2.2
  let psi : L →+* ℂ := rootMap.comp phi.toRingHom
  let W := completedMinpolyPlace v alpha halpha G
  let w : InfinitePlace L := W.1
  have hwv : w.comap (algebraMap K L) = v := W.2
  let hwvAbs : AbsoluteValue.LiesOver w.1 v.1 :=
    infinite_lies_comap v w hwv
  let iota : v.1.Completion →+* w.1.Completion :=
    completionLies v.1 w.1 hwvAbs
  letI : Algebra v.1.Completion w.1.Completion := iota.toAlgebra
  let beta : w.1.Completion := completionEmbedding w.1 alpha
  have hpsiBase : psi.comp (algebraMap K L) = v.embedding := by
    ext x
    change rootMap (phi (algebraMap K L x)) = v.embedding x
    rw [AlgHom.commutes]
    change rootMap (algebraMap v.1.Completion (AdjoinRoot G.1)
      (completionEmbedding v.1 x)) = v.embedding x
    change (AdjoinRoot.lift e z hz)
      (AdjoinRoot.of G.1 (completionEmbedding v.1 x)) = v.embedding x
    rw [AdjoinRoot.lift_of hz, completionEmbedding_apply]
    simp [e]
  have hpsiAlpha : psi alpha = z := by
    change rootMap (phi alpha) = z
    have hphiAlpha : phi alpha = AdjoinRoot.root G.1 := by
      unfold phi primitiveAdjoinRoot
      simpa only [PowerBasis.ofAdjoinEqTop_gen] using
        (PowerBasis.lift_gen
          (PowerBasis.ofAdjoinEqTop (Algebra.IsIntegral.isIntegral alpha) halpha)
          (AdjoinRoot.root G.1) _)
    rw [hphiAlpha]
    exact AdjoinRoot.lift_root hz
  have hwEmbedding : w.embedding = psi ∨
      w.embedding = NumberField.ComplexEmbedding.conjugate psi := by
    change (InfinitePlace.mk psi).embedding = psi ∨
      (InfinitePlace.mk psi).embedding = NumberField.ComplexEmbedding.conjugate psi
    exact InfinitePlace.embedding_mk_eq psi
  have hGeval : eval₂ iota beta G.1 = 0 := by
    rcases hwEmbedding with h | h
    · let E : w.1.Completion →+* ℂ :=
        InfinitePlace.Completion.extensionEmbedding w
      have hEbeta : E beta = z := by
        change InfinitePlace.Completion.extensionEmbedding w
          (completionEmbedding w.1 alpha) = z
        rw [completionEmbedding_apply,
          InfinitePlace.Completion.extensionEmbedding_coe]
        change w.embedding alpha = z
        rw [h, hpsiAlpha]
      have hEiota : E.comp iota = e := by
        apply DFunLike.ext _ _
        exact congrFun ((dense_range_embedding v.1).equalizer
          ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
            (completion_lies_isometry v.1 w.1 hwvAbs).continuous)
          (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous
          (funext fun x ↦ by
            change E (iota (completionEmbedding v.1 x)) =
              e (completionEmbedding v.1 x)
            rw [show iota (completionEmbedding v.1 x) =
                completionEmbedding w.1 (algebraMap K L x) by
              exact RingHom.congr_fun
                (completion_lies_comp v.1 w.1 hwvAbs) x]
            rw [completionEmbedding_apply, completionEmbedding_apply,
              InfinitePlace.Completion.extensionEmbedding_coe,
              InfinitePlace.Completion.extensionEmbedding_coe]
            change w.embedding (algebraMap K L x) = v.embedding x
            rw [h]
            exact RingHom.congr_fun hpsiBase x))
      apply E.injective
      rw [map_zero, Polynomial.hom_eval₂, hEiota, hEbeta]
      exact hz
    · let E : w.1.Completion →+* ℂ :=
        NumberField.ComplexEmbedding.conjugate
          (InfinitePlace.Completion.extensionEmbedding w)
      have hEbeta : E beta = z := by
        change starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w
          (completionEmbedding w.1 alpha)) = z
        rw [completionEmbedding_apply,
          InfinitePlace.Completion.extensionEmbedding_coe]
        change starRingEnd ℂ (w.embedding alpha) = z
        rw [h, NumberField.ComplexEmbedding.conjugate_coe_eq, hpsiAlpha]
        exact star_star z
      have hEiota : E.comp iota = e := by
        apply DFunLike.ext _ _
        exact congrFun ((dense_range_embedding v.1).equalizer
          ((Complex.continuous_conj.comp
              (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous).comp
            (completion_lies_isometry v.1 w.1 hwvAbs).continuous)
          (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous
          (funext fun x ↦ by
            change E (iota (completionEmbedding v.1 x)) =
              e (completionEmbedding v.1 x)
            rw [show iota (completionEmbedding v.1 x) =
                completionEmbedding w.1 (algebraMap K L x) by
              exact RingHom.congr_fun
                (completion_lies_comp v.1 w.1 hwvAbs) x]
            change starRingEnd ℂ
                (InfinitePlace.Completion.extensionEmbedding w
                  (completionEmbedding w.1 (algebraMap K L x))) =
              InfinitePlace.Completion.extensionEmbedding v
                (completionEmbedding v.1 x)
            rw [completionEmbedding_apply, completionEmbedding_apply,
              InfinitePlace.Completion.extensionEmbedding_coe,
              InfinitePlace.Completion.extensionEmbedding_coe]
            change starRingEnd ℂ (w.embedding (algebraMap K L x)) =
              v.embedding x
            rw [h, NumberField.ComplexEmbedding.conjugate_coe_eq]
            calc
              starRingEnd ℂ (starRingEnd ℂ (psi (algebraMap K L x))) =
                  psi (algebraMap K L x) := star_star _
              _ = v.embedding x := RingHom.congr_fun hpsiBase x))
      apply E.injective
      rw [map_zero, Polynomial.hom_eval₂, hEiota, hEbeta]
      exact hz
  have hGdvd : minpoly v.1.Completion beta ∣ G.1 := by
    apply minpoly.dvd
    rw [aeval_def]
    exact hGeval
  have hminIrreducible : Irreducible (minpoly v.1.Completion beta) :=
    (infiniteCompletedMinpoly v alpha W).2.1
  have hminMonic : (minpoly v.1.Completion beta).Monic :=
    (infiniteCompletedMinpoly v alpha W).2.2.1
  change minpoly v.1.Completion beta = G.1
  exact eq_of_monic_of_associated hminMonic G.2.2.1
    (hminIrreducible.associated_of_dvd G.2.1 hGdvd)

/-- The explicit place-to-factor map in the archimedean part of Proposition
8.1 is bijective. -/
theorem completed_minpoly_bijective
    (v : InfinitePlace K) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤) :
    Function.Bijective (infiniteCompletedMinpoly v alpha) := by
  classical
  let e := placesAboveMinpoly v alpha halpha
  letI : Finite (CompletedMinpolyFactor v.1 alpha) :=
    completed_minpoly_factor v.1 alpha
  letI : Fintype (CompletedMinpolyFactor v.1 alpha) := Fintype.ofFinite _
  letI : Fintype {w : InfinitePlace L // w.comap (algebraMap K L) = v} :=
    Fintype.ofEquiv (CompletedMinpolyFactor v.1 alpha) e.symm
  have hsurjective : Function.Surjective
      (infiniteCompletedMinpoly v alpha) := by
    intro G
    exact ⟨completedMinpolyPlace v alpha halpha G,
      completed_minpoly_roundtrip v alpha halpha G⟩
  exact (Fintype.bijective_iff_surjective_and_card _).2
    ⟨hsurjective, Fintype.card_congr e⟩

/-- The canonical form of Milne's Proposition 8.1, whose forward map is the
minimal polynomial in the corresponding completed extension. -/
noncomputable def infinitePlacesMinpoly
    (v : InfinitePlace K) (alpha : L)
    (halpha : Algebra.adjoin K {alpha} = ⊤) :
    {w : InfinitePlace L // w.comap (algebraMap K L) = v} ≃
      CompletedMinpolyFactor v.1 alpha :=
  Equiv.ofBijective (infiniteCompletedMinpoly v alpha)
    (completed_minpoly_bijective v alpha halpha)

end Archimedean

end

end Submission.NumberTheory.Milne
