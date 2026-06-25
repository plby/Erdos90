import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Submission.NumberTheory.Locals.KrasnerLemma


/-!
# Milne, Algebraic Number Theory, Exercise 7-7

The prime-to-residue-characteristic roots of unity in a local field inject
into its finite residue field.  We formulate the algebraic core for an
arbitrary local domain with finite residue field.  The hypothesis that the
natural number `n` is a unit is the intrinsic version of `n` being prime to
the residue characteristic.  We then construct Milne's Cauchy sequence of
weighted roots of unity in `PadicAlgCl p`, prove that convergence would force
infinitely many of those roots into one finite local extension by Krasner's
lemma, and conclude that `PadicAlgCl p` is not complete.
-/

namespace Submission.NumberTheory.Milne

open IsLocalRing ValuativeRel
open Filter IntermediateField
open scoped NormedField Topology Valued

noncomputable section

variable {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]

/-- Two `n`th roots of unity in a local domain have distinct residues when
`n` is a unit. -/
theorem residue_nat_cast
    {n : ℕ} (hn : IsUnit (n : A)) {a b : A}
    (ha : a ^ n = 1) (hb : b ^ n = 1)
    (hab : residue A a = residue A b) :
    a = b := by
  let s : A := ∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)
  have hmul : (a - b) * s = 0 := by
    rw [show (a - b) * s = a ^ n - b ^ n by
      exact (Commute.all a b).mul_geom_sum₂ n]
    rw [ha, hb, sub_self]
  have hsres : residue A s = (n : ResidueField A) * (residue A b) ^ (n - 1) := by
    rw [map_sum]
    calc
      ∑ i ∈ Finset.range n, residue A (a ^ i * b ^ (n - 1 - i)) =
          ∑ _i ∈ Finset.range n, (residue A b) ^ (n - 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [map_mul, map_pow, hab]
            rw [← pow_add]
            congr 1
            have hin : i < n := Finset.mem_range.mp hi
            omega
      _ = n • (residue A b) ^ (n - 1) := by simp
      _ = (n : ResidueField A) * (residue A b) ^ (n - 1) := by
        rw [nsmul_eq_mul]
  have hnres : (n : ResidueField A) ≠ 0 := by
    exact (hn.map (residue A)).ne_zero
  have hbres : residue A b ≠ 0 := by
    have hn0 : n ≠ 0 := by
      intro hnzero
      subst n
      simp at hn
    intro hbzero
    have : residue A (b ^ n) = 0 := by simp [map_pow, hbzero, hn0]
    simp [hb] at this
  have hs : s ≠ 0 := by
    intro hs0
    have : residue A s = 0 := by simp [hs0]
    rw [hsres] at this
    exact mul_ne_zero hnres (pow_ne_zero _ hbres) this
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hs)

/-- If a local domain has finite residue field and contains a primitive
`n`th root of unity, with `n` a unit, then `n` is at most the cardinality of
the residue field. -/
theorem primitive_residue_card
    [Finite (ResidueField A)] {n : ℕ} (hn : IsUnit (n : A))
    {zeta : A} (hzeta : IsPrimitiveRoot zeta n) :
    n ≤ Nat.card (ResidueField A) := by
  let f : Fin n → ResidueField A := fun i ↦ residue A (zeta ^ (i : ℕ))
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply hzeta.pow_inj i.isLt j.isLt
    have hi : (zeta ^ (i : ℕ)) ^ n = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hzeta.pow_eq_one, one_pow]
    have hj : (zeta ^ (j : ℕ)) ^ n = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hzeta.pow_eq_one, one_pow]
    exact residue_nat_cast hn
      hi hj hij
  simpa using Nat.card_le_card_of_injective f hf

/-- **Milne, Exercise 7-7, finiteness assertion.** In a local domain with
finite residue field, only finitely many orders of primitive roots of unity
can be prime to the residue characteristic. -/
theorem primitive_orders_cast
    [Finite (ResidueField A)] :
    {n : ℕ | IsUnit (n : A) ∧ ∃ zeta : A, IsPrimitiveRoot zeta n}.Finite := by
  apply Set.Finite.subset (Set.finite_Iic (Nat.card (ResidueField A)))
  intro n hn
  exact primitive_residue_card hn.1 hn.2.choose_spec

/-- The local-field specialization of Exercise 7-7.  Its valuation ring
contains primitive roots of only finitely many orders invertible in that
valuation ring. -/
theorem integer_primitive_orders
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    {n : ℕ | IsUnit (n : 𝒪[K]) ∧
      ∃ zeta : 𝒪[K], IsPrimitiveRoot zeta n}.Finite :=
  primitive_orders_cast

/-- **Milne, Exercise 7-7.** A nonarchimedean local field contains primitive
roots of only finitely many orders invertible in its valuation ring.  Every
root of unity has valuation one, so the preceding valuation-ring theorem
applies to roots in the field itself. -/
theorem primitive_root_orders
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    {n : ℕ | IsUnit (n : 𝒪[K]) ∧
      ∃ zeta : K, IsPrimitiveRoot zeta n}.Finite := by
  apply (integer_primitive_orders K).subset
  intro n hn
  obtain ⟨hnunit, zeta, hzeta⟩ := hn
  have hn0 : n ≠ 0 := by
    intro hnzero
    subst n
    simp at hnunit
  have hzetaVal : valuation K zeta = 1 := by
    apply (pow_eq_one_iff_of_nonneg (bot_le : 0 ≤ valuation K zeta) hn0).mp
    rw [← map_pow, hzeta.pow_eq_one, map_one]
  let zetaInteger : 𝒪[K] :=
    ⟨zeta, (Valuation.mem_integer_iff (valuation K) zeta).mpr hzetaVal.le⟩
  have hzetaInteger : IsPrimitiveRoot zetaInteger n := by
    apply IsPrimitiveRoot.of_map_of_injective (f := (𝒪[K]).subtype)
    · simpa [zetaInteger] using hzeta
    · exact Subtype.coe_injective
  exact ⟨hnunit, zetaInteger, hzetaInteger⟩

/-- Indexed-family form of Exercise 7-7: among any chosen family `zeta n`,
only finitely many prime-to-residue-characteristic indices can have `zeta n`
as a primitive `n`th root lying in the local field. -/
theorem primitive_root_indices
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (zeta : ℕ → K) :
    {n : ℕ | IsUnit (n : 𝒪[K]) ∧ IsPrimitiveRoot (zeta n) n}.Finite := by
  apply (primitive_root_orders K).subset
  intro n hn
  exact ⟨hn.1, zeta n, hn.2⟩

/-- A nonzero root of unity has norm one in any normed field. -/
theorem norm_primitive_root
    {F : Type*} [NormedField F] {n : ℕ} (hn : n ≠ 0)
    {zeta : F} (hzeta : IsPrimitiveRoot zeta n) :
    ‖zeta‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg zeta) hn).mp
  rw [← norm_pow, hzeta.pow_eq_one, norm_one]

/-- A natural number prime to `p` is a unit in the valuation ring of the
`p`-adic algebraic closure. -/
theorem cast_cl_integer
    (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : p.Coprime n) :
    IsUnit (n : Valued.integer (PadicAlgCl p)) := by
  rw [Valued.integer.isUnit_iff_norm_eq_one]
  change ‖(n : PadicAlgCl p)‖ = 1
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)),
    PadicAlgCl.norm_extends]
  exact Padic.norm_natCast_eq_one_iff.mpr hn

/-- Distinct primitive roots of the same order prime to `p` are a unit
distance apart in the `p`-adic algebraic closure. -/
theorem sub_primitive_roots
    (p : ℕ) [Fact p.Prime]
    {n : ℕ} (hn0 : n ≠ 0) (hn : p.Coprime n)
    {zeta xi : PadicAlgCl p}
    (hzeta : IsPrimitiveRoot zeta n) (hxi : IsPrimitiveRoot xi n)
    (hne : zeta ≠ xi) :
    ‖zeta - xi‖ = 1 := by
  have hzNorm : ‖zeta‖ = 1 := norm_primitive_root hn0 hzeta
  have hxNorm : ‖xi‖ = 1 := norm_primitive_root hn0 hxi
  let zetaInt : Valued.integer (PadicAlgCl p) :=
    ⟨zeta, (Valued.integer.mem_iff).mpr hzNorm.le⟩
  let xiInt : Valued.integer (PadicAlgCl p) :=
    ⟨xi, (Valued.integer.mem_iff).mpr hxNorm.le⟩
  have hnunit : IsUnit (n : Valued.integer (PadicAlgCl p)) :=
    cast_cl_integer p hn
  have hresne : residue (Valued.integer (PadicAlgCl p)) zetaInt ≠
      residue (Valued.integer (PadicAlgCl p)) xiInt := by
    intro heq
    apply hne
    exact congrArg Subtype.val
      (residue_nat_cast hnunit
        (by apply Subtype.ext; simpa [zetaInt] using hzeta.pow_eq_one)
        (by apply Subtype.ext; simpa [xiInt] using hxi.pow_eq_one) heq)
  have hsubunit : IsUnit (zetaInt - xiInt) := by
    have hnotmem : zetaInt - xiInt ∉
        IsLocalRing.maximalIdeal (Valued.integer (PadicAlgCl p)) := by
      intro hmem
      have hzero : residue (Valued.integer (PadicAlgCl p))
          (zetaInt - xiInt) = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr hmem
      apply hresne
      rw [← sub_eq_zero, ← map_sub]
      exact hzero
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Classical.not_not] at hnotmem
    exact hnotmem
  have hnorm := Valued.integer.isUnit_iff_norm_eq_one.mp hsubunit
  simpa [zetaInt, xiInt] using hnorm

/-- The partial sums used in Milne's proof, allowing any injective sequence
of prime-to-`p` orders. -/
def clUnityPartial
    (p : ℕ) [Fact p.Prime] (zeta : ℕ → PadicAlgCl p) (t : ℕ) :
    PadicAlgCl p :=
  ∑ i ∈ Finset.range t, zeta i * (p : PadicAlgCl p) ^ i

/-- The first root of unity moved by an automorphism gives the exact norm of
the displacement of a partial sum. -/
theorem cl_unity_separation
    (p : ℕ) [Fact p.Prime]
    (order : ℕ → ℕ) (zeta : ℕ → PadicAlgCl p)
    (horder0 : ∀ i, order i ≠ 0)
    (hcoprime : ∀ i, p.Coprime (order i))
    (hzeta : ∀ i, IsPrimitiveRoot (zeta i) (order i)) :
    ∀ t (sigma : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      sigma (clUnityPartial p zeta t) ≠
          clUnityPartial p zeta t →
      ∃ j < t,
        ‖sigma (clUnityPartial p zeta t) -
            clUnityPartial p zeta t‖ =
          ‖(p : PadicAlgCl p)‖ ^ j := by
  have hpNorm : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)),
      PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hpNormPos : 0 < ‖(p : PadicAlgCl p)‖ := norm_pos_iff.mpr (by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p))]
    exact (map_ne_zero (algebraMap ℚ_[p] (PadicAlgCl p))).mpr
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
  intro t
  induction t with
  | zero => simp [clUnityPartial]
  | succ t ih =>
      intro sigma hmove
      have hsum :
          clUnityPartial p zeta (t + 1) =
            clUnityPartial p zeta t +
              zeta t * (p : PadicAlgCl p) ^ t := by
        simp [clUnityPartial, Finset.sum_range_succ]
      by_cases hprev : sigma (clUnityPartial p zeta t) =
          clUnityPartial p zeta t
      · have hzmove : sigma (zeta t) ≠ zeta t := by
          intro hz
          apply hmove
          rw [hsum, map_add, map_mul, hz, hprev]
          simp
        refine ⟨t, Nat.lt_succ_self t, ?_⟩
        have hzsigma : IsPrimitiveRoot (sigma (zeta t)) (order t) :=
          (hzeta t).map_of_injective sigma.injective
        have hsigmap : sigma (p : PadicAlgCl p) = p := map_natCast sigma p
        have heq :
            sigma (clUnityPartial p zeta t +
                zeta t * (p : PadicAlgCl p) ^ t) -
              (clUnityPartial p zeta t +
                zeta t * (p : PadicAlgCl p) ^ t) =
              (sigma (zeta t) - zeta t) * (p : PadicAlgCl p) ^ t := by
          rw [map_add, map_mul, map_pow, hprev, hsigmap]
          ring
        rw [hsum, heq, norm_mul, norm_pow]
        rw [sub_primitive_roots p (horder0 t) (hcoprime t)
          hzsigma (hzeta t) hzmove, one_mul]
      · obtain ⟨j, hj, hnorm⟩ := ih sigma hprev
        refine ⟨j, hj.trans (Nat.lt_succ_self t), ?_⟩
        have hterm :
            ‖(sigma (zeta t) - zeta t) * (p : PadicAlgCl p) ^ t‖ <
              ‖sigma (clUnityPartial p zeta t) -
                clUnityPartial p zeta t‖ := by
          rw [hnorm, norm_mul, norm_pow]
          by_cases hz : sigma (zeta t) = zeta t
          · simp [hz, pow_pos hpNormPos]
          · have hzsigma : IsPrimitiveRoot (sigma (zeta t)) (order t) :=
              (hzeta t).map_of_injective sigma.injective
            rw [sub_primitive_roots p (horder0 t) (hcoprime t)
              hzsigma (hzeta t) hz, one_mul]
            exact pow_lt_pow_right_of_lt_one₀ hpNormPos hpNorm hj
        have hsigmap : sigma (p : PadicAlgCl p) = p := map_natCast sigma p
        have heq :
            sigma (clUnityPartial p zeta t +
                zeta t * (p : PadicAlgCl p) ^ t) -
              (clUnityPartial p zeta t +
                zeta t * (p : PadicAlgCl p) ^ t) =
              (sigma (clUnityPartial p zeta t) -
                clUnityPartial p zeta t) +
                ((sigma (zeta t) - zeta t) * (p : PadicAlgCl p) ^ t) := by
          rw [map_add, map_mul, map_pow, hsigmap]
          ring
        rw [hsum, heq]
        rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hterm.ne.symm,
          max_eq_left hterm.le, hnorm]

/-- The distance between two partial sums is bounded by the first omitted
power of `p`. -/
theorem padic_cl_unity
    (p : ℕ) [Fact p.Prime]
    (zeta : ℕ → PadicAlgCl p) (hzetaNorm : ∀ i, ‖zeta i‖ = 1) :
    ∀ {t s : ℕ}, t ≤ s →
      ‖clUnityPartial p zeta t -
          clUnityPartial p zeta s‖ ≤
        ‖(p : PadicAlgCl p)‖ ^ t := by
  have hpNormLe : ‖(p : PadicAlgCl p)‖ ≤ 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)),
      PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one.le
  intro t s hts
  induction s with
  | zero =>
      have : t = 0 := Nat.eq_zero_of_le_zero hts
      subst t
      simp [clUnityPartial]
  | succ s ih =>
      by_cases hteq : t = s + 1
      · subst t
        simp
      · have hts' : t ≤ s := Nat.le_of_lt_succ (lt_of_le_of_ne hts hteq)
        have hsum :
            clUnityPartial p zeta (s + 1) =
              clUnityPartial p zeta s +
                zeta s * (p : PadicAlgCl p) ^ s := by
          simp [clUnityPartial, Finset.sum_range_succ]
        have heq :
            clUnityPartial p zeta t -
                clUnityPartial p zeta (s + 1) =
              (clUnityPartial p zeta t -
                clUnityPartial p zeta s) +
                (-(zeta s * (p : PadicAlgCl p) ^ s)) := by
          rw [hsum]
          ring
        rw [heq]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
        · exact ih hts'
        · rw [norm_neg, norm_mul, norm_pow, hzetaNorm s, one_mul]
          exact pow_le_pow_of_le_one (norm_nonneg _) hpNormLe hts'

/-- If the partial sums converge, their distance from the limit is bounded by
the first omitted power of `p`. -/
theorem cl_unity_partial
    (p : ℕ) [Fact p.Prime]
    (zeta : ℕ → PadicAlgCl p) (hzetaNorm : ∀ i, ‖zeta i‖ = 1)
    {beta : PadicAlgCl p}
    (hlim : Tendsto (clUnityPartial p zeta) atTop (𝓝 beta))
    (t : ℕ) :
    ‖clUnityPartial p zeta t - beta‖ ≤
      ‖(p : PadicAlgCl p)‖ ^ t := by
  have htend : Tendsto
      (fun s ↦ ‖clUnityPartial p zeta t -
        clUnityPartial p zeta s‖)
      atTop (𝓝 ‖clUnityPartial p zeta t - beta‖) := by
    exact tendsto_norm.comp (tendsto_const_nhds.sub hlim)
  apply le_of_tendsto htend
  exact eventually_atTop.2 ⟨t, fun s hs ↦
    padic_cl_unity p zeta hzetaNorm hs⟩

/-- Convergence makes every sufficiently long partial sum closer to the limit
than to any distinct `ℚ_[p]`-conjugate, which is the hypothesis of Krasner's
lemma. -/
theorem cl_krasner_close
    (p : ℕ) [Fact p.Prime]
    (order : ℕ → ℕ) (zeta : ℕ → PadicAlgCl p)
    (horder0 : ∀ i, order i ≠ 0)
    (hcoprime : ∀ i, p.Coprime (order i))
    (hzeta : ∀ i, IsPrimitiveRoot (zeta i) (order i))
    {beta : PadicAlgCl p}
    (hlim : Tendsto (clUnityPartial p zeta) atTop (𝓝 beta)) :
    ∀ᶠ t in atTop,
      ∀ sigma : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        sigma (clUnityPartial p zeta t) ≠
            clUnityPartial p zeta t →
          ‖clUnityPartial p zeta t - beta‖ <
            ‖sigma (clUnityPartial p zeta t) -
              clUnityPartial p zeta t‖ := by
  have hpNorm : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)),
      PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hpNormPos : 0 < ‖(p : PadicAlgCl p)‖ := norm_pos_iff.mpr (by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p))]
    exact (map_ne_zero (algebraMap ℚ_[p] (PadicAlgCl p))).mpr
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
  have hzetaNorm : ∀ i, ‖zeta i‖ = 1 := fun i ↦
    norm_primitive_root (horder0 i) (hzeta i)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with t _ht sigma hmove
  obtain ⟨j, hj, hsep⟩ :=
    cl_unity_separation
      p order zeta horder0 hcoprime hzeta t sigma hmove
  calc
    ‖clUnityPartial p zeta t - beta‖ ≤
        ‖(p : PadicAlgCl p)‖ ^ t :=
      cl_unity_partial
        p zeta hzetaNorm hlim t
    _ < ‖(p : PadicAlgCl p)‖ ^ j :=
      pow_lt_pow_right_of_lt_one₀ hpNormPos hpNorm hj
    _ = ‖sigma (clUnityPartial p zeta t) -
        clUnityPartial p zeta t‖ := hsep.symm

/-- The prime-to-`p` orders of primitive roots lying in the finite extension
`ℚ_[p]⟮beta⟯` form a finite set. -/
theorem primitive_orders_cl
    (p : ℕ) [Fact p.Prime] (beta : PadicAlgCl p) :
    {n : ℕ | n.Coprime p ∧
      ∃ zeta : ℚ_[p]⟮beta⟯, IsPrimitiveRoot zeta n}.Finite := by
  let L := ℚ_[p]⟮beta⟯
  let hUltra : IsUltrametricDist L := inferInstance
  let v : Valuation L NNReal := @NormedField.valuation L inferInstance hUltra
  let valued : Valued L NNReal := @NormedField.toValued L inferInstance hUltra
  let metricUniform : UniformSpace L := PseudoMetricSpace.toUniformSpace
  have htop : valued.toTopologicalSpace = metricUniform.toTopologicalSpace := rfl
  letI : UniformSpace L := metricUniform
  letI : TopologicalSpace L := metricUniform.toTopologicalSpace
  letI : IsUniformAddGroup L := valued.toIsUniformAddGroup
  letI : FiniteDimensional ℚ_[p] L :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral beta)
  letI : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  letI : LocallyCompactSpace L := inferInstance
  letI : ValuativeRel L := ValuativeRel.ofValuation v
  haveI : v.Compatible := Valuation.Compatible.ofValuation _
  haveI : IsValuativeTopology L := by
    constructor
    intro s x
    have hmem := @Valued.mem_nhds L _ NNReal _ valued s x
    rw [htop] at hmem
    rw [hmem]
    change (∃ gamma : (MonoidWithZeroHom.ValueGroup₀ v)ˣ,
      {y | v.restrict (y - x) < gamma.1} ⊆ s) ↔ _
    rw [v.exists_setOf_restrict_le_iff x s]
    apply exists_congr
    intro gamma
    constructor
    · intro h y hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact h (by simpa)
    · intro h y hy
      apply h
      exact ⟨y - x, hy, by simp⟩
  haveI : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial v).mpr inferInstance
  haveI : IsNonarchimedeanLocalField L := {
    toIsValuativeTopology := inferInstance
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := inferInstance
  }
  have natCast_isUnit {n : ℕ} (hn : n.Coprime p) :
      IsUnit (n : Valuation.integer (ValuativeRel.valuation L)) := by
    apply (Valuation.integer.integers (ValuativeRel.valuation L)).isUnit_iff_valuation_eq_one.mpr
    change ValuativeRel.valuation L (n : L) = 1
    rw [← (ValuativeRel.isEquiv v (ValuativeRel.valuation L)).eq_one_iff_eq_one]
    change ‖(n : L)‖₊ = 1
    rw [← NNReal.coe_inj]
    change ‖(n : PadicAlgCl p)‖ = 1
    calc
      ‖(n : PadicAlgCl p)‖ = ‖(n : ℚ_[p])‖ := by
        rw [show (n : PadicAlgCl p) =
          algebraMap ℚ_[p] (PadicAlgCl p) (n : ℚ_[p]) by simp,
          PadicAlgCl.norm_extends]
      _ = 1 := (Padic.norm_natCast_eq_one_iff (p := p)).mpr hn.symm
  apply (primitive_root_orders L).subset
  intro n hn
  exact ⟨natCast_isUnit hn.1, hn.2⟩

/-- **Milne, Exercise 7-7, nonconvergence assertion.** For an injective
sequence of nonzero orders prime to `p`, the associated weighted primitive
roots have partial sums that cannot converge inside `PadicAlgCl p`. -/
theorem cl_unity_tendsto
    (p : ℕ) [Fact p.Prime]
    (order : ℕ → ℕ) (horderInj : Function.Injective order)
    (zeta : ℕ → PadicAlgCl p)
    (horder0 : ∀ i, order i ≠ 0)
    (hcoprime : ∀ i, p.Coprime (order i))
    (hzeta : ∀ i, IsPrimitiveRoot (zeta i) (order i))
    (beta : PadicAlgCl p) :
    ¬Tendsto (clUnityPartial p zeta) atTop (𝓝 beta) := by
  intro hlim
  have hclose := cl_krasner_close
    p order zeta horder0 hcoprime hzeta hlim
  let L := ℚ_[p]⟮beta⟯
  have hmem : ∀ᶠ t in atTop,
      clUnityPartial p zeta t ∈ L := by
    filter_upwards [hclose] with t ht
    let a := clUnityPartial p zeta t
    have hle : ℚ_[p]⟮a⟯ ≤ L :=
      krasner_adjoin_galois (PadicAlgCl.isNonarchimedean p) (by
        intro sigma hsigma
        exact ht sigma hsigma)
    exact hle (IntermediateField.mem_adjoin_simple_self ℚ_[p] a)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmem
  let T : Set ℕ := {n : ℕ | n.Coprime p ∧
    ∃ z : L, IsPrimitiveRoot z n}
  have hT : T.Finite :=
    primitive_orders_cl p beta
  have hpre : (order ⁻¹' T).Finite := hT.preimage horderInj.injOn
  obtain ⟨t, -, htNot⟩ := Set.infinite_univ.exists_notMem_finite
    (hpre.union (Set.finite_Iio N))
  have htPre : t ∉ order ⁻¹' T := fun ht ↦ htNot (Or.inl ht)
  have htIio : t ∉ Set.Iio N := fun ht ↦ htNot (Or.inr ht)
  have hNt : N ≤ t := Nat.le_of_not_gt htIio
  have hat : clUnityPartial p zeta t ∈ L := hN t hNt
  have hatsucc : clUnityPartial p zeta (t + 1) ∈ L :=
    hN (t + 1) (hNt.trans t.le_succ)
  have hterm : zeta t * (p : PadicAlgCl p) ^ t ∈ L := by
    have hsub := L.sub_mem hatsucc hat
    simpa [clUnityPartial, Finset.sum_range_succ] using hsub
  have hpMem : (p : PadicAlgCl p) ^ t ∈ L := by
    apply L.toSubfield.pow_mem
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p))]
    exact L.algebraMap_mem (p : ℚ_[p])
  have hpNe : (p : PadicAlgCl p) ^ t ≠ 0 := by
    apply pow_ne_zero
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p))]
    exact (map_ne_zero (algebraMap ℚ_[p] (PadicAlgCl p))).mpr
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hzmem : zeta t ∈ L := by
    have hdiv := L.div_mem hterm hpMem
    simpa [hpNe] using hdiv
  let zL : L := ⟨zeta t, hzmem⟩
  have hzL : IsPrimitiveRoot zL (order t) := by
    apply IsPrimitiveRoot.of_map_of_injective (f := L.val)
    · simpa [zL] using hzeta t
    · exact Subtype.coe_injective
  apply htPre
  exact ⟨(hcoprime t).symm, zL, hzL⟩

/-- The weighted root-of-unity partial sums are Cauchy. -/
theorem cauchy_cl_unity
    (p : ℕ) [Fact p.Prime]
    (zeta : ℕ → PadicAlgCl p) (hzeta : ∀ n, ‖zeta n‖ ≤ 1) :
    CauchySeq (clUnityPartial p zeta) := by
  have hp : ‖(p : PadicAlgCl p)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)),
      PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hg : Summable (fun n : ℕ ↦ ‖(p : PadicAlgCl p)‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg _) hp
  apply cauchySeq_range_of_norm_bounded hg.hasSum.tendsto_sum_nat.cauchySeq
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (hzeta n)

/-- **Milne, Exercise 7-7.** The algebraic closure of `ℚ_[p]`, equipped with
the uniquely extended `p`-adic norm, is not complete. -/
theorem padic_cl_complete (p : ℕ) [Fact p.Prime] :
    ¬CompleteSpace (PadicAlgCl p) := by
  intro hcomplete
  letI : CompleteSpace (PadicAlgCl p) := hcomplete
  let order : ℕ → ℕ := fun i ↦ p * i + 1
  choose zeta hzeta using fun i ↦
    HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (order i)
  have horder0 : ∀ i, order i ≠ 0 := by
    intro i
    dsimp [order]
    omega
  have hcoprime : ∀ i, p.Coprime (order i) := by
    intro i
    have h := (Nat.coprime_add_mul_left_right p 1 i).2
      (Nat.coprime_one_right p)
    simp [order]
  have horderInj : Function.Injective order := by
    intro i j hij
    dsimp [order] at hij
    exact Nat.mul_left_cancel (Fact.out : p.Prime).pos (Nat.add_right_cancel hij)
  have hcauchy : CauchySeq (clUnityPartial p zeta) :=
    cauchy_cl_unity p zeta
      (fun i ↦ (norm_primitive_root (horder0 i) (hzeta i)).le)
  obtain ⟨beta, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact cl_unity_tendsto
    p order horderInj zeta horder0 hcoprime hzeta beta hlim

end

end Submission.NumberTheory.Milne
