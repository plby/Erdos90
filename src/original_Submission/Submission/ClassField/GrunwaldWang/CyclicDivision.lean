import Submission.ClassField.NormCorrespondence.LocalStatements
import Submission.ClassField.BrauerGroups.CentralDivisionCSA
import Submission.ClassField.CrossedProducts.SubalgebraField
import Submission.ClassField.CrossedProducts.SplitNonemptyHom
import Submission.ClassField.CrossedProducts.FiniteExtensionExponent
import Submission.ClassField.GrunwaldWang.PossibleInfiniteDegree

/-!
# Chapter VIII, Section 2: cyclic splitting fields of division algebras

Theorem 2.6 uses Grunwald--Wang and the global Brauer invariant sequence to
construct a cyclic splitting field of the correct degree.  This file isolates
that global construction and the period computation as two narrow inputs.
Everything after their construction--embedding the field, proving that its
image is maximal commutative, and retaining the splitting assertion--is
proved from the existing central-simple-algebra API.
-/

namespace Submission.CField.GWang

open scoped IsMulCommutative

open Submission.CField.LFTheory

/-- The numerical endpoint in the proof of Theorem 2.6.  If `n ∣ d` and
`r^2 d^2 = n^2` with `n > 0`, then necessarily `r = 1` and `n = d`. -/
theorem matrix_size_degree
    {r d n : ℕ} (hn : 0 < n) (hnd : n ∣ d)
    (hdim : r ^ 2 * d ^ 2 = n ^ 2) :
    r = 1 ∧ n = d := by
  obtain ⟨k, rfl⟩ := hnd
  have hcancel : (r * k) ^ 2 = 1 := by
    apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < n ^ 2)
    calc
      (r * k) ^ 2 * n ^ 2 = r ^ 2 * (n * k) ^ 2 := by ring
      _ = n ^ 2 := hdim
      _ = 1 * n ^ 2 := by simp
  have hrk : r * k = 1 := by simpa using hcancel
  have hr : r = 1 := Nat.dvd_one.mp ⟨k, hrk.symm⟩
  have hk : k = 1 := Nat.dvd_one.mp ⟨r, by simpa [Nat.mul_comm] using hrk.symm⟩
  exact ⟨hr, by simp [hk]⟩

universe u

variable (K L D : Type u) [Field K] [Field L] [Algebra K L]
  [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [Module.Finite K D] [Module.Finite K L]

/-- **Theorem 2.6, conditional algebraic conclusion.** A cyclic extension of
the degree of a central division algebra embeds as a maximal subfield as soon
as it is known to split the algebra.  Grunwald--Wang is used in the source to
produce `L` and the splitting hypothesis. -/
theorem cyclic_splitting_embeds
    (n : ℕ) [IsGalois K L] [IsCyclic Gal(L/K)]
    (hD : Module.finrank K D = n ^ 2)
    (hL : Module.finrank K L = n)
    (hsplit : BGroups.ISBy K L D) :
    Nonempty (L →ₐ[K] D) :=
  (CProduca.split_nonempty_alg K L D n hD hL).mp hsplit

/-- Backwards-compatible name for the full statement. -/
abbrev DivisionCyclicityTheorem
    (K : Type u) [Field K] [NumberField K] : Prop :=
  (∀ (D : Type u) [DivisionRing D] [Algebra K D]
          [Algebra.IsCentral K D] [Module.Finite K D],
        orderOf (BGroups.brauerClass K (BGroups.centralDivisionCSA K D)) =
            Nat.sqrt (Module.finrank K D) ∧
          ∃ L : FASubext K,
            IsCyclic Gal(L.1/K) ∧
              ∃ i : L.1 →ₐ[K] D,
                CProduca.IsMaximalCommutative i.range ∧ BGroups.ISBy K L.1 D)

/-- The period computation in Theorem 2.6.  In the source this follows from
the global invariant sequence by taking the least common denominator of the
local invariants. -/
def PeriodDegreeBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (D : Type u) [DivisionRing D] [Algebra K D]
      [Algebra.IsCentral K D] [Module.Finite K D],
    orderOf (BGroups.brauerClass K (BGroups.centralDivisionCSA K D)) =
      Nat.sqrt (Module.finrank K D)

/-- The Grunwald--Wang construction in the source: there is a cyclic global
extension whose degree is the period of `D` and which splits `D`.  The bridge
does not assume the period--degree equality, an embedding, or maximality;
those are supplied separately or proved below. -/
def CyclicSplittingBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (D : Type u) [DivisionRing D] [Algebra K D]
      [Algebra.IsCentral K D] [Module.Finite K D],
    ∃ L : FASubext K,
      IsCyclic Gal(L.1/K) ∧
        Module.finrank K L.1 =
          orderOf (BGroups.brauerClass K (BGroups.centralDivisionCSA K D)) ∧
          BGroups.ISBy K L.1 D

/-- Regard the abstract cyclic number-field extension produced by Corollary
2.5 as a bundled finite abelian extension. -/
noncomputable def CEDataa.abelianExtension
    {K : Type u} [Field K] [NumberField K]
    (data : CEDataa K) :
    FAExt K := by
  letI : Field data.L := data.fieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  letI : IsCyclic Gal(data.L/K) := data.isCyclicKL
  exact
    { carrier := data.L
      field := inferInstance
      algebra := inferInstance
      finiteDimensional := inferInstance
      isGalois := inferInstance
      isAbelian := IsCyclic.isMulCommutative }

/-- Embed the cyclic extension supplied by Corollary 2.5 into the fixed
separable closure used by the statement of Theorem 2.6. -/
noncomputable def CEDataa.finiteAbelianSubextension
    {K : Type u} [Field K] [NumberField K]
    (data : CEDataa K) :
    FASubext K :=
  data.abelianExtension.finiteAbelianSubextension

/-- Embedding the extension from Corollary 2.5 into a separable closure does
not change its degree. -/
theorem CEDataa.finrank_fin_abeliansubexte
    {K : Type u} [Field K] [NumberField K]
    (data : CEDataa K) :
    letI : Field data.L := data.fieldL
    letI : Algebra K data.L := data.algebraKL
    letI : FiniteDimensional K data.L := data.finiteDimensionalKL
    Module.finrank K data.finiteAbelianSubextension.1 =
      Module.finrank K data.L := by
  let E := data.abelianExtension
  change Module.finrank K E.separableClosureField = Module.finrank K E.carrier
  exact E.algSeparableClosure.toLinearEquiv.finrank_eq.symm

/-- The chosen image in the separable closure remains cyclic over the base. -/
theorem CEDataa.cyclic_fin_abeliansubexte
    {K : Type u} [Field K] [NumberField K]
    (data : CEDataa K) :
    IsCyclic Gal(data.finiteAbelianSubextension.1/K) := by
  letI : Field data.L := data.fieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  letI : IsCyclic Gal(data.L/K) := data.isCyclicKL
  let E := data.abelianExtension
  letI : IsCyclic Gal(E.carrier/K) := by
    change IsCyclic Gal(data.L/K)
    infer_instance
  change IsCyclic Gal(E.separableClosureField/K)
  exact E.algSeparableClosure.autCongr.isCyclic.mp inferInstance

/-- The local-invariant input in the printed application preceding Theorem
2.6.  It records the finite support and denominators of the localized Brauer
class, injectivity of global localization through the lcm equality, and the
fact that matching those local degrees makes an extension split `D`.

It deliberately does not assume the existence, cyclicity, or global degree
of such an extension; Corollary 2.5 supplies all three. -/
structure BrauerLocalData
    (K : Type u) [Field K] [NumberField K]
    (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [Module.Finite K D] where
  places : Finset (Place K)
  localDegree : places → ℕ
  localDegree_pos : ∀ v, 0 < localDegree v
  infiniteDegree_possible : ∀ v : places, match v.1 with
    | .inl _ => True
    | .inr w => Nonempty (PossibleLocalDegree K w (localDegree v))
  period_eq_lcm :
    orderOf (BGroups.brauerClass K (BGroups.centralDivisionCSA K D)) =
      Finset.univ.lcm localDegree
  splits_matching_degrees :
    ∀ data : CEDataa K,
      letI : Field data.L := data.fieldL
      letI : Algebra K data.L := data.algebraKL
      (∀ v : places, data.HasLocalDegree v.1 (localDegree v)) →
        BGroups.ISBy K data.L D

/-- The sole remaining Brauer-theoretic input in the application: construct
the local denominator data of a global division algebra and prove its local
splitting criterion. -/
def BrauerLocalBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (D : Type u) [DivisionRing D] [Algebra K D]
      [Algebra.IsCentral K D] [Module.Finite K D],
    Nonempty (BrauerLocalData K D)

/-- Corollary 2.5 converts the local invariant data in the printed
application into a cyclic splitting field whose degree is the Brauer period. -/
theorem cyclicDivisionSplitting
    (h25 : (∀ (K : Type u) [Field K] [NumberField K]
          (S : Finset (Place K)) (n_v : S → ℕ),
          (∀ v, 0 < n_v v) →
          (∀ v : S, match v.1 with
            | .inl _ => True
            | .inr w => Nonempty (PossibleLocalDegree K w (n_v v))) →
            ∃ data : CEDataa K,
              letI : Field data.L := data.fieldL
              letI : Algebra K data.L := data.algebraKL
              Module.finrank K data.L = Finset.univ.lcm n_v ∧
                ∀ v : S, data.HasLocalDegree v.1 (n_v v)))
    (hlocal : BrauerLocalBridge.{u}) :
    CyclicSplittingBridge.{u} := by
  intro K _ _ D _ _ _ _
  obtain ⟨appData⟩ := hlocal K D
  obtain ⟨data, hdegree, hdegrees⟩ :=
    h25 K appData.places appData.localDegree appData.localDegree_pos
      appData.infiniteDegree_possible
  letI : Field data.L := data.fieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  letI : IsCyclic Gal(data.L/K) := data.isCyclicKL
  let L := data.finiteAbelianSubextension
  have hdataDegreePeriod :
    Module.finrank K data.L =
        orderOf (BGroups.brauerClass K (BGroups.centralDivisionCSA K D)) :=
    hdegree.trans appData.period_eq_lcm.symm
  have hsplitData : BGroups.ISBy K data.L D :=
    appData.splits_matching_degrees data hdegrees
  have hperiod :
      orderOf (BGroups.brauerClass K (BGroups.centralDivisionCSA K D)) =
        Nat.sqrt (Module.finrank K D) := by
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      exact CProduca.brauer_division_degree K D
    · rw [← hdataDegreePeriod]
      exact CProduca.division_dvd_split
        K D data.L hsplitData
  have hLDegree :
      Module.finrank K L.1 =
        orderOf (BGroups.brauerClass K (BGroups.centralDivisionCSA K D)) :=
    data.finrank_fin_abeliansubexte.trans hdataDegreePeriod
  refine ⟨L, data.cyclic_fin_abeliansubexte, hLDegree, ?_⟩
  let n := Nat.sqrt (Module.finrank K D)
  have hD : Module.finrank K D = n ^ 2 := by
    dsimp only [n]
    obtain ⟨d, hd⟩ := BGroups.finrank_simple_square K D
    rw [hd, Nat.sqrt_eq']
  have hdataDegree : Module.finrank K data.L = n := by
    exact hdataDegreePeriod.trans hperiod
  obtain ⟨i⟩ :=
    cyclic_splitting_embeds K data.L D n hD hdataDegree hsplitData
  let e : data.L ≃ₐ[K] L.1 :=
    data.abelianExtension.algSeparableClosure
  let j : L.1 →ₐ[K] D := i.comp e.symm.toAlgHom
  apply CProduca.embedding_split_sq K L.1 D j
  rw [hD, hLDegree, hperiod]

/-- The period--degree equality is forced by the cyclic splitting-field
bridge: the period divides the division-algebra degree, while the degree of
the division algebra divides every splitting-field degree. -/
theorem period_cyclic_splitting
    (hcyclic : CyclicSplittingBridge.{u}) :
    PeriodDegreeBridge.{u} := by
  intro K _ _ D _ _ _ _
  obtain ⟨L, _hLcyclic, hLdegree, hsplit⟩ := hcyclic K D
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    exact CProduca.brauer_division_degree K D
  · rw [← hLdegree]
    exact CProduca.division_dvd_split K D L.1 hsplit

private theorem alg_range_commutative
    {K L D : Type u} [Field K] [Field L] [Algebra K L]
    [DivisionRing D] [Algebra K D] (i : L →ₐ[K] D) :
    ∀ x y : i.range, x * y = y * x := by
  intro x y
  obtain ⟨a, ha⟩ := x.2
  obtain ⟨b, hb⟩ := y.2
  apply Subtype.ext
  change (x : D) * (y : D) = (y : D) * (x : D)
  rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]

/-- The exact source theorem follows from the two genuinely global inputs.
The maximal-subfield assertion is not part of either bridge. -/
theorem period_splitting_field
    (hperiod : PeriodDegreeBridge.{u})
    (hcyclic : CyclicSplittingBridge.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K],
      (∀ (D : Type u) [DivisionRing D] [Algebra K D]
              [Algebra.IsCentral K D] [Module.Finite K D],
            orderOf (BGroups.brauerClass K (BGroups.centralDivisionCSA K D)) =
                Nat.sqrt (Module.finrank K D) ∧
              ∃ L : FASubext K,
                IsCyclic Gal(L.1/K) ∧
                  ∃ i : L.1 →ₐ[K] D,
                    CProduca.IsMaximalCommutative i.range ∧ BGroups.ISBy K L.1 D) := by
  intro K _ _ D _ _ _ _
  have hperiodD := hperiod K D
  refine ⟨hperiodD, ?_⟩
  obtain ⟨L, hLcyclic, hLdegree, hsplit⟩ := hcyclic K D
  letI : IsCyclic Gal(L.1/K) := hLcyclic
  let n := Nat.sqrt (Module.finrank K D)
  have hD : Module.finrank K D = n ^ 2 := by
    dsimp only [n]
    obtain ⟨d, hd⟩ := BGroups.finrank_simple_square K D
    rw [hd, Nat.sqrt_eq']
  have hL : Module.finrank K L.1 = n := by
    exact hLdegree.trans hperiodD
  obtain ⟨i⟩ := cyclic_splitting_embeds K L.1 D n hD hL hsplit
  refine ⟨L, inferInstance, i, ?_, hsplit⟩
  have hcomm : ∀ x y : i.range, x * y = y * x :=
    alg_range_commutative i
  apply (CProduca.maximal_subfield_sqrt K D i.range hcomm).2
  let e : L.1 ≃ₐ[K] i.range := AlgEquiv.ofInjective i i.injective
  calc
    Module.finrank K i.range = Module.finrank K L.1 :=
      e.toLinearEquiv.finrank_eq.symm
    _ = Nat.sqrt (Module.finrank K D) := hL

/-- Theorem VIII.2.6 from its single genuinely global input: the
Grunwald--Wang construction of a cyclic splitting field of period degree.
The period--degree equality is a consequence, not a separate hypothesis. -/
theorem cyclic_splitting_field
    (hcyclic : CyclicSplittingBridge.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K],
      (∀ (D : Type u) [DivisionRing D] [Algebra K D]
              [Algebra.IsCentral K D] [Module.Finite K D],
            orderOf (BGroups.brauerClass K (BGroups.centralDivisionCSA K D)) =
                Nat.sqrt (Module.finrank K D) ∧
              ∃ L : FASubext K,
                IsCyclic Gal(L.1/K) ∧
                  ∃ i : L.1 →ₐ[K] D,
                    CProduca.IsMaximalCommutative i.range ∧ BGroups.ISBy K L.1 D) :=
  period_splitting_field
    (period_cyclic_splitting hcyclic) hcyclic

/-- The literal source theorem from Corollary 2.5 and the remaining
Brauer-local content of the printed application. -/
theorem cyclic_division_brauer
    (h25 : (∀ (K : Type u) [Field K] [NumberField K]
          (S : Finset (Place K)) (n_v : S → ℕ),
          (∀ v, 0 < n_v v) →
          (∀ v : S, match v.1 with
            | .inl _ => True
            | .inr w => Nonempty (PossibleLocalDegree K w (n_v v))) →
            ∃ data : CEDataa K,
              letI : Field data.L := data.fieldL
              letI : Algebra K data.L := data.algebraKL
              Module.finrank K data.L = Finset.univ.lcm n_v ∧
                ∀ v : S, data.HasLocalDegree v.1 (n_v v)))
    (hlocal : BrauerLocalBridge.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K],
      (∀ (D : Type u) [DivisionRing D] [Algebra K D]
              [Algebra.IsCentral K D] [Module.Finite K D],
            orderOf (BGroups.brauerClass K (BGroups.centralDivisionCSA K D)) =
                Nat.sqrt (Module.finrank K D) ∧
              ∃ L : FASubext K,
                IsCyclic Gal(L.1/K) ∧
                  ∃ i : L.1 →ₐ[K] D,
                    CProduca.IsMaximalCommutative i.range ∧ BGroups.ISBy K L.1 D) :=
  cyclic_splitting_field
    (cyclicDivisionSplitting h25 hlocal)

end Submission.CField.GWang
