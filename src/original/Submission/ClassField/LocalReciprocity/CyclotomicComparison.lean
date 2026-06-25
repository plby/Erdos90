import Mathlib.NumberTheory.Padics.ProperSpace
import Submission.ClassField.LubinTate.PadicGaloisAction
import Submission.ClassField.LocalReciprocity.Continuity
import Submission.ClassField.LocalReciprocity.AlgEquiv
import Submission.ClassField.LocalReciprocity.CyclicCase

/-!
# The cohomological/cyclotomic Lubin--Tate comparison

The finite cyclotomic Lubin--Tate action is constructed explicitly in
Chapter I.  This file puts the cohomologically normalized finite local Artin
map in the same root-field types.  The uniformizer part is unconditional:
the Lubin--Tate norm theorem puts the chosen uniformizer in the norm subgroup.
Thus the remaining orientation-sensitive theorem is solely the formula on
`Z_p`-units.
-/

namespace Submission.CField.LRecip

open Submission.CField.LFTheory
open Submission.CField.LTate
open Submission.CField.TCohomo
open Submission.CField.Shifting
open Submission.CField.LClass
open Submission.CField.CProduca
open Submission.CField.LBrauer
open scoped NormedField Topology

noncomputable section

variable (p : ℕ) [Fact p.Prime]

local instance padicCyclotomicComparisonValuativeRel : ValuativeRel ℚ_[p] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))

local instance padicCyclotomicComparisonCompatible :
    Valuation.Compatible (NormedField.valuation (K := ℚ_[p])) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := ℚ_[p]))

local instance padicCyclotomicComparisonLocalField :
    IsNonarchimedeanLocalField ℚ_[p] := by
  haveI htop : IsValuativeTopology ℚ_[p] := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ 𝓝 (0 : ℚ_[p]) ↔
        ∃ γ : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := ℚ_[p])))ˣ,
          {x | (NormedField.valuation (K := ℚ_[p])).restrict x < γ.1} ⊆ s from
      (NormedField.toValued (K := ℚ_[p])).is_topological_valuation s]
    simpa using
      (NormedField.valuation (K := ℚ_[p]))
        |>.exists_setOf_restrict_le_iff 0 s
  haveI hnontrivial : ValuativeRel.IsNontrivial ℚ_[p] :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := ℚ_[p]))).mpr inferInstance
  exact
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := hnontrivial }

/-- The valuation-integer uniformizer in the transported cyclotomic datum is
the rational prime `p` inside `Q_p`. -/
theorem padic_uniformizer_p :
    algebraMap
        (Valuation.integer (NormedField.valuation (K := ℚ_[p]))) ℚ_[p]
        (padicLubinDatum p).pi = (p : ℚ_[p]) := by
  rfl

/-- The cohomologically normalized finite local Artin map kills `p` on every
cyclotomic Lubin--Tate root field.  This is the unconditional uniformizer
half of Example I.3.13(b). -/
theorem abelian_artin_uniformizer
    (n : ℕ) :
    let D := padicLubinDatum p
    abelianArtinHom ℚ_[p] (D.RootField ℚ_[p] n)
        (Units.mk0 (p : ℚ_[p])
          (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) = 1 := by
  dsimp only
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let D := padicLubinDatum p
  let E := D.RootField ℚ_[p] n
  let varpi : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p])
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hnorm : varpi ∈ normSubgroup ℚ_[p] E := by
    obtain ⟨y, hy⟩ := D.norm_uniformizer ℚ_[p] n
    have hy0 : y ≠ 0 := by
      intro hzero
      rw [hzero, Algebra.norm_zero,
        padic_uniformizer_p] at hy
      exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hy.symm
    refine ⟨Units.mk0 y hy0, ?_⟩
    apply Units.ext
    simpa [varpi, padic_uniformizer_p] using hy
  have hker : varpi ∈
      (abelianArtinHom ℚ_[p] E).ker := by
    rw [abelian_artin_ker ℚ_[p] E]
    exact hnorm
  exact MonoidHom.mem_ker.mp hker

/-- The exact remaining finite arithmetic statement.  On `Z_p`-units, the
cohomological local Artin map must equal the inverse of the checked direct
Lubin--Tate orbit. -/
def PadicArtinNormalization : Prop :=
  ∀ (n : ℕ) (u : ℤ_[p]ˣ),
    let D := padicLubinDatum p
    abelianArtinHom ℚ_[p] (D.RootField ℚ_[p] n)
        (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u) =
      padicIntegerCyclotomic p n
        (padicIntInteger p (n + 1) u⁻¹)

/-- The same missing normalization expressed directly in the norm-residue
coordinate.  This is the form suited to a calculation with the local
fundamental class or a cyclic-product invariant. -/
def PadicCyclotomicNormalization : Prop :=
  ∀ (n : ℕ) (u : ℤ_[p]ˣ),
    let D := padicLubinDatum p
    let q := padicIntInteger p (n + 1) u⁻¹
    localNormResidue ℚ_[p] (D.RootField ℚ_[p] n)
        (Abelianization.of
          (padicIntegerCyclotomic p n q)) =
      QuotientGroup.mk' (normSubgroup ℚ_[p] (D.RootField ℚ_[p] n))
        (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u)

/-- A `Z_p`-unit embedded as a Galois invariant of the finite cyclotomic
Lubin--Tate root field. -/
noncomputable def padicEmbeddedInvariant
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let D := padicLubinDatum p
    let E := D.RootField ℚ_[p] n
    FMAct.invariants Gal(E/ℚ_[p]) Eˣ := by
  dsimp only
  let D := padicLubinDatum p
  let E := D.RootField ℚ_[p] n
  let x : ℚ_[p]ˣ :=
    Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u
  exact ⟨Units.map (algebraMap ℚ_[p] E).toMonoidHom x, by
    intro σ
    apply Units.ext
    exact σ.commutes x⟩

/-- The representative-level calculation that remains after rewriting the
finite norm-residue map as a cyclic product.  The cocycle may be any
normalized representative of the canonical local fundamental class; its
cyclic product on the fixed Lubin--Tate orbit must be the embedded base unit
modulo the finite-action norm. -/
def FundamentalCocycleCalculation (n : ℕ) : Prop :=
  let D := padicLubinDatum p
  let E := D.RootField ℚ_[p] n
  ∃ c : NMCocycl₂ (G := Gal(E/ℚ_[p])) (M := Eˣ),
    MHTwo.mk c =
        multiplicativeFundamentalClass ℚ_[p] E ∧
      ∀ u : ℤ_[p]ˣ,
        let q := padicIntInteger p (n + 1) u⁻¹
        let g :=
          padicIntegerCyclotomic p n q
        QuotientGroup.mk' (FMAct.norm Gal(E/ℚ_[p]) Eˣ).range
            (NMCocycl₂.cyclicProductInvariant c g) =
          QuotientGroup.mk'
            (FMAct.norm Gal(E/ℚ_[p]) Eˣ).range
            (padicEmbeddedInvariant p n u)

/-- The explicit fundamental-cocycle calculation at every finite level. -/
def PadicCocycleCalculation : Prop :=
  ∀ n : ℕ, FundamentalCocycleCalculation p n

set_option maxHeartbeats 3000000 in
-- The root-field Galois action, fundamental class, and invariant quotient elaborate together.
set_option synthInstance.maxHeartbeats 500000 in
-- Typeclass search simultaneously sees the root-field Galois action and invariant quotient.
/-- The levelwise fundamental-cocycle calculation gives the corresponding
norm-residue unit formula. -/
theorem padic_normalization_level
    (n : ℕ)
    (hcalc : FundamentalCocycleCalculation p n)
    (u : ℤ_[p]ˣ) :
    let D := padicLubinDatum p
    let q := padicIntInteger p (n + 1) u⁻¹
    localNormResidue ℚ_[p] (D.RootField ℚ_[p] n)
        (Abelianization.of
          (padicIntegerCyclotomic p n q)) =
      QuotientGroup.mk' (normSubgroup ℚ_[p] (D.RootField ℚ_[p] n))
        (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u) := by
  dsimp only
  let D := padicLubinDatum p
  let E := D.RootField ℚ_[p] n
  let x : ℚ_[p]ˣ :=
    Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u
  let q := padicIntInteger p (n + 1) u⁻¹
  let g := padicIntegerCyclotomic p n q
  obtain ⟨c, hc, hproduct⟩ := hcalc
  have hcohomologous : MHTwo.IsCohomologous
      (localFundamentalCocycle ℚ_[p] E) c := by
    rw [← MHTwo.mk_eq_iff]
    exact (mk_fundamental_cocycle ℚ_[p] E).trans hc.symm
  let invNorm := galoisInvariantsMod ℚ_[p] E
  calc
    localNormResidue ℚ_[p] E (Abelianization.of g) =
        invNorm
          (QuotientGroup.mk' (FMAct.norm Gal(E/ℚ_[p]) Eˣ).range
            (NMCocycl₂.cyclicProductInvariant
              (localFundamentalCocycle ℚ_[p] E) g)) :=
      fundamental_cyclic_product
        ℚ_[p] E g
    _ = invNorm
          (QuotientGroup.mk' (FMAct.norm Gal(E/ℚ_[p]) Eˣ).range
            (NMCocycl₂.cyclicProductInvariant c g)) := by
      rw [NMCocycl₂.cyclic_invariant_cohomologous
        hcohomologous g]
    _ = invNorm
          (QuotientGroup.mk' (FMAct.norm Gal(E/ℚ_[p]) Eˣ).range
            (padicEmbeddedInvariant p n u)) := by
      rw [hproduct u]
    _ = QuotientGroup.mk' (normSubgroup ℚ_[p] E) x := by
      exact galois_invariants_algebra
        ℚ_[p] E x

set_option maxHeartbeats 3000000 in
-- The root-field Galois action and both invariant quotients elaborate together.
set_option synthInstance.maxHeartbeats 500000 in
/-- Conversely, the norm-residue unit formula makes the canonical local
fundamental cocycle itself satisfy the required levelwise product
calculation.  Thus no additional representative choice remains. -/
theorem fundamental_cocycle_calculation
    (n : ℕ)
    (hnorm : PadicCyclotomicNormalization p) :
    FundamentalCocycleCalculation p n := by
  dsimp only [FundamentalCocycleCalculation]
  let D := padicLubinDatum p
  let E := D.RootField ℚ_[p] n
  refine ⟨localFundamentalCocycle ℚ_[p] E,
    mk_fundamental_cocycle ℚ_[p] E, ?_⟩
  intro u
  let x : ℚ_[p]ˣ :=
    Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u
  let q := padicIntInteger p (n + 1) u⁻¹
  let g := padicIntegerCyclotomic p n q
  let invNorm := galoisInvariantsMod ℚ_[p] E
  apply invNorm.injective
  calc
    invNorm
        (QuotientGroup.mk' (FMAct.norm Gal(E/ℚ_[p]) Eˣ).range
          (NMCocycl₂.cyclicProductInvariant
            (localFundamentalCocycle ℚ_[p] E) g)) =
        localNormResidue ℚ_[p] E
          (Abelianization.of g) :=
      (fundamental_cyclic_product
        ℚ_[p] E g).symm
    _ = QuotientGroup.mk' (normSubgroup ℚ_[p] E) x := hnorm n u
    _ = invNorm
        (QuotientGroup.mk' (FMAct.norm Gal(E/ℚ_[p]) Eˣ).range
          (padicEmbeddedInvariant p n u)) := by
      exact (galois_invariants_algebra
        ℚ_[p] E x).symm

/-- The norm-residue normalization constructs the requested fundamental
cocycle calculation at every finite cyclotomic level. -/
theorem fundamental_calculation_residue
    (hnorm : PadicCyclotomicNormalization p) :
    PadicCocycleCalculation p := by
  intro n
  exact fundamental_cocycle_calculation
    p n hnorm

/-- An explicit fundamental-cocycle calculation supplies the exact
norm-residue normalization required by the cyclotomic unit formula. -/
theorem normalization_fundamental_cocycle
    (hcalc : PadicCocycleCalculation p) :
    PadicCyclotomicNormalization p := by
  intro n u
  exact padic_normalization_level
    p n (hcalc n) u

/-- The explicit fundamental-cocycle calculation is equivalent to the
root-field norm-residue normalization. -/
theorem cocycle_calculation_residue :
    PadicCocycleCalculation p ↔
      PadicCyclotomicNormalization p := by
  exact ⟨normalization_fundamental_cocycle p,
    fundamental_calculation_residue p⟩

/-- The cohomological Artin comparison and the explicit norm-residue
calculation are literally equivalent; there is no remaining transport or
orientation ambiguity between them. -/
theorem artin_normalization_residue :
    PadicArtinNormalization p ↔
      PadicCyclotomicNormalization p := by
  constructor
  · intro h n u
    exact (abelian_artin_residue ℚ_[p]
      ((padicLubinDatum p).RootField ℚ_[p] n)
      (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u)
      (padicIntegerCyclotomic p n
        (padicIntInteger p (n + 1) u⁻¹))).mp (h n u)
  · intro h n u
    exact (abelian_artin_residue ℚ_[p]
      ((padicLubinDatum p).RootField ℚ_[p] n)
      (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u)
      (padicIntegerCyclotomic p n
        (padicIntInteger p (n + 1) u⁻¹))).mpr (h n u)

/-- The uniformizer formula transported from the Lubin--Tate root field to
any model of the same cyclotomic extension. -/
theorem abelian_cyclotomic_uniformizer
    (n : ℕ)
    (E : Type) [Field E] [Algebra ℚ_[p] E]
    [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E]
    [IsMulCommutative Gal(E/ℚ_[p])] :
    abelianArtinHom ℚ_[p] E
        (Units.mk0 (p : ℚ_[p])
          (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) = 1 := by
  let D := padicLubinDatum p
  let e := padicCyclotomicAlg p n E
  let varpi : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p])
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have htransport := DFunLike.congr_fun
    (abelian_artin_alg ℚ_[p] (D.RootField ℚ_[p] n) E e)
    varpi
  change e.autCongr (abelianArtinHom ℚ_[p]
      (D.RootField ℚ_[p] n) varpi) =
    abelianArtinHom ℚ_[p] E varpi at htransport
  rw [abelian_artin_uniformizer]
    at htransport
  change abelianArtinHom ℚ_[p] E varpi = 1
  calc
    abelianArtinHom ℚ_[p] E varpi = e.autCongr 1 := htransport.symm
    _ = 1 := map_one e.autCongr

/-- Once the root-field unit normalization is known, algebra-equivalence
naturality and the explicit fixed orbit give Milne's inverse cyclotomic
unit action in every model of the extension. -/
theorem abelian_artin_normalization
    (hunitNormalization : PadicArtinNormalization p)
    (n : ℕ) (u : ℤ_[p]ˣ)
    (E : Type) [Field E] [Algebra ℚ_[p] E]
    [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E]
    [IsMulCommutative Gal(E/ℚ_[p])] :
    abelianArtinHom ℚ_[p] E
        (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u) =
      padicCyclotomicAction p (n + 1)
        (padicCyclotomic_irreducible p n) (L := E) u := by
  let D := padicLubinDatum p
  let e := padicCyclotomicAlg p n E
  let x : ℚ_[p]ˣ := Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u
  let q := padicIntInteger p (n + 1) u⁻¹
  have hroot : abelianArtinHom ℚ_[p]
      (D.RootField ℚ_[p] n) x =
      padicIntegerCyclotomic p n q := by
    exact hunitNormalization n u
  have htransport := DFunLike.congr_fun
    (abelian_artin_alg ℚ_[p] (D.RootField ℚ_[p] n) E e)
    x
  change e.autCongr (abelianArtinHom ℚ_[p]
      (D.RootField ℚ_[p] n) x) =
    abelianArtinHom ℚ_[p] E x at htransport
  have hdirect := congrArg (fun orbit ↦ orbit q)
    (padic_cyclotomic_direct p n E)
  change e.autCongr
      (padicIntegerCyclotomic p n q) =
    padicIntegerGalois p n E q at hdirect
  calc
    abelianArtinHom ℚ_[p] E x =
        e.autCongr (abelianArtinHom ℚ_[p]
          (D.RootField ℚ_[p] n) x) := htransport.symm
    _ = e.autCongr
        (padicIntegerCyclotomic p n q) := by
      rw [hroot]
    _ = padicIntegerGalois p n E q := hdirect
    _ = padicCyclotomicAction p (n + 1)
        (padicCyclotomic_irreducible p n) (L := E) u :=
      padic_inv_action
        p n E u

end

end Submission.CField.LRecip
