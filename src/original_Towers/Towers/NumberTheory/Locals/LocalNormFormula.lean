import Towers.NumberTheory.Locals.ArbitraryPlaceClassification
import Towers.NumberTheory.Completions.LocalNormProduct


/-!
# The local norm formula

This file restates at its first occurrence Milne's Lemma 7.16.  Milne defers
the proof to Chapter 8, so the proofs here invoke the completion and local
norm results formalized there.
-/

namespace Towers.NumberTheory.Milne

open NumberField

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

noncomputable local instance finitePlaceFact (v : FinitePlace K) :
    Fact v.1.IsNontrivial :=
  ⟨finite_place_nontrivial v⟩

local instance finiteCompletionUltrametric (v : FinitePlace K) :
    IsUltrametricDist v.1.Completion := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one
  intro n
  rw [← map_natCast (completionEmbedding v.1) n, norm_completionEmbedding]
  exact (nonarchimedean_nat_cast v.1).1
    (place_nonarchimedean v) n

local instance finiteExtensionsFinite (v : FinitePlace K) :
    Finite {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v.1} :=
  absolute_extensions_separable v.1

noncomputable local instance finiteExtensionsFintype
    (v : FinitePlace K) :
    Fintype {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v.1} :=
  Fintype.ofFinite _

set_option backward.isDefEq.respectTransparency false in
local instance localNormFormulaCompletionPlaceAlgebra
    (v : FinitePlace K)
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v.1}) :
    Algebra v.1.Completion w.1.Completion :=
  (completionLies v.1 w.1 w.2).toAlgebra

local instance localNormFormulaCompletionPlaceSMul
    (v : FinitePlace K)
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v.1}) :
    SMul v.1.Completion w.1.Completion :=
  (localNormFormulaCompletionPlaceAlgebra v w).toSMul

local instance localNormFormulaCompletionPlaceModule
    (v : FinitePlace K)
    (w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v.1}) :
    Module v.1.Completion w.1.Completion :=
  Algebra.toModule

omit [NumberField L] in
/-- Milne, Lemma 7.16(b), finite-place form.  The absolute values `w` are
the unique extensions that restrict exactly to `v`; raising each one to its
local degree gives the normalized absolute value of the corresponding finite
place of `L`. -/
theorem place_local_formula (v : FinitePlace K) (x : L) :
    (∏ w : {w : AbsoluteValue L ℝ // AbsoluteValue.LiesOver w v.1},
        w.1 x ^ Module.finrank v.1.Completion w.1.Completion) =
      v (Algebra.norm K x) := by
  exact prod_finrank_norm v.1 x

open Classical in
/-- Milne, Lemma 7.16(b), infinite-place form.  The multiplicity is one at
a real place and two at a complex place, so these are precisely Milne's
normalized infinite-place values. -/
theorem infinite_place_formula (v : InfinitePlace K) (x : L) :
    (∏ w : {w : InfinitePlace L //
        w.comap (algebraMap K L) = v}, w.1 x ^ w.1.mult) =
      v (Algebra.norm K x) ^ v.mult :=
  prod_infinite_normalized v x

end

end Towers.NumberTheory.Milne
