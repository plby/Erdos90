import Submission.Group.FiniteWindow.Named


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Submission

/--
The full surjective-data frontier packages named data together with surjectivity
on the positive window and at the single boundary index.
-/
def PPDatum.PosfinwindowActibounrelaSurjdatawitness
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      Nonempty (H.PWRelasu depth)

/--
The next sharper frontier: construct active-surjective data on the positive
window `1 ≤ n ≤ N` together with a relator-only surjective datum at the single
boundary index `N + 1`.
-/
def PPDatum.PosfinWindactisurjBounrelawitn
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      ∃ (N : ℕ) (a : ℕ → ℕ),
        0 < a 0 ∧
        (∀ n, 1 ≤ n → n ≤ N →
          Nonempty (H.FinWindowactiveSurjdatum depth N n a)) ∧
        Nonempty (H.FinwindowBoundrelatorSurjdatum depth N a)

/--
Base data for the remaining positive-window task: choose a cutoff `N` and a
truncated coefficient sequence `a`, keeping only the essential positivity
condition on `a 0`.

This separates the eventual sequence choice from the later linear-algebra
surjectivity constructions.
-/
structure PPDatum.PosFinwindowBasedata
    (H : PPDatum) where
  N : ℕ
  a : ℕ → ℕ
  ha0 : 0 < a 0

/--
The positive-window core package: a base choice together with active-surjective
data for every genuinely nontrivial index `1 ≤ n ≤ N`.

This is a strict simplification of the current main frontier because it ignores
the single boundary index `N + 1`.
-/
structure PPDatum.PosfinWindowactiveCorepackage
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ)
    extends H.PosFinwindowBasedata where
  active :
    ∀ n, 1 ≤ n → n ≤ N →
      Nonempty (H.FinWindowactiveSurjdatum depth N n a)

/--
The remaining work can first be split off into choosing positive-window base
data.

This is weaker than the active-surjective witness because it does not yet ask
for any finite-dimensional spaces or maps.
-/
def PPDatum.PosFinwindowBasewitness
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      Nonempty H.PosFinwindowBasedata

/--
The next genuine core frontier: after choosing the base data, construct the
active-surjective datum on the positive window `1 ≤ n ≤ N`.
-/
def PPDatum.PosfinWindowactiveCorewitness
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      Nonempty (H.PosfinWindowactiveCorepackage depth)

/--
Once the base data `(N, a)` is fixed, the positive-window task becomes purely
local: construct the active-surjective datum for each index `1 ≤ n ≤ N`.

This is the direct analogue of passing from unnamed existential data to fixed
named coefficient packages in the richer `C.lean` bridge.
-/
structure PPDatum.PosfinWindowactiveExtpackage
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ)
    (base : H.PosFinwindowBasedata) where
  active :
    ∀ n, 1 ≤ n → n ≤ base.N →
      Nonempty (H.FinWindowactiveSurjdatum depth base.N n base.a)

/--
The positive-window core witness can be decomposed further into:

1. choose the base data `(N, a)`;
2. extend that fixed base data across the indices `1 ≤ n ≤ N`.
-/
def PPDatum.PosfinWindowactiveCoreext
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      (base : H.PosFinwindowBasedata) →
      Nonempty (H.PosfinWindowactiveExtpackage depth base)

/--
Once the positive window has been handled, it remains only to extend that core
package across the single boundary index `N + 1` by constructing one
relator-only surjective datum.

This is smaller than the previous frontier because it is a one-index extension
problem for already chosen `N` and `a`.
-/
def PPDatum.BoundfinWindowrelatorSurjext
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      (core : H.PosfinWindowactiveCorepackage depth) →
      Nonempty (H.FinwindowBoundrelatorSurjdatum depth core.N core.a)

/--
The boundary step does not actually depend on the active proofs on the
positive window, only on the chosen base data `(N, a)`.

So the remaining boundary task can be stated more sharply as a one-index
extension problem from fixed base data alone.
-/
def PPDatum.BoundfinWindowrelatorSurjbaseext
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      (base : H.PosFinwindowBasedata) →
      Nonempty (H.FinwindowBoundrelatorSurjdatum depth base.N base.a)

/--
A canonical dummy base choice that already satisfies the bare positivity
requirement `0 < a 0`.

This records explicitly that choosing base data is not the difficult part of
the bridge.
-/
def PPDatum.trivialpos_finwindow_basedata
    (H : PPDatum) : H.PosFinwindowBasedata where
  N := 0
  a := fun _ => 1
  ha0 := by decide

/--
Turn an extension package for fixed base data into the earlier core package.
-/
def PPDatum.posfin_windacticore_packextpack
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ}
    {base : H.PosFinwindowBasedata}
    (ext : H.PosfinWindowactiveExtpackage depth base) :
    H.PosfinWindowactiveCorepackage depth where
  N := base.N
  a := base.a
  ha0 := base.ha0
  active := ext.active

/--
Any positive-window core package already yields the weaker base witness by
forgetting the active-surjective part.
-/
theorem
    PPDatum.posfin_windowwindow_acticorewitn
    (H : PPDatum)
    (hwitness : H.PosfinWindowactiveCorewitness) :
    H.PosFinwindowBasewitness := by
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨core⟩
  exact ⟨{ N := core.N, a := core.a, ha0 := core.ha0 }⟩

/--
The dummy base choice already proves the weakened base witness.
-/
theorem PPDatum.pos_finwindow_basewitness
    (H : PPDatum) :
    H.PosFinwindowBasewitness := by
  intro rels depth hrels hmem hdepth
  exact ⟨H.trivialpos_finwindow_basedata⟩

/--
Base data plus an extension on the positive window already recover the earlier
positive-window core witness.
-/
theorem
    PPDatum.posfin_windowwindow_activecoreext
    (H : PPDatum)
    (hbase : H.PosFinwindowBasewitness)
    (hext : H.PosfinWindowactiveCoreext) :
    H.PosfinWindowactiveCorewitness := by
  intro rels depth hrels hmem hdepth
  rcases hbase hrels hmem hdepth with ⟨base⟩
  rcases hext hrels hmem hdepth base with ⟨ext⟩
  exact ⟨H.posfin_windacticore_packextpack ext⟩

/--
If the boundary relator datum can be constructed from fixed base data alone,
then it can certainly be constructed after a positive-window core package has
already been chosen.
-/
theorem
    PPDatum.boundfin_windowrelator_surjbaseext
    (H : PPDatum)
    (hboundary : H.BoundfinWindowrelatorSurjbaseext) :
    H.BoundfinWindowrelatorSurjext := by
  intro rels depth hrels hmem hdepth core
  exact
    hboundary hrels hmem hdepth
      { N := core.N, a := core.a, ha0 := core.ha0 }

/--
The previous positive-window-plus-boundary frontier is now a formal
consequence of two smaller pieces:

1. choose a positive-window core package;
2. extend it across the single boundary index `N + 1`.
-/
theorem
    PPDatum.posfin_windowwindow_relatorsurjext
    (H : PPDatum)
    (hcore : H.PosfinWindowactiveCorewitness)
    (hboundary : H.BoundfinWindowrelatorSurjext) :
    H.PosfinWindactisurjBounrelawitn := by
  intro rels depth hrels hmem hdepth
  rcases hcore hrels hmem hdepth with ⟨core⟩
  rcases hboundary hrels hmem hdepth core with ⟨boundary⟩
  exact ⟨core.N, core.a, core.ha0, core.active, ⟨boundary⟩⟩

/--
Positive-window active data together with a boundary relator-only datum already
imply the previous positive-and-boundary active-surjective witness.
-/
theorem
    PPDatum.pos_boundbound_relatorwitness
    (H : PPDatum)
    (hwitness : H.PosfinWindactisurjBounrelawitn) :
    H.PosboundFinwindowActisurjwitn := by
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, a, ha0, hmain, hboundary⟩
  refine ⟨N, a, ha0, ?_⟩
  intro n hn1 hnN1
  by_cases hnN : n ≤ N
  · exact hmain n hn1 hnN
  · have hEq : n = N + 1 := by omega
    subst hEq
    rcases hboundary with ⟨D⟩
    exact H.finwindowactive_surjdatumbound_relasurjdatu D

/--
Once a coefficientwise Hilbert-series witness is available for each minimal
presentation, the classical positivity conclusion follows immediately.
-/
theorem
    PPDatum.minpres_hilbseribrid_coefhilbwitn
    (H : PPDatum)
    (hwitness : H.CoefficientwiseHilbertWitness) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  intro rels depth hrels hmem hdepth t ht0 _ht1
  rcases hwitness hrels hmem hdepth with ⟨P, hPcoeff, hP0, hprodcoeff⟩
  exact
    GShafar.coefficientwise_hilbert_inequality
      (d := H.generatorRank) (r := H.relationRank) depth hdepth hPcoeff hP0 hprodcoeff t ht0

/--
An explicit truncated recursion already implies the coefficientwise witness
needed for the Hilbert-series bridge.
-/
theorem
    PPDatum.coeffhilbert_witnesstrunc_recurrewitness
    (H : PPDatum)
    (hwitness : H.TruncRecurrenceWitness) :
    H.CoefficientwiseHilbertWitness := by
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, a, ha, ha0, hrec⟩
  rcases
      GShafar.witness_polynomial_recurrence
        (d := H.generatorRank) (r := H.relationRank) (depth := depth) ha ha0 hrec with
    ⟨P, hPcoeff, hP0, hprodcoeff⟩
  exact ⟨P, hPcoeff, hP0, hprodcoeff⟩

/--
A finite-window truncation recurrence witness already extends to the full
all-`n` truncation recurrence witness.
-/
theorem
    PPDatum.truncrecurrence_witnessfin_trunrecuwitn
    (H : PPDatum)
    (hwitness : H.FinTruncRecurrewitness) :
    H.TruncRecurrenceWitness := by
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, a, ha, ha0, hrec⟩
  refine ⟨N, a, ha, ha0, ?_⟩
  intro n
  by_cases hn : n ≤ N + max 1 (Finset.univ.sup depth)
  · exact hrec n hn
  · have hzero :=
      GShafar.truncation_recurrence_window
        (a := a) (N := N) (d := H.generatorRank) (r := H.relationRank) (depth := depth)
        (n := n) (Nat.lt_of_not_ge hn)
    simp only [mul_ite, mul_zero, ge_iff_le] at hzero ⊢
    simp [hzero]

/--
Natural-number finite-window dimension inequalities already imply the
real-valued finite-window truncation recurrence needed above.
-/
theorem
    PPDatum.fintrunc_recurrewindow_dimineqwitness
    (H : PPDatum)
    (hwitness : H.FinWindowdimIneqwitness) :
    H.FinTruncRecurrewitness := by
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, a, ha0, hdim⟩
  refine ⟨N, (fun n => (a n : ℝ)), ?_, ?_, ?_⟩
  · intro n
    change (0 : ℝ) ≤ (a n : ℝ)
    exact_mod_cast (Nat.zero_le (a n) : 0 ≤ a n)
  · change (0 : ℝ) < (a 0 : ℝ)
    exact_mod_cast ha0
  · intro n hn
    have hdim' :
        (H.generatorRank : ℝ) * (if 1 ≤ n then
              if n - 1 ≤ N then (a (n - 1) : ℝ) else 0
            else 0) ≤
          (if n ≤ N then (a n : ℝ) else 0) +
            ∑ i, if depth i ≤ n then
              if n - depth i ≤ N then (a (n - depth i) : ℝ) else 0
            else 0 := by
      exact_mod_cast hdim n hn
    have hrec' :
        0 ≤
          (if n ≤ N then (a n : ℝ) else 0) -
            (H.generatorRank : ℝ) * (if 1 ≤ n then
              if n - 1 ≤ N then (a (n - 1) : ℝ) else 0
            else 0) +
            ∑ i, if depth i ≤ n then
              if n - depth i ≤ N then (a (n - depth i) : ℝ) else 0
            else 0 := by
      nlinarith
    simpa [GShafar.truncatedSequence] using hrec'

/--
Local surjective witnesses on the finite coefficient window already imply the
corresponding natural-number dimension inequalities.
-/
theorem
    PPDatum.finwindow_dimfin_windsurjwitn
    (H : PPDatum)
    (hwitness : H.FinWindowSurjwitness) :
    H.FinWindowdimIneqwitness := by
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, a, ha0, hsurj⟩
  refine ⟨N, a, ha0, ?_⟩
  intro n hn
  rcases hsurj n hn with ⟨D⟩
  exact H.finwindow_dimineq_surjdatum D

/--
The active-relator local surjective witnesses already imply the corresponding
natural-number finite-window dimension inequalities.
-/
theorem
    PPDatum.finwindow_dimwindow_actisurjwitn
    (H : PPDatum)
    (hwitness : H.FinWindowactiveSurjwitness) :
    H.FinWindowdimIneqwitness := by
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, a, ha0, hsurj⟩
  refine ⟨N, a, ha0, ?_⟩
  intro n hn
  rcases hsurj n hn with ⟨D⟩
  exact H.finwindow_dimineq_activesurjdatum D

/--
Hence a truncation-recursion witness is already enough to prove the full
Hilbert-series bridge.
-/
theorem PPDatum.minpres_hilbseribrid_trunrecuwitn
    (H : PPDatum)
    (hwitness : H.TruncRecurrenceWitness) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  exact
    H.minpres_hilbseribrid_coefhilbwitn
      (H.coeffhilbert_witnesstrunc_recurrewitness hwitness)

/--
The same bridge can be proved from the sharper finite-window recurrence
witness.
-/
theorem
    PPDatum.minpres_hilbserifin_trunrecuwitn
    (H : PPDatum)
    (hwitness : H.FinTruncRecurrewitness) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  exact
    H.minpres_hilbseribrid_trunrecuwitn
      (H.truncrecurrence_witnessfin_trunrecuwitn hwitness)

/--
The same bridge can already be proved from the natural-number finite-window
dimension-inequality frontier.
-/
theorem
    PPDatum.minpres_hilbseriwind_dimineqwitness
    (H : PPDatum)
    (hwitness : H.FinWindowdimIneqwitness) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  exact
    H.minpres_hilbserifin_trunrecuwitn
      (H.fintrunc_recurrewindow_dimineqwitness
        hwitness)

/--
The same bridge can already be proved from the local finite-window surjective
data.
-/
theorem
    PPDatum.minpreshilbert_seriesbridgefin_windsurjwitn
    (H : PPDatum)
    (hwitness : H.FinWindowSurjwitness) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  exact
    H.minpres_hilbseriwind_dimineqwitness
      (H.finwindow_dimfin_windsurjwitn hwitness)

/--
The same bridge can already be proved from the more local active-relator
surjective data.
-/
theorem
    PPDatum.minpres_hilbseriwind_actisurjwitn
    (H : PPDatum)
    (hwitness : H.FinWindowactiveSurjwitness) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  exact
    H.minpres_hilbseriwind_dimineqwitness
      (H.finwindow_dimwindow_actisurjwitn
        hwitness)

end Submission
