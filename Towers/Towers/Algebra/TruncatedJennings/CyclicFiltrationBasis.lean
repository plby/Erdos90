import Towers.Algebra.TruncatedJennings.MonomialBasis
import Towers.Algebra.TruncatedJennings.CyclicPCReps
import Towers.Algebra.DenseGenerators.WeightedFiltrationWords


open scoped commutatorElement

noncomputable section

namespace Towers
namespace TJennin

open MBData.HMData

universe u

/-- At cutoff zero the bounded-prefix monomial span is the span of the full monomial family. -/
lemma jennings_monomial_range
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {r : ℕ}
    (gen : Fin r → Q)
    (weight : Fin r → ℕ) :
    jenningsMonomialSpan (p := p) gen weight 0 =
      Submodule.span (ZMod p)
        (Set.range fun e : Fin r → Fin p =>
          jenningsMonomialFin p Q gen e) := by
  unfold jenningsMonomialSpan
  congr 1
  ext a
  simp

/-- A weight filtration containing every augmentation letter in weight one is all of the finite
group algebra at cutoff zero. -/
lemma WFilt.JzeroeqTopgroupalgSubonememone
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (W : WFilt p Q)
    (hletter :
      ∀ q : Q, groupAlgebraSub p Q q ∈ W.J 1) :
    W.J 0 = ⊤ := by
  apply top_unique
  calc
    ⊤ =
        Submodule.span (ZMod p)
          (Set.range
            (Finsupp.basisSingleOne : Module.Basis Q (ZMod p)
              (denseGroupAlgebra p Q))) :=
      (Finsupp.basisSingleOne : Module.Basis Q (ZMod p)
        (denseGroupAlgebra p Q)).span_eq.symm
    _ ≤ W.J 0 := by
      apply Submodule.span_le.mpr
      intro a ha
      rcases ha with ⟨q, rfl⟩
      have hsub :
          groupAlgebraSub p Q q ∈ W.J 0 :=
        W.anti (by omega) (hletter q)
      have hadd :
          groupAlgebraSub p Q q + 1 ∈ W.J 0 :=
        (W.J 0).add_mem hsub W.one_mem
      simpa [groupAlgebraSub,
        denseGeneratorsElement] using hadd

/-- A bounded monomial family of the correct cardinality is a basis as soon as its cutoff-zero
span is all of the finite group algebra. -/
noncomputable def boundedMonomialBasis
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Fintype Q]
    {r : ℕ}
    (gen : Fin r → Q)
    (weight : Fin r → ℕ)
    (htop : jenningsMonomialSpan (p := p) gen weight 0 = ⊤)
    (hcard : Fintype.card (Fin r → Fin p) = Fintype.card Q) :
    Module.Basis (Fin r → Fin p) (ZMod p)
      (denseGroupAlgebra p Q) := by
  classical
  apply basisOfTopLeSpanOfCardEqFinrank
    (fun e : Fin r → Fin p => jenningsMonomialFin p Q gen e)
  · rw [← jennings_monomial_range gen weight, htop]
  · calc
      Fintype.card (Fin r → Fin p) = Fintype.card Q := hcard
      _ = Module.finrank (ZMod p) (denseGroupAlgebra p Q) := by
        exact (Module.finrank_finsupp_self (ZMod p) (ι := Q)).symm

@[simp]
lemma bounded_monomial_basis
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Fintype Q]
    {r : ℕ}
    (gen : Fin r → Q)
    (weight : Fin r → ℕ)
    (htop : jenningsMonomialSpan (p := p) gen weight 0 = ⊤)
    (hcard : Fintype.card (Fin r → Fin p) = Fintype.card Q)
    (e : Fin r → Fin p) :
    boundedMonomialBasis gen weight htop hcard e =
      jenningsMonomialFin p Q gen e := by
  classical
  simp [boundedMonomialBasis]

/-- The high-weight spans of the extension-order basis are exactly the bounded-prefix monomial
spans used to define the cyclic filtration. -/
lemma jennings_monomial_high
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Fintype Q]
    {r : ℕ}
    (gen : Fin r → Q)
    (weight : Fin r → ℕ)
    (htop : jenningsMonomialSpan (p := p) gen weight 0 = ⊤)
    (hcard : Fintype.card (Fin r → Fin p) = Fintype.card Q)
    (s : ℕ) :
    jenningsMonomialSpan (p := p) gen weight s =
      basisHighSpan
        (p := p) (Q := Q)
        (boundedMonomialBasis gen weight htop hcard)
        (fun e : Fin r → Fin p =>
          expWeight (p := p) (r := r) weight e)
        s := by
  classical
  unfold jenningsMonomialSpan basisHighSpan
  congr 1
  ext a
  simp

/-- Jennings exponent weight is unchanged by a simultaneous reindexing of the weights and
exponents. -/
lemma exp_comp_equiv
    {p r s : ℕ}
    (σ : Fin r ≃ Fin s)
    (weight : Fin s → ℕ)
    (e : Fin s → Fin p) :
    expWeight (p := p) (r := r)
        (fun i => weight (σ i)) (fun i => e (σ i)) =
      expWeight (p := p) (r := s) weight e := by
  unfold expWeight
  exact σ.sum_comp (fun i => (e i).val * weight i)

/-- A high-weight span selected from a finite basis has dimension equal to the number of selected
basis indices. -/
lemma finrank_high_span
    {κ : Type*}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    [Fintype κ]
    (B : Module.Basis κ (ZMod p)
      (denseGroupAlgebra p Q))
    (weight : κ → ℕ)
    (s : ℕ) :
    Module.finrank (ZMod p)
        (basisHighSpan (p := p) (Q := Q) B weight s) =
      Fintype.card {e : κ // s ≤ weight e} := by
  classical
  unfold basisHighSpan
  rw [
    finrank_span_set_eq_card <|
      (B.linearIndependent.linearIndepOn _).id_image,
    Set.toFinset_card,
  ]
  simp only [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]
  exact Set.ncard_image_of_injective _ B.injective

/-- Weight-preserving reindexing does not change the dimension of a high-weight basis span. -/
lemma finrank_basis_high
    {κ ι : Type*}
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    [Finite κ] [Finite ι]
    (Bκ : Module.Basis κ (ZMod p)
      (denseGroupAlgebra p Q))
    (Bι : Module.Basis ι (ZMod p)
      (denseGroupAlgebra p Q))
    (weightκ : κ → ℕ)
    (weightι : ι → ℕ)
    (σ : κ ≃ ι)
    (hweight : ∀ i, weightκ i = weightι (σ i))
    (s : ℕ) :
    Module.finrank (ZMod p)
        (basisHighSpan (p := p) (Q := Q) Bκ weightκ s) =
      Module.finrank (ZMod p)
        (basisHighSpan (p := p) (Q := Q) Bι weightι s) := by
  letI := Fintype.ofFinite κ
  letI := Fintype.ofFinite ι
  rw [
    finrank_high_span Bκ weightκ s,
    finrank_high_span Bι weightι s,
  ]
  apply Fintype.card_congr
  exact
    σ.subtypeEquiv fun i => by
      rw [hweight i]

/-- The filtration obtained by adjoining representatives in descending boundary order agrees
with the canonical Jennings high-weight spans. -/
lemma OZReps.descprefzero_jeqcanon_highweightspan
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    (s : ℕ) :
    (O.descending_prefix_zero hbot hpow hcomm).W.J s =
      (MBData.canonical (p := p) (Q := Q) O).highWeightSpan s := by
  classical
  letI := Fintype.ofFinite Q
  let A := O.descending_prefix_zero hbot hpow hcomm
  have hletter :
      ∀ q : Q, groupAlgebraSub p Q q ∈ A.W.J 1 := by
    intro q
    simpa [A] using
      (O.groupalgsub_onememdesc_prefixzeromem
        hbot hpow hcomm hm
        (zassenhaus_filtration_one p Q (by norm_num) q))
  have htopW : A.W.J 0 = ⊤ :=
    WFilt.JzeroeqTopgroupalgSubonememone A.W hletter
  rcases
      O.descending_monomial_indices
        hbot hpow hcomm with
    ⟨r, gen, weight, hweight, hspan⟩
  have hspanA :
      ∀ t,
        A.W.J t =
          jenningsMonomialSpan (p := p) gen weight t := by
    simpa [A] using hspan
  have hr :
      r = (O.descendingBoundaryIndices m).length := by
    have hlength := congrArg List.length hweight
    simpa using hlength
  subst r
  let σ : Fin (O.descendingBoundaryIndices m).length ≃ Fin O.r :=
    O.descendingBoundaryEquiv
  have hweight_map :
      List.ofFn
          (fun i : Fin (O.descendingBoundaryIndices m).length =>
            O.weight (σ i)) =
        (O.descendingBoundaryIndices m).map O.weight := by
    simp [σ]
  have hweight_fun :
      weight =
        fun i : Fin (O.descendingBoundaryIndices m).length =>
          O.weight (σ i) := by
    apply List.ofFn_injective
    exact hweight.trans hweight_map.symm
  let σExp :
      (Fin (O.descendingBoundaryIndices m).length → Fin p) ≃
        (Fin O.r → Fin p) :=
    Equiv.arrowCongr σ (Equiv.refl (Fin p))
  have hσExp_weight :
      ∀ e : Fin (O.descendingBoundaryIndices m).length → Fin p,
        expWeight (p := p) weight e =
          expWeight (p := p) O.weight (σExp e) := by
    intro e
    rw [hweight_fun]
    simpa [σExp] using
      (exp_comp_equiv σ O.weight (σExp e))
  have hcard :
      Fintype.card
          (Fin (O.descendingBoundaryIndices m).length → Fin p) =
        Fintype.card Q := by
    calc
      Fintype.card
          (Fin (O.descendingBoundaryIndices m).length → Fin p) =
          Fintype.card (Fin O.r → Fin p) :=
        Fintype.card_congr σExp
      _ = Fintype.card Q :=
        Fintype.card_congr O.wordEquiv
  have htop :
      jenningsMonomialSpan (p := p) gen weight 0 = ⊤ :=
    (hspanA 0).symm.trans htopW
  let B :=
    boundedMonomialBasis gen weight htop hcard
  have hle :
      (MBData.canonical (p := p) (Q := Q) O).highWeightSpan s ≤
        A.W.J s := by
    unfold MBData.highWeightSpan basisHighSpan
    apply Submodule.span_le.mpr
    rintro a ⟨e, he, rfl⟩
    change O.jenningsMonomialBasis e ∈ A.W.J s
    rw [O.monomial_basis]
    exact
      A.W.anti he
        (A.W.ordered_jenningmonomia_finmem O.gen O.weight
          (fun i => O.descending_prefix_gen hbot hpow hcomm i) e)
  have hrank :
      Module.finrank (ZMod p) (A.W.J s) =
        Module.finrank (ZMod p)
          ((MBData.canonical (p := p) (Q := Q) O).highWeightSpan s) := by
    rw [hspanA s,
      jennings_monomial_high gen weight htop hcard s]
    change
      Module.finrank (ZMod p)
          (basisHighSpan (p := p) (Q := Q) B
            (fun e => expWeight (p := p) weight e) s) =
        Module.finrank (ZMod p)
          (basisHighSpan (p := p) (Q := Q) O.jenningsMonomialBasis
            (fun e => expWeight (p := p) O.weight e) s)
    exact
      finrank_basis_high
        B O.jenningsMonomialBasis
        (fun e => expWeight (p := p) weight e)
        (fun e => expWeight (p := p) O.weight e)
        σExp hσExp_weight s
  exact
    (Submodule.eq_of_le_of_finrank_le hle hrank.le).symm

/-- The canonical Jennings high-weight spans are multiplicative once the genuine explicit
Zassenhaus power and commutator laws hold. -/
theorem OZReps.canonhigh_weightspanmul_memzasslaws
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s))
    {s t : ℕ}
    {x y : denseGroupAlgebra p Q}
    (hx : x ∈ (MBData.canonical (p := p) (Q := Q) O).highWeightSpan s)
    (hy : y ∈ (MBData.canonical (p := p) (Q := Q) O).highWeightSpan t) :
    x * y ∈
      (MBData.canonical (p := p) (Q := Q) O).highWeightSpan (s + t) := by
  let A := O.descending_prefix_zero hbot hpow hcomm
  have hxA : x ∈ A.W.J s := by
    rw [OZReps.descprefzero_jeqcanon_highweightspan
      hm O hbot hpow hcomm s]
    exact hx
  have hyA : y ∈ A.W.J t := by
    rw [OZReps.descprefzero_jeqcanon_highweightspan
      hm O hbot hpow hcomm t]
    exact hy
  have hxyA : x * y ∈ A.W.J (s + t) :=
    A.W.mul_mem hxA hyA
  rw [OZReps.descprefzero_jeqcanon_highweightspan
    hm O hbot hpow hcomm (s + t)] at hxyA
  exact hxyA

/-- Package canonical high-weight multiplicativity for later augmentation-power arguments. -/
theorem OZReps.nonemp_highw_dataz
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    Nonempty
      (MBData.HMData
        (p := p) (Q := Q)
        (MBData.canonical (p := p) (Q := Q) O)) := by
  apply
    MBData.HMData.nonempty_canonical_high
      (p := p) (Q := Q) hm O
  intro s t x y hx hy
  exact
    OZReps.canonhigh_weightspanmul_memzasslaws
      hm O hbot hpow hcomm hx hy

/-- Genuine explicit Zassenhaus power and commutator laws imply the canonical all-word
low-coordinate vanishing statement. -/
theorem OZReps.lowweight_wordcoords_vanishzasslaws
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    O.LowWeightwordCoordsvanish := by
  rcases
      OZReps.nonemp_highw_dataz
        hm O hbot hpow hcomm with
    ⟨M⟩
  exact
    O.lowweight_wordcoorvani_forawordweig
      (low_coordinates_multiplicative O M)

/-- Genuine explicit Zassenhaus power and commutator laws yield the finite Jennings separation
data for a killed layer. -/
theorem OZReps.nonempty_separation_laws
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (O : OZReps (p := p) Q m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow : O.SelectedGeneratorBound)
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    Nonempty (JSData.{u, 0} (p := p) Q m) := by
  rcases
      OZReps.nonemp_highw_dataz
        hm O hbot hpow hcomm with
    ⟨M⟩
  exact
    separation_data_subspace
      (p := p) (Q := Q) O hbot
      (WSData.ofCanonicalMultiplicative
        (p := p) (Q := Q) (lt_of_lt_of_le Nat.zero_lt_one hm) O M)

/-- Genuine explicit Zassenhaus power and commutator laws construct finite Jennings separation
data directly for a killed layer. -/
theorem nonempty_separation_laws
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hpow :
      ∀ {r : ℕ} {x : Q},
        x ∈ zassenhausFiltration p Q r →
          x ^ p ∈ zassenhausFiltration p Q (p * r))
    (hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    Nonempty (JSData.{u, 0} (p := p) Q m) := by
  rcases
      WPForm.reps_commutator_law
        hm hbot hcomm with
    ⟨O⟩
  exact
    OZReps.nonempty_separation_laws
      hm O hbot (fun i => hpow (O.gen_mem i)) hcomm

/-- Exact-generator successor centrality constructs the cyclic-PC coordinates, while additive
exact-generator commutator bounds construct the multiplicative augmentation filtration on a
killed layer.  Selected representative powers follow directly from exact-weight provenance. -/
theorem
    nonempty_separation_law
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hsucc :
      WPForm.ExactSuccBound p Q m)
    (hexact :
      ∀ {r s : ℕ} {x y : Q},
        r < m →
        s < m →
        x ∈ exactGeneratorSet p Q r →
        y ∈ exactGeneratorSet p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    Nonempty (JSData.{u, 0} (p := p) Q m) := by
  have hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s) :=
    element_killed_bound
      hbot hexact
  rcases
    WPForm.nonempty_exact_succ
        hm hbot hsucc with
    ⟨O⟩
  exact
    OZReps.nonempty_separation_laws
      hm O.reps hbot
      (fun i =>
        exact_subset_filtration
          (exact_set_prime (O.gen_exact_mem i)))
      hcomm

/-- Exact-generator additive commutator bounds construct finite Jennings separation data on a
killed layer.  The successor-centrality input needed for cyclic-PC coordinates is a special
case of the induced full filtration law. -/
theorem jennings_separation_law
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {m : ℕ}
    (hm : 1 ≤ m)
    (hbot : zassenhausFiltration p Q m = ⊥)
    (hexact :
      ∀ {r s : ℕ} {x y : Q},
        r < m →
        s < m →
        x ∈ exactGeneratorSet p Q r →
        y ∈ exactGeneratorSet p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s)) :
    Nonempty (JSData.{u, 0} (p := p) Q m) := by
  have hcomm :
      ∀ {r s : ℕ} {x y : Q},
        x ∈ zassenhausFiltration p Q r →
        y ∈ zassenhausFiltration p Q s →
          ⁅x, y⁆ ∈ zassenhausFiltration p Q (r + s) :=
    element_killed_bound
      hbot hexact
  apply
    nonempty_separation_law
      hm hbot
  · intro r x _hr hx y
    exact
      hcomm
        (exact_subset_filtration hx)
        (by
          rw [filtration_one_top]
          exact Subgroup.mem_top y)
  · exact hexact

end TJennin
end Towers
