import Towers.Group.Zassenhaus.TriangularGHLaw
import Towers.Group.Zassenhaus.CollectionBoundThree
import Towers.Group.Zassenhaus.CoordinateDivisibilityBridge

namespace Towers

universe u

open scoped commutatorElement

namespace TCTex


/--
TeX Lemma 11 is the formal transport step from the free nilpotent truncation
to `Q / γ_n(Q)`: lift the target element through the surjective free quotient
map, apply the free Hall-coordinate bound, then map the normalized list back.
-/
lemma truncated_collection_truncation
    {p d n k : ℕ} [Fact p.Prime]
    (hfree : TruncationCollectionBound.{u} p d n k) :
    TruncatedCollectionBound.{u} p d n k := by
  intro Q _instGroupQ _instFiniteQ _hQ t ht x hx
  let F : Type u := FreeGroup (FreeGenerator.{u} d)
  let Nf : Subgroup F := Subgroup.lowerCentralSeries F (n - 1)
  let Nq : Subgroup Q := Subgroup.lowerCentralSeries Q (n - 1)
  let qQ : Q →* Q ⧸ Nq := QuotientGroup.mk' Nq
  let φ : F →* Q := FreeGroup.lift fun i : FreeGenerator.{u} d => t i.down
  have hφ : Function.Surjective φ := by
    have hRange :
        Set.range (fun i : FreeGenerator.{u} d => t i.down) =
          Set.range t := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.down, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨ULift.up i, rfl⟩
    rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure, hRange]
    exact ht
  have hφN :
      Nf ≤ (qQ.comp φ).ker := by
    intro y hy
    change qQ (φ y) = 1
    apply (QuotientGroup.eq_one_iff (N := Nq) (φ y)).mpr
    exact Subgroup.lowerCentralSeries.map φ (n - 1) (Subgroup.mem_map_of_mem φ hy)
  let φbar : F ⧸ Nf →* Q ⧸ Nq :=
    QuotientGroup.lift Nf (qQ.comp φ) hφN
  have hqQ : Function.Surjective qQ := QuotientGroup.mk'_surjective Nq
  have hφbar : Function.Surjective φbar := by
    exact
      QuotientGroup.lift_surjective_of_surjective
        Nf (qQ.comp φ) (hqQ.comp hφ) hφN
  have hxQuot :
      qQ x ∈ zassenhausFiltration p (Q ⧸ Nq) n := by
    have hxMap :
        qQ x ∈ Subgroup.map qQ (zassenhausFiltration p Q n) :=
      Subgroup.mem_map_of_mem qQ hx
    rw [filtration_without_width
      n qQ hqQ] at hxMap
    exact hxMap
  have hxFreeMap :
      qQ x ∈ Subgroup.map φbar
        (zassenhausFiltration p (F ⧸ Nf) n) := by
    rw [filtration_without_width
      n φbar hφbar]
    exact hxQuot
  rcases hxFreeMap with ⟨y, hy, hyMap⟩
  change LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n at y
  change y ∈ zassenhausFiltration
      p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n at hy
  have hyList :
      BNZass p d n k y :=
    hfree y hy
  simpa [φbar, hyMap] using hyList.mapHom φbar

/--
TeX Lemma 12, before the final residual completion: a quotient-level bounded
factorization lifts to an ambient normalized list whose residual error lies in
`γ_n(Q)`.
-/
def LiftedFactorizationBound
    (p d n k : ℕ) [Fact p.Prime] :
    Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q],
    IsPGroup p Q →
      ∀ t : Fin d → Q,
        GeneratedBy t →
          ∀ x : Q,
            x ∈ zassenhausFiltration p Q n →
              ∃ L : List (BSValue p d n Q),
                L.length ≤ k ∧
                  x * (L.map BSValue.eval).prod⁻¹ ∈
                    Subgroup.lowerCentralSeries Q (n - 1)

/--
TeX Lemma 5 plus the residual part of Lemma 13, isolated as the other hard
leaf: every `γ_n(Q)` residual has a uniformly bounded normalized factorization
using the weight-`n` commutator slot.
-/
def LowerCompletionBound
    (p d n k : ℕ) [Fact p.Prime] :
    Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q],
    IsPGroup p Q →
      ∀ t : Fin d → Q,
        GeneratedBy t →
          ∀ z : Q,
            z ∈ Subgroup.lowerCentralSeries Q (n - 1) →
              BNZass p d n k z

/--
The lifted quotient factorization is a formal consequence of the quotient
collection leaf: lift the chosen quotient arguments slotwise and read equality
in the quotient as membership in `γ_n(Q)`.
-/
lemma lifted_factorization_collection
    {p d n k : ℕ} [Fact p.Prime]
    (htrunc : TruncatedCollectionBound.{u} p d n k) :
    LiftedFactorizationBound.{u} p d n k := by
  intro Q _instGroupQ _instFiniteQ hQ t ht x hx
  let N : Subgroup Q := Subgroup.lowerCentralSeries Q (n - 1)
  obtain ⟨Lbar, hLbarLen, hLbarProd⟩ := htrunc Q hQ t ht x hx
  let L : List (BSValue p d n Q) :=
    liftScheduledList N Lbar
  refine ⟨L, ?_, ?_⟩
  · simpa [L, lift_scheduled_length] using hLbarLen
  · have hmapProd :
        QuotientGroup.mk' N
            ((L.map BSValue.eval).prod) =
          (Lbar.map BSValue.eval).prod := by
        simpa [L] using
          (lift_scheduled_prod
            (p := p) (d := d) (n := n) N Lbar)
    have hquot :
        QuotientGroup.mk' N
            ((L.map BSValue.eval).prod) =
          lowerCentralTruncation Q n x := by
        rw [hmapProd, hLbarProd]
    apply
      (QuotientGroup.eq_one_iff
        (N := N)
        (x * (L.map BSValue.eval).prod⁻¹)).mp
    calc
      QuotientGroup.mk' N
          (x * (L.map BSValue.eval).prod⁻¹) =
          lowerCentralTruncation Q n x *
            (QuotientGroup.mk' N
              ((L.map BSValue.eval).prod))⁻¹ := by
            simp only [map_mul, map_inv]
            rfl
      _ =
          lowerCentralTruncation Q n x *
            (lowerCentralTruncation Q n x)⁻¹ := by
            exact
              congrArg
                (fun y => lowerCentralTruncation Q n x * y⁻¹)
                hquot
      _ = 1 := by simp

/--
TeX Lemmas 12-13 assemble exactly as written: factor `x` modulo `γ_n(Q)`,
factor the residual `x u⁻¹` inside `γ_n(Q)`, then concatenate the residual
list before the lifted quotient list.
-/
lemma bounded_normalized_lifted
    {p d n kTrunc kResidual : ℕ} [Fact p.Prime]
    (htrunc : LiftedFactorizationBound.{u} p d n kTrunc)
    (hResidual : LowerCompletionBound.{u} p d n kResidual) :
    BoundedNormalizedList.{u}
      p d n (kResidual + kTrunc) := by
  intro Q _instGroupQ _instFiniteQ hQ t ht x hx
  obtain ⟨Lu, hLuLen, hResidualMem⟩ := htrunc Q hQ t ht x hx
  obtain ⟨Lz, hLzLen, hLzProd⟩ :=
    hResidual Q hQ t ht
      (x * (Lu.map BSValue.eval).prod⁻¹)
      hResidualMem
  refine ⟨Lz ++ Lu, ?_, ?_⟩
  · simpa [List.length_append] using Nat.add_le_add hLzLen hLuLen
  · rw [List.map_append, List.prod_append, hLzProd]
    group

/--
The list-level bounded statement packages into the fixed repeated schedule
requested by `PGColl`.
-/
lemma te_x_leaves
    {p d n kTrunc kResidual : ℕ} [Fact p.Prime]
    (htrunc : TruncatedCollectionBound.{u} p d n kTrunc)
    (hResidual : LowerCompletionBound.{u} p d n kResidual) :
    Nonempty (PGColl.{u} p d n) := by
  have hLifted :
      LiftedFactorizationBound.{u} p d n kTrunc :=
    lifted_factorization_collection
      htrunc
  have hList :
      BoundedNormalizedList.{u}
        p d n (kResidual + kTrunc) :=
    bounded_normalized_lifted
      hLifted
      hResidual
  exact
    Nonempty.map
      FSColl.toCollection
      (collection_normalized_list hList)

/--
TeX Lemma 5 should prove this existence statement.  The remaining content is
the bounded lower-central width argument for finite nilpotent `d`-generated
`p`-groups, applied to `γ_n(Q)`.
-/
theorem lower_completion_bound
    (p d n : ℕ) [Fact p.Prime]
    (hd : 0 < d)
    (hn : 2 ≤ n) :
    ∃ k : ℕ, LowerCompletionBound.{u} p d n k := by
  refine ⟨Fintype.card (LowerTailTuple d (n - 1)), ?_⟩
  intro Q _instGroupQ _instFiniteQ hQ t ht z hz
  letI : Group.IsNilpotent Q := hQ.isNilpotent
  have hfactor :
      ONFacta d (n - 1) t z :=
    normed_factorization_nilpotent
      hd t ht hz
  have hlist :
      BNZass
        p d ((n - 1) + 1)
        (Fintype.card (LowerTailTuple d (n - 1))) z :=
    normalized_normed_factorization
      (p := p) hfactor
  have hnOne : 1 ≤ n := by
    omega
  simpa [Nat.sub_add_cancel hnOne] using hlist

/--
Low-depth free-truncation collection bounds transport to quotient-level
collection bounds.
-/
theorem truncated_n_four
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4) :
    ∃ k : ℕ, TruncatedCollectionBound.{u} p d n k := by
  obtain ⟨k, hfree⟩ :=
    free_n_four
      p d n hn hn4
  exact
    ⟨k,
      truncated_collection_truncation
        hfree⟩

/--
Any free-truncation collection bound supplies the finite-`p`-group collection
package used by the profinite compactness argument.
-/
theorem free_truncation_bound
    (p d n k : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (hfree : TruncationCollectionBound.{u} p d n k) :
    Nonempty (PGColl.{u} p d n) := by
  by_cases hd : d ≤ 1
  · exact
      Nonempty.map
        FSColl.toCollection
        (p_collection_generators
          (p := p) (d := d) (n := n) hd)
  have hdpos : 0 < d := by omega
  have hTrunc :
      TruncatedCollectionBound.{u} p d n k :=
    truncated_collection_truncation
      hfree
  obtain ⟨kResidual, hResidual⟩ :=
    lower_completion_bound p d n hdpos hn
  exact
    te_x_leaves
      (kTrunc := k) (kResidual := kResidual)
      hTrunc hResidual

/--
Existential form of
`free_truncation_bound`.
-/
theorem collection_truncation_bound
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (hfree : ∃ k : ℕ,
      TruncationCollectionBound.{u} p d n k) :
    Nonempty (PGColl.{u} p d n) := by
  rcases hfree with ⟨k, hk⟩
  exact
    free_truncation_bound
      p d n k hn hk

/--
Concrete Hall-coordinate divisibility on the free nilpotent truncation is
enough to build the finite-`p`-group collection package.
-/
theorem collection_concrete_divisibility
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (hdiv :
      let H : ∀ s : ℕ, BCWta.{u} d s :=
        collectionConcreteCommutators.{u} d
      let hH :
        ∀ s : ℕ,
          1 ≤ s →
            s < n →
              (H s).FormsAssocGradedbasis (n := n) :=
        fun s hs hsn =>
          concrete_forms_associated
            d n s hs hsn
      ∀ y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
        y ∈ zassenhausFiltration
          p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n →
          HallCoordinateLattice (p := p) hn H hH y) :
    Nonempty (PGColl.{u} p d n) := by
  dsimp only at hdiv
  obtain ⟨k, hfree⟩ :=
    truncation_collection_divisibility
      p d n hn
      (fun s hs hsn =>
        concrete_forms_associated
          d n s hs hsn)
      hdiv
  exact
    free_truncation_bound
      p d n k hn hfree

end TCTex

/--
For depths at most four, the concrete Hall collection machinery supplies the
uniform finite-`p`-group Zassenhaus collection package.
-/
theorem collection_n_four
    (p d n : ℕ) [Fact p.Prime]
    (hn4 : n ≤ 4) :
    Nonempty (PGColl.{u} p d n) := by
  by_cases hn : n ≤ 1
  · exact
      Nonempty.map
        FSColl.toCollection
        (p_collection_one p d n hn)
  by_cases hd : d ≤ 1
  · exact
      Nonempty.map
        FSColl.toCollection
        (p_collection_generators
          (p := p) (d := d) (n := n) hd)
  have hn2 : 2 ≤ n := by omega
  have hdpos : 0 < d := by omega
  obtain ⟨kTrunc, hTrunc⟩ :=
    TCTex.truncated_n_four
      p d n hn2 hn4
  obtain ⟨kResidual, hResidual⟩ :=
    TCTex.lower_completion_bound
      p d n hdpos hn2
  exact
    TCTex.te_x_leaves
      (kTrunc := kTrunc) (kResidual := kResidual) hTrunc hResidual

end Towers
