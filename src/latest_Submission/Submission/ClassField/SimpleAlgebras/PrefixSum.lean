import Submission.ClassField.SimpleAlgebras.CompositionFactor

/-!
# Milne, Class Field Theory, Corollary IV.1.3

The decompositions in Corollary IV.1.3 give composition series whose factors
are the displayed simple summands. Jordan--Holder then supplies a permutation
matching isomorphic factors. This file constructs those filtrations and carries
out the argument.
-/

namespace Submission.CField.SAlgebr

universe u v w

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-- The sum of the members of `V` whose indices are strictly below `m`. -/
def prefixSum {n : ℕ} (V : Fin n → Submodule R M) (m : ℕ) : Submodule R M :=
  ⨆ i : Fin n, ⨆ (_ : i.val < m), V i

@[simp]
theorem prefixSum_zero {n : ℕ} (V : Fin n → Submodule R M) :
    prefixSum V 0 = ⊥ := by
  simp [prefixSum]

theorem prefixSum_succ {n : ℕ} (V : Fin n → Submodule R M)
    (m : ℕ) (hm : m < n) :
    prefixSum V (m + 1) = prefixSum V m ⊔ V ⟨m, hm⟩ := by
  apply le_antisymm
  · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
    by_cases him : i.val < m
    · exact le_sup_of_le_left <| le_iSup_of_le i <| le_iSup_of_le him le_rfl
    · have hieq : i = ⟨m, hm⟩ := by
        apply Fin.ext
        exact Nat.le_antisymm (Nat.le_of_lt_succ hi) (Nat.le_of_not_gt him)
      exact hieq ▸ le_sup_right
  · refine sup_le ?_ ?_
    · exact iSup_le fun i ↦ iSup_le fun hi ↦
        le_iSup_of_le i <| le_iSup_of_le (Nat.lt_succ_of_lt hi) le_rfl
    · exact le_iSup_of_le ⟨m, hm⟩ <|
        le_iSup_of_le (Nat.lt_succ_self m) le_rfl

theorem prefixSum_length {n : ℕ} (V : Fin n → Submodule R M) :
    prefixSum V n = ⨆ i, V i := by
  apply le_antisymm
  · exact iSup_le fun i ↦ iSup_le fun _ ↦ le_iSup V i
  · exact iSup_le fun i ↦
      le_iSup_of_le i <| le_iSup_of_le i.isLt le_rfl

theorem disjoint_prefixSum {n : ℕ} {V : Fin n → Submodule R M}
    (hV : iSupIndep V) (i : Fin n) :
    Disjoint (V i) (prefixSum V i.val) := by
  simpa only [prefixSum, Set.mem_setOf_eq] using
    hV.disjoint_biSup (x := i) (y := {j | j.val < i.val}) (by simp)

/-- A finite independent family of simple submodules gives the composition
series formed by its prefix sums. -/
noncomputable def compositionSimpleDecomposition {n : ℕ}
    (V : Fin n → Submodule R M) (hVind : iSupIndep V)
    (hVsimple : ∀ i, IsSimpleModule R (V i)) :
    CompositionSeries (Submodule R M) where
  length := n
  toFun i := prefixSum V i.val
  step i := by
    change prefixSum V i.val ⋖ prefixSum V (i.val + 1)
    rw [prefixSum_succ V i i.isLt]
    letI : IsSimpleModule R (V i) := hVsimple i
    apply covBy_sup_of_inf_covBy_right
    rw [(disjoint_prefixSum hVind i).symm.eq_bot]
    exact (isSimpleModule_iff_isAtom.mp inferInstance).bot_covBy

@[simp]
theorem composition_simple_head {n : ℕ}
    (V : Fin n → Submodule R M) (hVind : iSupIndep V)
    (hVsimple : ∀ i, IsSimpleModule R (V i)) :
    (compositionSimpleDecomposition V hVind hVsimple).head = ⊥ :=
  prefixSum_zero V

theorem composition_simple_last {n : ℕ}
    (V : Fin n → Submodule R M) (hVind : iSupIndep V)
    (hVsimple : ∀ i, IsSimpleModule R (V i))
    (hVtop : ⨆ i, V i = ⊤) :
    (compositionSimpleDecomposition V hVind hVsimple).last = ⊤ := by
  exact (prefixSum_length V).trans hVtop

/-- The factor added at step `i` of the prefix-sum composition series is the
simple summand `V i`. -/
theorem composition_simple_decomposition {n : ℕ}
    (V : Fin n → Submodule R M) (hVind : iSupIndep V)
    (hVsimple : ∀ i, IsSimpleModule R (V i)) (i : Fin n) :
    Nonempty
      (compositionFactor (compositionSimpleDecomposition V hVind hVsimple) i ≃ₗ[R]
        V i) := by
  let P := prefixSum V i.val
  let B := prefixSum V (i.val + 1)
  have hB : B = P ⊔ V i := prefixSum_succ V i i.isLt
  have hPB : P ≤ B := hB.symm ▸ le_sup_left
  have hVB : V i ≤ B := hB.symm ▸ le_sup_right
  have hdisj : Disjoint P (V i) := (disjoint_prefixSum hVind i).symm
  have hcompl : IsCompl (P.comap B.subtype) ((V i).comap B.subtype) := by
    have hic : IsCompl (⟨P, hPB⟩ : Set.Iic B) ⟨V i, hVB⟩ :=
      Set.Iic.isCompl_iff.mpr ⟨hdisj, hB.symm⟩
    apply (B.mapIic.isCompl_iff).mpr
    have hmapP : B.mapIic (P.comap B.subtype) = ⟨P, hPB⟩ := by
      apply Subtype.ext
      simp [Submodule.map_comap_subtype, hPB]
    have hmapV : B.mapIic ((V i).comap B.subtype) = ⟨V i, hVB⟩ := by
      apply Subtype.ext
      simp [Submodule.map_comap_subtype, hVB]
    rw [hmapP, hmapV]
    exact hic
  exact ⟨((P.comap B.subtype).quotientEquivOfIsCompl
    ((V i).comap B.subtype) hcompl).trans
      (Submodule.comapSubtypeEquivOfLe hVB)⟩

/-- **Corollary IV.1.3.** If the factors of two composition series are
identified with two indexed families of modules, then a permutation matches
linearly equivalent members of those families. -/
theorem composition_up_permutation
    (s t : CompositionSeries (Submodule R M))
    (hs0 : s.head = ⊥) (hs1 : s.last = ⊤)
    (ht0 : t.head = ⊥) (ht1 : t.last = ⊤)
    (V : Fin s.length → Type w) (W : Fin t.length → Type w)
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    (hV : ∀ i, Nonempty (compositionFactor s i ≃ₗ[R] V i))
    (hW : ∀ i, Nonempty (compositionFactor t i ≃ₗ[R] W i)) :
    ∃ e : Fin s.length ≃ Fin t.length,
      ∀ i, Nonempty (V i ≃ₗ[R] W (e i)) := by
  let h := compositionSeries_equivalent s t hs0 hs1 ht0 ht1
  refine ⟨h.choose, ?_⟩
  intro i
  obtain ⟨eV⟩ := hV i
  obtain ⟨eW⟩ := hW (h.choose i)
  have hfactor := h.choose_spec i
  change Nonempty
    (compositionFactor s i ≃ₗ[R] compositionFactor t (h.choose i)) at hfactor
  obtain ⟨efactor⟩ := hfactor
  exact ⟨eV.symm.trans (efactor.trans eW)⟩

/-- **Corollary IV.1.3.** Two finite internal direct-sum decompositions into
simple submodules have the same number of summands, up to permutation and
linear equivalence. -/
theorem simpleDecompositions_unique
    {r s : ℕ}
    (V : Fin r → Submodule R M) (W : Fin s → Submodule R M)
    (hVind : iSupIndep V) (hVtop : ⨆ i, V i = ⊤)
    (hWind : iSupIndep W) (hWtop : ⨆ i, W i = ⊤)
    (hVsimple : ∀ i, IsSimpleModule R (V i))
    (hWsimple : ∀ i, IsSimpleModule R (W i)) :
    ∃ e : Fin r ≃ Fin s, ∀ i, Nonempty (V i ≃ₗ[R] W (e i)) := by
  let Vseries := compositionSimpleDecomposition V hVind hVsimple
  let Wseries := compositionSimpleDecomposition W hWind hWsimple
  exact composition_up_permutation Vseries Wseries
    (composition_simple_head V hVind hVsimple)
    (composition_simple_last V hVind hVsimple hVtop)
    (composition_simple_head W hWind hWsimple)
    (composition_simple_last W hWind hWsimple hWtop)
    (fun i ↦ V i) (fun i ↦ W i)
    (composition_simple_decomposition V hVind hVsimple)
    (composition_simple_decomposition W hWind hWsimple)

end Submission.CField.SAlgebr
