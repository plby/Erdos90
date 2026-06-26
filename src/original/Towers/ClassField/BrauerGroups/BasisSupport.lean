import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Finsupp.SMul

/-!
# Chapter IV, Proposition 2.5

Milne calls a nonzero vector of a subspace *primordial* (relative to a fixed
basis) when its coordinate support is minimal and one of its nonzero
coordinates has been normalized to `1`.  The main point is that primordial
vectors span every subspace, even when the ambient vector space is infinite
dimensional.
-/

namespace Towers.CField.BGroups

open Module

variable {k ι V : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

/-- The finite set of basis coordinates occurring in a vector. -/
noncomputable def basisSupport (b : Basis ι k V) (v : V) : Finset ι :=
  (b.repr v).support

@[simp]
theorem basisSupport_zero (b : Basis ι k V) : basisSupport b (0 : V) = ∅ := by
  simp [basisSupport]

theorem basisSupport_smul (b : Basis ι k V) {c : k} (hc : c ≠ 0) (v : V) :
    basisSupport b (c • v) = basisSupport b v := by
  simpa [basisSupport] using
    (Finsupp.support_smul_eq (g := b.repr v) hc)

/-- A nonzero vector in `W` has minimal coordinate support among the nonzero
vectors of `W` whose support is contained in its own. -/
def ISMin (b : Basis ι k V) (W : Submodule k V) (w : V) : Prop :=
  w ∈ W ∧ w ≠ 0 ∧
    ∀ u ∈ W, u ≠ 0 → basisSupport b u ⊆ basisSupport b w →
      basisSupport b w ⊆ basisSupport b u

/-- A primordial vector is a support-minimal vector with one coordinate
normalized to `1`. -/
def IsPrimordial (b : Basis ι k V) (W : Submodule k V) (w : V) : Prop :=
  ISMin b W w ∧ ∃ i, b.repr w i = 1

theorem ISMin.smul {b : Basis ι k V} {W : Submodule k V} {w : V}
    (hw : ISMin b W w) {c : k} (hc : c ≠ 0) :
    ISMin b W (c • w) := by
  rcases hw with ⟨hwW, hw0, hmin⟩
  refine ⟨W.smul_mem c hwW, smul_ne_zero hc hw0, ?_⟩
  intro u huW hu0 husub
  rw [basisSupport_smul b hc] at husub ⊢
  exact hmin u huW hu0 husub

/-- Milne, Proposition IV.2.5(a): a nonzero vector whose support is contained
in that of a support-minimal vector is precisely a nonzero scalar multiple of
that vector. -/
theorem support_minimal_smul (b : Basis ι k V) (W : Submodule k V)
    {w w' : V} (hw : ISMin b W w) (hw'W : w' ∈ W) (hw'0 : w' ≠ 0) :
    basisSupport b w' ⊆ basisSupport b w ↔
      ∃ c : k, c ≠ 0 ∧ w' = c • w := by
  classical
  constructor
  · intro hsub
    have hrepr0 : b.repr w' ≠ 0 := fun h ↦
      hw'0 (b.repr.injective (by simpa using h))
    obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hrepr0
    have hw'j : b.repr w' j ≠ 0 := by
      simpa [basisSupport] using hj
    have hjw : j ∈ basisSupport b w := hsub (by simpa [basisSupport] using hj)
    have hwj : b.repr w j ≠ 0 := by
      simpa [basisSupport] using hjw
    let c : k := b.repr w' j / b.repr w j
    let u : V := w' - c • w
    have huW : u ∈ W := W.sub_mem hw'W (W.smul_mem c hw.1)
    have husub : basisSupport b u ⊆ basisSupport b w := by
      intro i hi
      by_contra hiw
      have hwi : b.repr w i = 0 := by
        simpa [basisSupport, Finsupp.mem_support_iff] using hiw
      have hw'i : b.repr w' i = 0 := by
        by_contra hw'i
        exact hiw (hsub (by simpa [basisSupport, Finsupp.mem_support_iff] using hw'i))
      have hui : b.repr u i = 0 := by
        simp [u, hw'i, hwi]
      have hui_ne : b.repr u i ≠ 0 := by
        simpa [basisSupport, Finsupp.mem_support_iff] using hi
      exact hui_ne hui
    have hju : j ∉ basisSupport b u := by
      simp [basisSupport, u, c, hwj]
    have hu0 : u = 0 := by
      by_contra hu0
      exact hju (hw.2.2 u huW hu0 husub hjw)
    refine ⟨c, div_ne_zero hw'j hwj, ?_⟩
    exact sub_eq_zero.mp hu0
  · rintro ⟨c, hc, rfl⟩
    exact (basisSupport_smul b hc w).le

/-- Milne, Proposition IV.2.5(b): the primordial elements of a subspace span
the entire subspace. -/
theorem span_primordial_eq (b : Basis ι k V) (W : Submodule k V) :
    Submodule.span k {w : V | IsPrimordial b W w} = W := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    intro w hw
    exact hw.1.1
  · intro w hwW
    induction hsw : basisSupport b w using Finset.strongInduction generalizing w with
    | H s ih =>
      by_cases hw0 : w = 0
      · simp [hw0]
      by_cases hmin : ISMin b W w
      · have hs : (basisSupport b w).Nonempty := by
          rw [basisSupport, Finsupp.support_nonempty_iff]
          exact fun h ↦ hw0 (b.repr.injective (by simpa using h))
        obtain ⟨j, hj⟩ := hs
        have hwj : b.repr w j ≠ 0 := by
          simpa [basisSupport] using hj
        let u : V := (b.repr w j)⁻¹ • w
        have huprim : IsPrimordial b W u := by
          refine ⟨hmin.smul (inv_ne_zero hwj), ⟨j, ?_⟩⟩
          simp [u, hwj]
        have huw : w = b.repr w j • u := by
          simp [u, hwj]
        rw [huw]
        exact Submodule.smul_mem _ _ (Submodule.subset_span huprim)
      · have hnotAll : ¬ ∀ u, u ∈ W → u ≠ 0 →
            basisSupport b u ⊆ basisSupport b w →
            basisSupport b w ⊆ basisSupport b u := by
          intro hall
          exact hmin ⟨hwW, hw0, hall⟩
        push Not at hnotAll
        have hnot :
            ∃ u, u ∈ W ∧ u ≠ 0 ∧ basisSupport b u ⊆ basisSupport b w ∧
              ¬basisSupport b w ⊆ basisSupport b u := hnotAll
        obtain ⟨u, huW, hu0, husub, hnsub⟩ := hnot
        have hult : basisSupport b u ⊂ basisSupport b w :=
          Finset.ssubset_iff_subset_ne.mpr
            ⟨husub, fun h ↦ hnsub h.symm.le⟩
        have hultS : basisSupport b u ⊂ s := by simpa [hsw] using hult
        have huSpan : u ∈ Submodule.span k {v : V | IsPrimordial b W v} :=
          ih (basisSupport b u) hultS huW rfl
        have hrepru0 : b.repr u ≠ 0 := fun h ↦
          hu0 (b.repr.injective (by simpa using h))
        obtain ⟨j, hju⟩ := Finsupp.support_nonempty_iff.mpr hrepru0
        have huj : b.repr u j ≠ 0 := by
          simpa [basisSupport] using hju
        have hjw : j ∈ basisSupport b w := husub (by simpa [basisSupport] using hju)
        let c : k := b.repr w j / b.repr u j
        let v : V := w - c • u
        have hvW : v ∈ W := W.sub_mem hwW (W.smul_mem c huW)
        have hvsub : basisSupport b v ⊆ basisSupport b w := by
          intro i hi
          by_contra hiw
          have hwi : b.repr w i = 0 := by
            simpa [basisSupport, Finsupp.mem_support_iff] using hiw
          have hui : b.repr u i = 0 := by
            by_contra hui
            exact hiw (husub (by simpa [basisSupport, Finsupp.mem_support_iff] using hui))
          have hvi : b.repr v i = 0 := by
            simp [v, hwi, hui]
          have hvi_ne : b.repr v i ≠ 0 := by
            simpa [basisSupport, Finsupp.mem_support_iff] using hi
          exact hvi_ne hvi
        have hjv : j ∉ basisSupport b v := by
          simp [basisSupport, v, c, huj]
        have hvlt : basisSupport b v ⊂ basisSupport b w :=
          Finset.ssubset_iff_subset_ne.mpr
            ⟨hvsub, fun h ↦ hjv (h ▸ hjw)⟩
        have hvltS : basisSupport b v ⊂ s := by simpa [hsw] using hvlt
        have hvSpan : v ∈ Submodule.span k {x : V | IsPrimordial b W x} :=
          ih (basisSupport b v) hvltS hvW rfl
        have hwdecomp : w = v + c • u := by
          simp [v]
        rw [hwdecomp]
        exact Submodule.add_mem _ hvSpan (Submodule.smul_mem _ c huSpan)

end Towers.CField.BGroups
