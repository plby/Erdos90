import Towers.Group.FiniteWindow.Dimension


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Towers

/--
The canonical positive window for the remaining bridge step: the maximal
declared relator depth.

This matches the richer bridge setup in `C.lean`, where the nontrivial window
is fixed to `1 ≤ n ≤ sup depth` and the single boundary index is `sup depth+1`.
-/
abbrev PPDatum.pos_finwindow_canoncutoff
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} : ℕ :=
  Finset.univ.sup depth

/--
Named coefficient data `a` for the canonical positive window.

The cutoff is no longer part of the choice: it is fixed canonically by the
depth function, so the only remaining base-level freedom is the coefficient
sequence itself.
-/
structure PPDatum.PosfinWindownamedCoeffpackage
    (H : PPDatum) where
  a : ℕ → ℕ
  ha0 : 0 < a 0

/--
For a fixed named coefficient package, choose the active map data on the
canonical positive window `1 ≤ n ≤ sup depth`.

This is smaller than choosing the whole positive-window active-data package at
once because the cutoff is already fixed canonically and the coefficients are
already frozen.
-/
structure PPDatum.PosfinWindownamedActivedataext
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ)
    (coeffs : H.PosfinWindownamedCoeffpackage) where
  active :
    ∀ n, 1 ≤ n → n ≤ H.pos_finwindow_canoncutoff (depth := depth) →
      H.FinWindowactiveMapdatum
        depth
        (H.pos_finwindow_canoncutoff (depth := depth))
        n
        coeffs.a

/--
A fixed finite coefficient window for the canonical positive window.

Once the cutoff is fixed to `sup depth`, the Hilbert-series bridge only needs
coefficients up to that bound; outside the window they are formally extended by
zero below.
-/
noncomputable def
    PPDatum.posfin_windownamed_coeffwindow
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (_hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (_hdepth : ∀ i, 2 ≤ depth i) :
    Fin (H.pos_finwindow_canoncutoff (depth := depth) + 1) → ℕ :=
  fun n => H.pres_aug_quotfinrank hrels n.1

/--
The finite coefficient window has positive constant term.

This separates the bare positivity requirement from the harder choice of the
whole finite window.
-/
theorem PPDatum.posfin_windnamecoef_windowzeropos
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i) :
    0 < H.posfin_windownamed_coeffwindow hrels hmem hdepth 0 := by
  simpa [PPDatum.posfin_windownamed_coeffwindow] using
    H.pres_augquot_finrankpos hrels 0

/--
The named coefficient sequence on `ℕ` is the formal zero-extension of the
finite coefficient window on `0, ..., sup depth`.
-/
noncomputable def
    PPDatum.posfin_windownamed_coeffsequence
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i) :
    ℕ → ℕ :=
  fun n =>
    if hn : n ≤ H.pos_finwindow_canoncutoff (depth := depth) then
      H.posfin_windownamed_coeffwindow hrels hmem hdepth
        ⟨n, Nat.lt_succ_of_le hn⟩
    else 0

/--
Inside the canonical coefficient window, the zero-extended sequence agrees
with the underlying finite data.
-/
@[simp] theorem PPDatum.posfin_windnamecoef_sequeqwind
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i)
    {n : ℕ}
    (hn : n ≤ H.pos_finwindow_canoncutoff (depth := depth)) :
    H.posfin_windownamed_coeffsequence hrels hmem hdepth n =
      H.posfin_windownamed_coeffwindow hrels hmem hdepth
        ⟨n, Nat.lt_succ_of_le hn⟩ := by
  simp [PPDatum.posfin_windownamed_coeffsequence, hn]

/--
Outside the canonical coefficient window, the named coefficient sequence
vanishes by construction.
-/
@[simp]
theorem PPDatum.posfinwindow_namecoefsequ_eqzerogtcutoff
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i)
    {n : ℕ}
    (hn : H.pos_finwindow_canoncutoff (depth := depth) < n) :
    H.posfin_windownamed_coeffsequence hrels hmem hdepth n = 0 := by
  simp [PPDatum.posfin_windownamed_coeffsequence, Nat.not_le_of_gt hn]

/--
If `depth i ≤ n ≤ sup depth`, then the shifted index `n - depth i` still lies
in the canonical coefficient window.
-/
theorem PPDatum.posfin_windownamedsub_depthlecutoff
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ}
    {n : ℕ}
    (hnN : n ≤ H.pos_finwindow_canoncutoff (depth := depth))
    {i : Fin H.relationRank}
    (_hdi : depth i ≤ n) :
    n - depth i ≤ H.pos_finwindow_canoncutoff (depth := depth) := by
  omega

/--
Consequently, within the active window, the shifted coefficient `a (n - depth
i)` is represented by the corresponding entry of the finite coefficient window.
-/
@[simp]
theorem PPDatum.posfinwindow_namecoefsequ_subdepeqwin
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i)
    {n : ℕ}
    (hnN : n ≤ H.pos_finwindow_canoncutoff (depth := depth))
    {i : Fin H.relationRank}
    (hdi : depth i ≤ n) :
    H.posfin_windownamed_coeffsequence hrels hmem hdepth (n - depth i) =
      H.posfin_windownamed_coeffwindow hrels hmem hdepth
        ⟨n - depth i, Nat.lt_succ_of_le
          (H.posfin_windownamedsub_depthlecutoff (depth := depth) hnN hdi)⟩ := by
  simp [PPDatum.posfin_windnamecoef_sequeqwind,
    H.posfin_windownamedsub_depthlecutoff (depth := depth) hnN hdi]

/--
The sequence obtained by zero-extension still has positive constant term.
-/
theorem PPDatum.posfin_windnamecoef_sequencezeropos
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i) :
    0 < H.posfin_windownamed_coeffsequence hrels hmem hdepth 0 := by
  simpa [PPDatum.posfin_windownamed_coeffsequence] using
    H.posfin_windnamecoef_windowzeropos hrels hmem hdepth

/--
A fixed named coefficient package for the canonical positive window.

This is now formal assembly from the finite coefficient window, its positivity
proof, and the zero-extension above.
-/
noncomputable def
    PPDatum.posfin_windownamed_coeffpackage
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i) :
    H.PosfinWindownamedCoeffpackage :=
  by
    refine {
      a := H.posfin_windownamed_coeffsequence hrels hmem hdepth
      ha0 := H.posfin_windnamecoef_sequencezeropos hrels hmem hdepth
    }

/--
The canonical cutoff attached to the named positive-window package layer.
-/
abbrev PPDatum.pos_finwindow_namedcutoff
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (_hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (_hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (_hdepth : ∀ i, 2 ≤ depth i) :=
  H.pos_finwindow_canoncutoff (depth := depth)

/--
The coefficient sequence `a` carried by the fixed named coefficient package.
-/
abbrev PPDatum.pos_finwindow_namedcoeffs
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i) :=
  (H.posfin_windownamed_coeffpackage hrels hmem hdepth).a

/--
The positivity witness `0 < a 0` carried by the fixed named coefficient
package.
-/
abbrev PPDatum.posfin_windownamed_coeffzeropos
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i) :=
  (H.posfin_windownamed_coeffpackage hrels hmem hdepth).ha0

/--
For the fixed named coefficient package, choose only the underlying
positive-window active spaces on the canonical cutoff.

This bookkeeping part is concrete: the genuinely nontrivial choice is the
linear map on these fixed spaces, which is separated below.
-/
noncomputable def
    PPDatum.posfin_windownamed_actispacdatu
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (_hn1 : 1 ≤ n)
    (_hnN : n ≤ H.pos_finwindow_canoncutoff (depth := depth)) :
    H.FWSpaced
      depth
      (H.pos_finwindow_canoncutoff (depth := depth))
      n
      (H.pos_finwindow_namedcoeffs hrels hmem hdepth) :=
  by
    exact
      H.coordfin_windowactive_spacedatum
        (depth := depth)
        (N := H.pos_finwindow_canoncutoff (depth := depth))
        (n := n)
        (a := H.pos_finwindow_namedcoeffs hrels hmem hdepth)

/--
At the first positive index `n = 1`, no relator contributes to the active
recurrence because all declared depths are at least `2`.

This isolates the base-step bookkeeping from the genuinely recursive interior
window.
-/
theorem PPDatum.posfinwindow_nameacticont_oneeqzero
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i) :
    (∑ i : Fin H.relationRank,
      if depth i ≤ 1 then
        (H.pos_finwindow_namedcoeffs hrels hmem hdepth) (1 - depth i)
      else 0) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hnot : ¬ depth i ≤ 1 := by
    have hi2 : 2 ≤ depth i := hdepth i
    omega
  simp [hnot]

/--
Named active-map data for the positive window `1 ≤ n ≤ N`, with the base
choice `(N, a)` included.

This separates the positive-window bookkeeping from the single boundary datum,
which only depends on the same base `(N, a)`.
-/
structure PPDatum.PosfinWindownamedActidatapack
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ) where
  N : ℕ
  a : ℕ → ℕ
  ha0 : 0 < a 0
  active :
    ∀ n, 1 ≤ n → n ≤ N →
      H.FinWindowactiveMapdatum depth N n a

/--
Once the fixed active-data package is chosen, the only remaining boundary
bookkeeping task is to choose the relator-side spaces at the index `N + 1`.

As in the active-window case, this concrete space choice is separated from the
later choice of the actual boundary linear map.
-/
noncomputable def
    PPDatum.posfin_windownamed_boundspacedatum
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i) :
    H.FBSpaced
      depth
      (H.pos_finwindow_namedcutoff hrels hmem hdepth)
      (H.pos_finwindow_namedcoeffs hrels hmem hdepth) :=
  by
    exact
      H.coordfin_windowbound_relaspacdatu
        (depth := depth)
        (N := H.pos_finwindow_namedcutoff hrels hmem hdepth)
        (a := H.pos_finwindow_namedcoeffs hrels hmem hdepth)

/--
For the fixed named boundary spaces, choose the actual relator-only boundary
linear map at the index `N + 1`.

Again the real content is arithmetic: after the coordinate spaces are fixed,
the boundary finrank comparison is exactly the corresponding coefficient
inequality.
-/
theorem PPDatum.posfin_windownamed_cutoffgedepth
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ}
    (i : Fin H.relationRank) :
    depth i ≤ H.pos_finwindow_canoncutoff (depth := depth) := by
  exact Finset.le_sup (s := Finset.univ) (f := depth) (by simp)

end Towers
