import Submission.Group.PresentedAugmentationQuotient


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Submission

/--
The first remaining classical frontier: for every minimal presentation with
chosen Zassenhaus depths, produce a coefficientwise Hilbert-series witness
polynomial.
-/
def PPDatum.CoefficientwiseHilbertWitness
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      ∃ P : Polynomial ℝ,
        (∀ n, 0 ≤ P.coeff n) ∧
        0 < P.coeff 0 ∧
        (∀ n, 0 ≤
          ((GShafar.relatorSeriesPolynomial
                H.generatorRank H.relationRank depth) * P).coeff n)

/--
The second remaining frontier: build an explicit truncated coefficient
recurrence from the presentation data.
-/
def PPDatum.TruncRecurrenceWitness
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      ∃ (N : ℕ) (a : ℕ → ℝ),
        (∀ n, 0 ≤ a n) ∧
        0 < a 0 ∧
        (∀ n, 0 ≤
          GShafar.truncatedSequence a N n
            - (H.generatorRank : ℝ) *
                (if 1 ≤ n then GShafar.truncatedSequence a N (n - 1) else 0)
            + ∑ i, if depth i ≤ n then
                GShafar.truncatedSequence a N (n - depth i) else 0)

/--
An even sharper remaining frontier: it is enough to verify the truncated
recurrence only on the finite window
`0 ≤ n ≤ N + max 1 (sup depth)`.
-/
def PPDatum.FinTruncRecurrewitness
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      ∃ (N : ℕ) (a : ℕ → ℝ),
        (∀ n, 0 ≤ a n) ∧
        0 < a 0 ∧
        (∀ n ≤ N + max 1 (Finset.univ.sup depth), 0 ≤
          GShafar.truncatedSequence a N n
            - (H.generatorRank : ℝ) *
                (if 1 ≤ n then GShafar.truncatedSequence a N (n - 1) else 0)
            + ∑ i, if depth i ≤ n then
                GShafar.truncatedSequence a N (n - depth i) else 0)

/--
An even more concrete finite-window frontier: choose a natural-number sequence
to play the role of quotient dimensions, and prove the truncated Hilbert-series
inequality directly in natural arithmetic.

This is closer to the intended augmentation-quotient application, where the
sequence really is built from finite dimensions.
-/
def PPDatum.FinWindowdimIneqwitness
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      ∃ (N : ℕ) (a : ℕ → ℕ),
        0 < a 0 ∧
        (∀ n ≤ N + max 1 (Finset.univ.sup depth),
          H.generatorRank * (if 1 ≤ n then
              if n - 1 ≤ N then a (n - 1) else 0
            else 0) ≤
            (if n ≤ N then a n else 0) +
              ∑ i, if depth i ≤ n then
                if n - depth i ≤ N then a (n - depth i) else 0
              else 0)

/--
Local finite-dimensional linear-algebra data at a single index `n` whose
surjectivity forces the corresponding Hilbert-series coefficient inequality.

This packages exactly the sort of per-index source/target map one expects from
the augmentation-quotient argument, but without yet committing to the concrete
spaces.
-/
structure PPDatum.FinWindowSurjdatum
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ) (N n : ℕ) (a : ℕ → ℕ) where
  X : Type
  Y : Type
  Z : Fin H.relationRank → Type
  [xAddGroup : AddCommGroup X]
  [instModuleX : Module (ZMod H.realizesFiniteNontrivial.p) X]
  [instFreeX : Module.Free (ZMod H.realizesFiniteNontrivial.p) X]
  [instFiniteX : Module.Finite (ZMod H.realizesFiniteNontrivial.p) X]
  [yAddGroup : AddCommGroup Y]
  [instModuleY : Module (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFreeY : Module.Free (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFiniteY : Module.Finite (ZMod H.realizesFiniteNontrivial.p) Y]
  [zAddGroup : ∀ i, AddCommGroup (Z i)]
  [instModuleZ : ∀ i, Module (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFreeZ : ∀ i, Module.Free (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFiniteZ : ∀ i, Module.Finite (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  hX : Module.finrank (ZMod H.realizesFiniteNontrivial.p) X =
    if n ≤ N then a n else 0
  hY : Module.finrank (ZMod H.realizesFiniteNontrivial.p) Y =
    if 1 ≤ n then
      if n - 1 ≤ N then a (n - 1) else 0
    else 0
  hZ : ∀ i, Module.finrank (ZMod H.realizesFiniteNontrivial.p) (Z i) =
    if depth i ≤ n then
      if n - depth i ≤ N then a (n - depth i) else 0
    else 0
  f : (X × ∀ i, Z i) →ₗ[ZMod H.realizesFiniteNontrivial.p] (Fin H.generatorRank → Y)
  hf : Function.Surjective f

attribute [instance] PPDatum.FinWindowSurjdatum.xAddGroup
attribute [instance] PPDatum.FinWindowSurjdatum.instModuleX
attribute [instance] PPDatum.FinWindowSurjdatum.instFreeX
attribute [instance] PPDatum.FinWindowSurjdatum.instFiniteX
attribute [instance] PPDatum.FinWindowSurjdatum.yAddGroup
attribute [instance] PPDatum.FinWindowSurjdatum.instModuleY
attribute [instance] PPDatum.FinWindowSurjdatum.instFreeY
attribute [instance] PPDatum.FinWindowSurjdatum.instFiniteY
attribute [instance] PPDatum.FinWindowSurjdatum.zAddGroup
attribute [instance] PPDatum.FinWindowSurjdatum.instModuleZ
attribute [instance] PPDatum.FinWindowSurjdatum.instFreeZ
attribute [instance] PPDatum.FinWindowSurjdatum.instFiniteZ

/--
At a fixed index `n`, a surjective linear map from the chosen source to the
chosen target already implies the required natural-number coefficient
inequality.
-/
theorem PPDatum.finwindow_dimineq_surjdatum
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} {N n : ℕ} {a : ℕ → ℕ}
    (D : H.FinWindowSurjdatum depth N n a) :
    H.generatorRank * (if 1 ≤ n then
        if n - 1 ≤ N then a (n - 1) else 0
      else 0) ≤
      (if n ≤ N then a n else 0) +
        ∑ i, if depth i ≤ n then
          if n - depth i ≤ N then a (n - depth i) else 0
        else 0 := by
  have hle :=
    Module.finrank_le_finrank_of_rank_le_rank
      (LinearMap.lift_rank_le_of_surjective D.f D.hf)
      (Module.rank_lt_aleph0 (ZMod H.realizesFiniteNontrivial.p)
        (D.X × ∀ i, D.Z i))
  simpa [Module.finrank_prod, Module.finrank_pi_fintype, D.hX, D.hY, D.hZ, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc, add_comm, add_left_comm, add_assoc] using hle

/--
The next concrete frontier: for each active index in the finite coefficient
window, choose explicit finite-dimensional source/target spaces and a
surjective linear map between them.

This is more local than the raw inequality witness because it isolates one
finite-dimensional linear-algebra problem at a time.
-/
def PPDatum.FinWindowSurjwitness
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      ∃ (N : ℕ) (a : ℕ → ℕ),
        0 < a 0 ∧
        (∀ n ≤ N + max 1 (Finset.univ.sup depth),
          Nonempty (H.FinWindowSurjdatum depth N n a))

/--
The active-relator version of the local surjective datum.

This is more concrete than `FinWindowSurjdatum` because the relator
side only ranges over those indices that can actually contribute at the chosen
coefficient `n`.
-/
structure PPDatum.FinWindowactiveSurjdatum
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ) (N n : ℕ) (a : ℕ → ℕ) where
  X : Type
  Y : Type
  Z : PPDatum.activeRelators H depth n → Type
  [xAddGroup : AddCommGroup X]
  [instModuleX : Module (ZMod H.realizesFiniteNontrivial.p) X]
  [instFreeX : Module.Free (ZMod H.realizesFiniteNontrivial.p) X]
  [instFiniteX : Module.Finite (ZMod H.realizesFiniteNontrivial.p) X]
  [yAddGroup : AddCommGroup Y]
  [instModuleY : Module (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFreeY : Module.Free (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFiniteY : Module.Finite (ZMod H.realizesFiniteNontrivial.p) Y]
  [zAddGroup : ∀ i, AddCommGroup (Z i)]
  [instModuleZ : ∀ i, Module (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFreeZ : ∀ i, Module.Free (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFiniteZ : ∀ i, Module.Finite (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  hX : Module.finrank (ZMod H.realizesFiniteNontrivial.p) X =
    if n ≤ N then a n else 0
  hY : Module.finrank (ZMod H.realizesFiniteNontrivial.p) Y =
    if 1 ≤ n then
      if n - 1 ≤ N then a (n - 1) else 0
    else 0
  hZ : ∀ i, Module.finrank (ZMod H.realizesFiniteNontrivial.p) (Z i) =
    if n - depth i.1 ≤ N then a (n - depth i.1) else 0
  f : (X × ∀ i, Z i) →ₗ[ZMod H.realizesFiniteNontrivial.p] (Fin H.generatorRank → Y)
  hf : Function.Surjective f

attribute [instance] PPDatum.FinWindowactiveSurjdatum.xAddGroup
attribute [instance] PPDatum.FinWindowactiveSurjdatum.instModuleX
attribute [instance] PPDatum.FinWindowactiveSurjdatum.instFreeX
attribute [instance] PPDatum.FinWindowactiveSurjdatum.instFiniteX
attribute [instance] PPDatum.FinWindowactiveSurjdatum.yAddGroup
attribute [instance] PPDatum.FinWindowactiveSurjdatum.instModuleY
attribute [instance] PPDatum.FinWindowactiveSurjdatum.instFreeY
attribute [instance] PPDatum.FinWindowactiveSurjdatum.instFiniteY
attribute [instance] PPDatum.FinWindowactiveSurjdatum.zAddGroup
attribute [instance] PPDatum.FinWindowactiveSurjdatum.instModuleZ
attribute [instance] PPDatum.FinWindowactiveSurjdatum.instFreeZ
attribute [instance] PPDatum.FinWindowactiveSurjdatum.instFiniteZ

/--
At a fixed index `n`, an active-relator surjective datum already implies the
natural-number Hilbert-series coefficient inequality.
-/
theorem PPDatum.finwindow_dimineq_activesurjdatum
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} {N n : ℕ} {a : ℕ → ℕ}
    (D : H.FinWindowactiveSurjdatum depth N n a) :
    H.generatorRank * (if 1 ≤ n then
        if n - 1 ≤ N then a (n - 1) else 0
      else 0) ≤
      (if n ≤ N then a n else 0) +
        ∑ i, if depth i ≤ n then
          if n - depth i ≤ N then a (n - depth i) else 0
        else 0 := by
  have hsum_active :
      (∑ i : PPDatum.activeRelators H depth n,
          if n ≤ N + depth i.1 then a (n - depth i.1) else 0) =
        ∑ i, if depth i ≤ n then
          if n ≤ N + depth i then a (n - depth i) else 0
        else 0 := by
    simpa using
      (H.sum_active_relatorseq depth n
        (fun i => if n ≤ N + depth i then a (n - depth i) else 0))
  have hle :=
    Module.finrank_le_finrank_of_rank_le_rank
      (LinearMap.lift_rank_le_of_surjective D.f D.hf)
      (Module.rank_lt_aleph0 (ZMod H.realizesFiniteNontrivial.p)
        (D.X × ∀ i, D.Z i))
  have htarget :
      Module.finrank (ZMod H.realizesFiniteNontrivial.p) (Fin H.generatorRank → D.Y) =
        H.generatorRank * (if 1 ≤ n then
          if n - 1 ≤ N then a (n - 1) else 0
        else 0) := by
    rw [Module.finrank_pi_fintype]
    rw [show (∑ _i : Fin H.generatorRank,
        Module.finrank (ZMod H.realizesFiniteNontrivial.p) D.Y) =
          H.generatorRank * Module.finrank (ZMod H.realizesFiniteNontrivial.p) D.Y by
        simp]
    rw [D.hY]
  have hsource :
      Module.finrank (ZMod H.realizesFiniteNontrivial.p)
          (D.X × ∀ i : PPDatum.activeRelators H depth n, D.Z i) =
        (if n ≤ N then a n else 0) +
          ∑ i : PPDatum.activeRelators H depth n,
            if n ≤ N + depth i.1 then a (n - depth i.1) else 0 := by
    rw [Module.finrank_prod, D.hX, Module.finrank_pi_fintype]
    rw [show
        (∑ i : PPDatum.activeRelators H depth n,
          Module.finrank (ZMod H.realizesFiniteNontrivial.p) (D.Z i)) =
          ∑ i : PPDatum.activeRelators H depth n,
            if n ≤ N + depth i.1 then a (n - depth i.1) else 0 by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [D.hZ]
        by_cases h1 : n - depth i.1 ≤ N
        · have h2 : n ≤ N + depth i.1 := by omega
          simp [h1, h2]
        · have h2 : ¬ n ≤ N + depth i.1 := by omega
          simp [h1, h2]]
  rw [htarget, hsource] at hle
  simpa [hsum_active] using hle

/--
The more local active-relator surjective frontier: for each index `n` in the
finite window, choose spaces only for the relators that actually contribute at
that coefficient.
-/
def PPDatum.FinWindowactiveSurjwitness
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      ∃ (N : ℕ) (a : ℕ → ℕ),
        0 < a 0 ∧
        (∀ n ≤ N + max 1 (Finset.univ.sup depth),
          Nonempty (H.FinWindowactiveSurjdatum depth N n a))

/--
A standard finite-dimensional `𝔽_p`-vector space of dimension `m`.
-/
abbrev PPDatum.coordinateSpace
    (H : PPDatum) (m : ℕ) :=
  Fin m → ZMod H.realizesFiniteNontrivial.p

/--
At index `n = 0`, the target term vanishes, so a trivial zero-target datum is
enough.
-/
theorem PPDatum.finwindow_activesurj_datumzero
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ}
    (N : ℕ) (a : ℕ → ℕ)
    (hdepth : ∀ i, 2 ≤ depth i) :
    Nonempty (H.FinWindowactiveSurjdatum depth N 0 a) := by
  classical
  refine ⟨{
    X := H.coordinateSpace (a 0)
    Y := H.coordinateSpace 0
    Z := fun _ => H.coordinateSpace 0
    xAddGroup := by infer_instance
    instModuleX := by infer_instance
    instFreeX := by infer_instance
    instFiniteX := by infer_instance
    yAddGroup := by infer_instance
    instModuleY := by infer_instance
    instFreeY := by infer_instance
    instFiniteY := by infer_instance
    zAddGroup := by intro i; infer_instance
    instModuleZ := by intro i; infer_instance
    instFreeZ := by intro i; infer_instance
    instFiniteZ := by intro i; infer_instance
    hX := by
      simp [PPDatum.coordinateSpace]
    hY := by
      simp [PPDatum.coordinateSpace]
    hZ := by
      intro i
      have hi : False := by
        have h0 : depth i.1 = 0 := Nat.eq_zero_of_le_zero i.2
        have h2 : 2 ≤ depth i.1 := hdepth i.1
        omega
      exact False.elim hi
    f := 0
    hf := by
      intro y
      refine ⟨0, ?_⟩
      exact Subsingleton.elim _ _
  }⟩

/--
For indices strictly beyond the boundary `N + 1`, the truncated target is
already zero, so again a trivial zero-target datum is enough.
-/
theorem PPDatum.finwindow_activesurj_datumgtbound
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ}
    {N n : ℕ}
    (a : ℕ → ℕ)
    (hgt : N + 1 < n) :
    Nonempty (H.FinWindowactiveSurjdatum depth N n a) := by
  classical
  refine ⟨{
    X := H.coordinateSpace 0
    Y := H.coordinateSpace 0
    Z := fun i => H.coordinateSpace
      (if n ≤ N + depth i.1 then a (n - depth i.1) else 0)
    xAddGroup := by infer_instance
    instModuleX := by infer_instance
    instFreeX := by infer_instance
    instFiniteX := by infer_instance
    yAddGroup := by infer_instance
    instModuleY := by infer_instance
    instFreeY := by infer_instance
    instFiniteY := by infer_instance
    zAddGroup := by intro i; infer_instance
    instModuleZ := by intro i; infer_instance
    instFreeZ := by intro i; infer_instance
    instFiniteZ := by intro i; infer_instance
    hX := by
      have hnN : ¬ n ≤ N := by omega
      simp [PPDatum.coordinateSpace, hnN]
    hY := by
      have hn1 : 1 ≤ n := by omega
      have hnm1N : ¬ n - 1 ≤ N := by omega
      simp [PPDatum.coordinateSpace, hn1, hnm1N]
    hZ := by
      intro i
      simp [PPDatum.coordinateSpace]
    f := 0
    hf := by
      intro y
      refine ⟨0, ?_⟩
      exact Subsingleton.elim _ _
  }⟩

/--
It is enough to construct the active-relator surjective data only on the
positive window `1 ≤ n ≤ N + 1`.

The missing cases are formally easier:
- `n = 0` has zero target
- `n ≥ N + 2` also has zero target because the truncated generator term has
  already disappeared
-/
def PPDatum.PosboundFinwindowActisurjwitn
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      ∃ (N : ℕ) (a : ℕ → ℕ),
        0 < a 0 ∧
        (∀ n, 1 ≤ n → n ≤ N + 1 →
          Nonempty (H.FinWindowactiveSurjdatum depth N n a))

/--
Positive-window plus boundary data already extend to the full finite-window
active-surjective witness.
-/
theorem
    PPDatum.finwindow_activewindow_actisurjwitn
    (H : PPDatum)
    (hwitness : H.PosboundFinwindowActisurjwitn) :
    H.FinWindowactiveSurjwitness := by
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, a, ha0, hmain⟩
  refine ⟨N, a, ha0, ?_⟩
  intro n hn
  by_cases h0 : n = 0
  · subst h0
    exact H.finwindow_activesurj_datumzero (depth := depth) N a hdepth
  · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0)
    by_cases hnb : n ≤ N + 1
    · exact hmain n hn1 hnb
    · have hgt : N + 1 < n := Nat.lt_of_not_ge hnb
      exact H.finwindow_activesurj_datumgtbound (depth := depth) a hgt

/--
Relator-only surjective data at the single boundary index `N + 1`.

This is the natural boundary analogue of the active-surjective datum: the
principal source term has disappeared, so only the active relator factors
remain.
-/
structure PPDatum.FinwindowBoundrelatorSurjdatum
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ) (N : ℕ) (a : ℕ → ℕ) where
  Y : Type
  Z : PPDatum.activeRelators H depth (N + 1) → Type
  [yAddGroup : AddCommGroup Y]
  [instModuleY : Module (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFreeY : Module.Free (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFiniteY : Module.Finite (ZMod H.realizesFiniteNontrivial.p) Y]
  [zAddGroup : ∀ i, AddCommGroup (Z i)]
  [instModuleZ : ∀ i, Module (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFreeZ : ∀ i, Module.Free (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFiniteZ : ∀ i, Module.Finite (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  hY : Module.finrank (ZMod H.realizesFiniteNontrivial.p) Y = a N
  hZ : ∀ i, Module.finrank (ZMod H.realizesFiniteNontrivial.p) (Z i) =
    if N + 1 ≤ N + depth i.1 then a (N + 1 - depth i.1) else 0
  f : (∀ i, Z i) →ₗ[ZMod H.realizesFiniteNontrivial.p] (Fin H.generatorRank → Y)
  hf : Function.Surjective f

attribute [instance]
  PPDatum.FinwindowBoundrelatorSurjdatum.yAddGroup
attribute [instance] PPDatum.FinwindowBoundrelatorSurjdatum.instModuleY
attribute [instance] PPDatum.FinwindowBoundrelatorSurjdatum.instFreeY
attribute [instance] PPDatum.FinwindowBoundrelatorSurjdatum.instFiniteY
attribute [instance]
  PPDatum.FinwindowBoundrelatorSurjdatum.zAddGroup
attribute [instance] PPDatum.FinwindowBoundrelatorSurjdatum.instModuleZ
attribute [instance] PPDatum.FinwindowBoundrelatorSurjdatum.instFreeZ
attribute [instance] PPDatum.FinwindowBoundrelatorSurjdatum.instFiniteZ

/--
A boundary relator-only surjective datum induces the full active-surjective
datum at the single boundary index `N + 1` by taking the principal source
factor to be `0`.
-/
theorem
    PPDatum.finwindowactive_surjdatumbound_relasurjdatu
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} {N : ℕ} {a : ℕ → ℕ}
    (D : H.FinwindowBoundrelatorSurjdatum depth N a) :
    Nonempty (H.FinWindowactiveSurjdatum depth N (N + 1) a) := by
  classical
  refine ⟨{
    X := H.coordinateSpace 0
    Y := D.Y
    Z := D.Z
    xAddGroup := by infer_instance
    instModuleX := by infer_instance
    instFreeX := by infer_instance
    instFiniteX := by infer_instance
    yAddGroup := D.yAddGroup
    instModuleY := D.instModuleY
    instFreeY := D.instFreeY
    instFiniteY := D.instFiniteY
    zAddGroup := D.zAddGroup
    instModuleZ := D.instModuleZ
    instFreeZ := D.instFreeZ
    instFiniteZ := D.instFiniteZ
    hX := by
      have hnot : ¬ N + 1 ≤ N := by omega
      simp [PPDatum.coordinateSpace, hnot]
    hY := by
      have h1 : 1 ≤ N + 1 := by omega
      have hN : N + 1 - 1 ≤ N := by omega
      simpa [h1, hN] using D.hY
    hZ := by
      intro i
      simpa using D.hZ i
    f := D.f.comp
      (LinearMap.snd (ZMod H.realizesFiniteNontrivial.p)
        (H.coordinateSpace 0)
        (∀ i : PPDatum.activeRelators H depth (N + 1), D.Z i))
    hf := by
      intro y
      rcases D.hf y with ⟨z, hz⟩
      refine ⟨(0, z), ?_⟩
      simpa using hz
  }⟩

/--
The active-relator local map datum without the final surjectivity proof.

This separates the bookkeeping of spaces, dimensions, and a named linear map
from the genuinely difficult surjectivity statement.
-/
structure PPDatum.FinWindowactiveMapdatum
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ) (N n : ℕ) (a : ℕ → ℕ) where
  X : Type
  Y : Type
  Z : PPDatum.activeRelators H depth n → Type
  [xAddGroup : AddCommGroup X]
  [instModuleX : Module (ZMod H.realizesFiniteNontrivial.p) X]
  [instFreeX : Module.Free (ZMod H.realizesFiniteNontrivial.p) X]
  [instFiniteX : Module.Finite (ZMod H.realizesFiniteNontrivial.p) X]
  [yAddGroup : AddCommGroup Y]
  [instModuleY : Module (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFreeY : Module.Free (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFiniteY : Module.Finite (ZMod H.realizesFiniteNontrivial.p) Y]
  [zAddGroup : ∀ i, AddCommGroup (Z i)]
  [instModuleZ : ∀ i, Module (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFreeZ : ∀ i, Module.Free (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFiniteZ : ∀ i, Module.Finite (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  hX : Module.finrank (ZMod H.realizesFiniteNontrivial.p) X =
    if n ≤ N then a n else 0
  hY : Module.finrank (ZMod H.realizesFiniteNontrivial.p) Y =
    if 1 ≤ n then
      if n - 1 ≤ N then a (n - 1) else 0
    else 0
  hZ : ∀ i, Module.finrank (ZMod H.realizesFiniteNontrivial.p) (Z i) =
    if n - depth i.1 ≤ N then a (n - depth i.1) else 0
  f : (X × ∀ i, Z i) →ₗ[ZMod H.realizesFiniteNontrivial.p] (Fin H.generatorRank → Y)

attribute [instance] PPDatum.FinWindowactiveMapdatum.xAddGroup
attribute [instance] PPDatum.FinWindowactiveMapdatum.instModuleX
attribute [instance] PPDatum.FinWindowactiveMapdatum.instFreeX
attribute [instance] PPDatum.FinWindowactiveMapdatum.instFiniteX
attribute [instance] PPDatum.FinWindowactiveMapdatum.yAddGroup
attribute [instance] PPDatum.FinWindowactiveMapdatum.instModuleY
attribute [instance] PPDatum.FinWindowactiveMapdatum.instFreeY
attribute [instance] PPDatum.FinWindowactiveMapdatum.instFiniteY
attribute [instance] PPDatum.FinWindowactiveMapdatum.zAddGroup
attribute [instance] PPDatum.FinWindowactiveMapdatum.instModuleZ
attribute [instance] PPDatum.FinWindowactiveMapdatum.instFreeZ
attribute [instance] PPDatum.FinWindowactiveMapdatum.instFiniteZ

/--
Add the missing surjectivity proof to an active-relator map datum.
-/
def PPDatum.finwindow_activesurj_datummapdatum
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} {N n : ℕ} {a : ℕ → ℕ}
    (D : H.FinWindowactiveMapdatum depth N n a)
    (hf : Function.Surjective D.f) :
    H.FinWindowactiveSurjdatum depth N n a where
  X := D.X
  Y := D.Y
  Z := D.Z
  xAddGroup := D.xAddGroup
  instModuleX := D.instModuleX
  instFreeX := D.instFreeX
  instFiniteX := D.instFiniteX
  yAddGroup := D.yAddGroup
  instModuleY := D.instModuleY
  instFreeY := D.instFreeY
  instFiniteY := D.instFiniteY
  zAddGroup := D.zAddGroup
  instModuleZ := D.instModuleZ
  instFreeZ := D.instFreeZ
  instFiniteZ := D.instFiniteZ
  hX := D.hX
  hY := D.hY
  hZ := D.hZ
  f := D.f
  hf := hf

/--
The boundary relator-only local map datum without the final surjectivity
proof.
-/
structure PPDatum.FinwindowBoundrelatorMapdatum
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ) (N : ℕ) (a : ℕ → ℕ) where
  Y : Type
  Z : PPDatum.activeRelators H depth (N + 1) → Type
  [yAddGroup : AddCommGroup Y]
  [instModuleY : Module (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFreeY : Module.Free (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFiniteY : Module.Finite (ZMod H.realizesFiniteNontrivial.p) Y]
  [zAddGroup : ∀ i, AddCommGroup (Z i)]
  [instModuleZ : ∀ i, Module (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFreeZ : ∀ i, Module.Free (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFiniteZ : ∀ i, Module.Finite (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  hY : Module.finrank (ZMod H.realizesFiniteNontrivial.p) Y = a N
  hZ : ∀ i, Module.finrank (ZMod H.realizesFiniteNontrivial.p) (Z i) =
    if N + 1 ≤ N + depth i.1 then a (N + 1 - depth i.1) else 0
  f : (∀ i, Z i) →ₗ[ZMod H.realizesFiniteNontrivial.p] (Fin H.generatorRank → Y)

attribute [instance] PPDatum.FinwindowBoundrelatorMapdatum.yAddGroup
attribute [instance] PPDatum.FinwindowBoundrelatorMapdatum.instModuleY
attribute [instance] PPDatum.FinwindowBoundrelatorMapdatum.instFreeY
attribute [instance] PPDatum.FinwindowBoundrelatorMapdatum.instFiniteY
attribute [instance] PPDatum.FinwindowBoundrelatorMapdatum.zAddGroup
attribute [instance] PPDatum.FinwindowBoundrelatorMapdatum.instModuleZ
attribute [instance] PPDatum.FinwindowBoundrelatorMapdatum.instFreeZ
attribute [instance] PPDatum.FinwindowBoundrelatorMapdatum.instFiniteZ

/--
Add the missing surjectivity proof to a boundary relator-only map datum.
-/
def PPDatum.finwindow_bounrelasurj_datummapdatum
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} {N : ℕ} {a : ℕ → ℕ}
    (D : H.FinwindowBoundrelatorMapdatum depth N a)
    (hf : Function.Surjective D.f) :
    H.FinwindowBoundrelatorSurjdatum depth N a where
  Y := D.Y
  Z := D.Z
  yAddGroup := D.yAddGroup
  instModuleY := D.instModuleY
  instFreeY := D.instFreeY
  instFiniteY := D.instFiniteY
  zAddGroup := D.zAddGroup
  instModuleZ := D.instModuleZ
  instFreeZ := D.instFreeZ
  instFiniteZ := D.instFiniteZ
  hY := D.hY
  hZ := D.hZ
  f := D.f
  hf := hf

/--
A local active-relator space package without a chosen linear map.

This isolates the purely dimensional part of the bookkeeping, so later named
packages can first fix spaces and only then choose the actual map whose
surjectivity is to be proved.
-/
structure PPDatum.FWSpaced
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ) (N n : ℕ) (a : ℕ → ℕ) where
  X : Type
  Y : Type
  Z : PPDatum.activeRelators H depth n → Type
  [xAddGroup : AddCommGroup X]
  [instModuleX : Module (ZMod H.realizesFiniteNontrivial.p) X]
  [instFreeX : Module.Free (ZMod H.realizesFiniteNontrivial.p) X]
  [instFiniteX : Module.Finite (ZMod H.realizesFiniteNontrivial.p) X]
  [yAddGroup : AddCommGroup Y]
  [instModuleY : Module (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFreeY : Module.Free (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFiniteY : Module.Finite (ZMod H.realizesFiniteNontrivial.p) Y]
  [zAddGroup : ∀ i, AddCommGroup (Z i)]
  [instModuleZ : ∀ i, Module (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFreeZ : ∀ i, Module.Free (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFiniteZ : ∀ i, Module.Finite (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  hX : Module.finrank (ZMod H.realizesFiniteNontrivial.p) X =
    if n ≤ N then a n else 0
  hY : Module.finrank (ZMod H.realizesFiniteNontrivial.p) Y =
    if 1 ≤ n then
      if n - 1 ≤ N then a (n - 1) else 0
    else 0
  hZ : ∀ i, Module.finrank (ZMod H.realizesFiniteNontrivial.p) (Z i) =
    if n - depth i.1 ≤ N then a (n - depth i.1) else 0

attribute [instance] PPDatum.FWSpaced.xAddGroup
attribute [instance] PPDatum.FWSpaced.instModuleX
attribute [instance] PPDatum.FWSpaced.instFreeX
attribute [instance] PPDatum.FWSpaced.instFiniteX
attribute [instance] PPDatum.FWSpaced.yAddGroup
attribute [instance] PPDatum.FWSpaced.instModuleY
attribute [instance] PPDatum.FWSpaced.instFreeY
attribute [instance] PPDatum.FWSpaced.instFiniteY
attribute [instance] PPDatum.FWSpaced.zAddGroup
attribute [instance] PPDatum.FWSpaced.instModuleZ
attribute [instance] PPDatum.FWSpaced.instFreeZ
attribute [instance] PPDatum.FWSpaced.instFiniteZ

/--
Attach a chosen linear map to a local active-relator space package.
-/
def PPDatum.finwindow_activemap_datumspacedatum
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} {N n : ℕ} {a : ℕ → ℕ}
    (D : H.FWSpaced depth N n a)
    (f : (D.X × ∀ i, D.Z i) →ₗ[ZMod H.realizesFiniteNontrivial.p]
      (Fin H.generatorRank → D.Y)) :
    H.FinWindowactiveMapdatum depth N n a where
  X := D.X
  Y := D.Y
  Z := D.Z
  xAddGroup := D.xAddGroup
  instModuleX := D.instModuleX
  instFreeX := D.instFreeX
  instFiniteX := D.instFiniteX
  yAddGroup := D.yAddGroup
  instModuleY := D.instModuleY
  instFreeY := D.instFreeY
  instFiniteY := D.instFiniteY
  zAddGroup := D.zAddGroup
  instModuleZ := D.instModuleZ
  instFreeZ := D.instFreeZ
  instFiniteZ := D.instFiniteZ
  hX := D.hX
  hY := D.hY
  hZ := D.hZ
  f := f

/--
A local boundary relator-space package without a chosen linear map.

As above, this keeps the coordinate-space bookkeeping separate from the later
choice of the actual boundary map.
-/
structure PPDatum.FBSpaced
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ) (N : ℕ) (a : ℕ → ℕ) where
  Y : Type
  Z : PPDatum.activeRelators H depth (N + 1) → Type
  [yAddGroup : AddCommGroup Y]
  [instModuleY : Module (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFreeY : Module.Free (ZMod H.realizesFiniteNontrivial.p) Y]
  [instFiniteY : Module.Finite (ZMod H.realizesFiniteNontrivial.p) Y]
  [zAddGroup : ∀ i, AddCommGroup (Z i)]
  [instModuleZ : ∀ i, Module (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFreeZ : ∀ i, Module.Free (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  [instFiniteZ : ∀ i, Module.Finite (ZMod H.realizesFiniteNontrivial.p) (Z i)]
  hY : Module.finrank (ZMod H.realizesFiniteNontrivial.p) Y = a N
  hZ : ∀ i, Module.finrank (ZMod H.realizesFiniteNontrivial.p) (Z i) =
    if N + 1 ≤ N + depth i.1 then a (N + 1 - depth i.1) else 0

attribute [instance] PPDatum.FBSpaced.yAddGroup
attribute [instance] PPDatum.FBSpaced.instModuleY
attribute [instance] PPDatum.FBSpaced.instFreeY
attribute [instance] PPDatum.FBSpaced.instFiniteY
attribute [instance] PPDatum.FBSpaced.zAddGroup
attribute [instance] PPDatum.FBSpaced.instModuleZ
attribute [instance] PPDatum.FBSpaced.instFreeZ
attribute [instance] PPDatum.FBSpaced.instFiniteZ

/--
Attach a chosen linear map to a boundary relator-space package.
-/
def PPDatum.finwindow_boundrelatormap_datumspacedatum
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} {N : ℕ} {a : ℕ → ℕ}
    (D : H.FBSpaced depth N a)
    (f : (∀ i, D.Z i) →ₗ[ZMod H.realizesFiniteNontrivial.p]
      (Fin H.generatorRank → D.Y)) :
    H.FinwindowBoundrelatorMapdatum depth N a where
  Y := D.Y
  Z := D.Z
  yAddGroup := D.yAddGroup
  instModuleY := D.instModuleY
  instFreeY := D.instFreeY
  instFiniteY := D.instFiniteY
  zAddGroup := D.zAddGroup
  instModuleZ := D.instModuleZ
  instFreeZ := D.instFreeZ
  instFiniteZ := D.instFiniteZ
  hY := D.hY
  hZ := D.hZ
  f := f

/--
A canonical coordinate-space model for the local active space datum.

This realizes the required finrank equalities using standard coordinate spaces
without yet choosing any linear map between them.
-/
noncomputable def PPDatum.coordfin_windowactive_spacedatum
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ}
    (N n : ℕ) (a : ℕ → ℕ) :
    H.FWSpaced depth N n a := by
  classical
  refine {
    X := H.coordinateSpace (if n ≤ N then a n else 0)
    Y := H.coordinateSpace
      (if 1 ≤ n then
        if n - 1 ≤ N then a (n - 1) else 0
      else 0)
    Z := fun i => H.coordinateSpace
      (if n - depth i.1 ≤ N then a (n - depth i.1) else 0)
    xAddGroup := by infer_instance
    instModuleX := by infer_instance
    instFreeX := by infer_instance
    instFiniteX := by infer_instance
    yAddGroup := by infer_instance
    instModuleY := by infer_instance
    instFreeY := by infer_instance
    instFiniteY := by infer_instance
    zAddGroup := by intro i; infer_instance
    instModuleZ := by intro i; infer_instance
    instFreeZ := by intro i; infer_instance
    instFiniteZ := by intro i; infer_instance
    hX := by
      simp [PPDatum.coordinateSpace]
    hY := by
      simp [PPDatum.coordinateSpace]
    hZ := by
      intro i
      simp [PPDatum.coordinateSpace]
  }

/--
A canonical coordinate-space model for the local boundary relator-space datum.
-/
noncomputable def PPDatum.coordfin_windowbound_relaspacdatu
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ}
    (N : ℕ) (a : ℕ → ℕ) :
    H.FBSpaced depth N a := by
  classical
  refine {
    Y := H.coordinateSpace (a N)
    Z := fun i => H.coordinateSpace
      (if N + 1 ≤ N + depth i.1 then a (N + 1 - depth i.1) else 0)
    yAddGroup := by infer_instance
    instModuleY := by infer_instance
    instFreeY := by infer_instance
    instFiniteY := by infer_instance
    zAddGroup := by intro i; infer_instance
    instModuleZ := by intro i; infer_instance
    instFreeZ := by intro i; infer_instance
    instFiniteZ := by intro i; infer_instance
    hY := by
      simp [PPDatum.coordinateSpace]
    hZ := by
      intro i
      simp [PPDatum.coordinateSpace]
  }

/--
A canonical coordinate-space model for the local active map datum.

For any chosen coefficient sequence `a`, this realizes the required finrank
equalities by taking standard coordinate spaces of the prescribed dimensions
and then attaching the zero linear map between them.

This remains useful as a bookkeeping example, but it is not used for the final
named surjectivity frontier.
-/
noncomputable def PPDatum.coordfin_windowactive_mapdatum
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ}
    (N n : ℕ) (a : ℕ → ℕ) :
    H.FinWindowactiveMapdatum depth N n a := by
  classical
  let D := H.coordfin_windowactive_spacedatum (depth := depth) N n a
  exact H.finwindow_activemap_datumspacedatum D 0

/--
A canonical coordinate-space model for the local boundary relator map datum.

As above, this realizes the required finrank equalities using standard
coordinate spaces and then attaches the zero linear map. It leaves the
genuinely nontrivial surjectivity question to later theorems.
-/
noncomputable def PPDatum.coordfin_windowbound_relatormapdatum
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ}
    (N : ℕ) (a : ℕ → ℕ) :
    H.FinwindowBoundrelatorMapdatum depth N a := by
  classical
  let D := H.coordfin_windowbound_relaspacdatu (depth := depth) N a
  exact H.finwindow_boundrelatormap_datumspacedatum D 0

/--
Project away the last `m - n` coordinates of a standard coordinate space.
-/
def PPDatum.coordinateProjection
    (K : Type*) [Field K] (m n : ℕ) (h : n ≤ m) :
    (Fin m → K) →ₗ[K] (Fin n → K) where
  toFun x i := x ⟨i.1, lt_of_lt_of_le i.2 h⟩
  map_add' x y := by
    ext i
    rfl
  map_smul' c x := by
    ext i
    rfl

/--
The coordinate projection is surjective: extend a vector on `Fin n` by zero on
the remaining coordinates of `Fin m`.
-/
theorem PPDatum.coordinateProjection_surjective
    (K : Type*) [Field K] (m n : ℕ) (h : n ≤ m) :
    Function.Surjective
      (PPDatum.coordinateProjection K m n h) := by
  intro y
  refine ⟨fun j => if hj : j.1 < n then y ⟨j.1, hj⟩ else 0, ?_⟩
  ext i
  simp [PPDatum.coordinateProjection, i.2]

/--
If the target finrank is at most the source finrank, there exists a surjective
linear map between the two finite free modules.

This is the abstract linear-algebra step that lets the remaining bridge
frontier be expressed as pure finrank inequalities.
-/
noncomputable def PPDatum.surj_linmap_finrankle
    (K : Type*) [Field K]
    (V W : Type*)
    [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Free K W] [Module.Finite K W]
    (h : Module.finrank K W ≤ Module.finrank K V) :
    V →ₗ[K] W := by
  let eV : V ≃ₗ[K] (Fin (Module.finrank K V) → K) :=
    LinearEquiv.ofFinrankEq V (Fin (Module.finrank K V) → K) <| by
      rw [Module.finrank_pi]
      simp
  let eW : W ≃ₗ[K] (Fin (Module.finrank K W) → K) :=
    LinearEquiv.ofFinrankEq W (Fin (Module.finrank K W) → K) <| by
      rw [Module.finrank_pi]
      simp
  exact
    (eW.symm.toLinearMap).comp
      ((PPDatum.coordinateProjection K
          (Module.finrank K V) (Module.finrank K W) h).comp eV.toLinearMap)

/--
The map produced by `surj_linmap_finrankle` is surjective.
-/
theorem PPDatum.surjlin_mapfinrank_lesurj
    (K : Type*) [Field K]
    (V W : Type*)
    [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Free K W] [Module.Finite K W]
    (h : Module.finrank K W ≤ Module.finrank K V) :
    Function.Surjective
      (PPDatum.surj_linmap_finrankle K V W h) := by
  let eV : V ≃ₗ[K] (Fin (Module.finrank K V) → K) :=
    LinearEquiv.ofFinrankEq V (Fin (Module.finrank K V) → K) <| by
      rw [Module.finrank_pi]
      simp
  let eW : W ≃ₗ[K] (Fin (Module.finrank K W) → K) :=
    LinearEquiv.ofFinrankEq W (Fin (Module.finrank K W) → K) <| by
      rw [Module.finrank_pi]
      simp
  change Function.Surjective
    ((eW.symm.toLinearMap).comp
      ((PPDatum.coordinateProjection K
          (Module.finrank K V) (Module.finrank K W) h).comp eV.toLinearMap))
  exact
    eW.symm.surjective.comp
      ((PPDatum.coordinateProjection_surjective K
          (Module.finrank K V) (Module.finrank K W) h).comp eV.surjective)

/--
The target finrank of an active space datum.
-/
theorem PPDatum.FWSpaced.target_finrank
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} {N n : ℕ} {a : ℕ → ℕ}
    (D : H.FWSpaced depth N n a) :
    Module.finrank (ZMod H.realizesFiniteNontrivial.p) (Fin H.generatorRank → D.Y) =
      H.generatorRank * (if 1 ≤ n then
        if n - 1 ≤ N then a (n - 1) else 0
      else 0) := by
  rw [Module.finrank_pi_fintype]
  rw [show (∑ _i : Fin H.generatorRank,
      Module.finrank (ZMod H.realizesFiniteNontrivial.p) D.Y) =
        H.generatorRank * Module.finrank (ZMod H.realizesFiniteNontrivial.p) D.Y by
      simp]
  rw [D.hY]

/--
The source finrank of an active space datum.
-/
theorem PPDatum.FWSpaced.source_finrank
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} {N n : ℕ} {a : ℕ → ℕ}
    (D : H.FWSpaced depth N n a) :
    Module.finrank (ZMod H.realizesFiniteNontrivial.p)
        (D.X × ∀ i : PPDatum.activeRelators H depth n, D.Z i) =
      (if n ≤ N then a n else 0) +
        ∑ i : PPDatum.activeRelators H depth n,
          if n ≤ N + depth i.1 then a (n - depth i.1) else 0 := by
  rw [Module.finrank_prod, D.hX, Module.finrank_pi_fintype]
  rw [show
      (∑ i : PPDatum.activeRelators H depth n,
        Module.finrank (ZMod H.realizesFiniteNontrivial.p) (D.Z i)) =
        ∑ i : PPDatum.activeRelators H depth n,
          if n ≤ N + depth i.1 then a (n - depth i.1) else 0 by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [D.hZ]
      by_cases h1 : n - depth i.1 ≤ N
      · have h2 : n ≤ N + depth i.1 := by omega
        simp [h1, h2]
      · have h2 : ¬ n ≤ N + depth i.1 := by omega
        simp [h1, h2]]

/--
The target finrank of a boundary relator-space datum.
-/
theorem PPDatum.FBSpaced.target_finrank
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} {N : ℕ} {a : ℕ → ℕ}
    (D : H.FBSpaced depth N a) :
    Module.finrank (ZMod H.realizesFiniteNontrivial.p) (Fin H.generatorRank → D.Y) =
      H.generatorRank * a N := by
  rw [Module.finrank_pi_fintype]
  rw [show (∑ _i : Fin H.generatorRank,
      Module.finrank (ZMod H.realizesFiniteNontrivial.p) D.Y) =
        H.generatorRank * Module.finrank (ZMod H.realizesFiniteNontrivial.p) D.Y by
      simp]
  rw [D.hY]

/--
The source finrank of a boundary relator-space datum.
-/
theorem PPDatum.FBSpaced.source_finrank
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} {N : ℕ} {a : ℕ → ℕ}
    (D : H.FBSpaced depth N a) :
    Module.finrank (ZMod H.realizesFiniteNontrivial.p)
        (∀ i : PPDatum.activeRelators H depth (N + 1), D.Z i) =
      ∑ i : PPDatum.activeRelators H depth (N + 1),
        if N + 1 ≤ N + depth i.1 then a (N + 1 - depth i.1) else 0 := by
  rw [Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [D.hZ]

/--
Combined named data for the remaining positive-window and boundary tasks:
choose `(N, a)`, choose an active map datum for each `1 ≤ n ≤ N`, and choose
one boundary relator map datum at `N + 1`.

Unlike the earlier false fixed-base surjectivity split, this only packages
data and does not yet claim those named maps are surjective.
-/
structure PPDatum.PosfinWindactibounReladatapack
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ)
    where
  N : ℕ
  a : ℕ → ℕ
  ha0 : 0 < a 0
  active :
    ∀ n, 1 ≤ n → n ≤ N →
      H.FinWindowactiveMapdatum depth N n a
  boundary :
    H.FinwindowBoundrelatorMapdatum depth N a

/--
The corrected data-level frontier: for each presentation, choose explicit base
data and named maps on the positive window and at the single boundary index.

This statement is genuinely weaker than the surjective witness because it only
asks for the bookkeeping data, not for any surjectivity proofs.
-/
def PPDatum.PosfinWindactibounReladatawitn
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      Nonempty
        (PPDatum.PosfinWindactibounReladatapack
          H depth)

/--
Even at the data level, the positive-window part can be made vacuous by taking
`N = 0`, so the first honest remaining obstruction is only surjectivity.
-/
theorem PPDatum.posfin_windactiboun_reladatawitn
    (H : PPDatum) :
    H.PosfinWindactibounReladatawitn := by
  intro rels depth hrels hmem hdepth
  classical
  refine ⟨{
    N := 0
    a := fun _ => 1
    ha0 := by decide
    active := by
      intro n hn1 hnN
      have hfalse : False := by omega
      exact False.elim hfalse
    boundary := by
      refine {
        Y := H.coordinateSpace 1
        Z := fun _ => H.coordinateSpace 0
        yAddGroup := by infer_instance
        instModuleY := by infer_instance
        instFreeY := by infer_instance
        instFiniteY := by infer_instance
        zAddGroup := by intro i; infer_instance
        instModuleZ := by intro i; infer_instance
        instFreeZ := by intro i; infer_instance
        instFiniteZ := by intro i; infer_instance
        hY := by
          simp [PPDatum.coordinateSpace]
        hZ := by
          intro i
          have hfalse : False := by
            have htwo : 2 ≤ depth i.1 := hdepth i.1
            omega
          exact False.elim hfalse
        f := 0
      }
  }⟩

/--
Named positive-window data together with surjectivity of all active maps on
`1 ≤ n ≤ N`, but not yet the boundary relator map.

This is strictly simpler than the full surjective package because the single
boundary surjectivity statement is left separate.
-/
structure PPDatum.PosfinWindowactiveSurjdatapackage
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ) where
  N : ℕ
  a : ℕ → ℕ
  ha0 : 0 < a 0
  active :
    ∀ n, 1 ≤ n → n ≤ N →
      H.FinWindowactiveMapdatum depth N n a
  boundary :
    H.FinwindowBoundrelatorMapdatum depth N a
  active_surj :
    ∀ n hn1 hnN, Function.Surjective (active n hn1 hnN).f

/--
Named positive-window data together with surjectivity on the positive window
and at the single boundary index.
-/
structure PPDatum.PWRelasu
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ) where
  N : ℕ
  a : ℕ → ℕ
  ha0 : 0 < a 0
  active :
    ∀ n, 1 ≤ n → n ≤ N →
      H.FinWindowactiveMapdatum depth N n a
  boundary :
    H.FinwindowBoundrelatorMapdatum depth N a
  active_surj :
    ∀ n hn1 hnN, Function.Surjective (active n hn1 hnN).f
  boundary_surj :
    Function.Surjective boundary.f

/--
Forget the surjectivity proofs and retain only the underlying named data.
-/
def PPDatum.PWRelasu.toDataPackage
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ}
    (D : H.PWRelasu depth) :
    H.PosfinWindactibounReladatapack depth where
  N := D.N
  a := D.a
  ha0 := D.ha0
  active := D.active
  boundary := D.boundary

/--
Forget only the boundary surjectivity proof, keeping the positive-window
surjective data package.
-/
def PPDatum.PWRelasu.active_surj_package
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ}
    (D : H.PWRelasu depth) :
    H.PosfinWindowactiveSurjdatapackage depth where
  N := D.N
  a := D.a
  ha0 := D.ha0
  active := D.active
  boundary := D.boundary
  active_surj := D.active_surj

/--
The smaller positive-window surjectivity frontier: choose named data and prove
surjectivity only for the active maps on `1 ≤ n ≤ N`.
-/
def PPDatum.PosfinWindowactiveSurjdatawitness
    (H : PPDatum) : Prop :=
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (∀ i, 2 ≤ depth i) →
      Nonempty (H.PosfinWindowactiveSurjdatapackage depth)

end Submission
