import Mathlib
import Towers.Group.DenseGenerators.ZassenhausCompact
import Towers.Topology.OpenNormal
import Towers.Group.PowerWidth.RestrictedBurnside


open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u
universe v w z

/-- Dense generation descends through a continuous surjection to a finite discrete target. -/
lemma GeneratedBy.of_dense_image
    {Γ Q : Type u}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure
            (Subgroup.closure (Set.range s)) = ⊤)
    (φ : Γ →* Q)
    (hφcont : Continuous (fun x : Γ => φ x))
    (hφsurj : Function.Surjective φ) :
    GeneratedBy (fun i : Fin d => φ (s i)) := by
  let K : Subgroup Q :=
    Subgroup.closure (Set.range (fun i : Fin d => φ (s i)))
  have hle : Subgroup.closure (Set.range s) ≤ K.comap φ := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hKclosed : IsClosed ((K : Subgroup Q) : Set Q) := by
    exact isClosed_discrete _
  have hpreclosed : IsClosed (((K.comap φ : Subgroup Γ) : Set Γ)) := by
    change IsClosed ((fun x : Γ => φ x) ⁻¹' ((K : Subgroup Q) : Set Q))
    exact hKclosed.preimage hφcont
  have htop_pre : (⊤ : Subgroup Γ) ≤ K.comap φ := by
    have hclosure :
        Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) ≤
          K.comap φ :=
      topological_closure_closed hle hpreclosed
    simpa [hs] using hclosure
  have htop : (⊤ : Subgroup Q) ≤ K := by
    intro y _hy
    rcases hφsurj y with ⟨x, rfl⟩
    exact htop_pre trivial
  exact top_unique htop
/-- The finite width/index package applies to every finite discrete quotient of the profinite
group generated densely by `s`. -/
lemma WIBound.apply_fin_discretequot
    {d m k B : ℕ}
    (hfin : WIBound.{u} d m k B)
    {Γ Q : Type u}
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure
            (Subgroup.closure (Set.range s)) = ⊤)
    (φ : Γ →* Q)
    (hφcont : Continuous (fun x : Γ => φ x))
    (hφsurj : Function.Surjective φ) :
    HPWidth Q m k ∧
      Nat.card (Q ⧸ powerSubgroup Q m) ≤ B := by
  exact
    hfin Q (fun i : Fin d => φ (s i))
      (GeneratedBy.of_dense_image s hs φ hφcont hφsurj)
/-- Power words commute with group homomorphisms. -/
lemma map_word_map
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (m k : ℕ) (x : Fin k → G) :
    φ (powerWordMap G m k x) =
      powerWordMap H m k (fun i : Fin k => φ (x i)) := by
  induction k with
  | zero =>
      simp [powerWordMap]
  | succ k ih =>
      simp [powerWordMap, ih (fun i : Fin k => x i.castSucc)]
/-- A surjective image of a group with bounded power width has the same width bound. -/
lemma HPWidth.map_surjective
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Surjective φ)
    {m k : ℕ}
    (hwidth : HPWidth G m k) :
    HPWidth H m k := by
  classical
  intro y hy
  have hyWord : y ∈ powerWordSubgroup H m := by
    simpa [power_subgroup_word (G := H) m] using hy
  rcases hyWord with ⟨r, z, hz⟩
  let x : Fin r → G := fun i => Classical.choose (hφ (z i))
  have hx : ∀ i : Fin r, φ (x i) = z i := fun i =>
    Classical.choose_spec (hφ (z i))
  have hx_fun : (fun i : Fin r => φ (x i)) = z := by
    funext i
    exact hx i
  have hmap := map_word_map φ m r x
  rw [hx_fun] at hmap
  have hxmem : powerWordMap G m r x ∈ powerSubgroup G m :=
    power_subgroup (G := G) m r x
  rcases hwidth (powerWordMap G m r x) hxmem with ⟨w, hw⟩
  refine ⟨fun i : Fin k => φ (w i), ?_⟩
  calc
    powerWordMap H m k (fun i : Fin k => φ (w i)) =
        φ (powerWordMap G m k w) := by
      exact (map_word_map φ m k w).symm
    _ = φ (powerWordMap G m r x) := by
      rw [hw]
    _ = powerWordMap H m r z := hmap
    _ = y := hz
/-- The minimal finite power width cannot increase under a surjective homomorphic image. -/
lemma width_number_surjective
    {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    (φ : G →* H) (hφ : Function.Surjective φ)
    (m : ℕ) :
    powerWidthNumber H m ≤ powerWidthNumber G m := by
  exact
    power_width_number
      (G := H) (m := m)
      (HPWidth.map_surjective
        (G := G) (H := H) φ hφ
        (width_number_spec G m))
/-- The minimal finite power width of a quotient is bounded by that of the original finite group. -/
lemma width_number_quotient
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] [Finite (G ⧸ N)]
    (m : ℕ) :
    powerWidthNumber (G ⧸ N) m ≤ powerWidthNumber G m := by
  exact
    width_number_surjective
      (G := G) (H := G ⧸ N)
      (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
      m
/-- A power word in a quotient can be lifted to a power word upstairs. -/
lemma quotient_word_lift
    {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal]
    (m k : ℕ) (x : Fin k → G ⧸ H) :
    ∃ y : Fin k → G,
      QuotientGroup.mk' H (powerWordMap G m k y) =
        powerWordMap (G ⧸ H) m k x := by
  classical
  let y : Fin k → G := fun i =>
    Classical.choose (QuotientGroup.mk'_surjective H (x i))
  have hy : ∀ i : Fin k, QuotientGroup.mk' H (y i) = x i := fun i =>
    Classical.choose_spec (QuotientGroup.mk'_surjective H (x i))
  refine ⟨y, ?_⟩
  have hfun :
      (fun i : Fin k => QuotientGroup.mk' H (y i)) = x := by
    funext i
    exact hy i
  have hmap := map_word_map (QuotientGroup.mk' H) m k y
  rw [hfun] at hmap
  exact hmap
/-- The image of a power subgroup lies in the power subgroup of the target. -/
lemma power_map_le
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H) (m : ℕ) :
    (powerSubgroup G m).map φ ≤ powerSubgroup H m := by
  rw [Subgroup.map_le_iff_le_comap]
  dsimp [powerSubgroup]
  refine Subgroup.normalClosure_le_normal ?_
  rintro y ⟨x, rfl⟩
  change φ (x ^ m) ∈ powerSubgroup H m
  simpa using pow_power_subgroup m (φ x)
/-- Power subgroups commute with binary products. -/
lemma powerSubgroup_prod
    (G H : Type u) [Group G] [Group H] (m : ℕ) :
    powerSubgroup (G × H) m =
      (powerSubgroup G m).prod (powerSubgroup H m) := by
  apply le_antisymm
  · dsimp [powerSubgroup]
    exact
      Subgroup.normalClosure_le_normal (by
        rintro y ⟨x, rfl⟩
        exact
          ⟨by simpa using pow_power_subgroup m x.1,
            by simpa using pow_power_subgroup m x.2⟩)
  · exact
      (Subgroup.prod_le_iff).mpr
        ⟨power_map_le (MonoidHom.inl G H) m,
          power_map_le (MonoidHom.inr G H) m⟩
/-- Power words in a product are computed componentwise. -/
lemma power_word_prod
    {G H : Type u} [Group G] [Group H]
    (m : ℕ) :
    ∀ (k : ℕ) (x : Fin k → G × H),
      powerWordMap (G × H) m k x =
        (powerWordMap G m k (fun i : Fin k => (x i).1),
          powerWordMap H m k (fun i : Fin k => (x i).2))
  | 0, _ => by
      ext <;> simp [powerWordMap]
  | k + 1, x => by
      ext <;>
        simp [powerWordMap, power_word_prod (G := G) (H := H) m k
          (fun i : Fin k => x i.castSucc)]
/-- Product groups inherit a common fixed power-width bound componentwise. -/
lemma HPWidth.prod
    {G H : Type u} [Group G] [Group H] {m k : ℕ}
    (hG : HPWidth G m k)
    (hH : HPWidth H m k) :
    HPWidth (G × H) m k := by
  intro g hg
  have hgprod :
      g ∈ (powerSubgroup G m).prod (powerSubgroup H m) := by
    simpa [powerSubgroup_prod (G := G) (H := H) m] using hg
  have hgG : g.1 ∈ powerSubgroup G m := (Subgroup.mem_prod.mp hgprod).1
  have hgH : g.2 ∈ powerSubgroup H m := (Subgroup.mem_prod.mp hgprod).2
  rcases hG g.1 hgG with ⟨x, hx⟩
  rcases hH g.2 hgH with ⟨y, hy⟩
  refine ⟨fun i : Fin k => (x i, y i), ?_⟩
  rw [power_word_prod]
  exact Prod.ext hx hy
/-- The minimal finite power width of a product is bounded by the maximum of the component
minimal widths. -/
lemma width_number_prod
    (G H : Type u) [Group G] [Finite G] [Group H] [Finite H]
    (m : ℕ) :
    powerWidthNumber (G × H) m ≤
      max (powerWidthNumber G m) (powerWidthNumber H m) := by
  let k : ℕ := max (powerWidthNumber G m) (powerWidthNumber H m)
  refine
    power_width_number
      (G := G × H) (m := m) ?_
  exact
    HPWidth.prod
      (G := G) (H := H) (m := m) (k := k)
      (HPWidth.mono_k
        (width_number_spec G m)
        (le_max_left _ _))
      (HPWidth.mono_k
        (width_number_spec H m)
        (le_max_right _ _))
/-- Elements of a power subgroup stay in the power subgroup after quotienting. -/
lemma power_subgroup_mk
    {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal]
    {m : ℕ} {g : G}
    (hg : g ∈ powerSubgroup G m) :
    QuotientGroup.mk' H g ∈ powerSubgroup (G ⧸ H) m := by
  exact
    (power_map_le (QuotientGroup.mk' H) m)
      ⟨g, hg, rfl⟩
/-- Quotient width can be represented by lifted upstairs power words. -/
lemma quotient_range_width
    {G : Type u} [Group G]
    (H : Subgroup G) [H.Normal]
    {m k : ℕ}
    (hwidth : HPWidth (G ⧸ H) m k)
    {g : G}
    (hg : QuotientGroup.mk' H g ∈ powerSubgroup (G ⧸ H) m) :
    QuotientGroup.mk' H g ∈
      Set.range
        (fun y : Fin k → G =>
          QuotientGroup.mk' H (powerWordMap G m k y)) := by
  rcases hwidth (QuotientGroup.mk' H g) hg with ⟨x, hx⟩
  rcases quotient_word_lift (G := G) H m k x with ⟨y, hy⟩
  exact ⟨y, hy.trans hx⟩
/-- A quotient by a subgroup containing the power subgroup has trivial power subgroup. -/
lemma power_subgroup_bot
    {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {m : ℕ}
    (hPH : powerSubgroup G m ≤ H) :
    powerSubgroup (G ⧸ H) m = ⊥ := by
  refine le_antisymm ?_ bot_le
  dsimp [powerSubgroup]
  refine Subgroup.normalClosure_le_normal ?_
  rintro y ⟨x, rfl⟩
  rcases QuotientGroup.mk'_surjective H x with ⟨a, rfl⟩
  change (QuotientGroup.mk' H a) ^ m = 1
  have hq : QuotientGroup.mk' H (a ^ m) = 1 := by
    exact
      (QuotientGroup.eq_one_iff (N := H) (a ^ m)).mpr
        (hPH (pow_power_subgroup m a))
  simpa using hq
/-- The quotient by the trivial subgroup has the same cardinality as the original group. -/
lemma nat_card_bot (G : Type*) [Group G] :
    Nat.card (G ⧸ (⊥ : Subgroup G)) = Nat.card G := by
  exact Nat.card_congr (QuotientGroup.quotientBot (G := G)).toEquiv
/-- If the quotient power subgroup is trivial, a bound on the quotient-by-power-subgroup is a
bound on the open-normal quotient itself. -/
lemma card_open_subgroup
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {m B : ℕ}
    (N : OpenNormalSubgroup Γ)
    (hPN : powerSubgroup Γ m ≤ N.toSubgroup)
    (hcard :
      Nat.card
          ((Γ ⧸ N.toSubgroup) ⧸
            powerSubgroup (Γ ⧸ N.toSubgroup) m) ≤ B) :
    Nat.card (Γ ⧸ N.toSubgroup) ≤ B := by
  have hbot :
      powerSubgroup (Γ ⧸ N.toSubgroup) m = ⊥ :=
    power_subgroup_bot
      (G := Γ) (H := N.toSubgroup) (m := m) hPN
  simpa [hbot, nat_card_bot] using hcard
/-- Open normal subgroups form a neighbourhood basis at `1`. -/
def OpenSubgroupBasis
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] : Prop :=
  ∀ U : Set Γ,
    U ∈ nhds (1 : Γ) →
      ∃ N : OpenNormalSubgroup Γ,
        (N.toSubgroup : Set Γ) ⊆ U
/-- Closed sets can be separated from exterior points by finite open-normal quotients. -/
def SubgroupsSeparateSets
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] : Prop :=
  ∀ ⦃C : Set Γ⦄,
    IsClosed C →
      ∀ g : Γ,
        g ∉ C →
          ∃ N : OpenNormalSubgroup Γ,
            QuotientGroup.mk' N.toSubgroup g ∉
              (QuotientGroup.mk' N.toSubgroup) '' C
/-- An open-normal basis at `1` separates closed sets from exterior points by quotients. -/
lemma subgroups_separate_sets
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hbasis : OpenSubgroupBasis Γ) :
    SubgroupsSeparateSets Γ := by
  intro C hC g hgC
  let U : Set Γ := {x : Γ | g * x ∉ C}
  have hU : U ∈ nhds (1 : Γ) := by
    have hCcompl : Cᶜ ∈ nhds g :=
      hC.isOpen_compl.mem_nhds hgC
    have hCcompl' : Cᶜ ∈ nhds ((fun x : Γ => g * x) (1 : Γ)) := by
      simpa using hCcompl
    have hpre :
        (fun x : Γ => g * x) ⁻¹' Cᶜ ∈ nhds (1 : Γ) :=
      ((continuous_const.mul continuous_id).continuousAt) hCcompl'
    simpa [U] using hpre
  rcases hbasis U hU with ⟨N, hNU⟩
  refine ⟨N, ?_⟩
  rintro ⟨c, hcC, hcq⟩
  have hq :
      QuotientGroup.mk' N.toSubgroup (g⁻¹ * c) = 1 := by
    calc
      QuotientGroup.mk' N.toSubgroup (g⁻¹ * c)
          =
            (QuotientGroup.mk' N.toSubgroup g)⁻¹ *
              QuotientGroup.mk' N.toSubgroup c := by
                simp
      _ = 1 := by
                simp [hcq]
  have hmem : g⁻¹ * c ∈ N.toSubgroup :=
    (QuotientGroup.eq_one_iff (N := N.toSubgroup) (g⁻¹ * c)).mp hq
  have hnotC : g * (g⁻¹ * c) ∉ C :=
    hNU hmem
  exact hnotC (by simpa [mul_assoc] using hcC)
/-- Compact-image residual detection by open-normal quotients. -/
def OpenClosedDetection
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (φ : X → Γ),
      Continuous φ →
        ∀ g : Γ,
          (∀ N : OpenNormalSubgroup Γ,
            QuotientGroup.mk' N.toSubgroup g ∈
              Set.range
                (fun x : X =>
                  QuotientGroup.mk' N.toSubgroup (φ x))) →
            g ∈ Set.range φ
/-- Closed-set separation implies compact-image detection by open-normal quotients. -/
lemma detection_separate_sets
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [T2Space Γ]
    (hsep : SubgroupsSeparateSets Γ) :
    OpenClosedDetection Γ := by
  intro X _ _ φ hφ g hquot
  by_contra hg
  have hclosed : IsClosed (Set.range φ) := by
    simpa using (isCompact_univ.image hφ).isClosed
  rcases hsep (C := Set.range φ) hclosed g hg with ⟨N, hN⟩
  apply hN
  rcases hquot N with ⟨x, hx⟩
  exact ⟨φ x, ⟨x, rfl⟩, hx⟩
/-- Compact totally disconnected topological groups have an open-normal subgroup basis at `1`. -/
lemma open_totally_disconnected
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] :
    OpenSubgroupBasis Γ := by
  intro U hU
  rcases mem_nhds_iff.mp hU with ⟨V, hVU, hVopen, h1V⟩
  rcases
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (G := Γ) hVopen h1V with
    ⟨N, hNV⟩
  exact ⟨N, hNV.trans hVU⟩
/-- In a compact totally disconnected topological group, open-normal quotients separate closed
sets from exterior points. -/
lemma subgroups_separate_disconnected
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] :
    SubgroupsSeparateSets Γ := by
  exact
    subgroups_separate_sets
      (open_totally_disconnected (Γ := Γ))
/-- Compact images in a compact totally disconnected topological group are detected by
open-normal quotients. -/
lemma detection_compact_disconnected
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] :
    OpenClosedDetection Γ := by
  letI : T2Space Γ := t_space_disconnected Γ
  intro X _ _ φ hφ g hquot
  let hsep : SubgroupsSeparateSets Γ :=
    subgroups_separate_disconnected (Γ := Γ)
  exact
    detection_separate_sets
      (Γ := Γ)
      hsep
      (φ := φ) hφ g hquot
/-- An open-normal quotient is discrete. -/
lemma open_discrete_topology
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (N : OpenNormalSubgroup Γ) :
    DiscreteTopology (Γ ⧸ N.toSubgroup) := by
  exact QuotientGroup.discreteTopology N.isOpen
/-- An open-normal quotient of a compact topological group is finite. -/
lemma open_normal_finite
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    (N : OpenNormalSubgroup Γ) :
    Finite (Γ ⧸ N.toSubgroup) := by
  exact N.toSubgroup.quotient_finite_of_isOpen N.isOpen
/-- The quotient map to an open-normal quotient is continuous. -/
lemma open_normal_continuous
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    (N : OpenNormalSubgroup Γ) :
    Continuous (fun x : Γ => QuotientGroup.mk' N.toSubgroup x) := by
  change Continuous (QuotientGroup.mk : Γ → Γ ⧸ N.toSubgroup)
  exact QuotientGroup.continuous_mk
/-- A subgroup containing an open subgroup is open. -/
lemma subgroup_open
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {K L : Subgroup Γ}
    (hKopen : IsOpen ((K : Subgroup Γ) : Set Γ))
    (hKL : K ≤ L) :
    IsOpen ((L : Subgroup Γ) : Set Γ) := by
  exact Subgroup.isOpen_mono hKL hKopen
/-- The full group as an open normal subgroup. -/
def open_top_aux
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] :
    OpenNormalSubgroup Γ :=
  { toSubgroup := ⊤
    isOpen' := by
      change IsOpen (Set.univ : Set Γ)
      exact isOpen_univ
    isNormal' := by
      infer_instance }
/-- Intersection of two open normal subgroups as an open normal subgroup. -/
def open_inf_aux
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    (N M : OpenNormalSubgroup Γ) :
    OpenNormalSubgroup Γ :=
  { toSubgroup := N.toSubgroup ⊓ M.toSubgroup
    isOpen' := by
      simpa using N.isOpen.inter M.isOpen
    isNormal' := by
      infer_instance }
/-- The join of a normal subgroup with an open normal subgroup is open normal. -/
def open_sup_aux
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (H : Subgroup Γ) [H.Normal]
    (M : OpenNormalSubgroup Γ) :
    OpenNormalSubgroup Γ :=
  { toSubgroup := H ⊔ M.toSubgroup
    isOpen' := by
      exact
        subgroup_open
          (K := M.toSubgroup)
          (L := H ⊔ M.toSubgroup)
          M.isOpen
          (show M.toSubgroup ≤ H ⊔ M.toSubgroup from le_sup_right)
    isNormal' := by
      infer_instance }
/-- Equality of quotient representatives from membership of the difference in the kernel. -/
lemma mk_inv_aux
    {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {a b : G}
    (h : a⁻¹ * b ∈ H) :
    QuotientGroup.mk' H a = QuotientGroup.mk' H b := by
  let q : G →* G ⧸ H := QuotientGroup.mk' H
  have hq : q (a⁻¹ * b) = 1 :=
    (QuotientGroup.eq_one_iff (N := H) (a⁻¹ * b)).mpr h
  calc
    q a = q a * 1 := by simp
    _ = q a * q (a⁻¹ * b) := by rw [hq]
    _ = q (a * (a⁻¹ * b)) := by simp
    _ = q b := by simp
/-- Membership of the difference in the kernel from equality of quotient representatives. -/
lemma inv_mk_aux
    {G : Type u} [Group G]
    {H : Subgroup G} [H.Normal]
    {a b : G}
    (h : QuotientGroup.mk' H a = QuotientGroup.mk' H b) :
    a⁻¹ * b ∈ H := by
  let q : G →* G ⧸ H := QuotientGroup.mk' H
  have hq : q (a⁻¹ * b) = 1 := by
    calc
      q (a⁻¹ * b) = (q a)⁻¹ * q b := by simp
      _ = (q b)⁻¹ * q b := by rw [h]
      _ = 1 := by simp
  exact (QuotientGroup.eq_one_iff (N := H) (a⁻¹ * b)).mp hq
/-- If `x ∈ H ⊔ M`, then its image modulo `M` is the image of an element of `H`. -/
lemma mk_sup_aux
    {Γ : Type u} [Group Γ]
    (H M : Subgroup Γ) [M.Normal]
    {x : Γ}
    (hx : x ∈ H ⊔ M) :
    QuotientGroup.mk' M x ∈
      (fun y : Γ => QuotientGroup.mk' M y) '' ((H : Subgroup Γ) : Set Γ) := by
  let q : Γ →* Γ ⧸ M := QuotientGroup.mk' M
  have hmap : q x ∈ H.map q := by
    have hH : H ≤ (H.map q).comap q := by
      intro y hy
      exact ⟨y, hy, rfl⟩
    have hM : M ≤ (H.map q).comap q := by
      intro y hy
      change q y ∈ H.map q
      have hy1 : q y = 1 :=
        (QuotientGroup.eq_one_iff (N := M) y).mpr hy
      rw [hy1]
      exact Subgroup.one_mem _
    exact (sup_le hH hM) hx
  rcases hmap with ⟨y, hyH, hyq⟩
  exact ⟨y, hyH, hyq⟩
/-- A closed normal subgroup of a compact totally disconnected group is separated from each
exterior point by an open normal overgroup. -/
lemma open_closed_not
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {H : Subgroup Γ} [H.Normal]
    (hHclosed : IsClosed ((H : Subgroup Γ) : Set Γ))
    {x : Γ}
    (hx : x ∉ H) :
    ∃ N : OpenNormalSubgroup Γ,
      H ≤ N.toSubgroup ∧ x ∉ N.toSubgroup := by
  let Hc : ClosedSubgroup Γ :=
    { toSubgroup := H
      isClosed' := hHclosed }
  let S : Set (Subgroup Γ) :=
    {K : Subgroup Γ | IsOpen ((K : Subgroup Γ) : Set Γ) ∧ (Hc : Subgroup Γ) ≤ K}
  have hH_eq : (Hc : Subgroup Γ) = sInf S := by
    simpa [S] using ProfiniteGrp.closedSubgroup_eq_sInf_open (G := Γ) Hc
  have hx_sInf : x ∉ (sInf S : Subgroup Γ) := by
    intro hxinf
    exact hx (by
      have hxHc : x ∈ (Hc : Subgroup Γ) := by
        simpa [hH_eq] using hxinf
      simpa [Hc] using hxHc)
  have hx_not_forall : ¬ ∀ K ∈ S, x ∈ K := by
    simpa [Subgroup.mem_sInf] using hx_sInf
  push Not at hx_not_forall
  rcases hx_not_forall with ⟨K, hKS, hxK⟩
  rcases hKS with ⟨hKopen, hHK⟩
  have hKclosed : IsClosed ((K : Subgroup Γ) : Set Γ) :=
    Subgroup.isClosed_of_isOpen K hKopen
  haveI : K.FiniteIndex := by
    letI : Finite (Γ ⧸ K) := K.quotient_finite_of_isOpen hKopen
    exact Subgroup.finiteIndex_of_finite_quotient
  have hcoreClosed : IsClosed ((K.normalCore : Subgroup Γ) : Set Γ) :=
    K.normalCore_isClosed hKclosed
  have hcoreOpen : IsOpen ((K.normalCore : Subgroup Γ) : Set Γ) :=
    K.normalCore.isOpen_of_isClosed_of_finiteIndex hcoreClosed
  let N : OpenNormalSubgroup Γ :=
    { toSubgroup := K.normalCore
      isOpen' := hcoreOpen
      isNormal' := inferInstance }
  refine ⟨N, ?_, ?_⟩
  · dsimp [N]
    exact Subgroup.normal_le_normalCore.mpr (by
      simpa [Hc] using hHK)
  · intro hxN
    exact hxK (K.normalCore_le hxN)
/-- Distinct cosets modulo a closed normal subgroup can be separated in an open-normal quotient
whose kernel still contains that subgroup. -/
lemma open_separating_pair
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {H : Subgroup Γ} [H.Normal]
    (hHclosed : IsClosed ((H : Subgroup Γ) : Set Γ))
    {a b : Γ}
    (hab : QuotientGroup.mk' H a ≠ QuotientGroup.mk' H b) :
    ∃ N : OpenNormalSubgroup Γ,
      H ≤ N.toSubgroup ∧
        QuotientGroup.mk' N.toSubgroup a ≠ QuotientGroup.mk' N.toSubgroup b := by
  have hdiff : a⁻¹ * b ∉ H := by
    intro hmem
    exact hab (QuotientGroup.eq.mpr hmem)
  rcases
      open_closed_not
        (Γ := Γ) (H := H) hHclosed hdiff with
    ⟨N, hHN, hdiffN⟩
  refine ⟨N, hHN, ?_⟩
  intro hq
  exact hdiffN (QuotientGroup.eq.mp hq)
/-- Closed-set separation gives an open normal overgroup of `H` excluding one exterior point. -/
lemma supergroup_separate_sets
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hsep : SubgroupsSeparateSets Γ)
    {H : Subgroup Γ} [H.Normal]
    (hHclosed : IsClosed ((H : Subgroup Γ) : Set Γ))
    {x : Γ}
    (hxH : x ∉ H) :
    ∃ N : OpenNormalSubgroup Γ,
      H ≤ N.toSubgroup ∧ x ∉ N.toSubgroup := by
  rcases hsep (C := ((H : Subgroup Γ) : Set Γ)) hHclosed x hxH with
    ⟨M, hMsep⟩
  let N : OpenNormalSubgroup Γ :=
    open_sup_aux (Γ := Γ) H M
  refine ⟨N, ?_, ?_⟩
  · dsimp [N, open_sup_aux]
    exact le_sup_left
  · intro hxN
    apply hMsep
    exact
      mk_sup_aux
        (H := H)
        (M := M.toSubgroup)
        (by
          simpa [N, open_sup_aux] using hxN)
/-- A finite set of points outside `H` can be avoided by one open normal overgroup of `H`. -/
lemma avoid_separate_sets
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hsep : SubgroupsSeparateSets Γ)
    {H : Subgroup Γ} [H.Normal]
    (hHclosed : IsClosed ((H : Subgroup Γ) : Set Γ))
    (F : Finset Γ)
    (hF : ∀ x, x ∈ F → x ∉ H) :
    ∃ N : OpenNormalSubgroup Γ,
      H ≤ N.toSubgroup ∧
        ∀ x, x ∈ F → x ∉ N.toSubgroup := by
  classical
  revert hF
  refine Finset.induction_on F ?base ?step
  · intro hF
    refine ⟨open_top_aux Γ, ?_, ?_⟩
    · intro x hx
      trivial
    · intro x hx
      simp at hx
  · intro a F ha ih hF
    have haH : a ∉ H := by
      exact hF a (by simp)
    have hFrest : ∀ x, x ∈ F → x ∉ H := by
      intro x hx
      exact hF x (Finset.mem_insert_of_mem hx)
    rcases ih hFrest with ⟨N₀, hHN₀, havoid₀⟩
    rcases
        supergroup_separate_sets
          (Γ := Γ)
          hsep
          (H := H)
          hHclosed
          haH with
      ⟨N₁, hHN₁, haN₁⟩
    let N : OpenNormalSubgroup Γ :=
      open_inf_aux N₀ N₁
    refine ⟨N, ?_, ?_⟩
    · intro x hxH
      exact ⟨hHN₀ hxH, hHN₁ hxH⟩
    · intro x hxInsert hxN
      have hxboth :
          x ∈ N₀.toSubgroup ∧ x ∈ N₁.toSubgroup := by
        simpa [N, open_inf_aux] using hxN
      rcases Finset.mem_insert.mp hxInsert with rfl | hxF
      · exact haN₁ hxboth.2
      · exact havoid₀ x hxF hxboth.1
/-- A finite indexed family of points outside `H` can be avoided by one open normal overgroup. -/
lemma supergroup_avoid_sets
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hsep : SubgroupsSeparateSets Γ)
    {H : Subgroup Γ} [H.Normal]
    (hHclosed : IsClosed ((H : Subgroup Γ) : Set Γ))
    {α : Type*} [Finite α]
    (x : α → Γ)
    (hx : ∀ a, x a ∉ H) :
    ∃ N : OpenNormalSubgroup Γ,
      H ≤ N.toSubgroup ∧
        ∀ a, x a ∉ N.toSubgroup := by
  classical
  letI := Fintype.ofFinite α
  let F : Finset Γ := Finset.univ.image x
  have hF : ∀ y, y ∈ F → y ∉ H := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨a, _ha, rfl⟩
    exact hx a
  rcases
      avoid_separate_sets
        (Γ := Γ)
        hsep
        (H := H)
        hHclosed
        F hF with
    ⟨N, hHN, havoid⟩
  refine ⟨N, hHN, ?_⟩
  intro a haN
  exact havoid (x a) (by simp [F]) haN
/-- A finite family of distinct cosets modulo `H` is separated by one open-normal quotient
containing `H`. -/
lemma open_supergroup_separating
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hsep : SubgroupsSeparateSets Γ)
    {H : Subgroup Γ} [H.Normal]
    (hHclosed : IsClosed ((H : Subgroup Γ) : Set Γ))
    {q : ℕ}
    (f : Fin q → Γ ⧸ H)
    (hf : Function.Injective f) :
    ∃ N : OpenNormalSubgroup Γ,
      H ≤ N.toSubgroup ∧
        ∃ r : Fin q → Γ,
          (∀ i, QuotientGroup.mk' H (r i) = f i) ∧
            Function.Injective
              (fun i : Fin q =>
                QuotientGroup.mk' N.toSubgroup (r i)) := by
  classical
  let r : Fin q → Γ := fun i =>
    Classical.choose (QuotientGroup.mk'_surjective H (f i))
  have hr : ∀ i, QuotientGroup.mk' H (r i) = f i := fun i =>
    Classical.choose_spec (QuotientGroup.mk'_surjective H (f i))
  let α := {ij : Fin q × Fin q // ij.1 ≠ ij.2}
  let x : α → Γ := fun a =>
    (r a.1.1)⁻¹ * r a.1.2
  have hx : ∀ a : α, x a ∉ H := by
    intro a hxH
    have hqeq : f a.1.1 = f a.1.2 := by
      rw [← hr a.1.1, ← hr a.1.2]
      exact mk_inv_aux (H := H) hxH
    exact a.2 (hf hqeq)
  rcases
      supergroup_avoid_sets
        (Γ := Γ)
        hsep
        (H := H)
        hHclosed
        (x := x)
        hx with
    ⟨N, hHN, havoid⟩
  refine ⟨N, hHN, r, hr, ?_⟩
  intro i j hij
  by_contra hne
  have hdiff : (r i)⁻¹ * r j ∈ N.toSubgroup :=
    inv_mk_aux
      (H := N.toSubgroup)
      hij
  exact
    (havoid ⟨(i, j), hne⟩)
      (by
        simpa [x] using hdiff)
/-- An injection from `Fin q` into a finite type bounds `q` by the type cardinality. -/
lemma nat_fin_injective
    {α : Type u} [Finite α]
    {q : ℕ}
    {f : Fin q → α}
    (hf : Function.Injective f) :
    q ≤ Nat.card α := by
  classical
  letI := Fintype.ofFinite α
  have hcard :
      Fintype.card (Fin q) ≤ Fintype.card α :=
    Fintype.card_le_of_injective f hf
  simpa [Nat.card_eq_fintype_card] using hcard
/-- An infinite type admits injections from all finite leading segments. -/
lemma injective_fin_infinite
    (α : Type u) [Infinite α]
    (B : ℕ) :
    ∃ f : Fin (B + 1) → α, Function.Injective f := by
  classical
  let e : ℕ ↪ α := Infinite.natEmbedding α
  refine ⟨fun i => e i.1, ?_⟩
  intro i j hij
  apply Fin.ext
  exact e.injective hij
/-- Uniformly bounded open-normal quotients above a closed normal subgroup force the full quotient
by that subgroup to be finite. -/
def BoundedOpenQuotients
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] : Prop :=
  ∀ {H : Subgroup Γ} [H.Normal],
    IsClosed ((H : Subgroup Γ) : Set Γ) →
      ∀ {B : ℕ},
        (∀ N : OpenNormalSubgroup Γ,
          H ≤ N.toSubgroup →
            Nat.card (Γ ⧸ N.toSubgroup) ≤ B) →
          Finite (Γ ⧸ H)
/-- Uniformly bounded open-normal quotients above closed normal subgroups force the full quotient
to be finite in compact totally disconnected topological groups. -/
theorem quotients_totally_disconnected
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] :
    BoundedOpenQuotients Γ := by
  classical
  intro H hHnormal hHclosed B hB
  letI : H.Normal := hHnormal
  by_contra hnotfinite
  haveI : Infinite (Γ ⧸ H) := by
    exact not_finite_iff_infinite.mp hnotfinite
  rcases injective_fin_infinite (Γ ⧸ H) B with
    ⟨f, hf⟩
  have hsep : SubgroupsSeparateSets Γ :=
    subgroups_separate_disconnected
      (Γ := Γ)
  rcases
      open_supergroup_separating
        (Γ := Γ)
        hsep
        (H := H)
        hHclosed
        f hf with
    ⟨N, hHN, r, _hr, hinj⟩
  haveI : Finite (Γ ⧸ N.toSubgroup) :=
    open_normal_finite (Γ := Γ) N
  have hlarge :
      B + 1 ≤ Nat.card (Γ ⧸ N.toSubgroup) := by
    exact
      nat_fin_injective
        (α := Γ ⧸ N.toSubgroup)
        (q := B + 1)
        (f := fun i : Fin (B + 1) =>
          QuotientGroup.mk' N.toSubgroup (r i))
        hinj
  have hsmall :
      Nat.card (Γ ⧸ N.toSubgroup) ≤ B :=
    hB N hHN
  omega
/-- If every open-normal quotient has power width `k`, then so does the compact group, provided
compact images are detected by open-normal quotients. -/
lemma width_open_normal
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {m k : ℕ}
    (hdet : OpenClosedDetection Γ)
    (hQwidth :
      ∀ N : OpenNormalSubgroup Γ,
        HPWidth (Γ ⧸ N.toSubgroup) m k) :
    HPWidth Γ m k := by
  intro g hg
  have hrange : g ∈ Set.range (powerWordMap Γ m k) := by
    refine
      hdet
        (φ := powerWordMap Γ m k)
        (continuous_power_word (Γ := Γ) m k)
        g
        ?_
    intro N
    have hgQ :
        QuotientGroup.mk' N.toSubgroup g ∈
          powerSubgroup (Γ ⧸ N.toSubgroup) m :=
      power_subgroup_mk
        (G := Γ) N.toSubgroup (m := m) hg
    simpa using
      quotient_range_width
        (G := Γ) N.toSubgroup
        (m := m) (k := k)
        (hQwidth N)
        hgQ
  rcases hrange with ⟨x, hx⟩
  exact ⟨x, hx⟩
/-- Open-normal quotient bounds imply finiteness of the quotient by a closed power subgroup. -/
lemma open_index_bound
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ]
    (hfinite : BoundedOpenQuotients Γ)
    {m k B : ℕ}
    (hwidth : HPWidth Γ m k)
    (hQindex :
      ∀ N : OpenNormalSubgroup Γ,
        Nat.card
          ((Γ ⧸ N.toSubgroup) ⧸
            powerSubgroup (Γ ⧸ N.toSubgroup) m) ≤ B) :
    Finite (Γ ⧸ powerSubgroup Γ m) := by
  let P : Subgroup Γ := powerSubgroup Γ m
  haveI : P.Normal := by
    dsimp [P]
    infer_instance
  have hPclosed : IsClosed ((P : Subgroup Γ) : Set Γ) := by
    simpa [P] using
      subgroup_closed_width
        (Γ := Γ) (m := m) (k := k) hwidth
  have hbound :
      ∀ N : OpenNormalSubgroup Γ,
        P ≤ N.toSubgroup →
          Nat.card (Γ ⧸ N.toSubgroup) ≤ B := by
    intro N hPN
    exact
      card_open_subgroup
        (Γ := Γ) (m := m) (B := B)
        N
        (by simpa [P] using hPN)
        (hQindex N)
  simpa [P] using
    hfinite (H := P) hPclosed (B := B) hbound
/-- Finite quotient width and index bounds over all open-normal quotients make the power subgroup
open, after the compactness/separation bridge properties have been supplied. -/
theorem width_index_bound
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ]
    {m k B : ℕ}
    (hdet : OpenClosedDetection Γ)
    (hfinite : BoundedOpenQuotients Γ)
    (hQ :
      ∀ N : OpenNormalSubgroup Γ,
        HPWidth (Γ ⧸ N.toSubgroup) m k ∧
          Nat.card
            ((Γ ⧸ N.toSubgroup) ⧸
              powerSubgroup (Γ ⧸ N.toSubgroup) m) ≤ B) :
    IsOpen ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) := by
  have hwidth : HPWidth Γ m k :=
    width_open_normal
      (Γ := Γ) (m := m) (k := k)
      hdet
      (fun N => (hQ N).1)
  have hfin :
      Finite (Γ ⧸ powerSubgroup Γ m) :=
    open_index_bound
      (Γ := Γ) (m := m) (k := k) (B := B)
      hfinite
      hwidth
      (fun N => (hQ N).2)
  letI : Finite (Γ ⧸ powerSubgroup Γ m) := hfin
  exact
    power_open_width
      (Γ := Γ) (m := m) (k := k)
      hwidth
/-- The finite width/index package supplies the open-normal quotient hypotheses for a densely
generated profinite group. -/
lemma open_width_bound
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d m k B : ℕ}
    (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure
            (Subgroup.closure (Set.range s)) = ⊤)
    (hfin : WIBound.{u} d m k B)
    (hdisc :
      ∀ N : OpenNormalSubgroup Γ,
        DiscreteTopology (Γ ⧸ N.toSubgroup))
    (hfiniteQ :
      ∀ N : OpenNormalSubgroup Γ,
        Finite (Γ ⧸ N.toSubgroup))
    (hcont :
      ∀ N : OpenNormalSubgroup Γ,
        Continuous
          (fun x : Γ => QuotientGroup.mk' N.toSubgroup x)) :
    ∀ N : OpenNormalSubgroup Γ,
      HPWidth (Γ ⧸ N.toSubgroup) m k ∧
        Nat.card
          ((Γ ⧸ N.toSubgroup) ⧸
            powerSubgroup (Γ ⧸ N.toSubgroup) m) ≤ B := by
  intro N
  letI : DiscreteTopology (Γ ⧸ N.toSubgroup) := hdisc N
  letI : Finite (Γ ⧸ N.toSubgroup) := hfiniteQ N
  exact
    WIBound.apply_fin_discretequot
      (d := d) (m := m) (k := k) (B := B)
      hfin
      (Γ := Γ) (Q := Γ ⧸ N.toSubgroup)
      s hs
      (QuotientGroup.mk' N.toSubgroup)
      (hcont N)
      (QuotientGroup.mk'_surjective N.toSubgroup)
/-- Finite quotient width/index bounds imply power-subgroup openness once the topological bridge
properties and quotient-topology facts are supplied. -/
theorem power_width_bound
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ]
    {d m k B : ℕ}
    (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure
            (Subgroup.closure (Set.range s)) = ⊤)
    (hdet : OpenClosedDetection Γ)
    (hfinite : BoundedOpenQuotients Γ)
    (hfin : WIBound.{u} d m k B)
    (hdisc :
      ∀ N : OpenNormalSubgroup Γ,
        DiscreteTopology (Γ ⧸ N.toSubgroup))
    (hfiniteQ :
      ∀ N : OpenNormalSubgroup Γ,
        Finite (Γ ⧸ N.toSubgroup))
    (hcont :
      ∀ N : OpenNormalSubgroup Γ,
        Continuous
          (fun x : Γ => QuotientGroup.mk' N.toSubgroup x)) :
    IsOpen ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) := by
  exact
    width_index_bound
      (Γ := Γ) (m := m) (k := k) (B := B)
      hdet
      hfinite
      (open_width_bound
        (Γ := Γ) (d := d) (m := m) (k := k) (B := B)
        s hs hfin hdisc hfiniteQ hcont)
/-- In compact totally disconnected topological groups, the finite width/index package and the
bounded-open-normal-quotient bridge imply power-subgroup openness. -/
theorem
    compact_totally_disconnected
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d m k B : ℕ}
    (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure
            (Subgroup.closure (Set.range s)) = ⊤)
    (hfinite : BoundedOpenQuotients Γ)
    (hfin : WIBound.{u} d m k B) :
    IsOpen ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) := by
  letI : T2Space Γ := t_space_disconnected Γ
  exact
    power_width_bound
      (Γ := Γ) (d := d) (m := m) (k := k) (B := B)
      s hs
      (detection_compact_disconnected (Γ := Γ))
      hfinite
      hfin
      (fun N => open_discrete_topology N)
      (fun N => open_normal_finite N)
      (fun N => open_normal_continuous N)
/-- In compact totally disconnected topological groups, finite width/index bounds alone imply
power-subgroup openness; the bounded-open-normal quotient bridge is now proved above. -/
theorem
    totally_disconnected_auto
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d m k B : ℕ}
    (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure
            (Subgroup.closure (Set.range s)) = ⊤)
    (hfin : WIBound.{u} d m k B) :
    IsOpen ((powerSubgroup Γ m : Subgroup Γ) : Set Γ) := by
  exact
    compact_totally_disconnected
      (Γ := Γ) (d := d) (m := m) (k := k) (B := B)
      s hs
      (quotients_totally_disconnected (Γ := Γ))
      hfin
end Towers
