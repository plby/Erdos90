import Mathlib
import Submission.Group.DenseGenerators.ZassenhausCompact


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u
universe v w z

lemma FCCover.factorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : FCCover p Γ n)
    {x : Γ}
    (hx : x ∈ (zassenhausFiltration p Γ n).topologicalClosure) :
    zGFact p Γ n x := by
  have hxprod :
      x ∈ zassenhausProductImage C.pieces := by
    exact C.closure_subset_product hx
  exact
    image_subset_factorization
      (p := p)
      (Γ := Γ)
      (n := n)
      (K := C.pieces)
      C.pieces_generators
      hxprod

lemma FCCover.topologicalClosure_le
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : FCCover p Γ n) :
    (zassenhausFiltration p Γ n).topologicalClosure ≤
      zassenhausFiltration p Γ n := by
  intro x hx
  exact
    image_subset_filtration
      (p := p)
      (Γ := Γ)
      (n := n)
      (K := C.pieces)
      C.pieces_generators
      (C.closure_subset_product hx)

lemma FCCover.isClosed
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (C : FCCover p Γ n) :
    IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) := by
  exact
    closed_topological_closure
      (Γ := Γ)
      (zassenhausFiltration p Γ n)
      C.topologicalClosure_le

lemma filtration_closed_factorization
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {n : ℕ}
    (hfactor :
      ∀ x : Γ,
        x ∈ (zassenhausFiltration p Γ n).topologicalClosure →
          zGFact p Γ n x) :
    IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) := by
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  have hle : D.topologicalClosure ≤ D := by
    dsimp [D]
    exact
      filtration_topological_factorization
        (p := p)
        (n := n)
        hfactor
  exact
    closed_topological_closure
      (Γ := Γ)
      D
      hle

lemma dense_self_range
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {n : ℕ} :
    DenseRange
      (fun g : Γ =>
        denseGeneratorsSelf p Γ n g) := by
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  have hsurj :
      Function.Surjective
        (fun g : Γ =>
          denseGeneratorsSelf p Γ n g) := by
    letI : D.Normal := by
      dsimp [D]
      exact zassenhausFiltration_normal p Γ n
    dsimp [denseGeneratorsSelf, denseSelfQuotient, D]
    exact QuotientGroup.mk'_surjective (zassenhausFiltration p Γ n)
  exact hsurj.denseRange

lemma dense_self_quotient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} :
    closure
        (((Subgroup.closure
          (Set.range
            (fun i : Fin d =>
              denseGeneratorsSelf p Γ n (s i)))) :
            Subgroup (denseSelfQuotient p Γ n)) :
          Set (denseSelfQuotient p Γ n)) =
      Set.univ := by
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  let q : Γ →* denseSelfQuotient p Γ n :=
    denseGeneratorsSelf p Γ n
  let H : Subgroup Γ := Subgroup.closure (Set.range s)
  let K : Subgroup (denseSelfQuotient p Γ n) :=
    Subgroup.closure (Set.range fun i : Fin d => q (s i))
  letI : D.Normal := by
    dsimp [D]
    exact zassenhausFiltration_normal p Γ n
  letI : (zassenhausFiltration p Γ n).Normal :=
    zassenhausFiltration_normal p Γ n
  have hq_cont : Continuous (fun g : Γ => q g) := by
    change Continuous (fun g : Γ => (QuotientGroup.mk' D) g)
    change Continuous (QuotientGroup.mk : Γ → Γ ⧸ D)
    exact QuotientGroup.continuous_mk
  have hq_dense : DenseRange (fun g : Γ => q g) := by
    dsimp [q]
    exact dense_self_range
      (p := p) (Γ := Γ) (n := n)
  have hH_closure :
      closure ((H : Subgroup Γ) : Set Γ) = Set.univ := by
    simpa [H, Subgroup.topologicalClosure_coe] using
      congrArg (fun L : Subgroup Γ => (L : Set Γ)) hs
  have hH_dense : Dense ((H : Subgroup Γ) : Set Γ) := by
    rw [dense_iff_closure_eq]
    exact hH_closure
  have hqH_dense :
      Dense (q '' ((H : Subgroup Γ) : Set Γ)) :=
    hq_dense.dense_image hq_cont hH_dense
  have himage_subset :
      q '' ((H : Subgroup Γ) : Set Γ) ⊆
        (K : Set (denseSelfQuotient p Γ n)) := by
    rintro y ⟨x, hx, rfl⟩
    change q x ∈ K
    change x ∈ H at hx
    dsimp [H] at hx
    refine Subgroup.closure_induction (k := Set.range s) ?mem ?one ?mul ?inv hx
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨i, rfl⟩
    · simpa only [map_one] using K.one_mem
    · intro x y _hx _hy hxK hyK
      simpa using K.mul_mem hxK hyK
    · intro x _hx hxK
      simpa using K.inv_mem hxK
  simpa [K, q] using (hqH_dense.mono himage_subset).closure_eq

lemma finite_dense_subgroup
    {Ω : Type u} [Group Ω] [TopologicalSpace Ω] [T2Space Ω]
    (H : Subgroup Ω)
    [Finite H]
    (hH_dense : closure ((H : Set Ω)) = Set.univ) :
    Finite Ω := by
  have hH_finite_set : (H : Set Ω).Finite :=
    Set.finite_coe_iff.mp (inferInstance : Finite H)
  have hH_closed : IsClosed (H : Set Ω) :=
    hH_finite_set.isClosed
  have hH_univ : (H : Set Ω) = Set.univ := by
    rw [← hH_closed.closure_eq]
    exact hH_dense
  have hsurj : Function.Surjective ((↑) : H → Ω) := by
    intro x
    have hx : x ∈ H := by
      change x ∈ (H : Set Ω)
      rw [hH_univ]
      exact Set.mem_univ x
    exact ⟨⟨x, hx⟩, rfl⟩
  exact Finite.of_surjective ((↑) : H → Ω) hsurj

lemma filtration_bot_ambient
    {p : ℕ}
    {Ω : Type u} [Group Ω]
    (H : Subgroup Ω)
    {n : ℕ}
    (htrivial : zassenhausFiltration p Ω n = ⊥) :
    zassenhausFiltration p H n = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  apply Subtype.ext
  have hx_ambient :
      H.subtype x ∈ zassenhausFiltration p Ω n :=
    filtration_map_mem
      (p := p)
      (n := n)
      (f := H.subtype)
      hx
  have hx_bot : H.subtype x ∈ (⊥ : Subgroup Ω) := by
    simpa [htrivial] using hx_ambient
  simpa using hx_bot

lemma subtype_generators_top
    {Ω : Type u} [Group Ω]
    {d : ℕ} (t : Fin d → Ω) :
    let H : Subgroup Ω := Subgroup.closure (Set.range t)
    let tH : Fin d → H := fun i => ⟨t i, Subgroup.subset_closure ⟨i, rfl⟩⟩
    Subgroup.closure (Set.range tH) = ⊤ := by
  intro H tH
  refine le_antisymm le_top ?_
  intro x _hx
  have hxH : (x : Ω) ∈ H :=
    x.property
  change x ∈ Subgroup.closure (Set.range tH)
  dsimp [H] at hxH
  refine
    Subgroup.closure_induction
      (k := Set.range t)
      (p :=
        fun y _ =>
          ∀ hy : y ∈ H,
            (⟨y, hy⟩ : H) ∈ Subgroup.closure (Set.range tH))
      ?mem ?one ?mul ?inv hxH x.property
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    intro hyH
    exact Subgroup.subset_closure ⟨i, Subtype.ext rfl⟩
  · intro h1
    have hone : (1 : H) ∈ Subgroup.closure (Set.range tH) :=
      (Subgroup.closure (Set.range tH)).one_mem
    have hsubtype_one : (⟨1, h1⟩ : H) = 1 :=
      Subtype.ext rfl
    rw [hsubtype_one]
    exact hone
  · intro x y hx hy hx_closure hy_closure hxy
    have hxH' : x ∈ H := by
      simpa [H] using hx
    have hyH' : y ∈ H := by
      simpa [H] using hy
    have hx_sub : (⟨x, hxH'⟩ : H) ∈ Subgroup.closure (Set.range tH) :=
      hx_closure hxH'
    have hy_sub : (⟨y, hyH'⟩ : H) ∈ Subgroup.closure (Set.range tH) :=
      hy_closure hyH'
    have hmul :
        (⟨x, hxH'⟩ : H) * (⟨y, hyH'⟩ : H) =
          (⟨x * y, hxy⟩ : H) := by
      rfl
    simpa [hmul] using
      (Subgroup.closure (Set.range tH)).mul_mem hx_sub hy_sub
  · intro x hx hx_closure hx_inv
    have hxH' : x ∈ H := by
      simpa [H] using hx
    have hx_sub : (⟨x, hxH'⟩ : H) ∈ Subgroup.closure (Set.range tH) :=
      hx_closure hxH'
    have hinv :
        ((⟨x, hxH'⟩ : H)⁻¹) =
          (⟨x⁻¹, hx_inv⟩ : H) := by
      rfl
    simpa [hinv] using
      (Subgroup.closure (Set.range tH)).inv_mem hx_sub

lemma lower_filtration_one
    {p : ℕ}
    {G : Type u} [Group G]
    {n : ℕ}
    (hn : 1 < n) :
    Subgroup.lowerCentralSeries G (n - 1) ≤ zassenhausFiltration p G n := by
  intro x hx
  rw [zassenhausFiltration]
  refine Subgroup.subset_closure ?_
  refine ⟨n - 1, 0, x, hx, ?_, ?_⟩
  · have hn_one_le : 1 ≤ n :=
      Nat.le_of_lt hn
    rw [pow_zero, mul_one, Nat.sub_add_cancel hn_one_le]
  · simp

lemma lower_bot_trivial
    {p : ℕ}
    {G : Type u} [Group G]
    {n : ℕ}
    (hn : 1 < n)
    (htrivial : zassenhausFiltration p G n = ⊥) :
    Subgroup.lowerCentralSeries G (n - 1) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxD : x ∈ zassenhausFiltration p G n :=
    lower_filtration_one
      (p := p)
      (G := G)
      hn
      hx
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    simpa [htrivial] using hxD
  simpa using hxbot

lemma pow_zassenhaus_filtration
    {p : ℕ}
    {G : Type u} [Group G]
    {n j : ℕ}
    (hbound : n ≤ p ^ j)
    (x : G) :
    x ^ (p ^ j) ∈ zassenhausFiltration p G n := by
  rw [zassenhausFiltration]
  refine Subgroup.subset_closure ?_
  refine ⟨0, j, x, ?_, ?_, rfl⟩
  · rw [Subgroup.lowerCentralSeries_zero]
    exact Subgroup.mem_top x
  · simpa using hbound

lemma pow_trivial_zassenhaus
    {p : ℕ}
    {G : Type u} [Group G]
    {n j : ℕ}
    (htrivial : zassenhausFiltration p G n = ⊥)
    (hbound : n ≤ p ^ j)
    (x : G) :
    x ^ (p ^ j) = 1 := by
  have hxD : x ^ (p ^ j) ∈ zassenhausFiltration p G n :=
    pow_zassenhaus_filtration
      (p := p)
      (G := G)
      (n := n)
      (j := j)
      hbound
      x
  have hxbot : x ^ (p ^ j) ∈ (⊥ : Subgroup G) := by
    simpa [htrivial] using hxD
  simpa using hxbot

lemma prime_power
    (p : ℕ) [Fact p.Prime]
    (n : ℕ) :
    ∃ j : ℕ, n ≤ p ^ j := by
  exact ⟨Nat.clog p n, Nat.le_pow_clog (Fact.out : p.Prime).one_lt n⟩

lemma uniform_exponent_trivial
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    {n : ℕ}
    (htrivial : zassenhausFiltration p G n = ⊥) :
    ∃ e : ℕ, 0 < e ∧ ∀ x : G, x ^ e = 1 := by
  rcases prime_power p n with ⟨j, hbound⟩
  refine ⟨p ^ j, ?_, ?_⟩
  · exact pow_pos (Fact.out : p.Prime).pos j
  · intro x
    exact
      pow_trivial_zassenhaus
        (p := p)
        (G := G)
        (n := n)
        (j := j)
        htrivial
        hbound
        x

lemma fg_range_top
    {Λ : Type u} [Group Λ]
    {d : ℕ} (t : Fin d → Λ)
    (hgen : Subgroup.closure (Set.range t) = ⊤) :
    Group.FG Λ := by
  rw [Group.fg_iff]
  refine ⟨Set.range t, ?_, ?_⟩
  · exact hgen
  · exact Set.finite_range t

lemma nilpotent_series_bot
    {Λ : Type u} [Group Λ]
    {c : ℕ}
    (hnil : Subgroup.lowerCentralSeries Λ c = ⊥) :
    Group.IsNilpotent Λ := by
  rw [Subgroup.nilpotent_iff_lowerCentralSeries]
  refine ⟨c, ?_⟩
  exact hnil

lemma torsion_uniform_exponent
    {Λ : Type u} [Monoid Λ]
    {e : ℕ}
    (hepos : 0 < e)
    (hexp : ∀ x : Λ, x ^ e = 1) :
    Monoid.IsTorsion Λ := by
  intro x
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨e, ?_, ?_⟩
  · exact hepos
  · exact hexp x

lemma quotient_torsion
    {Λ : Type u} [Group Λ]
    (N : Subgroup Λ) [N.Normal]
    (htorsion : Monoid.IsTorsion Λ) :
    Monoid.IsTorsion (Λ ⧸ N) := by
  exact
    IsTorsion.of_surjective
      (f := QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)
      htorsion

lemma subgroup_torsion
    {Λ : Type u} [Group Λ]
    (H : Subgroup Λ)
    (htorsion : Monoid.IsTorsion Λ) :
    Monoid.IsTorsion H := by
  exact IsTorsion.subgroup htorsion H

lemma comm_fg_uniform
    {A : Type u} [CommGroup A] [Group.FG A]
    {e : ℕ}
    (hepos : 0 < e)
    (hexp : ∀ x : A, x ^ e = 1) :
    Finite A := by
  have htor : Monoid.IsTorsion A :=
    torsion_uniform_exponent
      (Λ := A)
      hepos
      hexp
  exact CommGroup.finite_of_fg_torsion A htor

lemma center_subgroup_comm
    {Λ : Type u} [Group Λ]
    (x y : Subgroup.center Λ) :
    x * y = y * x := by
  ext
  exact (Subgroup.mem_center_iff.mp x.property y).symm

lemma center_fg_torsion
    {Λ : Type u} [Group Λ]
    [Group.FG (Subgroup.center Λ)]
    (htorsion : Monoid.IsTorsion Λ) :
    Finite (Subgroup.center Λ) := by
  letI : CommGroup (Subgroup.center Λ) :=
    { (inferInstance : Group (Subgroup.center Λ)) with
      mul_comm := center_subgroup_comm }
  have hcenter_torsion : Monoid.IsTorsion (Subgroup.center Λ) :=
    subgroup_torsion
      (Subgroup.center Λ)
      htorsion
  exact
    CommGroup.finite_of_fg_torsion
      (Subgroup.center Λ)
      hcenter_torsion

lemma finite_center_quotient
    {Λ : Type u} [Group Λ]
    (hcenter : Finite (Subgroup.center Λ))
    (hquot : Finite (Λ ⧸ Subgroup.center Λ)) :
    Finite Λ := by
  haveI : Finite (Subgroup.center Λ) := hcenter
  haveI : Finite (Λ ⧸ Subgroup.center Λ) := hquot
  exact Finite.of_subgroup_quotient (Subgroup.center Λ)

lemma center_quotient_fg
    {Λ : Type u} [Group Λ]
    [Group.FG Λ] :
    Group.FG (Λ ⧸ Subgroup.center Λ) := by
  infer_instance

lemma center_quotient_torsion
    {Λ : Type u} [Group Λ]
    (htorsion : Monoid.IsTorsion Λ) :
    Monoid.IsTorsion (Λ ⧸ Subgroup.center Λ) := by
  exact
    quotient_torsion
      (Subgroup.center Λ)
      htorsion

lemma center_fg_quotient
    {Λ : Type u} [Group Λ] [Group.FG Λ]
    (hquot : Finite (Λ ⧸ Subgroup.center Λ)) :
    Group.FG (Subgroup.center Λ) := by
  haveI : Finite (Λ ⧸ Subgroup.center Λ) := hquot
  haveI : (Subgroup.center Λ).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  exact inferInstance

lemma nilpotent_fg_center
    {Λ : Type u} [Group Λ] [Group.FG Λ] [Group.IsNilpotent Λ]
    (htorsion : Monoid.IsTorsion Λ)
    (hquot : Finite (Λ ⧸ Subgroup.center Λ)) :
    Finite Λ := by
  haveI : Group.FG (Subgroup.center Λ) :=
    center_fg_quotient
      (Λ := Λ)
      hquot
  have hcenter : Finite (Subgroup.center Λ) :=
    center_fg_torsion
      (Λ := Λ)
      htorsion
  exact
    finite_center_quotient
      (Λ := Λ)
      hcenter
      hquot

lemma nilpotent_fg_torsion
    {Λ : Type u} [Group Λ] [Group.FG Λ] [Group.IsNilpotent Λ]
    (htorsion : Monoid.IsTorsion Λ) :
    Finite Λ := by
  refine
    (Group.nilpotent_center_quotient_ind
      (P := fun G _ _ => Group.FG G → Monoid.IsTorsion G → Finite G)
      Λ
      ?_
      ?_)
      inferInstance
      htorsion
  · intro G _ _hsub _hfg _htorsion
    infer_instance
  · intro G _ _hnil ih hfg ht
    haveI : Group.FG G := hfg
    have hquot_torsion : Monoid.IsTorsion (G ⧸ Subgroup.center G) :=
      center_quotient_torsion
        (Λ := G)
        ht
    have hquot_fg : Group.FG (G ⧸ Subgroup.center G) :=
      center_quotient_fg
        (Λ := G)
    have hquot_finite : Finite (G ⧸ Subgroup.center G) :=
      ih
        hquot_fg
        hquot_torsion
    exact
      nilpotent_fg_center
        (Λ := G)
        ht
        hquot_finite

lemma fg_nilpotent_uniform
    {Λ : Type u} [Group Λ]
    {d : ℕ} (t : Fin d → Λ)
    {c e : ℕ}
    (hgen : Subgroup.closure (Set.range t) = ⊤)
    (hnil : Subgroup.lowerCentralSeries Λ c = ⊥)
    (hepos : 0 < e)
    (hexp : ∀ x : Λ, x ^ e = 1) :
    Finite Λ := by
  haveI : Group.FG Λ :=
    fg_range_top
      (Λ := Λ)
      t
      hgen
  haveI : Group.IsNilpotent Λ :=
    nilpotent_series_bot
      (Λ := Λ)
      hnil
  have htorsion : Monoid.IsTorsion Λ :=
    torsion_uniform_exponent
      (Λ := Λ)
      hepos
      hexp
  exact nilpotent_fg_torsion (Λ := Λ) htorsion

lemma fg_trivial_burnside
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [Group Λ]
    {d : ℕ} (t : Fin d → Λ)
    {n : ℕ}
    (hn : 1 < n)
    (hgen : Subgroup.closure (Set.range t) = ⊤)
    (htrivial : zassenhausFiltration p Λ n = ⊥) :
    Finite Λ := by
  have hnil : Subgroup.lowerCentralSeries Λ (n - 1) = ⊥ :=
    lower_bot_trivial
      (p := p)
      (G := Λ)
      hn
      htrivial
  rcases uniform_exponent_trivial
      (p := p)
      (G := Λ)
      htrivial with
    ⟨e, hepos, hexp⟩
  exact
    fg_nilpotent_uniform
      (Λ := Λ)
      t
      hgen
      hnil
      hepos
      hexp

lemma trivial_restricted_burnside
    {p : ℕ} [Fact p.Prime]
    {Ω : Type u} [Group Ω]
    {d : ℕ} (t : Fin d → Ω)
    {n : ℕ}
    (hn : 1 < n)
    (htrivial : zassenhausFiltration p Ω n = ⊥) :
    Finite (Subgroup.closure (Set.range t) : Subgroup Ω) := by
  let H : Subgroup Ω := Subgroup.closure (Set.range t)
  let tH : Fin d → H :=
    fun i => ⟨t i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hgenH : Subgroup.closure (Set.range tH) = ⊤ := by
    dsimp [tH, H]
    exact subtype_generators_top t
  have htrivialH : zassenhausFiltration p H n = ⊥ :=
    filtration_bot_ambient
      (p := p)
      (H := H)
      htrivial
  exact
    fg_trivial_burnside
      (p := p)
      (Λ := H)
      tH
      hn
      hgenH
      htrivialH

lemma compact_t_trivial
    {p : ℕ} [Fact p.Prime]
    {Ω : Type u} [Group Ω] [TopologicalSpace Ω] [IsTopologicalGroup Ω]
    [CompactSpace Ω] [T2Space Ω]
    {d : ℕ} (t : Fin d → Ω)
    (ht :
      closure (((Subgroup.closure (Set.range t)) : Subgroup Ω) : Set Ω) =
        Set.univ)
    {n : ℕ}
    (hn : 1 < n)
    (htrivial : zassenhausFiltration p Ω n = ⊥) :
    Finite Ω := by
  let H : Subgroup Ω := Subgroup.closure (Set.range t)
  haveI : Finite H :=
    trivial_restricted_burnside
      (p := p)
      (t := t)
      hn
      htrivial
  exact finite_dense_subgroup H ht

lemma dense_self_one
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ}
    (hclosed : IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ))
    (hn : 1 < n) :
    Finite (denseSelfQuotient p Γ n) := by
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  let Ω : Type u := denseSelfQuotient p Γ n
  let t : Fin d → Ω :=
    fun i => denseGeneratorsSelf p Γ n (s i)
  letI : D.Normal := by
    dsimp [D]
    exact zassenhausFiltration_normal p Γ n
  letI : (zassenhausFiltration p Γ n).Normal :=
    zassenhausFiltration_normal p Γ n
  haveI : IsClosed (D : Set Γ) := by
    simpa [D] using hclosed
  haveI : IsClosed ((zassenhausFiltration p Γ n : Subgroup Γ) : Set Γ) :=
    hclosed
  haveI : IsTopologicalGroup Ω := by
    dsimp [Ω, denseSelfQuotient]
    exact QuotientGroup.instIsTopologicalGroup
      (N := zassenhausFiltration p Γ n)
  haveI : T2Space Ω := by
    dsimp [Ω, denseSelfQuotient]
    infer_instance
  have ht_dense :
      closure (((Subgroup.closure (Set.range t)) : Subgroup Ω) : Set Ω) =
        Set.univ := by
    dsimp [t, Ω]
    exact dense_self_quotient
      (p := p) (Γ := Γ) s hs (n := n)
  have htrivial : zassenhausFiltration p Ω n = ⊥ := by
    dsimp [Ω]
    simpa [denseSelfQuotient, zassenhausSelfQuotient] using
      filtration_self_bot p Γ n
  change Finite Ω
  exact
    compact_t_trivial
      (p := p) (Ω := Ω) t ht_dense hn htrivial

lemma dense_self_data
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ]
    {n : ℕ} :
    Nonempty (DenseSelfData p Γ n) := by
  refine ⟨{ target_eq_bot := ?_ }⟩
  letI : (zassenhausFiltration p Γ n).Normal :=
    zassenhausFiltration_normal p Γ n
  have hself :
      zassenhausFiltration p (zassenhausSelfQuotient p Γ n) n = ⊥ :=
    filtration_self_bot p Γ n
  change
    zassenhausFiltration p
      (denseSelfQuotient p Γ n) n = ⊥
  simpa [denseSelfQuotient, zassenhausSelfQuotient] using hself

namespace STData

lemma self_test_data
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ]
    {n : ℕ}
    (Htop : STData p Γ n)
    (Halg : DenseSelfData p Γ n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ T : DGTest Γ,
      T.quotientMap g ∉
        DGTest.targetZassenhaus T p n := by
  let T : DGTest Γ :=
    Htop.finiteQuotientTest
  letI : Group T.quotientGroup := T.instGroup
  refine ⟨T, ?_⟩
  intro hgT
  let D : Subgroup Γ := zassenhausFiltration p Γ n
  letI : D.Normal := by
    dsimp [D]
    exact zassenhausFiltration_normal p Γ n
  have htarget_bot :
      DGTest.targetZassenhaus T p n = ⊥ := by
    dsimp
      [T,
       STData.finiteQuotientTest,
       DGTest.targetZassenhaus,
       denseSelfTarget]
    exact Halg.target_eq_bot
  have hg_bot :
      T.quotientMap g ∈ (⊥ : Subgroup T.quotientGroup) := by
    simpa [htarget_bot] using hgT
  have hg_eq_one :
      denseGeneratorsSelf p Γ n g = 1 := by
    have hT : T.quotientMap g = (1 : T.quotientGroup) := by
      simpa using hg_bot
    simpa
      [T,
       STData.finiteQuotientTest]
      using hT
  exact
    hg
      ((dense_zassenhaus_self
        (p := p) (Γ := Γ) (n := n) g).mp hg_eq_one)

end STData

end Submission
