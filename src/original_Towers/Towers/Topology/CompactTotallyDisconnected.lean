import Mathlib
import Mathlib


open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u
universe v w z

lemma nhds_compact_t
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {x : X} {V : Set X} (hV : V ∈ nhds x) :
    ∃ C : Set X, IsClosed C ∧ C ∈ nhds x ∧ C ⊆ V := by
  haveI : RegularSpace X := inferInstance
  have hregular :
      ∃ C ∈ nhds x, IsClosed C ∧ C ⊆ V :=
    exists_mem_nhds_isClosed_subset (x := x) hV
  rcases hregular with
    ⟨C, hCnhds, hCclosed, hCsubset⟩
  have hCclosed' : IsClosed C := hCclosed
  have hCnhds' : C ∈ nhds x := hCnhds
  exact ⟨C, hCclosed', hCnhds', hCsubset⟩

lemma clopen_not_separated
    {X : Type u} [TopologicalSpace X] [TotallySeparatedSpace X]
    {x y : X} (hxy : x ≠ y) :
    ∃ U : Set X, IsOpen U ∧ IsClosed U ∧ x ∈ U ∧ y ∉ U := by
  have hsep : IsTotallySeparated (Set.univ : Set X) :=
    TotallySeparatedSpace.isTotallySeparated_univ
  dsimp [IsTotallySeparated, Set.Pairwise] at hsep
  rcases hsep (Set.mem_univ x) (Set.mem_univ y) hxy with
    ⟨U, V, hUopen, hVopen, hxU, hyV, hcover, hdisj⟩
  have hcompl : Uᶜ = V := by
    ext z
    constructor
    · intro hzU
      have hzcover : z ∈ U ∪ V := hcover (Set.mem_univ z)
      rcases hzcover with hzU' | hzV
      · exact False.elim (hzU hzU')
      · exact hzV
    · intro hzV hzU
      exact (Set.disjoint_left.mp hdisj hzU hzV).elim
  have hUclosed : IsClosed U := by
    have hUcomplOpen : IsOpen Uᶜ := by
      simpa [hcompl] using hVopen
    have hclosed_compl : IsClosed (Uᶜ)ᶜ := hUcomplOpen.isClosed_compl
    simpa using hclosed_compl
  have hy_not_U : y ∉ U := by
    intro hyU
    exact (Set.disjoint_left.mp hdisj hyU hyV).elim
  exact ⟨U, hUopen, hUclosed, hxU, hy_not_U⟩

lemma disjoint_cover_clopen
    {X : Type u} [TopologicalSpace X]
    {x y : X} {U : Set X}
    (hUopen : IsOpen U) (hUclosed : IsClosed U) (hxU : x ∈ U) (hyU : y ∉ U) :
    ∃ U₀ V₀ : Set X,
      IsOpen U₀ ∧ IsOpen V₀ ∧ x ∈ U₀ ∧ y ∈ V₀ ∧
        (Set.univ : Set X) ⊆ U₀ ∪ V₀ ∧ Disjoint U₀ V₀ := by
  refine ⟨U, Uᶜ, hUopen, hUclosed.isOpen_compl, hxU, ?_, ?_, ?_⟩
  · exact hyU
  · intro z _hz
    by_cases hzU : z ∈ U
    · exact Or.inl hzU
    · exact Or.inr hzU
  · rw [Set.disjoint_left]
    intro z hzU hzUc
    exact hzUc hzU

lemma separated_univ_clopen
    {X : Type u} [TopologicalSpace X]
    (H :
      ∀ ⦃x y : X⦄, x ≠ y →
        ∃ U : Set X, IsOpen U ∧ IsClosed U ∧ x ∈ U ∧ y ∉ U) :
    IsTotallySeparated (Set.univ : Set X) := by
  dsimp [IsTotallySeparated, Set.Pairwise]
  intro x _hx y _hy hxy
  rcases H hxy with ⟨U, hUopen, hUclosed, hxU, hyU⟩
  exact
    disjoint_cover_clopen
      (X := X) hUopen hUclosed hxU hyU

lemma separated_clopen_separation
    {X : Type u} [TopologicalSpace X]
    (H :
      ∀ ⦃x y : X⦄, x ≠ y →
        ∃ U : Set X, IsOpen U ∧ IsClosed U ∧ x ∈ U ∧ y ∉ U) :
    TotallySeparatedSpace X := by
  exact
    ⟨separated_univ_clopen (X := X) H⟩

lemma clopen_compact_t
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X]
    {x y : X} (hxy : x ≠ y) :
    ∃ U : Set X, IsOpen U ∧ IsClosed U ∧ x ∈ U ∧ y ∉ U := by
  haveI : TotallySeparatedSpace X := by
    infer_instance
  exact clopen_not_separated (X := X) hxy

lemma disjoint_t_disconnected
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X]
    {x y : X} (hxy : x ≠ y) :
    ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧
        (Set.univ : Set X) ⊆ U ∪ V ∧ Disjoint U V := by
  rcases
      clopen_compact_t
        (X := X) hxy with
    ⟨U, hUopen, hUclosed, hxU, hyU⟩
  exact
    disjoint_cover_clopen
      (X := X) hUopen hUclosed hxU hyU

lemma totally_separated_disconnected
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] :
    TotallySeparatedSpace X := by
  refine ⟨?_⟩
  dsimp [IsTotallySeparated, Set.Pairwise]
  intro x _hx y _hy hxy
  exact
    disjoint_t_disconnected
      (X := X) hxy

lemma clopen_totally_separated
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallySeparatedSpace X]
    {x : X} {O : Set X} (hOopen : IsOpen O) (hxO : x ∈ O) :
    ∃ W : Set X, IsOpen W ∧ IsClosed W ∧ x ∈ W ∧ W ⊆ O := by
  classical
  have hsep :
      ∀ y : X, y ∉ O →
        ∃ U : Set X, IsOpen U ∧ IsClosed U ∧ x ∈ U ∧ y ∉ U := by
    intro y hyO
    have hxy : x ≠ y := by
      intro hxy
      subst y
      exact hyO hxO
    exact clopen_not_separated (X := X) hxy
  let A : X → Set X :=
    fun y =>
      if hy : y ∉ O then
        Classical.choose (hsep y hy)
      else
        Set.univ
  have hAopen : ∀ y : X, y ∈ Oᶜ → IsOpen (A y) := by
    intro y hy
    have hyO : y ∉ O := by simpa using hy
    have hspec := Classical.choose_spec (hsep y hyO)
    simpa [A, hyO] using hspec.1
  have hAclosed : ∀ y : X, y ∈ Oᶜ → IsClosed (A y) := by
    intro y hy
    have hyO : y ∉ O := by simpa using hy
    have hspec := Classical.choose_spec (hsep y hyO)
    simpa [A, hyO] using hspec.2.1
  have hxA : ∀ y : X, y ∈ Oᶜ → x ∈ A y := by
    intro y hy
    have hyO : y ∉ O := by simpa using hy
    have hspec := Classical.choose_spec (hsep y hyO)
    simpa [A, hyO] using hspec.2.2.1
  have hyNotA : ∀ y : X, y ∈ Oᶜ → y ∉ A y := by
    intro y hy
    have hyO : y ∉ O := by simpa using hy
    have hspec := Classical.choose_spec (hsep y hyO)
    simpa [A, hyO] using hspec.2.2.2
  have hcompact : IsCompact Oᶜ := hOopen.isClosed_compl.isCompact
  have hnhds :
      ∀ y ∈ Oᶜ, (A y)ᶜ ∈ nhds y := by
    intro y hy
    have hopen_compl : IsOpen (A y)ᶜ := (hAclosed y hy).isOpen_compl
    have hy_compl : y ∈ (A y)ᶜ := hyNotA y hy
    exact hopen_compl.mem_nhds hy_compl
  rcases hcompact.elim_nhds_subcover (fun y => (A y)ᶜ) hnhds with
    ⟨t, ht_sub, hcover⟩
  let W : Set X := t.inf A
  have hOpenInf :
      ∀ s : Finset X, (∀ y : X, y ∈ s → y ∈ Oᶜ) → IsOpen (s.inf A) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _hsub
      simp
    · intro a s ha ih hsub
      have haO : a ∈ Oᶜ := hsub a (by simp)
      have hsO : ∀ y : X, y ∈ s → y ∈ Oᶜ := by
        intro y hy
        exact hsub y (by simp [hy])
      have hInter : IsOpen (A a ∩ s.inf A) :=
        (hAopen a haO).inter (ih hsO)
      simpa [Finset.inf_insert] using hInter
  have hClosedInf :
      ∀ s : Finset X, (∀ y : X, y ∈ s → y ∈ Oᶜ) → IsClosed (s.inf A) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _hsub
      simp
    · intro a s ha ih hsub
      have haO : a ∈ Oᶜ := hsub a (by simp)
      have hsO : ∀ y : X, y ∈ s → y ∈ Oᶜ := by
        intro y hy
        exact hsub y (by simp [hy])
      have hInter : IsClosed (A a ∩ s.inf A) :=
        (hAclosed a haO).inter (ih hsO)
      simpa [Finset.inf_insert] using hInter
  have hxInf :
      ∀ s : Finset X, (∀ y : X, y ∈ s → y ∈ Oᶜ) → x ∈ s.inf A := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _hsub
      simp
    · intro a s ha ih hsub
      have haO : a ∈ Oᶜ := hsub a (by simp)
      have hsO : ∀ y : X, y ∈ s → y ∈ Oᶜ := by
        intro y hy
        exact hsub y (by simp [hy])
      have hxInter : x ∈ A a ∩ s.inf A :=
        ⟨hxA a haO, ih hsO⟩
      simpa [Finset.inf_insert] using hxInter
  have hMemInf :
      ∀ s : Finset X, ∀ z : X, z ∈ s.inf A →
        ∀ y : X, y ∈ s → z ∈ A y := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro z _hz y hy
      simp at hy
    · intro a s ha ih z hz y hy
      have hzInter : z ∈ A a ∩ s.inf A := by
        simpa [Finset.inf_insert] using hz
      rcases Finset.mem_insert.mp hy with rfl | hys
      · exact hzInter.1
      · exact ih z hzInter.2 y hys
  have hWopen : IsOpen W := by
    simpa [W] using hOpenInf t ht_sub
  have hWclosed : IsClosed W := by
    simpa [W] using hClosedInf t ht_sub
  have hxW : x ∈ W := by
    simpa [W] using hxInf t ht_sub
  have hWsubsetO : W ⊆ O := by
    intro z hzW
    by_contra hzO
    have hzOc : z ∈ Oᶜ := hzO
    have hzcover : z ∈ ⋃ y ∈ t, (A y)ᶜ := hcover hzOc
    rcases Set.mem_iUnion.mp hzcover with ⟨y, hycover⟩
    rcases Set.mem_iUnion.mp hycover with ⟨hyt, hznotA⟩
    have hzInf : z ∈ t.inf A := by
      simpa [W] using hzW
    have hzA : z ∈ A y := hMemInf t z hzInf y hyt
    exact hznotA hzA
  exact ⟨W, hWopen, hWclosed, hxW, hWsubsetO⟩

lemma clopen_nhds_separated
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallySeparatedSpace X]
    {x : X} {V : Set X} (hV : V ∈ nhds x) :
    ∃ W : Set X, IsOpen W ∧ IsClosed W ∧ W ∈ nhds x ∧ W ⊆ V := by
  rcases mem_nhds_iff.mp hV with
    ⟨O, hOsubsetV, hOopen, hxO⟩
  rcases
      clopen_totally_separated
        (x := x) hOopen hxO with
    ⟨W, hWopen, hWclosed, hxW, hWsubsetO⟩
  have hWnhds : W ∈ nhds x := hWopen.mem_nhds hxW
  have hWsubsetV : W ⊆ V := by
    intro y hy
    exact hOsubsetV (hWsubsetO hy)
  exact ⟨W, hWopen, hWclosed, hWnhds, hWsubsetV⟩

lemma clopen_separated_compact
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallySeparatedSpace X]
    {x : X} {C : Set X} (_hCclosed : IsClosed C) (hC : C ∈ nhds x) :
    ∃ W : Set X, IsOpen W ∧ IsClosed W ∧ W ∈ nhds x ∧ W ⊆ C := by
  exact
    clopen_nhds_separated
      (x := x) hC

lemma clopen_t_disconnected
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X]
    {x : X} {C : Set X} (hCclosed : IsClosed C) (hC : C ∈ nhds x) :
    ∃ W : Set X, IsOpen W ∧ IsClosed W ∧ W ∈ nhds x ∧ W ⊆ C := by
  haveI : TotallySeparatedSpace X :=
    totally_separated_disconnected (X := X)
  exact
    clopen_separated_compact
      (x := x) hCclosed hC

lemma clopen_compact_disconnected
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X]
    {x : X} {V : Set X} (hV : V ∈ nhds x) :
    ∃ W : Set X, IsOpen W ∧ IsClosed W ∧ W ∈ nhds x ∧ W ⊆ V := by
  rcases
      nhds_compact_t
        (x := x) hV with
    ⟨C, hCclosed, hCnhds, hCsubsetV⟩
  rcases
      clopen_t_disconnected
        (x := x) hCclosed hCnhds with
    ⟨W, hWopen, hWclosed, hWnhds, hWsubsetC⟩
  have hWsubsetV : W ⊆ V := by
    intro y hy
    exact hCsubsetV (hWsubsetC hy)
  exact ⟨W, hWopen, hWclosed, hWnhds, hWsubsetV⟩

lemma clopen_nhds_disconnected
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X]
    {x : X} {O : Set X} (hOopen : IsOpen O) (hxO : x ∈ O) :
    ∃ W : Set X, IsOpen W ∧ IsClosed W ∧ W ∈ nhds x ∧ W ⊆ O := by
  have hO : O ∈ nhds x := by
    exact hOopen.mem_nhds hxO
  exact
    clopen_compact_disconnected
      (x := x) hO

lemma clopen_nhds_t
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X]
    {x : X} {V : Set X} (hV : V ∈ nhds x) :
    ∃ W : Set X, IsOpen W ∧ IsClosed W ∧ x ∈ W ∧ W ⊆ V := by
  rcases
      clopen_compact_disconnected
        (x := x) hV with
    ⟨W, hWopen, hWclosed, hWnhds, hWsubsetV⟩
  have hxW : x ∈ W := by
    exact mem_of_mem_nhds hWnhds
  exact ⟨W, hWopen, hWclosed, hxW, hWsubsetV⟩

lemma clopen_subset_disconnected
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X]
    {x : X} {O : Set X} (hOopen : IsOpen O) (hxO : x ∈ O) :
    ∃ W : Set X, IsOpen W ∧ IsClosed W ∧ x ∈ W ∧ W ⊆ O := by
  rcases
      clopen_nhds_disconnected
        (x := x) hOopen hxO with
    ⟨W, hWopen, hWclosed, hWnhds, hWsubsetO⟩
  have hxW : x ∈ W := by
    exact mem_of_mem_nhds hWnhds
  exact ⟨W, hWopen, hWclosed, hxW, hWsubsetO⟩

lemma nhds_translate_compact
    {G : Type u} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {K O : Set G} (hK : IsCompact K) (hOopen : IsOpen O) (hKO : K ⊆ O) :
    ∃ N : Set G, N ∈ nhds (0 : G) ∧
      ∀ n : G, n ∈ N → ∀ k : G, k ∈ K → n + k ∈ O := by
  classical
  have hlocal :
      ∀ k : G, k ∈ K →
        ∃ NV : Set G × Set G,
          NV.1 ∈ nhds (0 : G) ∧ NV.2 ∈ nhds k ∧
            ∀ n : G, n ∈ NV.1 → ∀ z : G, z ∈ NV.2 → n + z ∈ O := by
    intro k hk
    have hOk : O ∈ nhds k := hOopen.mem_nhds (hKO hk)
    have hcont :
        ContinuousAt (fun p : G × G => p.1 + p.2) ((0 : G), k) :=
      continuous_add.continuousAt
    have hpre :
        {p : G × G | p.1 + p.2 ∈ O} ∈ nhds ((0 : G), k) := by
      have htarget : O ∈ nhds ((0 : G) + k) := by
        simpa using hOk
      exact hcont htarget
    rcases mem_nhds_prod_iff.mp hpre with ⟨N, hN, V, hV, hNV⟩
    refine ⟨(N, V), hN, hV, ?_⟩
    intro n hn z hz
    exact hNV (a := (n, z)) ⟨hn, hz⟩
  let Nloc : G → Set G :=
    fun k => if hk : k ∈ K then (Classical.choose (hlocal k hk)).1 else Set.univ
  let Vloc : G → Set G :=
    fun k => if hk : k ∈ K then (Classical.choose (hlocal k hk)).2 else Set.univ
  have hNloc : ∀ k : G, k ∈ K → Nloc k ∈ nhds (0 : G) := by
    intro k hk
    have hspec := Classical.choose_spec (hlocal k hk)
    simpa [Nloc, hk] using hspec.1
  have hVloc : ∀ k : G, k ∈ K → Vloc k ∈ nhds k := by
    intro k hk
    have hspec := Classical.choose_spec (hlocal k hk)
    simpa [Vloc, hk] using hspec.2.1
  have hNVloc :
      ∀ k : G, ∀ hk : k ∈ K,
        ∀ n : G, n ∈ Nloc k → ∀ z : G, z ∈ Vloc k → n + z ∈ O := by
    intro k hk n hn z hz
    have hspec := Classical.choose_spec (hlocal k hk)
    have hn' : n ∈ (Classical.choose (hlocal k hk)).1 := by
      simpa [Nloc, hk] using hn
    have hz' : z ∈ (Classical.choose (hlocal k hk)).2 := by
      simpa [Vloc, hk] using hz
    exact hspec.2.2 n hn' z hz'
  rcases hK.elim_nhds_subcover Vloc hVloc with
    ⟨t, ht_sub, hcover⟩
  have hInfMem :
      ∀ s : Finset G, (∀ y : G, y ∈ s → y ∈ K) →
        s.inf Nloc ∈ nhds (0 : G) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _hsub
      simp
    · intro a s ha ih hsub
      have haK : a ∈ K := hsub a (by simp)
      have hsK : ∀ y : G, y ∈ s → y ∈ K := by
        intro y hy
        exact hsub y (by simp [hy])
      have hInter : Nloc a ∩ s.inf Nloc ∈ nhds (0 : G) :=
        Filter.inter_mem (hNloc a haK) (ih hsK)
      simpa [Finset.inf_insert] using hInter
  have hMemInf :
      ∀ s : Finset G, ∀ n : G, n ∈ s.inf Nloc →
        ∀ y : G, y ∈ s → n ∈ Nloc y := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro n _hn y hy
      simp at hy
    · intro a s ha ih n hn y hy
      have hnInter : n ∈ Nloc a ∩ s.inf Nloc := by
        simpa [Finset.inf_insert] using hn
      rcases Finset.mem_insert.mp hy with rfl | hys
      · exact hnInter.1
      · exact ih n hnInter.2 y hys
  refine ⟨t.inf Nloc, hInfMem t ht_sub, ?_⟩
  intro n hn k hk
  have hkcover : k ∈ ⋃ y ∈ t, Vloc y := hcover hk
  rcases Set.mem_iUnion.mp hkcover with ⟨y, hycover⟩
  rcases Set.mem_iUnion.mp hycover with ⟨hyt, hkVy⟩
  have hyK : y ∈ K := ht_sub y hyt
  have hnNy : n ∈ Nloc y := hMemInf t n hn y hyt
  exact hNVloc y hyK n hnNy k hkVy

def clopenTranslateStabilizer
    (G : Type u) [AddGroup G] (W : Set G) : AddSubgroup G where
  carrier := {g : G | ∀ z : G, z ∈ W ↔ g + z ∈ W}
  zero_mem' := by
    intro z
    simp
  add_mem' := by
    intro a b ha hb z
    trans b + z ∈ W
    · exact hb z
    · simpa [add_assoc] using ha (b + z)
  neg_mem' := by
    intro a ha z
    simpa [add_assoc] using (ha (-a + z)).symm

lemma nhds_translate_preserves
    {G : Type u} [AddGroup G] {W N : Set G}
    (hpreserve : ∀ n : G, n ∈ N → ∀ z : G, z ∈ W ↔ n + z ∈ W) :
    N ⊆ ((clopenTranslateStabilizer G W : AddSubgroup G) : Set G) := by
  intro n hn
  change ∀ z : G, z ∈ W ↔ n + z ∈ W
  exact hpreserve n hn

lemma clopen_translate_stabilizer
    {G : Type u} [AddGroup G] {W : Set G} (h0W : (0 : G) ∈ W) :
    ((clopenTranslateStabilizer G W : AddSubgroup G) : Set G) ⊆ W := by
  intro g hg
  change (∀ z : G, z ∈ W ↔ g + z ∈ W) at hg
  have hg0 : g + 0 ∈ W := (hg 0).1 h0W
  simpa using hg0

lemma clopen_translate_nhds
    {G : Type u} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {W N : Set G}
    (hN : N ∈ nhds (0 : G))
    (hNsubset : N ⊆ ((clopenTranslateStabilizer G W : AddSubgroup G) : Set G)) :
    IsOpen ((clopenTranslateStabilizer G W : AddSubgroup G) : Set G) := by
  have hUnhds :
      ((clopenTranslateStabilizer G W : AddSubgroup G) : Set G) ∈
        nhds (0 : G) :=
    Filter.mem_of_superset hN hNsubset
  exact
    AddSubgroup.isOpen_of_mem_nhds
      (clopenTranslateStabilizer G W) hUnhds

lemma nhds_translate_clopen
    {G : Type u} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G]
    {W : Set G} (hWopen : IsOpen W) (hWclosed : IsClosed W) :
    ∃ N : Set G, N ∈ nhds (0 : G) ∧
      ∀ n : G, n ∈ N → ∀ z : G, z ∈ W ↔ n + z ∈ W := by
  have hWcompact : IsCompact W := hWclosed.isCompact
  have hWccompact : IsCompact Wᶜ := hWopen.isClosed_compl.isCompact
  rcases
      nhds_translate_compact
        (G := G) (K := W) (O := W) hWcompact hWopen (by
          intro z hz
          exact hz) with
    ⟨N₁, hN₁, hN₁sub⟩
  rcases
      nhds_translate_compact
        (G := G) (K := Wᶜ) (O := Wᶜ) hWccompact hWclosed.isOpen_compl (by
          intro z hz
          exact hz) with
    ⟨N₂, hN₂, hN₂sub⟩
  refine ⟨N₁ ∩ N₂, Filter.inter_mem hN₁ hN₂, ?_⟩
  intro n hn z
  constructor
  · intro hzW
    exact hN₁sub n hn.1 z hzW
  · intro hnzW
    by_contra hzW
    have hzWc : z ∈ Wᶜ := hzW
    have hnzWc : n + z ∈ Wᶜ := hN₂sub n hn.2 z hzWc
    exact hnzWc hnzW

lemma translate_preserving_nhds
    {G : Type u} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {W : Set G} (hW : W ∈ nhds (0 : G))
    (Hpreserve :
      ∃ N : Set G, N ∈ nhds (0 : G) ∧
        ∀ n : G, n ∈ N → ∀ z : G, z ∈ W ↔ n + z ∈ W) :
    ∃ U : AddSubgroup G,
      IsOpen ((U : AddSubgroup G) : Set G) ∧
        ((U : AddSubgroup G) : Set G) ⊆ W := by
  rcases Hpreserve with ⟨N, hN, hpreserve⟩
  let U : AddSubgroup G := clopenTranslateStabilizer G W
  have hNsubset : N ⊆ ((U : AddSubgroup G) : Set G) := by
    simpa [U] using
      nhds_translate_preserves
        (G := G) (W := W) (N := N) hpreserve
  have hUopen : IsOpen ((U : AddSubgroup G) : Set G) :=
    clopen_translate_nhds
      (G := G) (W := W) hN hNsubset
  have h0W : (0 : G) ∈ W := mem_of_mem_nhds hW
  have hUsubsetW : ((U : AddSubgroup G) : Set G) ⊆ W := by
    simpa [U] using
      clopen_translate_stabilizer
        (G := G) (W := W) h0W
  exact ⟨U, hUopen, hUsubsetW⟩

lemma clopen_totally_disconnected
    {G : Type u} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {W : Set G} (hWopen : IsOpen W) (hWclosed : IsClosed W)
    (hW : W ∈ nhds (0 : G)) :
    ∃ U : AddSubgroup G,
      IsOpen ((U : AddSubgroup G) : Set G) ∧
        ((U : AddSubgroup G) : Set G) ⊆ W := by
  have Hpreserve :
      ∃ N : Set G, N ∈ nhds (0 : G) ∧
        ∀ n : G, n ∈ N → ∀ z : G, z ∈ W ↔ n + z ∈ W :=
    nhds_translate_clopen
      (G := G) hWopen hWclosed
  exact
    translate_preserving_nhds
      (G := G) hW Hpreserve

lemma nhds_totally_disconnected
    {G : Type u} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {V : Set G} (hV : V ∈ nhds (0 : G)) :
    ∃ U : AddSubgroup G,
      IsOpen ((U : AddSubgroup G) : Set G) ∧
        ((U : AddSubgroup G) : Set G) ⊆ V := by
  rcases
      clopen_compact_disconnected
        (x := (0 : G)) hV with
    ⟨W, hWopen, hWclosed, hWnhds, hWsubset⟩
  rcases
      clopen_totally_disconnected
        (G := G) hWopen hWclosed hWnhds with
    ⟨U, hUopen, hUsubsetW⟩
  have hUsubsetV :
      ((U : AddSubgroup G) : Set G) ⊆ V := by
    intro x hx
    exact hWsubset (hUsubsetW hx)
  exact ⟨U, hUopen, hUsubsetV⟩

lemma nhds_compact_disconnected
    {R : Type u} [Ring R] [UniformSpace R] [IsTopologicalRing R]
    [CompleteSpace R] [T2Space R] [CompactSpace R] [TotallyDisconnectedSpace R]
    {V : Set R} (hV : V ∈ nhds (0 : R)) :
    ∃ U : AddSubgroup R,
      IsOpen ((U : AddSubgroup R) : Set R) ∧
        ((U : AddSubgroup R) : Set R) ⊆ V := by
  exact
    nhds_totally_disconnected
      (G := R) hV

end Towers
