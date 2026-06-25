import Mathlib
import Towers.Algebra.CompletedGroupAlgebra


open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u
universe v w z

def denseSignedElement
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (w : List (denseGeneratorsLetter d)) : Γ :=
  (w.map (denseLetterElement s)).prod

@[simp]
lemma dense_element_nil
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ) :
    denseSignedElement s [] = 1 := by
  simp [denseSignedElement]

@[simp]
lemma dense_element_cons
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (a : denseGeneratorsLetter d)
    (w : List (denseGeneratorsLetter d)) :
    denseSignedElement s (a :: w) =
      denseLetterElement s a *
        denseSignedElement s w := by
  simp [denseSignedElement]

lemma dense_element_append
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (w₁ w₂ : List (denseGeneratorsLetter d)) :
    denseSignedElement s (w₁ ++ w₂) =
      denseSignedElement s w₁ *
        denseSignedElement s w₂ := by
  rw [denseSignedElement]
  rw [List.map_append]
  rw [List.prod_append]
  rfl

def denseLetterFlip
    {d : ℕ} (a : denseGeneratorsLetter d) :
    denseGeneratorsLetter d :=
  (a.1, !a.2)

lemma letter_element_flip
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (a : denseGeneratorsLetter d) :
    denseLetterElement s
        (denseLetterFlip a) =
      (denseLetterElement s a)⁻¹ := by
  rcases a with ⟨i, b⟩
  cases b
  · simp [denseLetterFlip,
      denseLetterElement]
  · simp [denseLetterFlip,
      denseLetterElement]

def denseGeneratorsInverse
    {d : ℕ} (w : List (denseGeneratorsLetter d)) :
    List (denseGeneratorsLetter d) :=
  (w.map denseLetterFlip).reverse

lemma dense_element_inverse
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (w : List (denseGeneratorsLetter d)) :
    denseSignedElement s
        (denseGeneratorsInverse w) =
      (denseSignedElement s w)⁻¹ := by
  induction w with
  | nil =>
      rw [denseGeneratorsInverse]
      simp [denseSignedElement]
  | cons a w ih =>
      rw [denseGeneratorsInverse]
      rw [List.map_cons]
      rw [List.reverse_cons]
      rw [dense_element_append]
      change
        denseSignedElement s
            (denseGeneratorsInverse w) *
          denseSignedElement s
            [denseLetterFlip a] =
        (denseSignedElement s (a :: w))⁻¹
      rw [ih]
      have hsingle :
          denseSignedElement s
              [denseLetterFlip a] =
            (denseLetterElement s a)⁻¹ := by
        rw [dense_element_cons]
        rw [dense_element_nil]
        rw [mul_one]
        exact letter_element_flip s a
      rw [hsingle]
      rw [dense_element_cons]
      rw [mul_inv_rev]

lemma letter_element_closure
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (a : denseGeneratorsLetter d) :
    denseLetterElement s a ∈
      Subgroup.closure (Set.range s) := by
  by_cases h : a.2
  · rw [denseLetterElement, if_pos h]
    exact Subgroup.subset_closure ⟨a.1, rfl⟩
  · rw [denseLetterElement, if_neg h]
    exact
      (Subgroup.closure (Set.range s)).inv_mem
        (Subgroup.subset_closure ⟨a.1, rfl⟩)

lemma dense_generators_closure
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    (w : List (denseGeneratorsLetter d)) :
    denseSignedElement s w ∈
      Subgroup.closure (Set.range s) := by
  induction w with
  | nil =>
      rw [dense_element_nil]
      exact (Subgroup.closure (Set.range s)).one_mem
  | cons a w ih =>
      rw [dense_element_cons]
      exact
        (Subgroup.closure (Set.range s)).mul_mem
          (letter_element_closure s a)
          ih

lemma dense_element_closure
    {Γ : Type u} [Group Γ]
    {d : ℕ} (s : Fin d → Γ)
    {g : Γ}
    (hg : g ∈ Subgroup.closure (Set.range s)) :
    ∃ w : List (denseGeneratorsLetter d),
      denseSignedElement s w = g := by
  refine Subgroup.closure_induction (k := Set.range s) ?mem ?one ?mul ?inv hg
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    refine ⟨[(i, true)], ?_⟩
    rw [dense_element_cons]
    rw [dense_element_nil]
    simp [denseLetterElement]
  · refine ⟨[], ?_⟩
    rw [dense_element_nil]
  · intro x y _hx _hy hx_word hy_word
    rcases hx_word with ⟨wx, hwx⟩
    rcases hy_word with ⟨wy, hwy⟩
    refine ⟨wx ++ wy, ?_⟩
    rw [dense_element_append]
    rw [hwx, hwy]
  · intro x _hx hx_word
    rcases hx_word with ⟨wx, hwx⟩
    refine ⟨denseGeneratorsInverse wx, ?_⟩
    rw [dense_element_inverse]
    rw [hwx]

abbrev denseGeneratorsIndex (d n : ℕ) : Type :=
  Σ k : Fin (n + 1), List.Vector (denseGeneratorsLetter d) k

def denseGeneratorsEmpty (d n : ℕ) :
    denseGeneratorsIndex d n :=
  ⟨⟨0, Nat.succ_pos n⟩, List.Vector.nil⟩

def denseGeneratorsSingleton
    {d n : ℕ} (hn : 0 < n)
    (a : denseGeneratorsLetter d) :
    denseGeneratorsIndex d n :=
  ⟨⟨1, Nat.succ_lt_succ hn⟩, List.Vector.cons a List.Vector.nil⟩

def denseGeneratorsCons
    {d n : ℕ}
    (a : denseGeneratorsLetter d)
    (v : denseGeneratorsIndex d n)
    (hv : v.1.1 < n) :
    denseGeneratorsIndex d n :=
  ⟨⟨v.1.1 + 1, Nat.succ_lt_succ hv⟩, List.Vector.cons a v.2⟩

lemma dense_generators_index
    (d n : ℕ) :
    Finite (ULift.{u + 1} (denseGeneratorsIndex d n)) := by
  have hletters :
      Finite (denseGeneratorsLetter d) := by
    dsimp [denseGeneratorsLetter]
    infer_instance
  letI : Finite (denseGeneratorsLetter d) := hletters
  have hwords :
      Finite (denseGeneratorsIndex d n) := by
    dsimp [denseGeneratorsIndex]
    infer_instance
  letI : Finite (denseGeneratorsIndex d n) := hwords
  infer_instance

noncomputable def GCAmbien.ideal_quotsigned_augletter
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : denseGeneratorsLetter d) :
    A.completedGroupAlgebra ⧸
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  exact
    Ideal.Quotient.mk I
      ((A.canonicalUnit
        (denseLetterElement s a) :
          A.completedGroupAlgebra) - 1)

noncomputable def GCAmbien.ideal_quotcanon_unitclass
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (g : Γ) :
    A.completedGroupAlgebra ⧸
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  exact Ideal.Quotient.mk I (A.canonicalUnit g : A.completedGroupAlgebra)

noncomputable def GCAmbien.idealquot_canonunit_subone
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (g : Γ) :
    A.completedGroupAlgebra ⧸
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  exact
    Ideal.Quotient.mk I
      ((A.canonicalUnit g : A.completedGroupAlgebra) - 1)

noncomputable def GCAmbien.ideal_quot_boundedword
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (w : denseGeneratorsIndex d n) :
    A.completedGroupAlgebra ⧸
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  exact
    (w.2.toList.map fun a =>
      A.ideal_quotsigned_augletter (n := n) a).prod

@[simp]
lemma GCAmbien.ideal_quotbounded_wordempty
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.ideal_quot_boundedword (n := n)
      (denseGeneratorsEmpty d n) = 1 := by
  simp [GCAmbien.ideal_quot_boundedword,
    denseGeneratorsEmpty]

@[simp]
lemma GCAmbien.ideal_quotbounded_wordsingleton
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hn : 0 < n)
    (a : denseGeneratorsLetter d) :
    A.ideal_quot_boundedword (n := n)
      (denseGeneratorsSingleton hn a) =
      A.ideal_quotsigned_augletter (n := n) a := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  have hI_two_sided :
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra).IsTwoSided := by
    infer_instance
  letI :
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra).IsTwoSided := hI_two_sided
  simp [GCAmbien.ideal_quot_boundedword,
    denseGeneratorsSingleton]

noncomputable def GCAmbien.ideal_quotcanon_unitspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Submodule (ZMod p)
      (A.completedGroupAlgebra ⧸
        (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  exact
    Submodule.span (ZMod p)
      (Set.range fun g : Γ =>
        Ideal.Quotient.mk I
          (A.canonicalUnit g : A.completedGroupAlgebra))

noncomputable def GCAmbien.ideal_quotbounded_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Submodule (ZMod p)
      (A.completedGroupAlgebra ⧸
        (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  exact
    Submodule.span (ZMod p)
      (Set.range fun w :
          ULift.{u + 1} (denseGeneratorsIndex d n) =>
        A.ideal_quot_boundedword (n := n) w.down)

lemma GCAmbien.idealquot_boundedword_memspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (w : denseGeneratorsIndex d n) :
    A.ideal_quot_boundedword (n := n) w ∈
      A.ideal_quotbounded_wordspan n := by
  exact Submodule.subset_span ⟨ULift.up w, rfl⟩

lemma GCAmbien.onemem_idealquot_boundedwordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (1 : A.completedGroupAlgebra ⧸
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)) ∈
      A.ideal_quotbounded_wordspan n := by
  simpa using
    A.idealquot_boundedword_memspan
      (n := n) (denseGeneratorsEmpty d n)

lemma
    GCAmbien.idealquotsigned_auglettermem_boundedwordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hn : 0 < n)
    (a : denseGeneratorsLetter d) :
    A.ideal_quotsigned_augletter (n := n) a ∈
      A.ideal_quotbounded_wordspan n := by
  simpa using
    A.idealquot_boundedword_memspan
      (n := n) (denseGeneratorsSingleton hn a)

lemma
    GCAmbien.idealquot_boundedwordeq_topspanle
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hcanonical_top : A.ideal_quotcanon_unitspan n = ⊤)
    (hcanonical_le :
      A.ideal_quotcanon_unitspan n ≤
        A.ideal_quotbounded_wordspan n) :
    A.ideal_quotbounded_wordspan n = ⊤ := by
  refine le_antisymm le_top ?_
  intro x _hx
  have hxcanonical :
      x ∈ A.ideal_quotcanon_unitspan n := by
    rw [hcanonical_top]
    exact Submodule.mem_top
  exact hcanonical_le hxcanonical

lemma
    GCAmbien.idealquot_boundedwordeq_closedspanle
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hcanonical_dense :
      closure
        ((A.ideal_quotcanon_unitspan n :
          Set (A.completedGroupAlgebra ⧸
            (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)))) = Set.univ)
    (hbounded_closed :
      IsClosed
        ((A.ideal_quotbounded_wordspan n :
          Set (A.completedGroupAlgebra ⧸
            (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)))))
    (hcanonical_le :
      A.ideal_quotcanon_unitspan n ≤
        A.ideal_quotbounded_wordspan n) :
    A.ideal_quotbounded_wordspan n = ⊤ := by
  refine le_antisymm le_top ?_
  intro x _hx
  have hxclosure :
      x ∈
        closure
          ((A.ideal_quotcanon_unitspan n :
            Set (A.completedGroupAlgebra ⧸
              (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)))) := by
    rw [hcanonical_dense]
    exact Set.mem_univ x
  have hcanonical_subset :
      (A.ideal_quotcanon_unitspan n :
        Set (A.completedGroupAlgebra ⧸
          (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra))) ⊆
        (A.ideal_quotbounded_wordspan n :
          Set (A.completedGroupAlgebra ⧸
            (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra))) := by
    intro y hy
    exact hcanonical_le hy
  have hclosure_subset :
      closure
        ((A.ideal_quotcanon_unitspan n :
          Set (A.completedGroupAlgebra ⧸
            (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)))) ⊆
        (A.ideal_quotbounded_wordspan n :
          Set (A.completedGroupAlgebra ⧸
            (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra))) := by
    exact closure_minimal hcanonical_subset hbounded_closed
  exact hclosure_subset hxclosure

lemma
    GCAmbien.idealquot_unitspanspan_closedaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan)
    (_hclosed : A.ClosedAugPower n) :
    closure
      ((A.ideal_quotcanon_unitspan n :
        Set (A.completedGroupAlgebra ⧸
          (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)))) = Set.univ := by
    
                                                                                              
                                                                                                
                                                                    
    
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  let quotientMap : A.completedGroupAlgebra →ₐ[ZMod p] A.completedGroupAlgebra ⧸ I :=
    Ideal.Quotient.mkₐ (ZMod p) I
  let algebraSpan : Submodule (ZMod p) A.completedGroupAlgebra :=
    Submodule.span (ZMod p)
      (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))
  let quotientSpan : Submodule (ZMod p) (A.completedGroupAlgebra ⧸ I) :=
    A.ideal_quotcanon_unitspan n
  have himage_subset :
      quotientMap '' (algebraSpan : Set A.completedGroupAlgebra) ⊆
        (quotientSpan : Set (A.completedGroupAlgebra ⧸ I)) := by
    have himage_range :
        quotientMap.toLinearMap ''
            (Set.range fun g : Γ =>
              (A.canonicalUnit g : A.completedGroupAlgebra)) =
          Set.range fun g : Γ =>
            quotientMap (A.canonicalUnit g : A.completedGroupAlgebra) := by
      ext y
      constructor
      · rintro ⟨x, ⟨g, rfl⟩, rfl⟩
        exact ⟨g, rfl⟩
      · rintro ⟨g, rfl⟩
        exact ⟨(A.canonicalUnit g : A.completedGroupAlgebra), ⟨g, rfl⟩, rfl⟩
    rintro y ⟨x, hx, rfl⟩
    have hximage :
        quotientMap.toLinearMap x ∈
          Submodule.span (ZMod p)
            (quotientMap.toLinearMap ''
              (Set.range fun g : Γ =>
                (A.canonicalUnit g : A.completedGroupAlgebra))) :=
      (Submodule.image_span_subset_span
        quotientMap.toLinearMap
        (Set.range fun g : Γ =>
          (A.canonicalUnit g : A.completedGroupAlgebra))) ⟨x, hx, rfl⟩
    rw [himage_range] at hximage
    simpa [quotientSpan, GCAmbien.ideal_quotcanon_unitspan,
      quotientMap, I] using hximage
  apply Set.eq_univ_iff_forall.mpr
  intro y
  rcases Ideal.Quotient.mkₐ_surjective (ZMod p) I y with ⟨x, rfl⟩
  have hx : x ∈ closure (algebraSpan : Set A.completedGroupAlgebra) := by
    rw [show closure (algebraSpan : Set A.completedGroupAlgebra) = Set.univ by
      simpa [GCAmbien.DenseAlgebraSpan,
        algebraSpan] using hdense]
    exact Set.mem_univ x
  have hquotient_image :
      quotientMap x ∈
        closure (quotientMap '' (algebraSpan : Set A.completedGroupAlgebra)) :=
    mem_closure_image
      (idealQuotient_mkₐ_continuous (𝕜 := ZMod p) I).continuousAt hx
  exact closure_mono himage_subset hquotient_image

lemma GCAmbien.fgideal_quotbounded_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (A.ideal_quotbounded_wordspan n).FG := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  haveI :
      Finite
        (ULift.{u + 1} (denseGeneratorsIndex d n)) :=
    dense_generators_index d n
  rw [GCAmbien.ideal_quotbounded_wordspan]
  exact
    Submodule.fg_span
      (Set.finite_range fun w :
          ULift.{u + 1} (denseGeneratorsIndex d n) =>
        A.ideal_quot_boundedword (n := n) w.down)

lemma GCAmbien.modulefin_idealquot_boundedwordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Module.Finite (ZMod p) (A.ideal_quotbounded_wordspan n) := by
  exact
    Module.Finite.of_fg
      (A.fgideal_quotbounded_wordspan (n := n))

lemma GCAmbien.finideal_quotbounded_wordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Finite (A.ideal_quotbounded_wordspan n) := by
  haveI :
      Module.Finite (ZMod p) (A.ideal_quotbounded_wordspan n) :=
    A.modulefin_idealquot_boundedwordspan (n := n)
  haveI : Finite (ZMod p) := by
    haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
    infer_instance
  exact Module.finite_of_finite (ZMod p)

lemma GCAmbien.setfin_idealquot_boundedwordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (A.ideal_quotbounded_wordspan n :
      Set (A.completedGroupAlgebra ⧸
        (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra))).Finite := by
  classical
  haveI : Finite (A.ideal_quotbounded_wordspan n) :=
    A.finideal_quotbounded_wordspan (n := n)
  haveI : Fintype (A.ideal_quotbounded_wordspan n) :=
    Fintype.ofFinite (A.ideal_quotbounded_wordspan n)
  exact
    Set.toFinite
      (A.ideal_quotbounded_wordspan n :
        Set (A.completedGroupAlgebra ⧸
          (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)))

lemma
    GCAmbien.idealquot_boundedword_closedaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hclosed : A.ClosedAugPower n) :
    IsClosed
      ((A.ideal_quotbounded_wordspan n :
        Set (A.completedGroupAlgebra ⧸
          (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)))) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  have hI_closed : IsClosed (I : Set A.completedGroupAlgebra) := by
    simpa [I, GCAmbien.ClosedAugPower]
      using hclosed
  have hT2 :
      T2Space (A.completedGroupAlgebra ⧸ I) :=
    t_space_closed I hI_closed
  letI : T2Space (A.completedGroupAlgebra ⧸ I) := hT2
  have hfinite :
      (A.ideal_quotbounded_wordspan n :
        Set (A.completedGroupAlgebra ⧸
          (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra))).Finite :=
    A.setfin_idealquot_boundedwordspan (n := n)
  exact hfinite.isClosed

lemma
    GCAmbien.idealquotcanon_unitclasseq_suboneaddone
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (g : Γ) :
    A.ideal_quotcanon_unitclass (n := n) g =
      A.idealquot_canonunit_subone (n := n) g + 1 := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  rw [GCAmbien.ideal_quotcanon_unitclass,
    GCAmbien.idealquot_canonunit_subone]
  change
    Ideal.Quotient.mk I (A.canonicalUnit g : A.completedGroupAlgebra) =
      Ideal.Quotient.mk I
          ((A.canonicalUnit g : A.completedGroupAlgebra) - 1) + 1
  rw [map_sub, map_one, sub_add_cancel]

lemma
    GCAmbien.idealquot_unitclass_subonemem
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (g : Γ)
    (hsub :
      A.idealquot_canonunit_subone (n := n) g ∈
        A.ideal_quotbounded_wordspan n) :
    A.ideal_quotcanon_unitclass (n := n) g ∈
      A.ideal_quotbounded_wordspan n := by
  have hone :
      (1 : A.completedGroupAlgebra ⧸
        (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)) ∈
        A.ideal_quotbounded_wordspan n :=
    A.onemem_idealquot_boundedwordspan (n := n)
  have hsum :
      A.idealquot_canonunit_subone (n := n) g + 1 ∈
        A.ideal_quotbounded_wordspan n :=
    (A.ideal_quotbounded_wordspan n).add_mem hsub hone
  rw [A.idealquotcanon_unitclasseq_suboneaddone (n := n) g]
  exact hsum

lemma
    GCAmbien.idealquot_unitspan_subonemem
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hsub :
      ∀ g : Γ,
        A.idealquot_canonunit_subone (n := n) g ∈
          A.ideal_quotbounded_wordspan n) :
    A.ideal_quotcanon_unitspan n ≤
      A.ideal_quotbounded_wordspan n := by
  rw [GCAmbien.ideal_quotcanon_unitspan]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨g, rfl⟩
  simpa [GCAmbien.ideal_quotcanon_unitclass] using
    A.idealquot_unitclass_subonemem
      (n := n) g (hsub g)

lemma dense_generators_ambient
    {R : Type u} [Ring R]
    (I : Ideal R)
    {m n : ℕ} {a : R}
    (hbound : n ≤ m)
    (ha : a ∈ I ^ m) :
    a ∈ I ^ n := by
  exact Ideal.pow_le_pow_right hbound ha

lemma GCAmbien.canonunit_subone_memaugideal
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (x : Γ) :
    (A.canonicalUnit x : A.completedGroupAlgebra) - 1 ∈
      A.augmentationIdeal := by
  rw [A.augmentation_ideal_ker]
  change
    A.augmentationMap.toRingHom
        ((A.canonicalUnit x : A.completedGroupAlgebra) - 1) = 0
  simp [map_sub, A.canonicalUnit_augmentation x]

lemma
    GCAmbien.idealquot_signedaugfactor_memaugideal
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : denseGeneratorsLetter d) :
    (A.canonicalUnit (denseLetterElement s a) :
        A.completedGroupAlgebra) - 1 ∈
      A.augmentationIdeal := by
  exact
    A.canonunit_subone_memaugideal
      (denseLetterElement s a)

lemma GCAmbien.idealquot_signaugfact_prodmempower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (w : List (denseGeneratorsLetter d)) :
    (w.map fun a =>
        (A.canonicalUnit (denseLetterElement s a) :
            A.completedGroupAlgebra) - 1).prod ∈
      A.augmentationIdeal ^ w.length := by
  letI : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  induction w with
  | nil =>
      rw [List.map_nil, List.prod_nil, List.length_nil]
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      trivial
  | cons a w ih =>
      let head : A.completedGroupAlgebra :=
        (A.canonicalUnit (denseLetterElement s a) :
            A.completedGroupAlgebra) - 1
      let tail : A.completedGroupAlgebra :=
        (w.map fun b =>
          (A.canonicalUnit (denseLetterElement s b) :
              A.completedGroupAlgebra) - 1).prod
      have hhead_one : head ∈ A.augmentationIdeal ^ 1 := by
        have hhead : head ∈ A.augmentationIdeal := by
          dsimp [head]
          exact A.idealquot_signedaugfactor_memaugideal a
        simpa [Submodule.pow_one] using hhead
      have htail : tail ∈ A.augmentationIdeal ^ w.length := by
        dsimp [tail]
        exact ih
      have hmul :
          head * tail ∈ A.augmentationIdeal ^ (1 + w.length) := by
        rw [Ideal.IsTwoSided.pow_add (I := A.augmentationIdeal) 1 w.length]
        exact Ideal.mul_mem_mul hhead_one htail
      simpa [head, tail, Nat.add_comm] using hmul

noncomputable def
    GCAmbien.idealquot_signedaug_factorsclass
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (w : List (denseGeneratorsLetter d)) :
    A.completedGroupAlgebra ⧸
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  exact
    Ideal.Quotient.mk I
      ((w.map fun a =>
        (A.canonicalUnit (denseLetterElement s a) :
            A.completedGroupAlgebra) - 1).prod)

noncomputable def
    GCAmbien.idealquot_signedaug_factprodclas
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (w : List (denseGeneratorsLetter d)) :
    A.completedGroupAlgebra ⧸
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  exact
    (w.map fun a => A.ideal_quotsigned_augletter (n := n) a).prod

lemma
    GCAmbien.idealquot_signaugfact_classeqproduct
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (w : List (denseGeneratorsLetter d)) :
    A.idealquot_signedaug_factorsclass (n := n) w =
      A.idealquot_signedaug_factprodclas (n := n) w := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  induction w with
  | nil =>
      simp [
        GCAmbien.idealquot_signedaug_factorsclass,
        GCAmbien.idealquot_signedaug_factprodclas,
        GCAmbien.ideal_quotsigned_augletter,
        I]
  | cons a w ih =>
      have htail :
          Ideal.Quotient.mk I
              ((w.map fun b =>
                (A.canonicalUnit (denseLetterElement s b) :
                    A.completedGroupAlgebra) - 1).prod) =
            (w.map fun b =>
              A.ideal_quotsigned_augletter (n := n) b).prod := by
        simpa [
          GCAmbien.idealquot_signedaug_factorsclass,
          GCAmbien.idealquot_signedaug_factprodclas,
          I] using ih
      simp [
        GCAmbien.idealquot_signedaug_factorsclass,
        GCAmbien.idealquot_signedaug_factprodclas,
        GCAmbien.ideal_quotsigned_augletter,
        I, map_mul, htail]

lemma
    GCAmbien.idealquot_signedaug_eqzeromem
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (w : List (denseGeneratorsLetter d))
    (hmem :
      (w.map fun a =>
          (A.canonicalUnit (denseLetterElement s a) :
              A.completedGroupAlgebra) - 1).prod ∈
        A.augmentationIdeal ^ n) :
    A.idealquot_signedaug_factorsclass (n := n) w = 0 := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  rw [
    GCAmbien.idealquot_signedaug_factorsclass]
  change
    Ideal.Quotient.mk I
        ((w.map fun a =>
          (A.canonicalUnit (denseLetterElement s a) :
              A.completedGroupAlgebra) - 1).prod) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa [I] using hmem)

noncomputable def GCAmbien.idealquot_signedword_productterm
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : denseGeneratorsLetter d)
    (w : List (denseGeneratorsLetter d)) :
    A.completedGroupAlgebra ⧸
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  exact
    Ideal.Quotient.mk I
      (((A.canonicalUnit (denseLetterElement s a) :
          A.completedGroupAlgebra) - 1) *
        ((A.canonicalUnit (denseSignedElement s w) :
          A.completedGroupAlgebra) - 1))

noncomputable def GCAmbien.idealquot_signedaug_leftmul
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : denseGeneratorsLetter d) :
    (A.completedGroupAlgebra ⧸
        (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)) →ₗ[ZMod p]
      (A.completedGroupAlgebra ⧸
        (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  exact
    { toFun := fun x => A.ideal_quotsigned_augletter (n := n) a * x
      map_add' := by
        intro x y
        rw [mul_add]
      map_smul' := by
        intro c x
        simp [RingHom.id_apply]}

lemma
    GCAmbien.idealquotsigned_wordeqleft_mulsubone
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : denseGeneratorsLetter d)
    (w : List (denseGeneratorsLetter d)) :
    A.idealquot_signedword_productterm (n := n) a w =
      A.idealquot_signedaug_leftmul (n := n) a
        (A.idealquot_canonunit_subone (n := n)
          (denseSignedElement s w)) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  simp [GCAmbien.idealquot_signedword_productterm,
    GCAmbien.idealquot_signedaug_leftmul,
    GCAmbien.ideal_quotsigned_augletter,
    GCAmbien.idealquot_canonunit_subone,
    map_mul]

lemma
    GCAmbien.idealquot_signedaug_memspanlt
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : denseGeneratorsLetter d)
    (v : denseGeneratorsIndex d n)
    (hv : v.1.1 < n) :
    A.idealquot_signedaug_leftmul (n := n) a
        (A.ideal_quot_boundedword (n := n) v) ∈
      A.ideal_quotbounded_wordspan n := by
  have hmem :
      A.ideal_quot_boundedword (n := n)
          (denseGeneratorsCons a v hv) ∈
        A.ideal_quotbounded_wordspan n :=
    A.idealquot_boundedword_memspan
      (n := n) (denseGeneratorsCons a v hv)
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  have heq :
      A.idealquot_signedaug_leftmul (n := n) a
          (A.ideal_quot_boundedword (n := n) v) =
        A.ideal_quot_boundedword (n := n)
          (denseGeneratorsCons a v hv) := by
    simp [GCAmbien.idealquot_signedaug_leftmul,
      GCAmbien.ideal_quot_boundedword,
      GCAmbien.ideal_quotsigned_augletter,
      denseGeneratorsCons,
      GCAmbien.ideal_quot_boundedword]
  rw [heq]
  exact hmem

lemma
    GCAmbien.idealquot_signedaugword_eqmkcons
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : denseGeneratorsLetter d)
    (v : denseGeneratorsIndex d n) :
    A.idealquot_signedaug_leftmul (n := n) a
        (A.ideal_quot_boundedword (n := n) v) =
      A.idealquot_signedaug_factorsclass (n := n)
        (a :: v.2.toList) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  have hquotient_product :
      A.idealquot_signedaug_factorsclass (n := n)
          (a :: v.2.toList) =
        A.idealquot_signedaug_factprodclas (n := n)
          (a :: v.2.toList) :=
    A.idealquot_signaugfact_classeqproduct
      (n := n) (a :: v.2.toList)
  have hleft_product :
      A.idealquot_signedaug_leftmul (n := n) a
          (A.ideal_quot_boundedword (n := n) v) =
        A.idealquot_signedaug_factprodclas (n := n)
          (a :: v.2.toList) := by
    simp [GCAmbien.idealquot_signedaug_leftmul,
      GCAmbien.ideal_quot_boundedword,
      GCAmbien.idealquot_signedaug_factprodclas]
  exact hleft_product.trans hquotient_product.symm

lemma
    GCAmbien.idealquot_signedaug_memspantop
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : denseGeneratorsLetter d)
    (v : denseGeneratorsIndex d n)
    (hv : n ≤ v.1.1) :
    A.idealquot_signedaug_leftmul (n := n) a
        (A.ideal_quot_boundedword (n := n) v) ∈
      A.ideal_quotbounded_wordspan n := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  let w : List (denseGeneratorsLetter d) := a :: v.2.toList
  have hprod_power :
      (w.map fun b =>
          (A.canonicalUnit (denseLetterElement s b) :
              A.completedGroupAlgebra) - 1).prod ∈
        A.augmentationIdeal ^ w.length :=
    A.idealquot_signaugfact_prodmempower w
  have hv_len : v.2.toList.length = v.1.1 := by
    simp
  have hdegree_tail : n ≤ v.2.toList.length := by
    simpa [hv_len] using hv
  have hdegree : n ≤ w.length := by
    dsimp [w]
    exact Nat.le_trans hdegree_tail (Nat.le_succ v.2.toList.length)
  have hprod_power_n :
      (w.map fun b =>
          (A.canonicalUnit (denseLetterElement s b) :
              A.completedGroupAlgebra) - 1).prod ∈
        A.augmentationIdeal ^ n :=
    dense_generators_ambient
      (I := A.augmentationIdeal) (m := w.length) (n := n) hdegree hprod_power
  have hquotient_zero :
      A.idealquot_signedaug_factorsclass (n := n) w = 0 :=
    A.idealquot_signedaug_eqzeromem
      (n := n) w hprod_power_n
  have hmul_eq :
      A.idealquot_signedaug_leftmul (n := n) a
          (A.ideal_quot_boundedword (n := n) v) =
        A.idealquot_signedaug_factorsclass (n := n) w := by
    dsimp [w]
    simpa using
      A.idealquot_signedaugword_eqmkcons
        (n := n) a v
  rw [hmul_eq, hquotient_zero]
  exact (A.ideal_quotbounded_wordspan n).zero_mem

lemma
    GCAmbien.idealquotsigned_augmulmem_boundedwordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (_hn : n ≠ 0)
    (a : denseGeneratorsLetter d)
    {x : A.completedGroupAlgebra ⧸
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)}
    (hx : x ∈ A.ideal_quotbounded_wordspan n) :
    A.idealquot_signedaug_leftmul (n := n) a x ∈
      A.ideal_quotbounded_wordspan n := by
  let S : Set (A.completedGroupAlgebra ⧸
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)) :=
    Set.range fun v :
        ULift.{u + 1} (denseGeneratorsIndex d n) =>
      A.ideal_quot_boundedword (n := n) v.down
  have hxspan : x ∈ Submodule.span (ZMod p) S := by
    simpa [GCAmbien.ideal_quotbounded_wordspan, S] using hx
  change
    A.idealquot_signedaug_leftmul (n := n) a x ∈
      Submodule.span (ZMod p) S
  refine Submodule.span_induction
    (s := S)
    (p := fun y _ =>
      A.idealquot_signedaug_leftmul (n := n) a y ∈
        Submodule.span (ZMod p) S)
    ?mem ?zero ?add ?smul hxspan
  · intro y hy
    rcases hy with ⟨v, rfl⟩
    by_cases hv : v.down.1.1 < n
    · simpa [S] using
        A.idealquot_signedaug_memspanlt
          (n := n) a v.down hv
    · have hvtop : n ≤ v.down.1.1 := le_of_not_gt hv
      simpa [S] using
        A.idealquot_signedaug_memspantop
          (n := n) a v.down hvtop
  · change
      A.idealquot_signedaug_leftmul (n := n) a 0 ∈
        Submodule.span (ZMod p) S
    rw [LinearMap.map_zero]
    exact Submodule.zero_mem _
  · intro x y _hx _hy hx_mem hy_mem
    change
      A.idealquot_signedaug_leftmul (n := n) a (x + y) ∈
        Submodule.span (ZMod p) S
    rw [LinearMap.map_add]
    exact Submodule.add_mem _ hx_mem hy_mem
  · intro c x _hx hx_mem
    change
      A.idealquot_signedaug_leftmul (n := n) a (c • x) ∈
        Submodule.span (ZMod p) S
    rw [LinearMap.map_smul]
    exact Submodule.smul_mem _ c hx_mem

lemma
    GCAmbien.idealquot_unitsubbounded_wordspannil
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.idealquot_canonunit_subone (n := n)
        (denseSignedElement s []) ∈
      A.ideal_quotbounded_wordspan n := by
  have hzero :
      A.idealquot_canonunit_subone (n := n)
          (denseSignedElement s []) =
        (0 : A.completedGroupAlgebra ⧸
          (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)) := by
    have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
      rw [A.augmentation_ideal_ker]
      infer_instance
    letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
    let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
    have hI_two_sided : I.IsTwoSided := by
      dsimp [I]
      infer_instance
    letI : I.IsTwoSided := hI_two_sided
    rw [GCAmbien.idealquot_canonunit_subone]
    change
      Ideal.Quotient.mk I
          ((A.canonicalUnit (denseSignedElement s []) :
              A.completedGroupAlgebra) - 1) = 0
    simp
  rw [hzero]
  exact (A.ideal_quotbounded_wordspan n).zero_mem

lemma
    GCAmbien.idealquot_unitsubbounded_wordspansing
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hn : n ≠ 0)
    (a : denseGeneratorsLetter d) :
    A.idealquot_canonunit_subone (n := n)
        (denseSignedElement s [a]) ∈
      A.ideal_quotbounded_wordspan n := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hletter :
      A.ideal_quotsigned_augletter (n := n) a ∈
        A.ideal_quotbounded_wordspan n :=
    A.idealquotsigned_auglettermem_boundedwordspan (n := n) hnpos a
  have heq :
      A.idealquot_canonunit_subone (n := n)
          (denseSignedElement s [a]) =
        A.ideal_quotsigned_augletter (n := n) a := by
    have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
      rw [A.augmentation_ideal_ker]
      infer_instance
    letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
    let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
    have hI_two_sided : I.IsTwoSided := by
      dsimp [I]
      infer_instance
    letI : I.IsTwoSided := hI_two_sided
    rw [GCAmbien.idealquot_canonunit_subone,
      GCAmbien.ideal_quotsigned_augletter]
    change
      Ideal.Quotient.mk I
          ((A.canonicalUnit (denseSignedElement s [a]) :
              A.completedGroupAlgebra) - 1) =
        Ideal.Quotient.mk I
          ((A.canonicalUnit (denseLetterElement s a) :
              A.completedGroupAlgebra) - 1)
    simp [denseSignedElement]
  rw [heq]
  exact hletter

lemma
    GCAmbien.idealquot_signedwordmem_boundedwordspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hn : n ≠ 0)
    (a : denseGeneratorsLetter d)
    (w : List (denseGeneratorsLetter d))
    (htail :
      A.idealquot_canonunit_subone (n := n)
          (denseSignedElement s w) ∈
        A.ideal_quotbounded_wordspan n) :
    A.idealquot_signedword_productterm (n := n) a w ∈
      A.ideal_quotbounded_wordspan n := by
  have hleft :
      A.idealquot_signedaug_leftmul (n := n) a
          (A.idealquot_canonunit_subone (n := n)
            (denseSignedElement s w)) ∈
        A.ideal_quotbounded_wordspan n :=
    A.idealquotsigned_augmulmem_boundedwordspan
      (n := n) hn a htail
  rw [A.idealquotsigned_wordeqleft_mulsubone (n := n) a w]
  exact hleft

lemma
    GCAmbien.idealquot_unitsubbounded_wordspancons
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hn : n ≠ 0)
    (a : denseGeneratorsLetter d)
    (w : List (denseGeneratorsLetter d))
    (htail :
      A.idealquot_canonunit_subone (n := n)
          (denseSignedElement s w) ∈
        A.ideal_quotbounded_wordspan n)
    (hproduct :
      A.idealquot_signedword_productterm (n := n) a w ∈
        A.ideal_quotbounded_wordspan n) :
    A.idealquot_canonunit_subone (n := n)
        (denseSignedElement s (a :: w)) ∈
      A.ideal_quotbounded_wordspan n := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hletter :
      A.ideal_quotsigned_augletter (n := n) a ∈
        A.ideal_quotbounded_wordspan n :=
    A.idealquotsigned_auglettermem_boundedwordspan (n := n) hnpos a
  have hsum :
      A.idealquot_signedword_productterm (n := n) a w +
          A.ideal_quotsigned_augletter (n := n) a +
        A.idealquot_canonunit_subone (n := n)
          (denseSignedElement s w) ∈
        A.ideal_quotbounded_wordspan n :=
    (A.ideal_quotbounded_wordspan n).add_mem
      ((A.ideal_quotbounded_wordspan n).add_mem hproduct hletter)
      htail
  have heq :
      A.idealquot_canonunit_subone (n := n)
          (denseSignedElement s (a :: w)) =
        A.idealquot_signedword_productterm (n := n) a w +
            A.ideal_quotsigned_augletter (n := n) a +
          A.idealquot_canonunit_subone (n := n)
            (denseSignedElement s w) := by
    have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
      rw [A.augmentation_ideal_ker]
      infer_instance
    letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
    let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
    have hI_two_sided : I.IsTwoSided := by
      dsimp [I]
      infer_instance
    letI : I.IsTwoSided := hI_two_sided
    have hidentity :
        (A.canonicalUnit (denseSignedElement s (a :: w)) :
            A.completedGroupAlgebra) - 1 =
          ((A.canonicalUnit (denseLetterElement s a) :
              A.completedGroupAlgebra) - 1) *
            ((A.canonicalUnit (denseSignedElement s w) :
              A.completedGroupAlgebra) - 1) +
          ((A.canonicalUnit (denseLetterElement s a) :
              A.completedGroupAlgebra) - 1) +
          ((A.canonicalUnit (denseSignedElement s w) :
              A.completedGroupAlgebra) - 1) := by
      rw [dense_element_cons]
      simp only [map_mul, Units.val_mul]
      noncomm_ring
    rw [GCAmbien.idealquot_canonunit_subone,
      GCAmbien.idealquot_signedword_productterm,
      GCAmbien.ideal_quotsigned_augletter]
    change
      Ideal.Quotient.mk I
          ((A.canonicalUnit (denseSignedElement s (a :: w)) :
              A.completedGroupAlgebra) - 1) =
        Ideal.Quotient.mk I
            (((A.canonicalUnit (denseLetterElement s a) :
                A.completedGroupAlgebra) - 1) *
              ((A.canonicalUnit (denseSignedElement s w) :
                A.completedGroupAlgebra) - 1)) +
          Ideal.Quotient.mk I
            ((A.canonicalUnit (denseLetterElement s a) :
                A.completedGroupAlgebra) - 1) +
          Ideal.Quotient.mk I
            ((A.canonicalUnit (denseSignedElement s w) :
                A.completedGroupAlgebra) - 1)
    rw [hidentity]
    simp [map_add]
  rw [heq]
  exact hsum

lemma
    GCAmbien.idealquot_unitsub_wordnezero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (_hn : n ≠ 0)
    (w : List (denseGeneratorsLetter d)) :
    A.idealquot_canonunit_subone (n := n)
        (denseSignedElement s w) ∈
      A.ideal_quotbounded_wordspan n := by
  induction w with
  | nil =>
      exact
        A.idealquot_unitsubbounded_wordspannil (n := n)
  | cons a w ih =>
      exact
        A.idealquot_unitsubbounded_wordspancons
          (n := n) _hn a w ih
          (A.idealquot_signedwordmem_boundedwordspan
            (n := n) _hn a w ih)

lemma
    GCAmbien.idealquot_unitsub_closuretwole
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hn : 2 ≤ n)
    (g : Γ)
    (hg : g ∈ Subgroup.closure (Set.range s)) :
    A.idealquot_canonunit_subone (n := n) g ∈
      A.ideal_quotbounded_wordspan n := by
  have htwo_pos : 0 < (2 : ℕ) := by decide
  have hn_pos : 0 < n := lt_of_lt_of_le htwo_pos hn
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn_pos
  rcases dense_element_closure
      (s := s) hg with ⟨w, hw⟩
  have hword :
      A.idealquot_canonunit_subone (n := n)
          (denseSignedElement s w) ∈
        A.ideal_quotbounded_wordspan n :=
    A.idealquot_unitsub_wordnezero
      (n := n) hn_ne w
  simpa [hw] using hword

lemma
    GCAmbien.idealquot_unitsub_powedenssubg
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hclosed : A.ClosedAugPower n)
    (H :
      ∀ g : Γ,
        g ∈ Subgroup.closure (Set.range s) →
          A.idealquot_canonunit_subone (n := n) g ∈
            A.ideal_quotbounded_wordspan n)
    (g : Γ) :
    A.idealquot_canonunit_subone (n := n) g ∈
      A.ideal_quotbounded_wordspan n := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  let quotientMap : A.completedGroupAlgebra →ₐ[ZMod p] A.completedGroupAlgebra ⧸ I :=
    Ideal.Quotient.mkₐ (ZMod p) I
  let f : Γ → A.completedGroupAlgebra ⧸ I := fun x =>
    quotientMap ((A.canonicalUnit x : A.completedGroupAlgebra) - 1)
  have hcanonical :
      Continuous fun x : Γ => (A.canonicalUnit x : A.completedGroupAlgebra) := by
    exact Units.continuous_val.comp A.canonicalUnit_continuous
  have hf : Continuous f := by
    have hsub :
        Continuous fun x : Γ =>
          (A.canonicalUnit x : A.completedGroupAlgebra) - 1 := by
      exact hcanonical.sub continuous_const
    exact (idealQuotient_mkₐ_continuous (𝕜 := ZMod p) I).comp hsub
  have hclosed_span :
      IsClosed
        ((A.ideal_quotbounded_wordspan n :
          Set (A.completedGroupAlgebra ⧸ I))) := by
    simpa [I] using
      A.idealquot_boundedword_closedaugpower hclosed
  have hclosed_preimage :
      IsClosed
        (f ⁻¹'
          (A.ideal_quotbounded_wordspan n :
            Set (A.completedGroupAlgebra ⧸ I))) :=
    hclosed_span.preimage hf
  have hdense :
      closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) = Set.univ := by
    simpa [Subgroup.topologicalClosure_coe] using
      congrArg (fun H : Subgroup Γ => (H : Set Γ)) hs
  have hsubset :
      ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) ⊆
        f ⁻¹'
          (A.ideal_quotbounded_wordspan n :
            Set (A.completedGroupAlgebra ⧸ I)) := by
    intro x hx
    have hxmem :
        A.idealquot_canonunit_subone (n := n) x ∈
          A.ideal_quotbounded_wordspan n :=
      H x hx
    simpa [f, quotientMap, I,
      GCAmbien.idealquot_canonunit_subone] using hxmem
  have hclosure_subset :
      closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) ⊆
        f ⁻¹'
          (A.ideal_quotbounded_wordspan n :
            Set (A.completedGroupAlgebra ⧸ I)) :=
    closure_minimal hsubset hclosed_preimage
  have hg :
      g ∈ closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) := by
    rw [hdense]
    exact Set.mem_univ g
  have hfg :
      f g ∈
        (A.ideal_quotbounded_wordspan n :
          Set (A.completedGroupAlgebra ⧸ I)) :=
    hclosure_subset hg
  simpa [f, quotientMap, I,
    GCAmbien.idealquot_canonunit_subone] using hfg

lemma
    GCAmbien.idealquot_unitsub_powertwole
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hclosed : A.ClosedAugPower n)
    (hn : 2 ≤ n)
    (g : Γ) :
    A.idealquot_canonunit_subone (n := n) g ∈
      A.ideal_quotbounded_wordspan n := by
  exact
    A.idealquot_unitsub_powedenssubg
      (n := n) hclosed
      (fun x hx =>
        A.idealquot_unitsub_closuretwole
          (n := n) hn x hx)
      g

lemma
    GCAmbien.idealquot_unitspan_powertwole
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hclosed : A.ClosedAugPower n)
    (hn : 2 ≤ n) :
    A.ideal_quotcanon_unitspan n ≤
      A.ideal_quotbounded_wordspan n := by
  exact
    A.idealquot_unitspan_subonemem
      (n := n)
      (fun g =>
        A.idealquot_unitsub_powertwole
          (n := n) hclosed hn g)

lemma
    GCAmbien.idealquot_boundedwordeq_powertwole
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan)
    (hclosed : A.ClosedAugPower n)
    (hn : 2 ≤ n) :
    A.ideal_quotbounded_wordspan n = ⊤ := by
  have hcanonical_dense :
      closure
        ((A.ideal_quotcanon_unitspan n :
          Set (A.completedGroupAlgebra ⧸
            (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)))) = Set.univ := by
    exact
      A.idealquot_unitspanspan_closedaugpower
        hdense hclosed
  have hbounded_closed :
      IsClosed
        ((A.ideal_quotbounded_wordspan n :
          Set (A.completedGroupAlgebra ⧸
            (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)))) := by
    exact A.idealquot_boundedword_closedaugpower hclosed
  have hcanonical_le :
      A.ideal_quotcanon_unitspan n ≤
        A.ideal_quotbounded_wordspan n := by
    exact
      A.idealquot_unitspan_powertwole
        hclosed hn
  exact
    A.idealquot_boundedwordeq_closedspanle
      hcanonical_dense hbounded_closed hcanonical_le

lemma dense_spanning_ambient
    {R : Type*} {M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M]
    {ι : Type*} [Finite ι]
    (w : ι → M)
    (hspan : Submodule.span R (Set.range w) = ⊤) :
    Module.Finite R M := by
  rw [Module.finite_def]
  exact
    Submodule.fg_def.mpr
      ⟨Set.range w, Set.finite_range w, hspan⟩

structure GCAmbien.FinIdealquotSpanningfam
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type (u + 2) where
  power_two_sided :
    (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra).IsTwoSided
  index : Type (u + 1)
  [finite_index : Finite index]
  quotientWord :
    index →
      A.completedGroupAlgebra ⧸
        (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)
  quotient_span_top :
    letI : (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra).IsTwoSided :=
      power_two_sided
    Submodule.span (ZMod p) (Set.range quotientWord) = ⊤

attribute [instance]
  GCAmbien.FinIdealquotSpanningfam.finite_index

lemma
    GCAmbien.finideal_quotaug_finspanningfam
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (F : A.FinIdealquotSpanningfam n) :
    Finite (A.completedGroupAlgebra ⧸
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)) := by
  letI :
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra).IsTwoSided :=
    F.power_two_sided
  letI : Finite F.index := F.finite_index
  have hmodule_finite :
      Module.Finite (ZMod p)
        (A.completedGroupAlgebra ⧸
          (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)) := by
    exact
      dense_spanning_ambient
        (R := ZMod p)
        (M := A.completedGroupAlgebra ⧸
          (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra))
        F.quotientWord
        F.quotient_span_top
  haveI :
      Module.Finite (ZMod p)
        (A.completedGroupAlgebra ⧸
          (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)) :=
    hmodule_finite
  haveI : Finite (ZMod p) := by
    haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
    infer_instance
  exact Module.finite_of_finite (ZMod p)

lemma
    GCAmbien.existsfin_idealquot_powertwole
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan)
    (hclosed : A.ClosedAugPower n)
    (_hn : 2 ≤ n) :
    Nonempty (A.FinIdealquotSpanningfam n) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  have hI_two_sided :
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra).IsTwoSided := by
    infer_instance
  have hspan :
      A.ideal_quotbounded_wordspan n = ⊤ := by
    exact
      A.idealquot_boundedwordeq_powertwole
        hdense hclosed _hn
  refine ⟨?_⟩
  exact
    { power_two_sided := hI_two_sided
      index := ULift.{u + 1} (denseGeneratorsIndex d n)
      finite_index := dense_generators_index d n
      quotientWord := fun w =>
        A.ideal_quot_boundedword (n := n) w.down
      quotient_span_top := by
        simpa [GCAmbien.ideal_quotbounded_wordspan]
          using hspan }

lemma
    GCAmbien.finideal_quotaug_powertwole
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan)
    (hclosed : A.ClosedAugPower n)
    (_hn : 2 ≤ n) :
    Finite (A.completedGroupAlgebra ⧸
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)) := by
  rcases
    A.existsfin_idealquot_powertwole
      hdense hclosed _hn with
    ⟨F⟩
  exact A.finideal_quotaug_finspanningfam F

lemma
    GCAmbien.openaug_powerpower_twole
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan)
    (hclosed : A.ClosedAugPower n)
    (hn : 2 ≤ n) :
    IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
      Set A.completedGroupAlgebra) := by
  have haugmentation_two_sided : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  letI : A.augmentationIdeal.IsTwoSided := haugmentation_two_sided
  let I : Ideal A.completedGroupAlgebra := A.augmentationIdeal ^ n
  have hI_two_sided : I.IsTwoSided := by
    dsimp [I]
    infer_instance
  letI : I.IsTwoSided := hI_two_sided
  have hI_closed : IsClosed (I : Set A.completedGroupAlgebra) := by
    simpa [I, GCAmbien.ClosedAugPower]
      using hclosed
  have hfinite :
      Finite (A.completedGroupAlgebra ⧸ I) := by
    simpa [I] using
      A.finideal_quotaug_powertwole
        hdense hclosed hn
  have hI_open : IsOpen (I : Set A.completedGroupAlgebra) := by
    exact ideal_open_closed I hI_closed hfinite
  simpa [I] using hI_open

structure GCAmbien.FinLeftgenAugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type (u + 2) where
  leftGeneratingFamily :
    DGFam
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)

lemma
    GCAmbien.closedaug_powerfin_leftaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (G : A.FinLeftgenAugpower n) :
    A.ClosedAugPower n := by
  have hclosed :
      IsClosed ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) := by
    exact G.leftGeneratingFamily.isClosed_ideal
  simpa [GCAmbien.ClosedAugPower]
    using hclosed

noncomputable def GCAmbien.signedAugmentationFactor
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : denseGeneratorsLetter d) :
    A.completedGroupAlgebra :=
  (A.canonicalUnit (denseLetterElement s a) :
      A.completedGroupAlgebra) - 1

lemma GCAmbien.signedaug_factormem_augideal
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : denseGeneratorsLetter d) :
    A.signedAugmentationFactor a ∈ A.augmentationIdeal := by
  simpa [GCAmbien.signedAugmentationFactor]
    using A.idealquot_signedaugfactor_memaugideal a

noncomputable def GCAmbien.signedaug_letterleft_spanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Set A.completedGroupAlgebra :=
  Set.range
    (fun coeff :
        ULift.{u} (denseGeneratorsLetter d) →
          A.completedGroupAlgebra =>
      ∑ a : ULift.{u} (denseGeneratorsLetter d),
        coeff a * A.signedAugmentationFactor a.down)

lemma GCAmbien.zeromem_signedaugletter_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (0 : A.completedGroupAlgebra) ∈ A.signedaug_letterleft_spanset := by
  classical
  refine ⟨fun _ => 0, ?_⟩
  simp

lemma GCAmbien.addmem_signedaugletter_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x y : A.completedGroupAlgebra}
    (hx : x ∈ A.signedaug_letterleft_spanset)
    (hy : y ∈ A.signedaug_letterleft_spanset) :
    x + y ∈ A.signedaug_letterleft_spanset := by
  classical
  rcases hx with ⟨cx, rfl⟩
  rcases hy with ⟨cy, rfl⟩
  refine ⟨fun a => cx a + cy a, ?_⟩
  simp [add_mul, Finset.sum_add_distrib]

lemma GCAmbien.leftmulmem_signedaugletter_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (r : A.completedGroupAlgebra)
    {x : A.completedGroupAlgebra}
    (hx : x ∈ A.signedaug_letterleft_spanset) :
    r * x ∈ A.signedaug_letterleft_spanset := by
  classical
  rcases hx with ⟨cx, rfl⟩
  refine ⟨fun a => r * cx a, ?_⟩
  simp [Finset.mul_sum, mul_assoc]

lemma GCAmbien.signedaug_factormem_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : denseGeneratorsLetter d) :
  A.signedAugmentationFactor a ∈ A.signedaug_letterleft_spanset := by
  classical
  refine ⟨fun b => if b = ULift.up a then 1 else 0, ?_⟩
  change
    (∑ b : ULift.{u} (denseGeneratorsLetter d),
      (if b = ULift.up a then 1 else 0) *
        A.signedAugmentationFactor b.down) =
      A.signedAugmentationFactor a
  rw [Fintype.sum_eq_single (ULift.up a)]
  · simp
  · intro b hb
    simp [hb]

lemma
    GCAmbien.unitsub_onemem_setsignedword
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (w : List (denseGeneratorsLetter d)) :
    (A.canonicalUnit (denseSignedElement s w) :
        A.completedGroupAlgebra) - 1 ∈
      A.signedaug_letterleft_spanset := by
  induction w with
  | nil =>
      have hzero :
          (A.canonicalUnit (denseSignedElement s []) :
              A.completedGroupAlgebra) - 1 = 0 := by
        simp [denseSignedElement]
      rw [hzero]
      exact A.zeromem_signedaugletter_leftspanset
  | cons a w ih =>
      have htail :
          (A.canonicalUnit (denseSignedElement s w) :
              A.completedGroupAlgebra) - 1 ∈
            A.signedaug_letterleft_spanset :=
        ih
      have hleft :
          (A.canonicalUnit (denseLetterElement s a) :
              A.completedGroupAlgebra) *
              ((A.canonicalUnit (denseSignedElement s w) :
                A.completedGroupAlgebra) - 1) ∈
            A.signedaug_letterleft_spanset :=
        A.leftmulmem_signedaugletter_leftspanset
          (A.canonicalUnit (denseLetterElement s a) :
            A.completedGroupAlgebra)
          htail
      have hletter :
          A.signedAugmentationFactor a ∈
            A.signedaug_letterleft_spanset :=
        A.signedaug_factormem_leftspanset a
      have hsum :
          (A.canonicalUnit (denseLetterElement s a) :
              A.completedGroupAlgebra) *
              ((A.canonicalUnit (denseSignedElement s w) :
                A.completedGroupAlgebra) - 1) +
            A.signedAugmentationFactor a ∈
            A.signedaug_letterleft_spanset :=
        A.addmem_signedaugletter_leftspanset hleft hletter
      have heq :
          (A.canonicalUnit (denseSignedElement s (a :: w)) :
              A.completedGroupAlgebra) - 1 =
            (A.canonicalUnit (denseLetterElement s a) :
                A.completedGroupAlgebra) *
                ((A.canonicalUnit (denseSignedElement s w) :
                  A.completedGroupAlgebra) - 1) +
              A.signedAugmentationFactor a := by
        rw [dense_element_cons]
        simp only [map_mul, Units.val_mul,
          GCAmbien.signedAugmentationFactor]
        noncomm_ring
      rw [heq]
      exact hsum

lemma
    GCAmbien.unitsub_onemem_setmemclosure
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {g : Γ}
    (hg : g ∈ Subgroup.closure (Set.range s)) :
    (A.canonicalUnit g : A.completedGroupAlgebra) - 1 ∈
      A.signedaug_letterleft_spanset := by
  rcases dense_element_closure
      (s := s) hg with
    ⟨w, hw⟩
  have hword :
      (A.canonicalUnit (denseSignedElement s w) :
          A.completedGroupAlgebra) - 1 ∈
        A.signedaug_letterleft_spanset :=
    A.unitsub_onemem_setsignedword w
  simpa [hw] using hword

lemma
    GCAmbien.unitsub_onememletter_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (g : Γ) :
    (A.canonicalUnit g : A.completedGroupAlgebra) - 1 ∈
      closure A.signedaug_letterleft_spanset := by
  let S : Set A.completedGroupAlgebra :=
    A.signedaug_letterleft_spanset
  let f : Γ → A.completedGroupAlgebra := fun x =>
    (A.canonicalUnit x : A.completedGroupAlgebra) - 1
  have hcanonical :
      Continuous fun x : Γ => (A.canonicalUnit x : A.completedGroupAlgebra) :=
    Units.continuous_val.comp A.canonicalUnit_continuous
  have hf : Continuous f := by
    exact hcanonical.sub continuous_const
  have hclosed_preimage : IsClosed (f ⁻¹' closure S) :=
    isClosed_closure.preimage hf
  have hdense :
      closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) =
        Set.univ := by
    simpa [Subgroup.topologicalClosure_coe] using
      congrArg (fun H : Subgroup Γ => (H : Set Γ)) hs
  have hsubset :
      ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) ⊆
        f ⁻¹' closure S := by
    intro x hx
    exact
      subset_closure
        (A.unitsub_onemem_setmemclosure
          hx)
  have hclosure_subset :
      closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) ⊆
        f ⁻¹' closure S :=
    closure_minimal hsubset hclosed_preimage
  have hg :
      g ∈ closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) := by
    rw [hdense]
    exact Set.mem_univ g
  exact hclosure_subset hg

abbrev denseAugmentationIndex (d n : ℕ) : Type :=
  List.Vector (denseGeneratorsLetter d) n

                                                         
@[reducible] noncomputable def dense_fintype_index
    (d n : ℕ) :
    Fintype (ULift.{u} (denseAugmentationIndex d n)) := by
  classical
  dsimp [denseAugmentationIndex,
    denseGeneratorsLetter]
  infer_instance

noncomputable def GCAmbien.aug_power_wordgen
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (w : denseAugmentationIndex d n) :
    A.completedGroupAlgebra :=
  (w.toList.map fun a => A.signedAugmentationFactor a).prod

lemma GCAmbien.aug_powerword_genmem
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (w : denseAugmentationIndex d n) :
    A.aug_power_wordgen w ∈ A.augmentationIdeal ^ n := by
  have hmem :
      (w.toList.map fun a =>
          (A.canonicalUnit (denseLetterElement s a) :
              A.completedGroupAlgebra) - 1).prod ∈
        A.augmentationIdeal ^ w.toList.length := by
    exact A.idealquot_signaugfact_prodmempower w.toList
  simpa [GCAmbien.aug_power_wordgen,
    GCAmbien.signedAugmentationFactor]
    using hmem

noncomputable def GCAmbien.augpower_wordleft_spanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Set A.completedGroupAlgebra :=
  Set.range
    (fun coeff :
        ULift.{u} (denseAugmentationIndex d n) →
          A.completedGroupAlgebra =>
      ∑ w : ULift.{u} (denseAugmentationIndex d n),
        coeff w * A.aug_power_wordgen w.down)

structure GCAmbien.AugIdealletterDensespan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type (u + 2) where
  dense_span :
    (A.augmentationIdeal : Set A.completedGroupAlgebra) ⊆
      closure A.signedaug_letterleft_spanset

noncomputable def
    GCAmbien.augideal_fintopo_leftgenfam
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.AugIdealletterDensespan) :
    TGFam A.augmentationIdeal := by
  classical
  exact
    { index := ULift.{u} (denseGeneratorsLetter d)
      finite_index := inferInstance
      generator := fun a => A.signedAugmentationFactor a.down
      generator_mem := fun a =>
        A.signedaug_factormem_augideal a.down
      dense_span := by
        simpa [GCAmbien.signedaug_letterleft_spanset]
          using H.dense_span }

structure GCAmbien.AugPowerwordDensespan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type (u + 2) where
  dense_span :
    ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) ⊆
      closure
        (Set.range
          (fun coeff :
              ULift.{u} (denseAugmentationIndex d n) →
                A.completedGroupAlgebra =>
            ∑ w : ULift.{u} (denseAugmentationIndex d n),
              coeff w * A.aug_power_wordgen w.down))

lemma GCAmbien.aug_powerword_genzero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (w : denseAugmentationIndex d 0) :
    A.aug_power_wordgen w = 1 := by
  rw [List.Vector.eq_nil w]
  simp [GCAmbien.aug_power_wordgen]

lemma GCAmbien.memaug_powerwordleft_spansetzero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (x : A.completedGroupAlgebra) :
    x ∈ A.augpower_wordleft_spanset 0 := by
  classical
  refine ⟨fun _ => x, ?_⟩
  change
    (∑ w : ULift.{u} (denseAugmentationIndex d 0),
      x * A.aug_power_wordgen w.down) = x
  rw [Fintype.sum_eq_single (ULift.up (List.Vector.nil :
      denseAugmentationIndex d 0))]
  · simp [GCAmbien.aug_powerword_genzero]
  · intro b hb
    have hbempty :
        b = ULift.up (List.Vector.nil :
          denseAugmentationIndex d 0) := by
      cases b with
      | up w =>
          simp [List.Vector.eq_nil w]
    exact False.elim (hb hbempty)

lemma GCAmbien.augpowerword_leftspanset_zeroequniv
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.augpower_wordleft_spanset 0 = Set.univ := by
  ext x
  constructor
  · intro _hx
    exact Set.mem_univ x
  · intro _hx
    exact A.memaug_powerwordleft_spansetzero x

lemma GCAmbien.zeromem_augpowerword_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (0 : A.completedGroupAlgebra) ∈ A.augpower_wordleft_spanset n := by
  classical
  refine ⟨fun _ => 0, ?_⟩
  simp

lemma GCAmbien.addmem_augpowerword_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x y : A.completedGroupAlgebra}
    (hx : x ∈ A.augpower_wordleft_spanset n)
    (hy : y ∈ A.augpower_wordleft_spanset n) :
    x + y ∈ A.augpower_wordleft_spanset n := by
  classical
  rcases hx with ⟨cx, rfl⟩
  rcases hy with ⟨cy, rfl⟩
  refine ⟨fun w => cx w + cy w, ?_⟩
  simp [add_mul, Finset.sum_add_distrib]

lemma GCAmbien.leftmulmem_augpowerword_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (r : A.completedGroupAlgebra)
    {x : A.completedGroupAlgebra}
    (hx : x ∈ A.augpower_wordleft_spanset n) :
    r * x ∈ A.augpower_wordleft_spanset n := by
  classical
  rcases hx with ⟨cx, rfl⟩
  refine ⟨fun w => r * cx w, ?_⟩
  simp [Finset.mul_sum, mul_assoc]

lemma GCAmbien.augpower_wordgenmem_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (w : denseAugmentationIndex d n) :
    A.aug_power_wordgen w ∈ A.augpower_wordleft_spanset n := by
  classical
  refine ⟨fun v => if v = ULift.up w then 1 else 0, ?_⟩
  change
    (∑ v : ULift.{u} (denseAugmentationIndex d n),
      (if v = ULift.up w then 1 else 0) *
        A.aug_power_wordgen v.down) =
      A.aug_power_wordgen w
  rw [Fintype.sum_eq_single (ULift.up w)]
  · simp
  · intro v hv
    simp [hv]

lemma GCAmbien.finsetsummem_augpowerword_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {ι : Type u} (t : Finset ι) (f : ι → A.completedGroupAlgebra)
    (hf : ∀ i ∈ t, f i ∈ A.augpower_wordleft_spanset n) :
    t.sum f ∈ A.augpower_wordleft_spanset n := by
  classical
  revert hf
  refine Finset.induction_on t ?zero ?insert
  · intro _hf
    simpa using A.zeromem_augpowerword_leftspanset (n := n)
  · intro i t hit ih hf
    rw [Finset.sum_insert hit]
    exact
      A.addmem_augpowerword_leftspanset
        (hf i (Finset.mem_insert_self i t))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma
    GCAmbien.leftmul_memclosureword_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (r : A.completedGroupAlgebra)
    {x : A.completedGroupAlgebra}
    (hx : x ∈ closure (A.augpower_wordleft_spanset n)) :
    r * x ∈ closure (A.augpower_wordleft_spanset n) := by
  let S : Set A.completedGroupAlgebra := A.augpower_wordleft_spanset n
  have hcont : Continuous fun y : A.completedGroupAlgebra => r * y :=
    continuous_const.mul continuous_id
  have hx_image :
      r * x ∈ closure ((fun y : A.completedGroupAlgebra => r * y) '' S) := by
    exact mem_closure_image hcont.continuousAt (by simpa [S] using hx)
  have himage_subset :
      (fun y : A.completedGroupAlgebra => r * y) '' S ⊆ closure S := by
    rintro y ⟨z, hz, rfl⟩
    exact subset_closure
      (A.leftmulmem_augpowerword_leftspanset (n := n) r (by simpa [S] using hz))
  exact closure_minimal himage_subset isClosed_closure hx_image

lemma GCAmbien.aug_powerword_gencons
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (a : denseGeneratorsLetter d)
    (w : denseAugmentationIndex d n) :
    A.aug_power_wordgen (List.Vector.cons a w) =
      A.signedAugmentationFactor a * A.aug_power_wordgen w := by
  simp [GCAmbien.aug_power_wordgen,
    List.Vector.toList_cons]

lemma
    GCAmbien.leftmul_signedaugsucc_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (r : A.completedGroupAlgebra)
    (a : denseGeneratorsLetter d)
    (w : denseAugmentationIndex d n) :
    r * (A.signedAugmentationFactor a * A.aug_power_wordgen w) ∈
      A.augpower_wordleft_spanset (n + 1) := by
  have hgen :
      A.aug_power_wordgen (List.Vector.cons a w) ∈
        A.augpower_wordleft_spanset (n + 1) :=
    A.augpower_wordgenmem_leftspanset (List.Vector.cons a w)
  have hproduct :
      A.signedAugmentationFactor a * A.aug_power_wordgen w ∈
        A.augpower_wordleft_spanset (n + 1) := by
    simpa [GCAmbien.aug_powerword_gencons]
      using hgen
  exact A.leftmulmem_augpowerword_leftspanset (n := n + 1) r hproduct

lemma
    GCAmbien.mulaug_powerwordletter_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {z : A.completedGroupAlgebra}
    (hz : z ∈ A.signedaug_letterleft_spanset)
    (w : denseAugmentationIndex d n) :
    z * A.aug_power_wordgen w ∈
      A.augpower_wordleft_spanset (n + 1) := by
  classical
  rcases hz with ⟨coeff, rfl⟩
  have hsum :
      (∑ a : ULift.{u} (denseGeneratorsLetter d),
        coeff a *
          (A.signedAugmentationFactor a.down *
            A.aug_power_wordgen w)) ∈
        A.augpower_wordleft_spanset (n + 1) := by
    refine
      A.finsetsummem_augpowerword_leftspanset
        (n := n + 1) Finset.univ
        (fun a =>
          coeff a *
            (A.signedAugmentationFactor a.down *
              A.aug_power_wordgen w)) ?_
    intro a _ha
    exact
      A.leftmul_signedaugsucc_leftspanset
        (n := n) (coeff a) a.down w
  have hrewrite :
      (∑ a : ULift.{u} (denseGeneratorsLetter d),
        coeff a * A.signedAugmentationFactor a.down) *
          A.aug_power_wordgen w =
        ∑ a : ULift.{u} (denseGeneratorsLetter d),
          coeff a *
            (A.signedAugmentationFactor a.down *
              A.aug_power_wordgen w) := by
    simp [Finset.sum_mul, mul_assoc]
  rw [hrewrite]
  exact hsum

lemma
    GCAmbien.signedaug_factormulsucc_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.AugIdealletterDensespan)
    (a : denseGeneratorsLetter d)
    (r : A.completedGroupAlgebra)
    (w : denseAugmentationIndex d n) :
    A.signedAugmentationFactor a * r * A.aug_power_wordgen w ∈
      closure (A.augpower_wordleft_spanset (n + 1)) := by
  letI : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  let x : A.completedGroupAlgebra := A.signedAugmentationFactor a * r
  let W : A.completedGroupAlgebra := A.aug_power_wordgen w
  have hxI : x ∈ A.augmentationIdeal := by
    dsimp [x]
    exact A.augmentationIdeal.mul_mem_right r
      (A.signedaug_factormem_augideal a)
  have hxclosure :
      x ∈ closure A.signedaug_letterleft_spanset :=
    H.dense_span hxI
  have hcont : Continuous fun z : A.completedGroupAlgebra => z * W :=
    continuous_id.mul continuous_const
  have hximage :
      x * W ∈
        closure
          ((fun z : A.completedGroupAlgebra => z * W) ''
            A.signedaug_letterleft_spanset) := by
    exact mem_closure_image hcont.continuousAt hxclosure
  have himage_subset :
      ((fun z : A.completedGroupAlgebra => z * W) ''
          A.signedaug_letterleft_spanset) ⊆
        closure (A.augpower_wordleft_spanset (n + 1)) := by
    rintro y ⟨z, hz, rfl⟩
    exact subset_closure
      (A.mulaug_powerwordletter_leftspanset
        (n := n) hz w)
  have hxsucc :
      x * W ∈ closure (A.augpower_wordleft_spanset (n + 1)) :=
    closure_minimal himage_subset isClosed_closure hximage
  simpa [x, W, mul_assoc] using hxsucc

lemma GCAmbien.zeromemclosure_augpowerword_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (0 : A.completedGroupAlgebra) ∈ closure (A.augpower_wordleft_spanset n) := by
  exact subset_closure (A.zeromem_augpowerword_leftspanset (n := n))

lemma GCAmbien.addmemclosure_augpowerword_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x y : A.completedGroupAlgebra}
    (hx : x ∈ closure (A.augpower_wordleft_spanset n))
    (hy : y ∈ closure (A.augpower_wordleft_spanset n)) :
    x + y ∈ closure (A.augpower_wordleft_spanset n) := by
  let S : Set A.completedGroupAlgebra := A.augpower_wordleft_spanset n
  have hactual_add_right :
      ∀ z ∈ S, z + y ∈ closure S := by
    intro z hz
    have hcont : Continuous fun t : A.completedGroupAlgebra => z + t :=
      continuous_const.add continuous_id
    have hyimage :
        z + y ∈ closure ((fun t : A.completedGroupAlgebra => z + t) '' S) := by
      exact mem_closure_image hcont.continuousAt (by simpa [S] using hy)
    have himage_subset :
        ((fun t : A.completedGroupAlgebra => z + t) '' S) ⊆ closure S := by
      rintro w ⟨t, ht, rfl⟩
      exact subset_closure
        (A.addmem_augpowerword_leftspanset
          (n := n) (by simpa [S] using hz) (by simpa [S] using ht))
    exact closure_minimal himage_subset isClosed_closure hyimage
  have hcont : Continuous fun z : A.completedGroupAlgebra => z + y :=
    continuous_id.add continuous_const
  have hximage :
      x + y ∈ closure ((fun z : A.completedGroupAlgebra => z + y) '' S) := by
    exact mem_closure_image hcont.continuousAt (by simpa [S] using hx)
  have himage_subset :
      ((fun z : A.completedGroupAlgebra => z + y) '' S) ⊆ closure S := by
    rintro w ⟨z, hz, rfl⟩
    exact hactual_add_right z hz
  exact closure_minimal himage_subset isClosed_closure hximage

lemma
    GCAmbien.finsetsum_memclosureword_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {ι : Type u} (t : Finset ι) (f : ι → A.completedGroupAlgebra)
    (hf : ∀ i ∈ t, f i ∈ closure (A.augpower_wordleft_spanset n)) :
    t.sum f ∈ closure (A.augpower_wordleft_spanset n) := by
  classical
  revert hf
  refine Finset.induction_on t ?zero ?insert
  · intro _hf
    simpa using A.zeromemclosure_augpowerword_leftspanset (n := n)
  · intro i t hit ih hf
    rw [Finset.sum_insert hit]
    exact
      A.addmemclosure_augpowerword_leftspanset
        (hf i (Finset.mem_insert_self i t))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

noncomputable def
    GCAmbien.augpower_wordclosure_leftideal
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (n : ℕ) : Ideal A.completedGroupAlgebra where
  carrier := closure (A.augpower_wordleft_spanset n)
  zero_mem' := by
    exact A.zeromemclosure_augpowerword_leftspanset (n := n)
  add_mem' := by
    intro x y hx hy
    exact
      A.addmemclosure_augpowerword_leftspanset
        (n := n) hx hy
  smul_mem' := by
    intro r x hx
    change r * x ∈ closure (A.augpower_wordleft_spanset n)
    exact
      A.leftmul_memclosureword_leftspanset
        (n := n) r hx

lemma
    GCAmbien.memaug_powewordclos_leftidealiff
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x : A.completedGroupAlgebra} :
    x ∈ A.augpower_wordclosure_leftideal n ↔
      x ∈ closure (A.augpower_wordleft_spanset n) := by
  rfl

lemma
    GCAmbien.signedaugfactor_mulleftword_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.AugIdealletterDensespan)
    (a : denseGeneratorsLetter d)
    (r : A.completedGroupAlgebra)
    {y : A.completedGroupAlgebra}
    (hy : y ∈ A.augpower_wordleft_spanset n) :
    A.signedAugmentationFactor a * r * y ∈
      closure (A.augpower_wordleft_spanset (n + 1)) := by
  classical
  rcases hy with ⟨coeff, rfl⟩
  have hsum :
      (∑ w : ULift.{u} (denseAugmentationIndex d n),
        A.signedAugmentationFactor a * (r * coeff w) *
          A.aug_power_wordgen w.down) ∈
        closure (A.augpower_wordleft_spanset (n + 1)) := by
    refine
      A.finsetsum_memclosureword_leftspanset
        (n := n + 1) Finset.univ
        (fun w =>
          A.signedAugmentationFactor a * (r * coeff w) *
            A.aug_power_wordgen w.down) ?_
    intro w _hw
    exact
      A.signedaug_factormulsucc_leftspanset
        (n := n) H a (r * coeff w) w.down
  have hrewrite :
      A.signedAugmentationFactor a * r *
          (∑ w : ULift.{u} (denseAugmentationIndex d n),
            coeff w * A.aug_power_wordgen w.down) =
        ∑ w : ULift.{u} (denseAugmentationIndex d n),
          A.signedAugmentationFactor a * (r * coeff w) *
            A.aug_power_wordgen w.down := by
    simp [Finset.mul_sum, mul_assoc]
  rw [hrewrite]
  exact hsum

lemma
    GCAmbien.signedaugfactor_mulspanword_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.AugIdealletterDensespan)
    (a : denseGeneratorsLetter d)
    (r : A.completedGroupAlgebra)
    {y : A.completedGroupAlgebra}
    (hy : y ∈ closure (A.augpower_wordleft_spanset n)) :
    A.signedAugmentationFactor a * r * y ∈
      closure (A.augpower_wordleft_spanset (n + 1)) := by
  let T : Set A.completedGroupAlgebra := A.augpower_wordleft_spanset n
  let U : Set A.completedGroupAlgebra := A.augpower_wordleft_spanset (n + 1)
  have hcont :
      Continuous fun y : A.completedGroupAlgebra =>
        A.signedAugmentationFactor a * r * y :=
    continuous_const.mul continuous_id
  have hyimage :
      A.signedAugmentationFactor a * r * y ∈
        closure
          ((fun t : A.completedGroupAlgebra =>
            A.signedAugmentationFactor a * r * t) '' T) := by
    exact mem_closure_image hcont.continuousAt (by simpa [T] using hy)
  have himage_subset :
      ((fun t : A.completedGroupAlgebra =>
          A.signedAugmentationFactor a * r * t) '' T) ⊆ closure U := by
    rintro z ⟨t, ht, rfl⟩
    exact
      A.signedaugfactor_mulleftword_leftspanset
        (n := n) H a r (by simpa [T] using ht)
  exact closure_minimal himage_subset isClosed_closure hyimage

lemma
    GCAmbien.mulmemclosure_succleftword_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.AugIdealletterDensespan)
    {z y : A.completedGroupAlgebra}
    (hz : z ∈ A.signedaug_letterleft_spanset)
    (hy : y ∈ closure (A.augpower_wordleft_spanset n)) :
    z * y ∈ closure (A.augpower_wordleft_spanset (n + 1)) := by
  classical
  rcases hz with ⟨coeff, rfl⟩
  have hsum :
      (∑ a : ULift.{u} (denseGeneratorsLetter d),
        coeff a * (A.signedAugmentationFactor a.down * y)) ∈
        closure (A.augpower_wordleft_spanset (n + 1)) := by
    refine
      A.finsetsum_memclosureword_leftspanset
        (n := n + 1) Finset.univ
        (fun a => coeff a * (A.signedAugmentationFactor a.down * y)) ?_
    intro a _ha
    have hletter_tail :
        A.signedAugmentationFactor a.down * y ∈
          closure (A.augpower_wordleft_spanset (n + 1)) := by
      simpa [mul_assoc] using
        A.signedaugfactor_mulspanword_leftspanset
          (n := n) H a.down 1 hy
    exact
      A.leftmul_memclosureword_leftspanset
        (n := n + 1) (coeff a) hletter_tail
  have hrewrite :
      (∑ a : ULift.{u} (denseGeneratorsLetter d),
        coeff a * A.signedAugmentationFactor a.down) * y =
        ∑ a : ULift.{u} (denseGeneratorsLetter d),
          coeff a * (A.signedAugmentationFactor a.down * y) := by
    simp [Finset.sum_mul, mul_assoc]
  rw [hrewrite]
  exact hsum

lemma
    GCAmbien.mulmemclosure_succidealword_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.AugIdealletterDensespan)
    {x y : A.completedGroupAlgebra}
    (hx : x ∈ A.augmentationIdeal)
    (hy : y ∈ closure (A.augpower_wordleft_spanset n)) :
    x * y ∈ closure (A.augpower_wordleft_spanset (n + 1)) := by
  let S : Set A.completedGroupAlgebra := A.signedaug_letterleft_spanset
  let U : Set A.completedGroupAlgebra := A.augpower_wordleft_spanset (n + 1)
  have hxclosure : x ∈ closure S := by
    simpa [S] using H.dense_span hx
  have hcont : Continuous fun z : A.completedGroupAlgebra => z * y :=
    continuous_id.mul continuous_const
  have hximage :
      x * y ∈ closure ((fun z : A.completedGroupAlgebra => z * y) '' S) := by
    exact mem_closure_image hcont.continuousAt hxclosure
  have himage_subset :
      ((fun z : A.completedGroupAlgebra => z * y) '' S) ⊆ closure U := by
    rintro w ⟨z, hz, rfl⟩
    exact
      A.mulmemclosure_succleftword_leftspanset
        (n := n) H (by simpa [S] using hz) hy
  exact closure_minimal himage_subset isClosed_closure hximage

lemma
    GCAmbien.mulmem_closuresucc_memaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.AugIdealletterDensespan)
    (IH : A.AugPowerwordDensespan n)
    {x y : A.completedGroupAlgebra}
    (hx : x ∈ A.augmentationIdeal)
    (hy : y ∈ A.augmentationIdeal ^ n) :
    x * y ∈ closure (A.augpower_wordleft_spanset (n + 1)) := by
  have hyclosure : y ∈ closure (A.augpower_wordleft_spanset n) := by
    simpa [GCAmbien.augpower_wordleft_spanset]
      using IH.dense_span hy
  exact
    A.mulmemclosure_succidealword_leftspanset
      (n := n) H hx hyclosure

lemma
    GCAmbien.augideal_mulaugclosure_leftidealsucc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.AugIdealletterDensespan)
    (IH : A.AugPowerwordDensespan n) :
    A.augmentationIdeal * A.augmentationIdeal ^ n ≤
      A.augpower_wordclosure_leftideal (n + 1) := by
  rw [Ideal.mul_le]
  intro x hx y hy
  change x * y ∈ closure (A.augpower_wordleft_spanset (n + 1))
  exact
    A.mulmem_closuresucc_memaugpower
      (n := n) H IH hx hy

lemma
    GCAmbien.memclosure_succleftideal_mulaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.AugIdealletterDensespan)
    (IH : A.AugPowerwordDensespan n)
    {x : A.completedGroupAlgebra}
    (hx : x ∈ A.augmentationIdeal * A.augmentationIdeal ^ n) :
    x ∈ closure (A.augpower_wordleft_spanset (n + 1)) := by
  have hle :
      A.augmentationIdeal * A.augmentationIdeal ^ n ≤
        A.augpower_wordclosure_leftideal (n + 1) :=
    A.augideal_mulaugclosure_leftidealsucc
      (n := n) H IH
  exact
    (A.memaug_powewordclos_leftidealiff
      (n := n + 1)).1 (hle hx)

lemma
    GCAmbien.memclosure_succleftmem_augpowersucc
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.AugIdealletterDensespan)
    (IH : A.AugPowerwordDensespan n)
    {x : A.completedGroupAlgebra}
    (hx : x ∈ A.augmentationIdeal ^ (n + 1)) :
    x ∈ closure (A.augpower_wordleft_spanset (n + 1)) := by
  letI : A.augmentationIdeal.IsTwoSided := by
    rw [A.augmentation_ideal_ker]
    infer_instance
  have hxprod : x ∈ A.augmentationIdeal * A.augmentationIdeal ^ n := by
    simpa [Ideal.IsTwoSided.pow_succ] using hx
  exact
    A.memclosure_succleftideal_mulaugpower
      (n := n) H IH hxprod

lemma
    GCAmbien.existsaug_powerword_densespanzero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Nonempty (A.AugPowerwordDensespan 0) := by
  refine ⟨{ dense_span := ?_ }⟩
  intro x _hx
  exact
    subset_closure
      (by
        simpa [
          GCAmbien.augpower_wordleft_spanset
        ] using A.memaug_powerwordleft_spansetzero x)

lemma
    GCAmbien.existsaugpower_wordsuccideal_letterdensespan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.AugIdealletterDensespan)
    (IH : Nonempty (A.AugPowerwordDensespan n)) :
    Nonempty (A.AugPowerwordDensespan (n + 1)) := by
  rcases IH with ⟨IHn⟩
  refine ⟨{ dense_span := ?_ }⟩
  intro x hx
  exact
    A.memclosure_succleftmem_augpowersucc
      (n := n) H IHn hx

lemma
    GCAmbien.existsaugpower_wordspanideal_letterdensespan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.AugIdealletterDensespan) :
    Nonempty (A.AugPowerwordDensespan n) := by
  induction n with
  | zero =>
      exact A.existsaug_powerword_densespanzero
  | succ n ih =>
      exact
        A.existsaugpower_wordsuccideal_letterdensespan
          H ih

noncomputable def GCAmbien.canon_unit_linspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Submodule (ZMod p) A.completedGroupAlgebra :=
  Submodule.span (ZMod p)
    (Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))

noncomputable def GCAmbien.augmentationAdjustedElement
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (x : A.completedGroupAlgebra) :
    A.completedGroupAlgebra :=
  x - algebraMap (ZMod p) A.completedGroupAlgebra (A.augmentationMap x)

noncomputable def GCAmbien.aug_adjustedcanon_spanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Set A.completedGroupAlgebra :=
  A.augmentationAdjustedElement ''
    (A.canon_unit_linspan : Set A.completedGroupAlgebra)

lemma
    GCAmbien.closureunitlin_spaneqdense_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan) :
    closure (A.canon_unit_linspan : Set A.completedGroupAlgebra) = Set.univ := by
  simpa [
    GCAmbien.DenseAlgebraSpan,
    GCAmbien.canon_unit_linspan
  ] using hdense

lemma
    GCAmbien.memclosure_unitlindense_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan)
    (x : A.completedGroupAlgebra) :
    x ∈ closure (A.canon_unit_linspan : Set A.completedGroupAlgebra) := by
  have hclosure :
      closure (A.canon_unit_linspan : Set A.completedGroupAlgebra) = Set.univ :=
    A.closureunitlin_spaneqdense_unitalgspan hdense
  have hx_univ : x ∈ (Set.univ : Set A.completedGroupAlgebra) := by
    trivial
  simp [hclosure]

lemma GCAmbien.zeromem_clossignlett_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    (0 : A.completedGroupAlgebra) ∈
      closure A.signedaug_letterleft_spanset := by
  exact subset_closure A.zeromem_signedaugletter_leftspanset

lemma GCAmbien.addmem_clossignlett_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x y : A.completedGroupAlgebra}
    (hx : x ∈ closure A.signedaug_letterleft_spanset)
    (hy : y ∈ closure A.signedaug_letterleft_spanset) :
    x + y ∈ closure A.signedaug_letterleft_spanset := by
  refine map_mem_closure₂ continuous_add hx hy ?_
  intro a ha b hb
  exact A.addmem_signedaugletter_leftspanset ha hb

lemma
    GCAmbien.leftmul_memcloslett_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (r : A.completedGroupAlgebra)
    {x : A.completedGroupAlgebra}
    (hx : x ∈ closure A.signedaug_letterleft_spanset) :
    r * x ∈ closure A.signedaug_letterleft_spanset := by
  refine map_mem_closure (mulLeft_continuous r) hx ?_
  intro y hy
  exact A.leftmulmem_signedaugletter_leftspanset r hy

lemma GCAmbien.smulmem_clossignlett_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (c : ZMod p)
    {x : A.completedGroupAlgebra}
    (hx : x ∈ closure A.signedaug_letterleft_spanset) :
    c • x ∈ closure A.signedaug_letterleft_spanset := by
  have hmul :
      algebraMap (ZMod p) A.completedGroupAlgebra c * x ∈
        closure A.signedaug_letterleft_spanset :=
    A.leftmul_memcloslett_leftspanset
      (algebraMap (ZMod p) A.completedGroupAlgebra c) hx
  simpa [Algebra.smul_def] using hmul

lemma GCAmbien.aug_adjusted_elementzero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    A.augmentationAdjustedElement 0 = 0 := by
  simp [GCAmbien.augmentationAdjustedElement]

lemma GCAmbien.aug_adjusted_elementadd
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (x y : A.completedGroupAlgebra) :
    A.augmentationAdjustedElement (x + y) =
      A.augmentationAdjustedElement x + A.augmentationAdjustedElement y := by
  simp only [
    GCAmbien.augmentationAdjustedElement,
    map_add
  ]
  abel

lemma GCAmbien.aug_adjusted_elementsmul
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (c : ZMod p)
    (x : A.completedGroupAlgebra) :
    A.augmentationAdjustedElement (c • x) =
      c • A.augmentationAdjustedElement x := by
  have hself : algebraMap (ZMod p) (ZMod p) c = c := by
    simp
  simp only [
    GCAmbien.augmentationAdjustedElement,
    Algebra.smul_def,
    map_mul,
    AlgHom.commutes
  ]
  simp only [hself]
  rw [mul_sub]

lemma GCAmbien.aug_adjustedelement_canonunit
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (g : Γ) :
    A.augmentationAdjustedElement (A.canonicalUnit g : A.completedGroupAlgebra) =
      (A.canonicalUnit g : A.completedGroupAlgebra) - 1 := by
  simp [
    GCAmbien.augmentationAdjustedElement,
    A.canonicalUnit_augmentation g
  ]

lemma GCAmbien.aug_adjusted_elementcont
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Continuous A.augmentationAdjustedElement := by
  have hscalar :
      Continuous fun c : ZMod p =>
        algebraMap (ZMod p) A.completedGroupAlgebra c := by
    exact continuous_of_discreteTopology
  have hconstant_part :
      Continuous fun x : A.completedGroupAlgebra =>
        algebraMap (ZMod p) A.completedGroupAlgebra (A.augmentationMap x) :=
    hscalar.comp A.augmentationMap_continuous
  simpa [GCAmbien.augmentationAdjustedElement] using
    continuous_id.sub hconstant_part

lemma GCAmbien.augadjusted_elementeq_memaugideal
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    {x : A.completedGroupAlgebra}
    (hx : x ∈ A.augmentationIdeal) :
    A.augmentationAdjustedElement x = x := by
  have hxpreimage :
      x ∈ A.augmentationMap ⁻¹' ({0} : Set (ZMod p)) := by
    rw [← A.aug_idealeq_preimzero]
    exact hx
  have hxzero : A.augmentationMap x = 0 := by
    simpa using hxpreimage
  simp [
    GCAmbien.augmentationAdjustedElement,
    hxzero
  ]

lemma
    GCAmbien.augadjusted_spansetletter_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hsubone :
      ∀ g : Γ,
        (A.canonicalUnit g : A.completedGroupAlgebra) - 1 ∈
          closure A.signedaug_letterleft_spanset) :
    A.aug_adjustedcanon_spanset ⊆
      closure A.signedaug_letterleft_spanset := by
  rintro z ⟨y, hy, rfl⟩
  refine Submodule.span_induction
    (s := Set.range fun g : Γ => (A.canonicalUnit g : A.completedGroupAlgebra))
    (p := fun y _ =>
      A.augmentationAdjustedElement y ∈
        closure A.signedaug_letterleft_spanset)
    ?mem ?zero ?add ?smul hy
  · intro y hy
    rcases hy with ⟨g, rfl⟩
    change
      A.augmentationAdjustedElement (A.canonicalUnit g : A.completedGroupAlgebra) ∈
        closure A.signedaug_letterleft_spanset
    rw [A.aug_adjustedelement_canonunit g]
    exact hsubone g
  · change
      A.augmentationAdjustedElement 0 ∈
        closure A.signedaug_letterleft_spanset
    rw [A.aug_adjusted_elementzero]
    exact A.zeromem_clossignlett_leftspanset
  · intro x y _hx _hy hx_mem hy_mem
    change
      A.augmentationAdjustedElement (x + y) ∈
        closure A.signedaug_letterleft_spanset
    rw [A.aug_adjusted_elementadd x y]
    exact A.addmem_clossignlett_leftspanset hx_mem hy_mem
  · intro c x _hx hx_mem
    change
      A.augmentationAdjustedElement (c • x) ∈
        closure A.signedaug_letterleft_spanset
    rw [A.aug_adjusted_elementsmul c x]
    exact A.smulmem_clossignlett_leftspanset c hx_mem

lemma
    GCAmbien.augidealsubset_closadjudens_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan) :
    (A.augmentationIdeal : Set A.completedGroupAlgebra) ⊆
      closure A.aug_adjustedcanon_spanset := by
  intro x hx
  have hx_dense :
      x ∈ closure (A.canon_unit_linspan : Set A.completedGroupAlgebra) :=
    A.memclosure_unitlindense_unitalgspan hdense x
  have hmaps :
      Set.MapsTo A.augmentationAdjustedElement
        (A.canon_unit_linspan : Set A.completedGroupAlgebra)
        A.aug_adjustedcanon_spanset := by
    intro y hy
    exact ⟨y, hy, rfl⟩
  have hx_adjusted :
      A.augmentationAdjustedElement x ∈
        closure A.aug_adjustedcanon_spanset :=
    map_mem_closure A.aug_adjusted_elementcont hx_dense hmaps
  have hfix :
      A.augmentationAdjustedElement x = x :=
    A.augadjusted_elementeq_memaugideal hx
  simpa [hfix] using hx_adjusted

lemma
    GCAmbien.closureaug_adjuspanlett_leftspanset
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hsubone :
      ∀ g : Γ,
        (A.canonicalUnit g : A.completedGroupAlgebra) - 1 ∈
          closure A.signedaug_letterleft_spanset) :
    closure A.aug_adjustedcanon_spanset ⊆
      closure A.signedaug_letterleft_spanset := by
  have hsubset :
      A.aug_adjustedcanon_spanset ⊆
        closure A.signedaug_letterleft_spanset :=
    A.augadjusted_spansetletter_leftspanset
      hsubone
  have hclosed :
      IsClosed (closure A.signedaug_letterleft_spanset) :=
    isClosed_closure
  exact closure_minimal hsubset hclosed

lemma
    GCAmbien.augidealsubset_closleftdens_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan)
    (hsubone :
      ∀ g : Γ,
        (A.canonicalUnit g : A.completedGroupAlgebra) - 1 ∈
          closure A.signedaug_letterleft_spanset) :
    (A.augmentationIdeal : Set A.completedGroupAlgebra) ⊆
      closure A.signedaug_letterleft_spanset := by
  intro x hx
  have hx_adjusted :
      x ∈ closure A.aug_adjustedcanon_spanset :=
    A.augidealsubset_closadjudens_unitalgspan
      hdense hx
  have hclosure_subset :
      closure A.aug_adjustedcanon_spanset ⊆
        closure A.signedaug_letterleft_spanset :=
    A.closureaug_adjuspanlett_leftspanset
      hsubone
  exact hclosure_subset hx_adjusted

lemma
    GCAmbien.existsaug_idealettdens_unitalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan) :
    Nonempty (A.AugIdealletterDensespan) := by
  exact
    ⟨{
      dense_span :=
        A.augidealsubset_closleftdens_unitalgspan
          hdense
          (fun g =>
            A.unitsub_onememletter_leftspanset g) }⟩

structure GCAmbien.FintopologiLeftgenAugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    (n : ℕ)
    (A : GCAmbien (p := p) (Γ := Γ) s hs) :
    Type (u + 2) where
  topologicalGeneratingFamily :
    TGFam
      (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)

noncomputable def
    GCAmbien.fintopologi_leftaugpower_worddensespan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (H : A.AugPowerwordDensespan n) :
    A.FintopologiLeftgenAugpower n := by
  classical
  refine
    ⟨{ index := ULift.{u} (denseAugmentationIndex d n)
       finite_index := dense_fintype_index d n
       generator := fun w => A.aug_power_wordgen w.down
       generator_mem := fun w =>
         A.aug_powerword_genmem w.down
       dense_span := ?_ }⟩
  simpa using H.dense_span

lemma
    GCAmbien.closedaug_powertopologi_leftaugpower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (G : A.FintopologiLeftgenAugpower n) :
    A.ClosedAugPower n := by
  have hclosed :
      IsClosed ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) := by
    exact G.topologicalGeneratingFamily.isClosed_ideal
  simpa [GCAmbien.ClosedAugPower]
    using hclosed

lemma
    gens_core_two
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        Nonempty (A.FintopologiLeftgenAugpower n) := by
  rcases completed_ambient_span
      (p := p) (Γ := Γ) s hs with
    ⟨A, hdense⟩
  rcases
      A.existsaug_idealettdens_unitalgspan
        hdense with
    ⟨Hletters⟩
  rcases
      A.existsaugpower_wordspanideal_letterdensespan
        (n := n) Hletters with
    ⟨Hpower⟩
  exact
    ⟨A, hdense,
      ⟨A.fintopologi_leftaugpower_worddensespan
        Hpower⟩⟩

lemma
    gens_closed_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        A.ClosedAugPower n := by
  rcases
      gens_core_two
        (p := p) (Γ := Γ) s hs (n := n) _hn with
    ⟨A, hdense, hgen⟩
  rcases hgen with ⟨G⟩
  exact
    ⟨A, hdense,
      A.closedaug_powertopologi_leftaugpower G⟩

lemma
    gens_open_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
          Set A.completedGroupAlgebra) := by
  rcases
      gens_closed_core
        (p := p) (Γ := Γ) s hs (n := n) hn with
    ⟨A, hdense, hclosed⟩
  have hopen :
      IsOpen ((A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra) :
        Set A.completedGroupAlgebra) := by
    exact
      A.openaug_powerpower_twole
        hdense hclosed hn
  exact ⟨A, hdense, hopen⟩

lemma
    gens_completed_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        Nonempty (A.ContAugPowerkernel n) := by
  rcases
      gens_open_core
        (p := p) (Γ := Γ) s hs (n := n) _hn with
    ⟨A, hdense, hopen⟩
  exact
    ⟨A, hdense,
      A.contaug_powerkernel_openaugpower
        (p := p) (Γ := Γ) (s := s) (hs := hs) hopen⟩

lemma
    gens_completed_two
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        A.ClosedAugPower n := by
  rcases
      gens_completed_core
        (p := p) (Γ := Γ) s hs (n := n) hn with
    ⟨A, hdense, hK⟩
  exact
    ⟨A, hdense,
      A.closedaug_powernonempty_contkernel hK⟩

lemma
    gens_topological_two
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        A.TopoAugQuot n := by
  rcases
      gens_completed_core
        (p := p) (Γ := Γ) s hs (n := n) hn with
    ⟨A, hdense, hK⟩
  exact
    ⟨A, hdense,
      A.topoaug_quotnonempty_contkernel hK⟩

lemma
    gens_completed_topological
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        A.TopoAugQuot n := by
  exact
    gens_topological_two
      (p := p) (Γ := Γ) s hs (n := n) _hn

lemma
    gens_completed_aug
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        Nonempty (A.ContAugPowerkernel n) := by
  exact
    gens_completed_core
      (p := p) (Γ := Γ) s hs (n := n) _hn

lemma
    dense_gens_completed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        A.ClosedAugPower n := by
  exact
    gens_closed_core
      (p := p) (Γ := Γ) s hs (n := n) _hn

lemma
    GCAmbien.existsfin_algaugtrunc_powertwole
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan)
    (hclosed : A.ClosedAugPower n)
    (_hn : 2 ≤ n) :
    Nonempty (A.FAAugtru n) := by
  have hfinite :
      Finite (A.completedGroupAlgebra ⧸
        (A.augmentationIdeal ^ n : Ideal A.completedGroupAlgebra)) := by
    exact
      A.finideal_quotaug_powertwole
        hdense hclosed _hn
  exact
    ⟨A.finalg_augtrunc_finidealquot hfinite⟩

lemma
    GCAmbien.existsfin_algaugquot_powertwole
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : GCAmbien (p := p) (Γ := Γ) s hs)
    (hdense : A.DenseAlgebraSpan)
    (hclosed : A.ClosedAugPower n)
    (_hn : 2 ≤ n) :
    ∃ Q :
      GAAug
        (p := p) (Γ := Γ) (s := s) (hs := hs) n A,
      Finite Q.augmentationQuotient := by
  rcases
    A.existsfin_algaugtrunc_powertwole
      hdense hclosed _hn with
    ⟨T⟩
  exact A.existsfin_algaug_finalgtrunc T

lemma
    dense_gens_closed
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (_hn : 2 ≤ n) :
    ∃ A : GCAmbien (p := p) (Γ := Γ) s hs,
      A.DenseAlgebraSpan ∧
        Nonempty (A.FCAugpow n) := by
  rcases
      dense_gens_completed
        (p := p) (Γ := Γ) s hs _hn with
    ⟨A, hdense, hclosed⟩
  rcases
      A.existsfin_algaugquot_powertwole
        (p := p) (Γ := Γ) (s := s) (hs := hs) hdense hclosed _hn with
    ⟨Q, hfiniteQ⟩
  exact
    ⟨A, hdense,
      A.finclosed_augpowerfin_algquotclosed
        Q hfiniteQ hclosed⟩

end Towers
