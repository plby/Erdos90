import Mathlib
import Towers.Group.ZassenhausFiniteQuotient.Test
import Towers.Group.DenseGenerators.ZassenhausCompact
import Towers.Group.DenseGenerators.InitialZassenhausTerms
import Towers.Group.ZassenhausTrivial


open scoped Topology Pointwise

noncomputable section

namespace Towers

universe u
universe v w z


namespace DCModel

/-- Zassenhaus triviality transports backward across a multiplicative equivalence.

This is the small algebraic fact needed to use the quotient-range equivalence stored in a completed
group algebra model: the range of the quotient-unit map is isomorphic to the intrinsic quotient
`Γ / D_n(Γ)`, whose own `D_n` is trivial. -/
lemma filtration_bot_equiv
    {p : ℕ}
    {A B : Type u} [Group A] [Group B]
    {n : ℕ}
    (e : A ≃* B)
    (hB : zassenhausFiltration p B n = ⊥) :
    zassenhausFiltration p A n = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  let f : A →* B := e.toMonoidHom
  have hxB :
      f x ∈ zassenhausFiltration p B n := by
    exact
      filtration_map_mem
        (p := p)
        (n := n)
        (f := f)
        hx
  have hxbot : f x ∈ (⊥ : Subgroup B) := by
    simpa [hB] using hxB
  have hfx_one : f x = 1 := by
    exact Subgroup.mem_bot.mp hxbot
  exact e.injective (by simpa [f] using hfx_one)

/-- The quotient-unit range in a completed group algebra model has trivial target `D_n`.

The model records a multiplicative equivalence from the quotient-unit range to the intrinsic
self-quotient `Γ / D_n(Γ)`.  Since `D_n` is trivial in that self-quotient, the same is true in the
range. -/
lemma range_filtration_bot
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    zassenhausFiltration p M.quotientUnitMap.range n = ⊥ := by
  letI : Ring M.augmentationQuotient := M.instQuotientRing
  let Q : Type u := generators_jennings_approx (p := p) (Γ := Γ) s hs n
  have hQ : zassenhausFiltration p Q n = ⊥ := by
    dsimp [Q, generators_jennings_approx]
    simpa [denseSelfQuotient, zassenhausSelfQuotient] using
      filtration_self_bot p Γ n
  exact
    filtration_bot_equiv
      (p := p)
      (A := M.quotientUnitMap.range)
      (B := Q)
      (n := n)
      M.quotientEquiv
      hQ

/-- If `g` is not in `D_n(Γ)`, its image under the quotient-unit range map is nontrivial.

This is just the recorded Jennings-Lazard kernel identity in the completed group algebra model,
read through `rangeRestrict`. -/
lemma range_restrict_ne
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    M.quotientUnitMap.rangeRestrict g ≠ 1 := by
  letI : Ring M.augmentationQuotient := M.instQuotientRing
  intro hg_one
  have hgker : g ∈ M.quotientUnitMap.ker := by
    change M.quotientUnitMap g = 1
    simpa [MonoidHom.rangeRestrict] using congrArg Subtype.val hg_one
  have hgD : g ∈ zassenhausFiltration p Γ n := by
    simpa [M.unit_map_ker] using hgker
  exact hg hgD

/-- The quotient-unit map remains continuous after restricting its codomain to its range. -/
lemma range_restrict_continuous
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n) :
    letI := M.quotientTopology
    Continuous M.quotientUnitMap.rangeRestrict := by
  letI : Ring M.augmentationQuotient := M.instQuotientRing
  letI : TopologicalSpace M.augmentationQuotient := M.quotientTopology
  simpa [MonoidHom.rangeRestrict] using
    M.quotient_unit_continuous.subtype_mk
      (fun g : Γ => ⟨g, rfl⟩)

/-- The quotient-unit range of a finite discrete completed model is a finite quotient test.

This is the formal packaging step from the completed group algebra quotient to the finite quotient
tests used in the closed-overgroup criterion. -/
def finiteQuotientTest
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hfinite : Finite M.augmentationQuotient)
    (hdiscrete :
      letI := M.quotientTopology
      DiscreteTopology M.quotientUnitMap.range) :
    DGTest Γ := by
  letI : Ring M.augmentationQuotient := M.instQuotientRing
  letI : TopologicalSpace M.augmentationQuotient := M.quotientTopology
  letI : Finite M.quotientUnitMap.range :=
    dense_completed_model
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) M hfinite
  letI : DiscreteTopology M.quotientUnitMap.range := hdiscrete
  exact
    DGTest.ofHom
      M.quotientUnitMap.rangeRestrict
      (M.range_restrict_continuous
        (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n))

/-- A finite discrete completed model separates every element outside `D_n`.

The quotient test is the range of the model's quotient-unit map.  Its target
`D_n` is trivial by the equivalence with `Γ / D_n(Γ)`, while an element outside
`D_n(Γ)` has nontrivial range image by the model's kernel identity. -/
lemma test_not_target
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCModel (p := p) (Γ := Γ) s hs n)
    (hfinite : Finite M.augmentationQuotient)
    (hdiscrete :
      letI := M.quotientTopology
      DiscreteTopology M.quotientUnitMap.range)
    {g : Γ}
    (hg : g ∉ zassenhausFiltration p Γ n) :
    ∃ T : DGTest Γ,
      T.quotientMap g ∉
        DGTest.targetZassenhaus T p n := by
  letI : Ring M.augmentationQuotient := M.instQuotientRing
  letI : TopologicalSpace M.augmentationQuotient := M.quotientTopology
  letI : Finite M.quotientUnitMap.range :=
    dense_completed_model
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) M hfinite
  letI : DiscreteTopology M.quotientUnitMap.range := hdiscrete
  let T : DGTest Γ :=
    M.finiteQuotientTest
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) hfinite hdiscrete
  refine ⟨T, ?_⟩
  have htarget_bot :
      zassenhausFiltration p M.quotientUnitMap.range n = ⊥ := by
    exact M.range_filtration_bot (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n)
  have hne :
      M.quotientUnitMap.rangeRestrict g ≠ 1 := by
    exact M.range_restrict_ne
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) hg
  intro hg_target
  have hg_target' :
      M.quotientUnitMap.rangeRestrict g ∈
        zassenhausFiltration p M.quotientUnitMap.range n := by
    simpa [T, finiteQuotientTest, DGTest.targetZassenhaus]
      using hg_target
  have hg_bot :
      M.quotientUnitMap.rangeRestrict g ∈ (⊥ : Subgroup M.quotientUnitMap.range) := by
    simpa [htarget_bot] using hg_target'
  exact hne (Subgroup.mem_bot.mp hg_bot)


end DCModel

end Towers
