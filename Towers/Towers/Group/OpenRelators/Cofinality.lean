import Towers.Group.OpenRelators.NormalRelatorFactorization
import Towers.Group.FreeGroupSeparation
import Towers.Group.ProPPresentation


open scoped Topology

noncomputable section

namespace Towers
namespace ONCofina

open PRFact
open PRQuotie
open ONFact

universe u v

variable
    {p : ℕ}
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [CompactSpace F]
    [Group G]
    {ι : Type*}
    {relator : ι → F}

/--
An indexed family of open-normal subgroups is cofinal when every open-normal
subgroup contains one member of the family.
-/
def CofinalOpenFamily
    {κ : Type v}
    (B : κ → OpenNormalSubgroup F) :
    Prop :=
  ∀ N : OpenNormalSubgroup F, ∃ k : κ, (B k : Subgroup F) ≤ N

/--
Algebraic relation-subgroup generation tested only on an indexed family of
open-normal quotients.
-/
def GeneratedAlgebraicallyAlong
    {κ : Type v}
    (q : F →* G)
    (relator : ι → F)
    (B : κ → OpenNormalSubgroup F) :
    Prop :=
  ∀ k : κ,
    GeneratedAlgebraicallyOpen q relator (B k)

omit [IsTopologicalGroup F] [CompactSpace F] in
lemma of_eq_le
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N)
    {x y : F}
    (hxy :
      QuotientGroup.mk' (M : Subgroup F) x =
        QuotientGroup.mk' (M : Subgroup F) y) :
    QuotientGroup.mk' (N : Subgroup F) x =
      QuotientGroup.mk' (N : Subgroup F) y := by
  apply inv_mul_eq_one.mp
  apply (QuotientGroup.eq_one_iff (N := (N : Subgroup F)) (x⁻¹ * y)).2
  exact hMN (inv_mul_quotient hxy)

omit [IsTopologicalGroup F] [CompactSpace F] in
/--
Algebraic relation-subgroup generation descends from a finer open-normal
quotient to every coarser quotient.
-/
lemma generated_algebraically_open
    {q : F →* G}
    {relator : ι → F}
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N)
    (hM : GeneratedAlgebraicallyOpen q relator M) :
    GeneratedAlgebraicallyOpen q relator N := by
  intro x hx
  rcases hM x hx with ⟨y, hyrel, hyx⟩
  exact ⟨y, hyrel, of_eq_le hMN hyx⟩

omit [IsTopologicalGroup F] [CompactSpace F] in
/--
A cofinal family of open-normal quotients is enough to test algebraic
relation-subgroup generation in every open-normal quotient.
-/
lemma algebraically_every_along
    {κ : Type v}
    (q : F →* G)
    (relator : ι → F)
    (B : κ → OpenNormalSubgroup F)
    (hB : CofinalOpenFamily B) :
    GeneratedAlgebraicallyEvery q relator ↔
      GeneratedAlgebraicallyAlong q relator B := by
  constructor
  · intro h k
    exact h (B k)
  · intro h N
    rcases hB N with ⟨k, hk⟩
    exact generated_algebraically_open hk (h k)

/--
For a pro-`p` source, a cofinal open-normal family is enough to test all finite
relator-killing `p`-group quotient factorizations.
-/
lemma factorization_along_pro
    {κ : Type v}
    (hProP : ProP.ProPGroup p F)
    (q : F →* G)
    (B : κ → OpenNormalSubgroup F)
    (hB : CofinalOpenFamily B) :
    QuotientFactorizationProperty p relator q ↔
      GeneratedAlgebraicallyAlong q relator B := by
  rw [property_every_pro
    hProP q]
  exact algebraically_every_along
    q relator B hB

/--
For a pro-`p` source, the full finite-map factorization property has the same
cofinal open-normal formulation.
-/
lemma property_algebraically_along
    {κ : Type v}
    (hProP : ProP.ProPGroup p F)
    (q : F →* G)
    (B : κ → OpenNormalSubgroup F)
    (hB : CofinalOpenFamily B) :
    FactorizationProperty p relator q ↔
      GeneratedAlgebraicallyAlong q relator B := by
  rw [factorization_property_quotient]
  exact factorization_along_pro
    hProP q B hB

/-- The `n`th open-normal Zassenhaus subgroup of a topologically generated pro-`p` group. -/
def zassenhausOpenNormal
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (n : ℕ) :
    OpenNormalSubgroup F where
  toOpenSubgroup :=
    ⟨zassenhausFiltration p F n,
      ProP.filtration_topologically_generates p hProP s hs n⟩
  isNormal' := zassenhausFiltration_normal p F n

@[simp] lemma zassenhaus_normal_subgroup
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (n : ℕ) :
    (zassenhausOpenNormal hProP s hs n : Subgroup F) =
      zassenhausFiltration p F n := rfl

/--
The open-normal Zassenhaus subgroups are cofinal among all open-normal
subgroups of a topologically generated pro-`p` group.
-/
lemma open_normal_cofinal
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s) :
    CofinalOpenFamily
      (zassenhausOpenNormal hProP s hs) := by
  intro N
  let qN : F →* F ⧸ (N : Subgroup F) := QuotientGroup.mk' (N : Subgroup F)
  letI : DiscreteTopology (F ⧸ (N : Subgroup F)) :=
    pro_discrete_topology N
  letI : Finite (F ⧸ (N : Subgroup F)) :=
    pro_p_open N
  rcases TBluepr.filtration_eventually_bot
      (Fact.out : Nat.Prime p)
      (F ⧸ (N : Subgroup F))
      (hProP N) with
    ⟨depth, hbot⟩
  refine ⟨depth + 1, ?_⟩
  change zassenhausFiltration p F (depth + 1) ≤ N
  simpa [qN] using TBluepr.filtration_target_bot qN hbot

/--
For a topologically generated pro-`p` source, finite relator quotient
factorization is exactly algebraic relation-subgroup generation in the
Zassenhaus finite layers.
-/
lemma algebraically_along_pro
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (q : F →* G) :
    QuotientFactorizationProperty p relator q ↔
      GeneratedAlgebraicallyAlong q relator
        (zassenhausOpenNormal hProP s hs) := by
  exact factorization_along_pro
    hProP q (zassenhausOpenNormal hProP s hs)
    (open_normal_cofinal hProP s hs)

end ONCofina
end Towers
