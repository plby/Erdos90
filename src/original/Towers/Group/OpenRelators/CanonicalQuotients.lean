import Towers.Group.OpenRelators.TargetLayers


open scoped Topology

noncomputable section

namespace Towers
namespace OCQuotie

open PRFact
open PRQuotie
open ONFact
open ONCofina
open OTLayers

universe u v w

variable
    {p : ℕ}
    {F G P : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [CompactSpace F]
    [Group G]
    [Group P]
    {ι : Type w}
    {relator : ι → F}
    {q : F →* G}
    {α : F →* P}

/--
A family of actual surjective finite relator-killing `p`-group quotients is
kernel-cofinal when every actual such quotient lies above the kernel of one
family member.  The order is reversed because finer quotients have smaller
kernels.
-/
def CofinalRelatorFamily
    {κ : Type v}
    (Q : κ → RQShadow p F relator) :
    Prop :=
  ∀ S : RQShadow p F relator,
    ∃ k : κ, (Q k).map.ker ≤ S.map.ker

/--
If an open-normal finite layer lies inside the kernel of a relator-killing map,
then the canonical algebraic relator quotient of that layer also lies above
the map kernel.  This is the universal property of killing the layer and the
displayed relators algebraically.
-/
lemma algebraic_kills_relators
    (hProP : ProP.ProPGroup p F)
    (relator : ι → F)
    (α : F →* P)
    (N : OpenNormalSubgroup F)
    (hN : (N : Subgroup F) ≤ α.ker)
    (hkill : KillsRelators relator α) :
    (algebraicOpenNormal hProP N (relator := relator)).map.ker ≤
      α.ker := by
  intro x hx
  rcases (algebraic_open_relator
    hProP N x).mp hx with ⟨y, hyrel, hyx⟩
  have hyker : y ∈ α.ker :=
    (kills_relators_relation relator α).mp hkill hyrel
  have hdiff : y⁻¹ * x ∈ α.ker :=
    hN (inv_mul_quotient hyx)
  simpa [mul_assoc] using α.ker.mul_mem hyker hdiff

/--
The canonical algebraic relator quotients of all open-normal finite layers are
kernel-cofinal among actual surjective finite relator-killing `p`-group
quotients of a pro-`p` source.
-/
lemma algebraic_cofinal_pro
    (hProP : ProP.ProPGroup p F) :
    CofinalRelatorFamily
      (fun N : OpenNormalSubgroup F =>
        algebraicOpenNormal hProP N (relator := relator)) := by
  intro S
  let N : OpenNormalSubgroup F := kernelOpenSubgroup S
  exact ⟨N, algebraic_kills_relators
    hProP relator S.map N (by simp [N]) S.toRShadow.relator_killed⟩

omit [IsTopologicalGroup F] [CompactSpace F] in
/--
To test finite relator quotient factorization, it is enough to test any
kernel-cofinal family of actual surjective finite relator-killing `p`-group
quotients.
-/
lemma property_along_cofinal
    {κ : Type v}
    (q : F →* G)
    (Q : κ → RQShadow p F relator)
    (hQ : CofinalRelatorFamily Q) :
    QuotientFactorizationProperty p relator q ↔
      ∀ k : κ, q.ker ≤ (Q k).map.ker := by
  constructor
  · intro hfactor k
    exact hfactor (Q k)
  · intro hfactor S
    rcases hQ S with ⟨k, hk⟩
    exact (hfactor k).trans hk

/--
For a pro-`p` source, finite relator quotient factorization can be tested on
the canonical algebraic relator quotient of every open-normal finite layer.
-/
lemma property_algebraic_kernels
    (hProP : ProP.ProPGroup p F)
    (q : F →* G) :
    QuotientFactorizationProperty p relator q ↔
      ∀ N : OpenNormalSubgroup F,
        q.ker ≤ (algebraicOpenNormal hProP N
          (relator := relator)).map.ker := by
  exact property_along_cofinal
    q
    (fun N : OpenNormalSubgroup F =>
      algebraicOpenNormal hProP N (relator := relator))
    (algebraic_cofinal_pro
      hProP)

/--
The canonical actual finite relator quotient obtained from the `n`th
Zassenhaus open-normal finite layer of a topologically generated pro-`p`
source.
-/
abbrev zassenhausRelatorQuotient
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (n : ℕ) :
    RQShadow p F relator :=
  algebraicOpenNormal hProP
    (zassenhausOpenNormal hProP s hs n)

/--
If one Zassenhaus finite layer lies inside the kernel of a relator-killing map,
then the canonical relator quotient of that layer lies above the map kernel.
-/
lemma zassenhaus_kills_relators
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (α : F →* P)
    (n : ℕ)
    (hN : (zassenhausOpenNormal hProP s hs n : Subgroup F) ≤ α.ker)
    (hkill : KillsRelators relator α) :
    (zassenhausRelatorQuotient hProP s hs n
      (relator := relator)).map.ker ≤ α.ker := by
  exact algebraic_kills_relators
    hProP relator α (zassenhausOpenNormal hProP s hs n) hN hkill

/--
Every actual surjective finite relator-killing `p`-group quotient lies above one
canonical Zassenhaus finite-layer relator quotient of a topologically generated
pro-`p` source.
-/
lemma zassenhaus_relator_shadow
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (S : RQShadow p F relator) :
    ∃ n : ℕ, (zassenhausRelatorQuotient hProP s hs n
      (relator := relator)).map.ker ≤ S.map.ker := by
  rcases open_p_relator
      hProP s hs S.map S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group
      S.toRShadow.relator_killed with
    ⟨n, hN⟩
  exact ⟨n, zassenhaus_kills_relators
    hProP s hs S.map n hN S.toRShadow.relator_killed⟩

/--
The canonical Zassenhaus finite-layer relator quotients are kernel-cofinal
among actual surjective finite relator-killing `p`-group quotients of a
topologically generated pro-`p` source.
-/
lemma cofinal_pro_p
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s) :
    CofinalRelatorFamily
      (zassenhausRelatorQuotient hProP s hs (relator := relator)) := by
  exact zassenhaus_relator_shadow
    hProP s hs

/--
For a topologically generated pro-`p` source, finite relator quotient
factorization can be tested on the one directed canonical family of
Zassenhaus finite-layer relator quotients.
-/
lemma property_kernels_pro
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (q : F →* G) :
    QuotientFactorizationProperty p relator q ↔
      ∀ n : ℕ, q.ker ≤ (zassenhausRelatorQuotient hProP s hs n
        (relator := relator)).map.ker := by
  exact property_along_cofinal
    q
    (zassenhausRelatorQuotient hProP s hs (relator := relator))
    (cofinal_pro_p
      hProP s hs)

/--
For a surjective candidate quotient, finite relator quotient factorization is
equivalent to unique factorization of every canonical Zassenhaus finite-layer
relator quotient through that candidate.
-/
lemma property_pro_p
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (q : F →* G)
    (hq : Function.Surjective q) :
    QuotientFactorizationProperty p relator q ↔
      ∀ n : ℕ, FactorsUniquelyThrough q
        (zassenhausRelatorQuotient hProP s hs n
          (relator := relator)).map := by
  rw [property_kernels_pro
    hProP s hs q]
  exact forall_congr' fun n =>
    (uniquely_through_ker q
      (zassenhausRelatorQuotient hProP s hs n (relator := relator)).map
      hq).symm

/--
Failure of finite relator quotient factorization is witnessed by one
candidate-kernel element surviving in one canonical Zassenhaus finite-layer
relator quotient.
-/
lemma factorization_property_pro
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (q : F →* G) :
    ¬ QuotientFactorizationProperty p relator q ↔
      ∃ n : ℕ, ∃ x : F, x ∈ q.ker ∧
        x ∉ (zassenhausRelatorQuotient hProP s hs n
          (relator := relator)).map.ker := by
  rw [property_kernels_pro
    hProP s hs q]
  simp only [not_forall, SetLike.not_le_iff_exists]

end OCQuotie
end Towers
