import Towers.Group.OpenRelators.CanonicalQuotients


open scoped Topology

noncomputable section

namespace Towers
namespace OCTower

open PRFact
open PRQuotie
open ONFact
open ONCofina
open OCQuotie

universe u w

variable
    {p : ℕ}
    {F G : Type u}
    [Group F]
    [TopologicalSpace F]
    [IsTopologicalGroup F]
    [CompactSpace F]
    [Group G]
    {ι : Type w}
    {relator : ι → F}

/--
Every element of an open-normal finite layer dies in that layer's canonical
algebraic relator quotient.
-/
lemma open_algebraic_relator
    (hProP : ProP.ProPGroup p F)
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    (N : Subgroup F) ≤
      (algebraicOpenNormal hProP N (relator := relator)).map.ker := by
  intro x hx
  rw [algebraic_open_relator hProP N x]
  have hxone : QuotientGroup.mk' (N : Subgroup F) x = 1 :=
    (QuotientGroup.eq_one_iff (N := (N : Subgroup F)) x).2 hx
  rw [hxone]
  exact Subgroup.one_mem _

/--
Nested open-normal finite layers induce reverse kernel containment between their
canonical algebraic relator quotients.
-/
lemma algebraic_open_kernel
    (hProP : ProP.ProPGroup p F)
    (relator : ι → F)
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N) :
    (algebraicOpenNormal hProP M (relator := relator)).map.ker ≤
      (algebraicOpenNormal hProP N (relator := relator)).map.ker := by
  exact algebraic_kills_relators
    hProP
    relator
    (algebraicOpenNormal hProP N (relator := relator)).map
    M
    (hMN.trans (open_algebraic_relator
      hProP relator N))
    (algebraicOpenNormal hProP N (relator := relator)).toRShadow.relator_killed

/--
The canonical transition from the algebraic relator quotient of a finer
open-normal finite layer to that of a coarser layer.
-/
def algebraicOpenTransition
    (hProP : ProP.ProPGroup p F)
    (relator : ι → F)
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N) :
    (algebraicOpenNormal hProP M
      (relator := relator)).Target →*
      (algebraicOpenNormal hProP N
        (relator := relator)).Target :=
  factorSurjective
    (algebraicOpenNormal hProP M (relator := relator)).map
    (algebraicOpenNormal hProP N (relator := relator)).map
    (algebraicOpenNormal hProP M (relator := relator)).map_surjective
    (algebraic_open_kernel hProP relator hMN)

/--
The canonical transition commutes with the ambient quotient maps.
-/
lemma algebraic_open_comp
    (hProP : ProP.ProPGroup p F)
    (relator : ι → F)
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N) :
    (algebraicOpenTransition hProP relator hMN).comp
        (algebraicOpenNormal hProP M (relator := relator)).map =
      (algebraicOpenNormal hProP N (relator := relator)).map := by
  exact factor_map_of
    (algebraicOpenNormal hProP M (relator := relator)).map
    (algebraicOpenNormal hProP N (relator := relator)).map
    (algebraicOpenNormal hProP M (relator := relator)).map_surjective
    (algebraic_open_kernel hProP relator hMN)

/--
The canonical transition sends the class of every ambient element to its class
in the coarser algebraic relator quotient.
-/
lemma algebraic_open_transition
    (hProP : ProP.ProPGroup p F)
    (relator : ι → F)
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N)
    (x : F) :
    algebraicOpenTransition hProP relator hMN
        ((algebraicOpenNormal hProP M (relator := relator)).map x) =
      (algebraicOpenNormal hProP N (relator := relator)).map x := by
  have hcomp := congrArg
    (fun φ : F →*
        (algebraicOpenNormal hProP N
          (relator := relator)).Target => φ x)
    (algebraic_open_comp hProP relator hMN)
  exact hcomp

/--
The canonical transition is surjective.
-/
lemma algebraic_open_surjective
    (hProP : ProP.ProPGroup p F)
    (relator : ι → F)
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N) :
    Function.Surjective
      (algebraicOpenTransition hProP relator hMN) := by
  intro y
  rcases (algebraicOpenNormal hProP N
    (relator := relator)).map_surjective y with ⟨x, rfl⟩
  exact ⟨(algebraicOpenNormal hProP M
    (relator := relator)).map x,
    algebraic_open_transition hProP relator hMN x⟩

/--
The canonical transition is the unique map commuting with the ambient quotient
maps.
-/
lemma algebraic_open_unique
    (hProP : ProP.ProPGroup p F)
    (relator : ι → F)
    {M N : OpenNormalSubgroup F}
    (hMN : (M : Subgroup F) ≤ N)
    (β :
      (algebraicOpenNormal hProP M
        (relator := relator)).Target →*
        (algebraicOpenNormal hProP N
          (relator := relator)).Target)
    (hβ : β.comp
        (algebraicOpenNormal hProP M (relator := relator)).map =
      (algebraicOpenNormal hProP N (relator := relator)).map) :
    β = algebraicOpenTransition hProP relator hMN := by
  apply MonoidHom.ext
  intro y
  rcases (algebraicOpenNormal hProP M
    (relator := relator)).map_surjective y with ⟨x, rfl⟩
  have hβx := congrArg
    (fun φ : F →*
        (algebraicOpenNormal hProP N
          (relator := relator)).Target => φ x)
    hβ
  have htransitionx := algebraic_open_transition
    hProP relator hMN x
  exact hβx.trans htransitionx.symm

/--
Canonical algebraic relator quotient transitions compose along nested
open-normal finite layers.
-/
lemma algebraic_transition_comp
    (hProP : ProP.ProPGroup p F)
    (relator : ι → F)
    {L M N : OpenNormalSubgroup F}
    (hLM : (L : Subgroup F) ≤ M)
    (hMN : (M : Subgroup F) ≤ N) :
    (algebraicOpenTransition hProP relator hMN).comp
        (algebraicOpenTransition hProP relator hLM) =
      algebraicOpenTransition hProP relator
        (hLM.trans hMN) := by
  apply algebraic_open_unique
    hProP relator (hLM.trans hMN)
  rw [MonoidHom.comp_assoc,
    algebraic_open_comp,
    algebraic_open_comp]

/--
The canonical algebraic relator quotient transition at one layer is the
identity.
-/
lemma algebraic_open_refl
    (hProP : ProP.ProPGroup p F)
    (relator : ι → F)
    (N : OpenNormalSubgroup F) :
    algebraicOpenTransition hProP relator
        (show (N : Subgroup F) ≤ N from le_rfl) =
      MonoidHom.id
        (algebraicOpenNormal hProP N
          (relator := relator)).Target := by
  symm
  apply algebraic_open_unique
    hProP relator (show (N : Subgroup F) ≤ N from le_rfl)
  rfl

/--
Deeper Zassenhaus open-normal finite layers lie inside shallower layers.
-/
lemma zassenhaus_open_normal
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (zassenhausOpenNormal hProP s hs m : Subgroup F) ≤
      zassenhausOpenNormal hProP s hs n := by
  change zassenhausFiltration p F m ≤ zassenhausFiltration p F n
  exact zassenhausFiltration_antitone p F hnm

/--
The kernels of canonical Zassenhaus finite-layer relator quotients decrease
with depth.
-/
lemma relator_quotient_kernel
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (zassenhausRelatorQuotient hProP s hs m
      (relator := relator)).map.ker ≤
      (zassenhausRelatorQuotient hProP s hs n
        (relator := relator)).map.ker := by
  exact algebraic_open_kernel
    hProP relator (zassenhaus_open_normal hProP s hs hnm)

/--
The canonical transition from the deeper `m`th Zassenhaus finite-layer relator
quotient to the shallower `n`th one.
-/
abbrev zassenhausRelatorTransition
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (zassenhausRelatorQuotient hProP s hs m
      (relator := relator)).Target →*
      (zassenhausRelatorQuotient hProP s hs n
        (relator := relator)).Target :=
  algebraicOpenTransition hProP relator
    (zassenhaus_open_normal hProP s hs hnm)

/--
The canonical Zassenhaus relator quotient transition commutes with the ambient
quotient maps.
-/
lemma zassenhaus_relator_comp
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (zassenhausRelatorTransition hProP s hs
        (relator := relator) hnm).comp
        (zassenhausRelatorQuotient hProP s hs m
          (relator := relator)).map =
      (zassenhausRelatorQuotient hProP s hs n
        (relator := relator)).map := by
  exact algebraic_open_comp
    hProP relator (zassenhaus_open_normal hProP s hs hnm)

/--
Canonical Zassenhaus relator quotient transitions compose along increasing
depths.
-/
lemma quotient_transition_comp
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    {n m k : ℕ}
    (hnm : n ≤ m)
    (hmk : m ≤ k) :
    (zassenhausRelatorTransition hProP s hs
        (relator := relator) hnm).comp
        (zassenhausRelatorTransition hProP s hs
          (relator := relator) hmk) =
      zassenhausRelatorTransition hProP s hs
        (relator := relator) (hnm.trans hmk) := by
  exact algebraic_transition_comp
    hProP
    relator
    (zassenhaus_open_normal hProP s hs hmk)
    (zassenhaus_open_normal hProP s hs hnm)

/--
The canonical Zassenhaus relator quotient transition at one depth is the
identity.
-/
lemma zassenhaus_transition_refl
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (n : ℕ) :
    zassenhausRelatorTransition hProP s hs
        (relator := relator) (Nat.le_refl n) =
      MonoidHom.id
        (zassenhausRelatorQuotient hProP s hs n
          (relator := relator)).Target := by
  exact algebraic_open_refl
    hProP relator (zassenhausOpenNormal hProP s hs n)

/--
Canonical Zassenhaus relator quotient transitions are surjective.
-/
lemma zassenhaus_transition_surjective
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    {n m : ℕ}
    (hnm : n ≤ m) :
    Function.Surjective
      (zassenhausRelatorTransition hProP s hs
        (relator := relator) hnm) := by
  exact algebraic_open_surjective
    hProP relator (zassenhaus_open_normal hProP s hs hnm)

end OCTower
end Towers
