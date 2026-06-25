import Submission.Group.OpenRelators.Cofinality


open scoped Topology

noncomputable section

namespace Submission
namespace OTLayers

open PRFact
open PRQuotie
open ONFact
open ONCofina

universe u w

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
    {q : F →* G}
    {relator : ι → F}
    {α : F →* P}

/--
The open-normal subgroup cut out by the kernel of one actual continuous finite
discrete `p`-group map killing the displayed relators.
-/
def openNormalSubgroup
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    OpenNormalSubgroup F :=
  kernelOpenSubgroup
    (RQShadow.relatorShadowRange
      (RShadow.ofMap α hα hP hkill))

omit [IsTopologicalGroup F] [CompactSpace F] in
@[simp] lemma open_normal_subgroup
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    (openNormalSubgroup α hα hP hkill : Subgroup F) =
      α.ker := by
  rw [openNormalSubgroup, kernel_open_subgroup,
    RQShadow.relator_shadow_range]
  rfl

omit [IsTopologicalGroup F] [CompactSpace F] in
/--
If candidate-kernel generation is proved in one open-normal finite layer lying
inside the kernel of an actual relator-killing map, then that actual map kills
the whole candidate kernel.
-/
lemma kernel_kills_relators
    [TopologicalSpace P]
    (q : F →* G)
    (relator : ι → F)
    (α : F →* P)
    (N : OpenNormalSubgroup F)
    (hN : (N : Subgroup F) ≤ α.ker)
    (hgen : GeneratedAlgebraicallyOpen q relator N)
    (hkill : KillsRelators relator α) :
    q.ker ≤ α.ker := by
  intro x hx
  rcases hgen x hx with ⟨y, hyrel, hyx⟩
  have hyker : y ∈ α.ker :=
    (kills_relators_relation relator α).mp hkill hyrel
  have hdiff : y⁻¹ * x ∈ α.ker :=
    hN (inv_mul_quotient hyx)
  simpa [mul_assoc] using α.ker.mul_mem hyker hdiff

omit [IsTopologicalGroup F] [CompactSpace F] in
/--
If candidate-kernel generation is proved in one open-normal finite layer lying
inside the kernel of an actual relator-killing map, then the actual map factors
uniquely through any surjective candidate quotient.
-/
lemma uniquely_through_kills
    [TopologicalSpace P]
    (q : F →* G)
    (relator : ι → F)
    (α : F →* P)
    (N : OpenNormalSubgroup F)
    (hq : Function.Surjective q)
    (hN : (N : Subgroup F) ≤ α.ker)
    (hgen : GeneratedAlgebraicallyOpen q relator N)
    (hkill : KillsRelators relator α) :
    FactorsUniquelyThrough q α := by
  apply factors_uniquely_ker q α hq
  exact kernel_kills_relators
    q relator α N hN hgen hkill

/--
For a topologically generated pro-`p` source, one canonical Zassenhaus finite
layer lies inside the kernel of every actual continuous finite discrete
relator-killing `p`-group map.
-/
lemma open_p_relator
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    ∃ n : ℕ, (zassenhausOpenNormal hProP s hs n : Subgroup F) ≤ α.ker := by
  rcases open_normal_cofinal hProP s hs
      (openNormalSubgroup α hα hP hkill) with
    ⟨n, hn⟩
  exact ⟨n, by
    rw [open_normal_subgroup] at hn
    exact hn⟩

/--
The least canonical Zassenhaus depth whose finite layer lies inside the kernel
of one actual continuous finite discrete relator-killing `p`-group map.
-/
def targetDepthRelator
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    ℕ := by
  letI : DecidablePred
      (fun n : ℕ => (zassenhausOpenNormal hProP s hs n : Subgroup F) ≤ α.ker) :=
    Classical.decPred _
  exact Nat.find (open_p_relator
    hProP s hs α hα hP hkill)

/--
At the canonical target depth of one actual finite relator-killing `p`-group
map, the corresponding Zassenhaus finite layer lies inside that map's kernel.
-/
lemma openFinRelator
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α) :
    (zassenhausOpenNormal hProP s hs
        (targetDepthRelator hProP s hs α hα hP hkill) :
      Subgroup F) ≤ α.ker := by
  letI : DecidablePred
      (fun n : ℕ => (zassenhausOpenNormal hProP s hs n : Subgroup F) ≤ α.ker) :=
    Classical.decPred _
  rw [targetDepthRelator]
  exact Nat.find_spec (open_p_relator
    hProP s hs α hα hP hkill)

/--
The canonical target Zassenhaus depth of one actual finite relator-killing
`p`-group map is the least Zassenhaus depth whose finite layer lies inside that
map's kernel.
-/
lemma target_depth_open
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α)
    {n : ℕ}
    (hn : (zassenhausOpenNormal hProP s hs n : Subgroup F) ≤ α.ker) :
    targetDepthRelator hProP s hs α hα hP hkill ≤ n := by
  letI : DecidablePred
      (fun n : ℕ => (zassenhausOpenNormal hProP s hs n : Subgroup F) ≤ α.ker) :=
    Classical.decPred _
  rw [targetDepthRelator]
  exact Nat.find_min'
    (open_p_relator
      hProP s hs α hα hP hkill)
    hn

/--
Every Zassenhaus finite layer at or deeper than the canonical target depth of
one actual finite relator-killing `p`-group map lies inside that map's kernel.
-/
lemma open_normal_relator
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α)
    {n : ℕ}
    (htarget :
      targetDepthRelator hProP s hs α hα hP hkill ≤ n) :
    (zassenhausOpenNormal hProP s hs n : Subgroup F) ≤ α.ker := by
  change zassenhausFiltration p F n ≤ α.ker
  exact (zassenhausFiltration_antitone p F htarget).trans
    (openFinRelator
      hProP s hs α hα hP hkill)

/--
Candidate-kernel generation at the canonical target Zassenhaus depth of one
actual finite relator-killing `p`-group map is enough to kill the candidate
kernel in that map.
-/
lemma fin_p_relator
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (q : F →* G)
    (relator : ι → F)
    (α : F →* P)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α)
    (hgen : GeneratedAlgebraicallyOpen q relator
      (zassenhausOpenNormal hProP s hs
        (targetDepthRelator hProP s hs α hα hP hkill))) :
    q.ker ≤ α.ker := by
  exact kernel_kills_relators
    q relator α
    (zassenhausOpenNormal hProP s hs
      (targetDepthRelator hProP s hs α hα hP hkill))
    (openFinRelator
      hProP s hs α hα hP hkill)
    hgen
    hkill

/--
Candidate-kernel generation at the canonical target Zassenhaus depth of one
actual finite relator-killing `p`-group map is enough for unique factorization
through any surjective candidate quotient.
-/
lemma
unique_through_relator
    [Fact p.Prime]
    [TotallyDisconnectedSpace F]
    [TopologicalSpace P]
    [DiscreteTopology P]
    [Finite P]
    (hProP : ProP.ProPGroup p F)
    {d : ℕ}
    (s : Fin d → F)
    (hs : ProP.TopologicallyGenerates s)
    (q : F →* G)
    (relator : ι → F)
    (α : F →* P)
    (hq : Function.Surjective q)
    (hα : Continuous α)
    (hP : IsPGroup p P)
    (hkill : KillsRelators relator α)
    (hgen : GeneratedAlgebraicallyOpen q relator
      (zassenhausOpenNormal hProP s hs
        (targetDepthRelator hProP s hs α hα hP hkill))) :
    FactorsUniquelyThrough q α := by
  apply factors_uniquely_ker q α hq
  exact fin_p_relator
    hProP s hs q relator α hα hP hkill hgen

end OTLayers
end Submission
