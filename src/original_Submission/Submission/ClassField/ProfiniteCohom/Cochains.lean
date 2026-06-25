import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.LocallyConstant.Basic
import Submission.ClassField.ProfiniteCohom.FixedOpenNormal
import Submission.Topology.OpenNormal

/-!
# Milne, Class Field Theory, Proposition II.4.2: cochain preliminaries

These are the first two compactness steps in Milne's proof.  A continuous
cochain from a compact space to a discrete module has finite image, and a
single open normal subgroup fixes every value in that image.
-/

namespace Submission.CField.PCohom

open Filter Set
open scoped Pointwise Topology

/-- A continuous map from a compact space to a discrete space has finite
image. -/
theorem continuous_compact_discrete
    {A B : Type*} [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace B] [DiscreteTopology B]
    {f : A → B} (hf : Continuous f) :
    (range f).Finite :=
  (isCompact_range hf).finite_of_discrete

/-- A continuous map from a profinite group to a discrete space is constant
on the right cosets of some open normal subgroup.

Applied to the profinite group `Fin r → G`, this is the finite-cover argument
in Milne's footnote to Proposition II.4.2. -/
theorem open_normal_invariant
    {P Y : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [TotallyDisconnectedSpace P]
    [TopologicalSpace Y] [DiscreteTopology Y]
    (f : P → Y) (hf : Continuous f) :
    ∃ N : OpenNormalSubgroup P, ∀ p n, n ∈ N → f (p * n) = f p := by
  have hrange : (range f).Finite :=
    continuous_compact_discrete hf
  have hsep : ∀ y : Y,
      ∃ V ∈ 𝓝 (1 : P), f ⁻¹' {y} * V ⊆ f ⁻¹' {y} := by
    intro y
    exact compact_open_separated_mul_right
      ((isClosed_discrete {y}).preimage hf).isCompact
      ((isOpen_discrete {y}).preimage hf) subset_rfl
  choose V hV hmul using hsep
  let W : Set P := ⋂ y ∈ range f, V y
  have hW : W ∈ 𝓝 (1 : P) := by
    exact (Filter.biInter_mem hrange).2 fun y _ ↦ hV y
  obtain ⟨U, hUW, hUopen, hUone⟩ := mem_nhds_iff.mp hW
  obtain ⟨N, hN⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUopen hUone
  refine ⟨N, ?_⟩
  intro p n hn
  have hyp : f p ∈ range f := ⟨p, rfl⟩
  have hnW : n ∈ W := hUW (hN hn)
  have hnV : n ∈ V (f p) := by
    exact mem_iInter₂.mp hnW (f p) hyp
  exact hmul (f p) (Set.mul_mem_mul (show p ∈ f ⁻¹' {f p} by simp) hnV)

/-- An open normal subgroup of a finite power `G^r` contains the coordinate
power of one open normal subgroup of `G`. -/
theorem open_normal_pi
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (r : ℕ) (K : OpenNormalSubgroup (Fin r → G)) :
    ∃ N : OpenNormalSubgroup G,
      ∀ x : Fin r → G, (∀ i, x i ∈ N) → x ∈ K := by
  obtain ⟨u, hu, huK⟩ :=
    isOpen_pi_iff'.mp K.isOpen (1 : Fin r → G) K.one_mem
  choose N hN using fun i : Fin r ↦
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (hu i).1 (by simpa using (hu i).2)
  let N₀ : OpenNormalSubgroup G := Finset.univ.inf N
  refine ⟨N₀, ?_⟩
  intro x hx
  apply huK
  intro i hi
  exact hN i ((Finset.inf_le (f := N) (Finset.mem_univ i)) (hx i))

/-- The factorization step in the proof of Proposition II.4.2.  Every
continuous `r`-cochain on a profinite group with values in a discrete space
factors through `(G/N)^r` for some open normal subgroup `N`. -/
theorem continuous_through_open
    {G Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    [TopologicalSpace Y] [DiscreteTopology Y]
    (r : ℕ) (f : (Fin r → G) → Y) (hf : Continuous f) :
    ∃ N : OpenNormalSubgroup G,
      f.FactorsThrough
        (fun x i ↦ QuotientGroup.mk' (N : Subgroup G) (x i)) := by
  obtain ⟨K, hK⟩ := open_normal_invariant f hf
  obtain ⟨N, hN⟩ := open_normal_pi r K
  refine ⟨N, ?_⟩
  intro x y hxy
  have hxyi : ∀ i, ∃ z ∈ (N : Subgroup G), x i * z = y i := by
    intro i
    exact (QuotientGroup.mk'_eq_mk' (N : Subgroup G)).mp (congrFun hxy i)
  choose z hzN hxz using hxyi
  have hzK : z ∈ K := hN z hzN
  have hmul : f (x * z) = f x := hK x z hzK
  have hxyz : x * z = y := funext hxz
  simpa [hxyz] using hmul.symm

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [MulAction G X] [TopologicalSpace X] [DiscreteTopology X] [ContinuousSMul G X]

/-- A finite set in a discrete continuous profinite `G`-set is fixed
pointwise by one open normal subgroup. -/
theorem open_normal_fixes
    (s : Set X) (hs : s.Finite) :
    ∃ N : OpenNormalSubgroup G,
      ∀ x ∈ s, (N : Subgroup G) ≤ MulAction.stabilizer G x := by
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      obtain ⟨N, -⟩ :=
        ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
          (G := G) isOpen_univ (mem_univ 1)
      exact ⟨N, by simp⟩
  | @insert x s hxs hs ih =>
      obtain ⟨N₁, hN₁⟩ := open_normal_stabilizer (G := G) x
      obtain ⟨N₂, hN₂⟩ := ih
      refine ⟨N₁ ⊓ N₂, ?_⟩
      intro y hy
      rcases mem_insert_iff.mp hy with rfl | hy
      · exact le_trans (show (N₁ ⊓ N₂ : OpenNormalSubgroup G) ≤ N₁ from inf_le_left) hN₁
      · exact le_trans (show (N₁ ⊓ N₂ : OpenNormalSubgroup G) ≤ N₂ from inf_le_right) (hN₂ y hy)

/-- The values of one continuous cochain are all fixed by a common open
normal subgroup.  This is Milne's subgroup `H₀`. -/
theorem open_fixes_range
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (f : A → X) (hf : Continuous f) :
    ∃ N : OpenNormalSubgroup G,
      ∀ a, (N : Subgroup G) ≤ MulAction.stabilizer G (f a) := by
  obtain ⟨N, hN⟩ := open_normal_fixes
    (G := G) (range f) (continuous_compact_discrete hf)
  exact ⟨N, fun a ↦ hN (f a) ⟨a, rfl⟩⟩

/-- The full cochain-level assertion used in Proposition II.4.2.  A
continuous cochain descends to a cochain on a finite quotient, with values in
the elements fixed by the quotient kernel. -/
theorem cochain_descends_points
    (r : ℕ) (f : (Fin r → G) → X) (hf : Continuous f) :
    ∃ N : OpenNormalSubgroup G,
      ∃ fN : (Fin r → G ⧸ (N : Subgroup G)) → MulAction.fixedPoints N X,
        ∀ x, (fN (fun i ↦ QuotientGroup.mk' (N : Subgroup G) (x i)) : X) = f x := by
  obtain ⟨H₀, hH₀⟩ := open_fixes_range (G := G) f hf
  obtain ⟨H₁, hH₁⟩ := continuous_through_open r f hf
  let N : OpenNormalSubgroup G := H₀ ⊓ H₁
  let q : (Fin r → G) → (Fin r → G ⧸ (N : Subgroup G)) :=
    fun x i ↦ QuotientGroup.mk' (N : Subgroup G) (x i)
  have hfix : ∀ x, (N : Subgroup G) ≤ MulAction.stabilizer G (f x) := by
    intro x
    exact le_trans (show N ≤ H₀ from inf_le_left) (hH₀ x)
  have hfac : f.FactorsThrough q := by
    intro x y hxy
    apply hH₁
    funext i
    apply (QuotientGroup.mk'_eq_mk' (H₁ : Subgroup G)).2
    obtain ⟨z, hz, hxz⟩ :=
      (QuotientGroup.mk'_eq_mk' (N : Subgroup G)).1 (congrFun hxy i)
    exact ⟨z, (show N ≤ H₁ from inf_le_right) hz, hxz⟩
  let g : (Fin r → G) → MulAction.fixedPoints N X := fun x ↦
    ⟨f x, fun n ↦ MulAction.mem_stabilizer_iff.mp (hfix x n.property)⟩
  have hg : g.FactorsThrough q := by
    intro x y hxy
    apply Subtype.ext
    exact hfac hxy
  let fN : (Fin r → G ⧸ (N : Subgroup G)) → MulAction.fixedPoints N X :=
    Function.extend q g (fun _ ↦ g 1)
  refine ⟨N, fN, ?_⟩
  intro x
  change (Function.extend q g (fun _ ↦ g 1) (q x)).1 = f x
  rw [hg.extend_apply]

end Submission.CField.PCohom
