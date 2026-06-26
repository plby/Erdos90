import Mathlib
import Towers.Algebra.CompletedGroupAlgebra.CoreBoundedWords
import Towers.Group.PGroup
import Towers.Group.Zassenhaus.Core
import Towers.Group.DenseGenerators.ZassenhausDegreeTwo
import Towers.Group.DenseGenerators.ZassenhausSurjective
import Towers.Group.FrattiniFunctor
import Towers.Group.FinitePGS
import Towers.Group.ProPJennings
import Towers.Group.ProPTopology
import Towers.Group.ProPClosed
import Towers.Group.ZassenhausTrivial

open scoped IsMulCommutative


/-!
# Free pro-p presentations

This file records the topological presentation interface needed by HMR cutting.
It deliberately does not identify a free pro-`p` group with an ordinary
`FreeGroup`: the former carries a profinite topology and a continuous universal
property.

The construction of free pro-`p` groups and the standard depth-two theorem for
minimal pro-`p` presentations are substantial results, so they are exposed as
named theorems below.
-/

open scoped Pointwise Topology

noncomputable section

namespace Towers

universe u v

open PPJennin

namespace ProP

/-- A witness that `G` has a topological generating family of size `d`. -/
def GeneratorCountWitness (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (d : ℕ) : Prop :=
  ∃ s : Fin d → G, TopologicallyGenerates s

/-- The possible finite cardinalities of topological generating families. -/
def generatorCounts (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Set ℕ :=
  {d | GeneratorCountWitness G d}

/-- The pro-`p` generator rank `d_p(G)`, defined as the least size of a finite
topological generating family. It is meaningful once `FiniteGeneratorRank`
is available. -/
noncomputable def generatorRank (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : ℕ :=
  sInf (generatorCounts G)

/-- The assertion that `G` is topologically finitely generated. -/
def FiniteGeneratorRank (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : Prop :=
  (generatorCounts G).Nonempty

/--
Finite-shadow reflection for the positive Zassenhaus subgroup of a finitely
generated pro-`p` group.

This is the remaining group-theoretic input for pro-`p` Zassenhaus openness.
Its proof should use only continuous finite `p`-group shadows of `G`; it must
not use automatic continuity of arbitrary finite-index subgroups.
-/
theorem shadow_intersection_pro
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (_hProP : ProPGroup p G)
    {d : ℕ} (_s : Fin d → G)
    (_hs : TopologicallyGenerates _s)
    {n : ℕ} (_hn : 1 < n) :
    Nonempty
      (FiniteShadowIntersection
        (p := p) (Γ := G) _s _hs n) := by
  refine ⟨?_⟩
  refine ⟨?_⟩
  intro g hg
  by_contra hmem
  have hclosed :
      IsClosed ((zassenhausFiltration p G n : Subgroup G) : Set G) :=
    closed_pro_p p _hProP _s _hs n
  rcases
      separate_sets_disconnected
        hclosed g hmem with
    ⟨N, hN⟩
  letI : DiscreteTopology (G ⧸ N.toSubgroup) :=
    pro_discrete_topology N
  letI : Finite (G ⧸ N.toSubgroup) :=
    pro_p_open N
  let q : G →* G ⧸ N.toSubgroup := QuotientGroup.mk' N.toSubgroup
  have hqg : q g ∈ zassenhausFiltration p (G ⧸ N.toSubgroup) n :=
    hg q (pro_open_continuous N)
  apply hN
  have hmap :
      Subgroup.map q (zassenhausFiltration p G n) =
        zassenhausFiltration p (G ⧸ N.toSubgroup) n :=
    filtration_without_width
      n q (QuotientGroup.mk'_surjective N.toSubgroup)
  have hqg_map :
      q g ∈ Subgroup.map q (zassenhausFiltration p G n) := by
    rw [hmap]
    exact hqg
  exact hqg_map

lemma pro_dense_subgroup
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

lemma pro_fg_torsion
    (G : Type u) [Group G] [Group.IsNilpotent G]
    [Group.FG G] (hT : Monoid.IsTorsion G) :
    Finite G := by
  classical
  let P : (G : Type u) → [Group G] → [Group.IsNilpotent G] → Prop :=
    fun (G : Type u) [Group G] [Group.IsNilpotent G] =>
      Group.FG G → Monoid.IsTorsion G → Finite G
  exact
    Group.nilpotent_center_quotient_ind (P := P) G
      (hbase := by
        intro G _ _hsub hfg hT
        exact Finite.of_injective (fun _ : G => PUnit.unit)
          (fun x y _ => Subsingleton.elim x y))
      (hstep := by
        intro G _ _hNil ih hfg hT
        haveI : Group.FG G := hfg
        haveI : Group.FG (G ⧸ Subgroup.center G) := inferInstance
        have hTquot : Monoid.IsTorsion (G ⧸ Subgroup.center G) :=
          IsTorsion.of_surjective
            (QuotientGroup.mk'_surjective (Subgroup.center G)) hT
        haveI : Finite (G ⧸ Subgroup.center G) :=
          ih inferInstance hTquot
        haveI : (Subgroup.center G).FiniteIndex :=
          Subgroup.finiteIndex_of_finite_quotient
        haveI : Group.FG (Subgroup.center G) := inferInstance
        letI : CommGroup (Subgroup.center G) :=
          { (inferInstance : Group (Subgroup.center G)) with
            mul_comm := mul_comm' }
        have hTcenter : Monoid.IsTorsion (Subgroup.center G) :=
          IsTorsion.subgroup hT (Subgroup.center G)
        haveI : Finite (Subgroup.center G) :=
          CommGroup.finite_of_fg_torsion (Subgroup.center G) hTcenter
        exact Finite.of_subgroup_quotient (Subgroup.center G))
      inferInstance hT

/--
The Zassenhaus filtration terms of a topologically finitely generated pro-`p`
group are open.

This is the standard pro-`p` Zassenhaus openness theorem.  It is deliberately
exposed in the pro-`p` presentation layer: applications should use this result
directly rather than the stronger automatic-continuity theorem for arbitrary
finitely generated profinite groups.
-/
theorem filtration_topologically_generates
    (p : ℕ) [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (_hProP : ProPGroup p G)
    {d : ℕ} (_s : Fin d → G)
    (_hs : TopologicallyGenerates _s)
    (n : ℕ) :
    IsOpen ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  by_cases hn : n ≤ 1
  · rw [zassenhaus_filtration_top p G hn]
    exact isOpen_univ
  · have hn' : 1 < n := by omega
    let Hshadow :
        FiniteShadowIntersection
          (p := p) (Γ := G) _s _hs n :=
      Classical.choice
        (shadow_intersection_pro
          p _hProP _s _hs hn')
    let H : Subgroup G := Subgroup.closure (Set.range _s)
    let D : Subgroup H := zassenhausFiltration p H n
    letI : D.Normal := by
      dsimp [D]
      exact zassenhausFiltration_normal p H n
    let Q : Type u := H ⧸ D
    letI : Group Q := by
      dsimp [Q]
      infer_instance
    haveI : Group.FG H := by
      dsimp [H]
      infer_instance
    haveI : Group.FG Q := by
      dsimp [Q]
      exact Group.fg_of_surjective (QuotientGroup.mk'_surjective D)
    have hQbot : zassenhausFiltration p Q n = ⊥ := by
      simpa [Q, D, zassenhausSelfQuotient] using
        (filtration_self_bot p H n)
    letI : Group.IsNilpotent Q :=
      nilpotent_filtration_bot hn' hQbot
    have hQTorsion : Monoid.IsTorsion Q := by
      have hQPGroup : IsPGroup p Q :=
        p_filtration_bot hQbot
      intro x
      rcases hQPGroup x with ⟨k, hk⟩
      exact isOfFinOrder_iff_pow_eq_one.mpr
        ⟨p ^ k, pow_pos (Fact.out : Nat.Prime p).pos k, hk⟩
    letI : Finite Q :=
      pro_fg_torsion Q hQTorsion
    let K : Subgroup G := D.map H.subtype
    let J : Subgroup G := Subgroup.normalClosure (K : Set G)
    let C : Subgroup G := J.topologicalClosure
    have hCclosed : IsClosed (C : Set G) := by
      dsimp [C]
      exact Subgroup.isClosed_topologicalClosure J
    letI : J.Normal := by
      dsimp [J]
      exact Subgroup.normalClosure_normal
    letI : C.Normal := by
      dsimp [C]
      exact Subgroup.is_normal_topologicalClosure J
    have hC_le : C ≤ zassenhausFiltration p G n := by
      intro g hg
      apply Hshadow.forall_finite_quotient g
      intro Λ _instGroupΛ _instTopΛ _instDiscreteΛ _instFiniteΛ φ hφ
      let L : Subgroup G := (zassenhausFiltration p Λ n).comap φ
      letI : (zassenhausFiltration p Λ n).Normal :=
        zassenhausFiltration_normal p Λ n
      letI : L.Normal := by
        dsimp [L]
        exact
          (show (zassenhausFiltration p Λ n).Normal from inferInstance).comap φ
      have hLclosed : IsClosed (L : Set G) := by
        change
          IsClosed
            ((fun x : G => φ x) ⁻¹'
              ((zassenhausFiltration p Λ n : Subgroup Λ) : Set Λ))
        exact (isClosed_discrete _).preimage hφ
      have hK_le_L : K ≤ L := by
        intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        exact
          filtration_map_mem
            (p := p) (n := n) (f := φ.comp H.subtype) hy
      have hJ_le_L : J ≤ L := by
        dsimp [J]
        exact Subgroup.normalClosure_le_normal hK_le_L
      have hC_le_L : C ≤ L := by
        dsimp [C]
        exact
          pro_topological_closed
            hJ_le_L hLclosed
      exact hC_le_L hg
    let q : G →* G ⧸ C := QuotientGroup.mk' C
    have hD_le_ker : D ≤ (q.comp H.subtype).ker := by
      intro x hx
      apply (QuotientGroup.eq_one_iff (N := C) (H.subtype x)).mpr
      apply J.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      exact ⟨x, hx, rfl⟩
    let ψ : Q →* G ⧸ C :=
      QuotientGroup.lift D (q.comp H.subtype) hD_le_ker
    let L : Subgroup (G ⧸ C) := ψ.range
    haveI : Finite L := by
      exact
        Finite.of_surjective ψ.rangeRestrict
          ψ.rangeRestrict_surjective
    let M : Subgroup (G ⧸ C) :=
      Subgroup.closure (Set.range (fun i : Fin d => q (_s i)))
    have hM_le_L : M ≤ L := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      let siH : H :=
        ⟨_s i, Subgroup.subset_closure ⟨i, rfl⟩⟩
      refine ⟨QuotientGroup.mk' D siH, ?_⟩
      change
        ((QuotientGroup.lift D (q.comp H.subtype) hD_le_ker).comp
            (QuotientGroup.mk' D)) siH =
          q (_s i)
      rw [QuotientGroup.lift_comp_mk']
      rfl
    haveI : Finite M := by
      exact
        Finite.of_injective
          (fun x : M => (⟨x, hM_le_L x.property⟩ : L))
          (fun x y h =>
            Subtype.ext (congrArg (fun z : L => (z : G ⧸ C)) h))
    letI : IsClosed (C : Set G) := hCclosed
    letI : T2Space (G ⧸ C) := by
      infer_instance
    have hMdense :
        closure ((M : Subgroup (G ⧸ C)) : Set (G ⧸ C)) =
          Set.univ := by
      simpa [M, q] using
        (pro_dense_generators
          (Hq := C) _s _hs)
    haveI : Finite (G ⧸ C) :=
      pro_dense_subgroup M hMdense
    haveI : C.FiniteIndex :=
      Subgroup.finiteIndex_of_finite_quotient
    exact
      Subgroup.isOpen_mono hC_le
        (C.isOpen_of_isClosed_of_finiteIndex hCclosed)

/-- A finite generator rank is realized by an actual dense family. -/
theorem generator_rank_counts
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : FiniteGeneratorRank G) :
    GeneratorCountWitness G (generatorRank G) := by
  exact Nat.sInf_mem hG

/-- A homomorphism bundled with the continuity required in the pro-`p`
category. -/
structure ContinuousHom (G : Type u) (H : Type v)
    [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] where
  toMonoidHom : G →* H
  continuous_toFun : Continuous toMonoidHom

instance ContinuousHom.instFunLike
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] :
    FunLike (ContinuousHom G H) G H where
  coe f := f.toMonoidHom
  coe_injective' := by
    intro f g h
    cases f
    cases g
    congr
    apply MonoidHom.ext
    intro x
    exact congrFun h x

@[simp] theorem ContinuousHom.coe_monoidHom
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (f : ContinuousHom G H) :
    ⇑f.toMonoidHom = f := rfl

/--
A free pro-`p` group on `d` generators, bundled with its profinite structure and
continuous universal property.

The target is kept in the same universe as the free group. This is sufficient
for the project-local presentation layer and avoids introducing a separate
universe-lifting API.
-/
structure FreeGroup (p d : ℕ) where
  Carrier : Type u
  [instGroup : Group Carrier]
  [instTopologicalSpace : TopologicalSpace Carrier]
  [topologicalGroup : IsTopologicalGroup Carrier]
  [instCompactSpace : CompactSpace Carrier]
  [totallyDisconnected : TotallyDisconnectedSpace Carrier]
  generator : Fin d → Carrier
  dense_generator : TopologicallyGenerates generator
  isProP : ProPGroup p Carrier
  lift :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [TotallyDisconnectedSpace G],
      ProPGroup p G → (Fin d → G) → ContinuousHom Carrier G
  lift_generator :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [TotallyDisconnectedSpace G]
      (hG : ProPGroup p G) (s : Fin d → G) (i : Fin d),
      lift hG s (generator i) = s i
  lift_unique :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [TotallyDisconnectedSpace G]
      (hG : ProPGroup p G) (s : Fin d → G) (f : ContinuousHom Carrier G),
      (∀ i, f (generator i) = s i) → f = lift hG s

attribute [instance] FreeGroup.instGroup
attribute [instance] FreeGroup.instTopologicalSpace
attribute [instance] FreeGroup.topologicalGroup
attribute [instance] FreeGroup.instCompactSpace
attribute [instance] FreeGroup.totallyDisconnected

namespace FGBuild

theorem ContinuousHom.ext_topologi_generates
    {F H : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    {s : Fin d → F} (hs : TopologicallyGenerates s)
    (f g : ContinuousHom F H) (h : ∀ i, f (s i) = g (s i)) :
    f = g := by
  let E : Subgroup F :=
    { carrier := {x | f x = g x}
      one_mem' := by
        change f 1 = g 1
        rw [show f 1 = 1 from f.toMonoidHom.map_one,
          show g 1 = 1 from g.toMonoidHom.map_one]
      mul_mem' := by
        intro x y hx hy
        change f.toMonoidHom (x * y) = g.toMonoidHom (x * y)
        rw [map_mul, map_mul]
        change f.toMonoidHom x = g.toMonoidHom x at hx
        change f.toMonoidHom y = g.toMonoidHom y at hy
        rw [hx, hy]
      inv_mem' := by
        intro x hx
        change f.toMonoidHom x⁻¹ = g.toMonoidHom x⁻¹
        rw [map_inv, map_inv]
        change f.toMonoidHom x = g.toMonoidHom x at hx
        rw [hx] }
  have hEclosed : IsClosed (E : Set F) := by
    change IsClosed {x | f x = g x}
    exact isClosed_eq f.continuous_toFun g.continuous_toFun
  have hclosure : Subgroup.closure (Set.range s) ≤ E := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  have htop : (⊤ : Subgroup F) ≤ E := by
    rw [← hs]
    exact Subgroup.topologicalClosure_minimal _ hclosure hEclosed
  apply ContinuousHom.instFunLike.coe_injective'
  funext x
  change f x = g x
  exact htop (by simp)

/-- A copy of `Fin n` without its built-in cyclic group structure. -/
def SCarrie (n : ℕ) :=
  Fin n

namespace SCarrie

instance (n : ℕ) : Finite (SCarrie n) := by
  exact Finite.of_equiv (Fin n) (Equiv.refl _)

def equivFin (n : ℕ) : SCarrie n ≃ Fin n :=
  Equiv.refl _

end SCarrie

/-- A finite `p`-group together with a displayed `d`-tuple.  Using `SCarrie card`
keeps the indexing type small while the actual product factors are lifted into
the universe of the free group. -/
structure PGTuple (p d : ℕ) where
  card : ℕ
  [group : Group (SCarrie card)]
  isPGroup : IsPGroup p (SCarrie card)
  generator : Fin d → SCarrie card

namespace PGTuple

def Carrier (Q : PGTuple p d) :=
  ULift.{u} (SCarrie Q.card)

instance (Q : PGTuple p d) : Group Q.Carrier := by
  letI : Group (SCarrie Q.card) := Q.group
  exact Equiv.ulift.group

instance (Q : PGTuple p d) : Finite Q.Carrier := by
  exact Finite.of_equiv (SCarrie Q.card) Equiv.ulift.symm

instance (Q : PGTuple p d) : TopologicalSpace Q.Carrier := ⊥

instance (Q : PGTuple p d) : DiscreteTopology Q.Carrier := ⟨rfl⟩

instance (Q : PGTuple p d) : IsTopologicalGroup Q.Carrier := by
  infer_instance

instance (Q : PGTuple p d) : CompactSpace Q.Carrier := by
  exact Finite.compactSpace

instance (Q : PGTuple p d) : TotallyDisconnectedSpace Q.Carrier := by
  infer_instance

end PGTuple

abbrev Ambient (p d : ℕ) :=
  ∀ Q : PGTuple p d, Q.Carrier

instance (p d : ℕ) : Group (Ambient.{u} p d) := by
  unfold Ambient
  infer_instance

instance (p d : ℕ) : IsTopologicalGroup (Ambient.{u} p d) := by
  unfold Ambient
  letI : ∀ Q : PGTuple p d, IsTopologicalGroup Q.Carrier :=
    fun Q => PGTuple.instIsTopologicalGroupCarrier Q
  exact Pi.topologicalGroup

def ambientGenerator (p d : ℕ) (i : Fin d) : Ambient.{u} p d :=
  fun Q => ULift.up (Q.generator i)

def ambientGenerated (p d : ℕ) : Subgroup (Ambient.{u} p d) :=
  Subgroup.closure (Set.range (ambientGenerator.{u} p d))

abbrev Carrier (p d : ℕ) :=
  (ambientGenerated.{u} p d).topologicalClosure

instance (p d : ℕ) : CompactSpace (Carrier.{u} p d) :=
  isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_topologicalClosure (ambientGenerated p d)).isCompact

def generator (p d : ℕ) (i : Fin d) : Carrier.{u} p d :=
  ⟨ambientGenerator p d i,
    (ambientGenerated p d).le_topologicalClosure (Subgroup.subset_closure (Set.mem_range_self i))⟩

theorem dense_generator (p d : ℕ) :
    TopologicallyGenerates (generator.{u} p d) := by
  let S := Subgroup.closure (Set.range (generator.{u} p d))
  let inclusion : Carrier.{u} p d →* Ambient.{u} p d :=
    Subgroup.subtype _
  have hgenerated : ambientGenerated.{u} p d ≤ S.map inclusion := by
    unfold ambientGenerated
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨generator p d i, Subgroup.subset_closure (Set.mem_range_self i), rfl⟩
  apply le_antisymm le_top
  intro x _
  change x ∈ closure (S : Set (Carrier p d))
  rw [closure_subtype]
  apply closure_mono (s := (ambientGenerated p d : Set (Ambient p d)))
  · intro y hy
    rcases hgenerated hy with ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · exact x.property

theorem isProP (p d : ℕ) [Fact p.Prime] :
    ProPGroup p (Carrier.{u} p d) := by
  intro N
  rcases isOpen_induced_iff.mp
      (show IsOpen (N : Set (Carrier.{u} p d)) from N.isOpen') with
    ⟨U, hUopen, hUN⟩
  have h1U : (1 : Ambient.{u} p d) ∈ U := by
    have h1N : (1 : Carrier.{u} p d) ∈ (N : Set (Carrier.{u} p d)) := N.one_mem
    rw [← hUN] at h1N
    exact h1N
  rcases (isOpen_pi_iff.mp hUopen) 1 h1U with ⟨I, V, hV, hVU⟩
  let proj : Carrier.{u} p d →* (∀ Q : I, (Q.val : PGTuple p d).Carrier) :=
    { toFun := fun x Q => (x : Ambient p d) (Subtype.val Q)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hker : proj.ker ≤ (N : Subgroup (Carrier p d)) := by
    intro x hx
    change proj x = 1 at hx
    change x ∈ (N : Set (Carrier p d))
    rw [← hUN]
    apply hVU
    intro Q hQI
    have hxQ : (x : Ambient p d) Q = 1 := congrFun hx ⟨Q, hQI⟩
    change (x : Ambient p d) Q ∈ V Q
    rw [hxQ]
    exact (hV Q hQI).2
  have hprod : IsPGroup p (∀ Q : I, (Q.val : PGTuple p d).Carrier) := by
    apply Towers.p_pi_fintype
    intro Q x
    rcases Q.val.isPGroup x.down with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply ULift.ext
    exact hk
  have hrange : IsPGroup p proj.range :=
    hprod.to_subgroup proj.range
  have hquotKer : IsPGroup p (Carrier.{u} p d ⧸ proj.ker) :=
    hrange.of_equiv (QuotientGroup.quotientKerEquivRange proj).symm
  let q : (Carrier.{u} p d ⧸ proj.ker) →* (Carrier.{u} p d ⧸ (N : Subgroup (Carrier p d))) :=
    QuotientGroup.lift proj.ker (QuotientGroup.mk' (N : Subgroup (Carrier p d))) (by
      simpa using hker)
  apply hquotKer.of_surjective q
  intro y
  rcases QuotientGroup.mk'_surjective (N : Subgroup (Carrier p d)) y with ⟨x, rfl⟩
  refine ⟨QuotientGroup.mk' proj.ker x, ?_⟩
  simp [q]

noncomputable def quotientEquiv
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (N : OpenNormalSubgroup G) :
    (G ⧸ (N : Subgroup G)) ≃ Fin (Nat.card (G ⧸ (N : Subgroup G))) := by
  letI : Finite (G ⧸ (N : Subgroup G)) :=
    Subgroup.quotient_finite_of_isOpen (N : Subgroup G) N.isOpen'
  exact Finite.equivFin _

noncomputable def quotientTuple
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (hG : ProPGroup p G) (s : Fin d → G)
    (N : OpenNormalSubgroup G) : PGTuple p d := by
  let e := (quotientEquiv N).trans (SCarrie.equivFin _).symm
  letI groupFin : Group (SCarrie (Nat.card (G ⧸ (N : Subgroup G)))) := e.symm.group
  exact
    { card := Nat.card (G ⧸ (N : Subgroup G))
      group := groupFin
      isPGroup := (hG N).of_equiv
        { toEquiv := e
          map_mul' := by
            intro x y
            change e (x * y) = e (e.symm (e x) * e.symm (e y))
            simp }
      generator := fun i => e (QuotientGroup.mk' (N : Subgroup G) (s i)) }

def evaluation (Q : PGTuple p d) :
    Carrier.{u} p d →* Q.Carrier where
  toFun x := (x : Ambient p d) Q
  map_one' := rfl
  map_mul' _ _ := rfl

theorem evaluation_continuous (Q : PGTuple p d) :
    Continuous (evaluation Q) :=
  (continuous_apply Q).comp continuous_subtype_val

@[simp] theorem evaluation_generator (Q : PGTuple p d) (i : Fin d) :
    evaluation Q (generator p d i) = ULift.up (Q.generator i) :=
  rfl

noncomputable def quotientTupleEquiv
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (hG : ProPGroup p G) (s : Fin d → G)
    (N : OpenNormalSubgroup G) :
    (G ⧸ (N : Subgroup G)) ≃* PGTuple.Carrier.{u} (quotientTuple hG s N) := by
  let e := (quotientEquiv N).trans (SCarrie.equivFin _).symm
  let Q := quotientTuple hG s N
  refine
    { toFun := fun x => ULift.up (e x)
      invFun := fun x => e.symm x.down
      left_inv := fun x => by simp
      right_inv := fun x => by
        cases x
        simp
      map_mul' := ?_ }
  intro x y
  change ULift.up (e (x * y)) =
    ULift.up (e (e.symm (e x) * e.symm (e y)))
  simp

noncomputable def quotientCoordinate
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (hG : ProPGroup p G) (s : Fin d → G)
    (N : OpenNormalSubgroup G) :
    ContinuousHom (Carrier.{u} p d) (G ⧸ (N : Subgroup G)) := by
  let Q := quotientTuple hG s N
  refine
    { toMonoidHom :=
        (quotientTupleEquiv hG s N).symm.toMonoidHom.comp (evaluation Q)
      continuous_toFun := ?_ }
  change Continuous (fun x =>
    (quotientTupleEquiv hG s N).symm ((evaluation Q) x))
  apply Continuous.comp ?_ (evaluation_continuous Q)
  exact continuous_of_discreteTopology

@[simp] theorem quotientCoordinate_generator
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (hG : ProPGroup p G) (s : Fin d → G)
    (N : OpenNormalSubgroup G) (i : Fin d) :
    quotientCoordinate hG s N (generator p d i) =
      QuotientGroup.mk' (N : Subgroup G) (s i) := by
  change (quotientTupleEquiv hG s N).symm
      ((evaluation (quotientTuple hG s N)) (generator p d i)) =
    QuotientGroup.mk' (N : Subgroup G) (s i)
  rw [evaluation_generator]
  change (quotientTupleEquiv hG s N).symm
      (quotientTupleEquiv hG s N (QuotientGroup.mk' (N : Subgroup G) (s i))) =
    QuotientGroup.mk' (N : Subgroup G) (s i)
  exact (quotientTupleEquiv hG s N).left_inv _

theorem quotientCoordinate_map
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (hG : ProPGroup p G) (s : Fin d → G)
    (N M : OpenNormalSubgroup G) (hNM : (N : Subgroup G) ≤ (M : Subgroup G)) :
    (QuotientGroup.map (N : Subgroup G) (M : Subgroup G) (MonoidHom.id G) hNM).comp
        (quotientCoordinate hG s N).toMonoidHom =
      (quotientCoordinate hG s M).toMonoidHom := by
  let left : ContinuousHom (Carrier.{u} p d) (G ⧸ (M : Subgroup G)) :=
    { toMonoidHom :=
        (QuotientGroup.map (N : Subgroup G) (M : Subgroup G) (MonoidHom.id G) hNM).comp
          (quotientCoordinate hG s N).toMonoidHom
      continuous_toFun :=
        (show Continuous
              (QuotientGroup.map (N : Subgroup G) (M : Subgroup G) (MonoidHom.id G) hNM) from
            continuous_of_discreteTopology).comp
          (quotientCoordinate hG s N).continuous_toFun }
  let right : ContinuousHom (Carrier.{u} p d) (G ⧸ (M : Subgroup G)) :=
    quotientCoordinate hG s M
  have hleft_right : left = right := by
    apply ContinuousHom.ext_topologi_generates (dense_generator p d)
    intro i
    rw [show left (generator p d i) =
        QuotientGroup.map (N : Subgroup G) (M : Subgroup G) (MonoidHom.id G) hNM
          (quotientCoordinate hG s N (generator p d i)) from rfl,
      quotientCoordinate_generator, quotientCoordinate_generator]
    rfl
  exact congrArg ContinuousHom.toMonoidHom hleft_right

noncomputable def quotientCone
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : ProPGroup p G) (s : Fin d → G) :
    CategoryTheory.Limits.Cone (ProfiniteGrp.diagram (ProfiniteGrp.of G)) where
  pt := ProfiniteGrp.of (Carrier.{u} p d)
  π :=
    { app := fun N => by
        letI : TopologicalSpace (G ⧸ (N : Subgroup G)) := ⊥
        letI : DiscreteTopology (G ⧸ (N : Subgroup G)) := ⟨rfl⟩
        letI : IsTopologicalGroup (G ⧸ (N : Subgroup G)) := by infer_instance
        exact
          ProfiniteGrp.ofHom
            (Y := (ProfiniteGrp.diagram (ProfiniteGrp.of G)).obj N)
            { toMonoidHom :=
                (quotientTupleEquiv hG s N).symm.toMonoidHom.comp
                  (evaluation (quotientTuple hG s N))
              continuous_toFun := by
                exact
                  (show Continuous
                      (fun x : PGTuple.Carrier.{u} (quotientTuple hG s N) =>
                        ((quotientTupleEquiv hG s N).symm x :
                          (ProfiniteGrp.diagram (ProfiniteGrp.of G)).obj N)) from
                    continuous_of_discreteTopology).comp
                      (evaluation_continuous (quotientTuple hG s N)) }
      naturality := by
        intro N M f
        apply ProfiniteGrp.hom_ext
        apply ContinuousMonoidHom.ext
        intro x
        simpa [ProfiniteGrp.diagram, ProfiniteGrp.toFiniteQuotientFunctor] using
          (DFunLike.congr_fun
            (quotientCoordinate_map hG s N M (CategoryTheory.leOfHom f)) x).symm }

noncomputable def lift
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : ProPGroup p G) (s : Fin d → G) :
    ContinuousHom (Carrier.{u} p d) G := by
  let f :=
    (ProfiniteGrp.isLimitCone (ProfiniteGrp.of G)).lift (quotientCone hG s)
  exact
    { toMonoidHom := f.hom.toMonoidHom
      continuous_toFun := f.hom.continuous_toFun }

theorem lift_generator
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : ProPGroup p G) (s : Fin d → G) (i : Fin d) :
    lift hG s (generator p d i) = s i := by
  apply ProfiniteGrp.toLimit_injective (ProfiniteGrp.of G)
  apply Subtype.ext
  funext N
  have hfac :=
    (ProfiniteGrp.isLimitCone (ProfiniteGrp.of G)).fac (quotientCone hG s) N
  have happ := congrArg (fun f => f (generator p d i)) hfac
  have happ' :
      QuotientGroup.mk' (N : Subgroup G) (lift hG s (generator p d i)) =
        quotientCoordinate hG s N (generator p d i) := by
    simpa only [lift, quotientCone, ProfiniteGrp.cone, ProfiniteGrp.proj,
      ProfiniteGrp.hom_comp, ProfiniteGrp.hom_ofHom, ContinuousMonoidHom.comp_toFun] using happ
  change QuotientGroup.mk' (N : Subgroup G) (lift hG s (generator p d i)) =
    QuotientGroup.mk' (N : Subgroup G) (s i)
  exact happ'.trans (quotientCoordinate_generator hG s N i)

theorem lift_unique
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : ProPGroup p G) (s : Fin d → G) (f : ContinuousHom (Carrier.{u} p d) G)
    (hf : ∀ i, f (generator p d i) = s i) :
    f = lift hG s := by
  apply ContinuousHom.ext_topologi_generates (dense_generator p d)
  intro i
  rw [hf i, lift_generator hG s i]

end FGBuild

/-- Construction of the free pro-`p` group on a finite family. -/
theorem freeGroup_exists (p d : ℕ) [Fact p.Prime] :
    Nonempty (FreeGroup.{u} p d) := by
  exact
    ⟨{ Carrier := FGBuild.Carrier p d
       generator := FGBuild.generator p d
       dense_generator := FGBuild.dense_generator p d
       isProP := FGBuild.isProP p d
       lift := FGBuild.lift
       lift_generator := FGBuild.lift_generator
       lift_unique := FGBuild.lift_unique }⟩

/-- A chosen free pro-`p` group on `d` generators. -/
noncomputable def freeGroup (p d : ℕ) [Fact p.Prime] : FreeGroup.{u} p d :=
  Classical.choice (freeGroup_exists p d)

/--
A finite free pro-`p` presentation of `G`: a continuous quotient of a free
pro-`p` group whose kernel is topologically normally generated by the listed
relators.
-/
structure Presentation (p d r : ℕ) (G : Type v)
    [Group G] [TopologicalSpace G] where
  free : FreeGroup.{u} p d
  quotientMap : free.Carrier →* G
  quotientMap_continuous : Continuous quotientMap
  quotientMap_surjective : Function.Surjective quotientMap
  relator : Fin r → free.Carrier
  kernel_eq :
    MonoidHom.ker quotientMap =
      (Subgroup.normalClosure (Set.range relator)).topologicalClosure

/-- A relator in a pro-`p` presentation has depth at least `n` when it belongs
to the closure of the `n`th algebraic Zassenhaus term of the free pro-`p`
group. -/
def Presentation.RelatorsHaveDepthleast
    {p d r : ℕ} {G : Type v} [Group G] [TopologicalSpace G]
    (P : Presentation.{u, v} p d r G) (n : ℕ) : Prop :=
  ∀ i, P.relator i ∈ (zassenhausFiltration p P.free.Carrier n).topologicalClosure

/-- A witness that `G` has a pro-`p` presentation with `d` generators and `r`
relations. -/
def RelationCountWitness (p : ℕ) (G : Type v) [Group G] [TopologicalSpace G]
    (d r : ℕ) : Prop :=
  Nonempty (Presentation.{v, v} p d r G)

/-- The possible relation counts in presentations on a fixed number of
generators. -/
def relationCountsGenerators (p : ℕ) (G : Type u) [Group G]
    [TopologicalSpace G] (d : ℕ) : Set ℕ :=
  {r | RelationCountWitness p G d r}

/-- The pro-`p` relation rank `r_p(G)`: the least relation count among finite
presentations on exactly `d_p(G)` generators. -/
noncomputable def relationRank (p : ℕ) (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] : ℕ :=
  sInf (relationCountsGenerators p G (generatorRank G))

/-- The assertion that `G` has a finite pro-`p` presentation on a minimal
topological generating family. -/
def FiniteRelationRank (p : ℕ) (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  (relationCountsGenerators p G (generatorRank G)).Nonempty

/-- A finite relation rank is realized by an actual free pro-`p`
presentation. -/
theorem relation_rank_counts
    (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : FiniteRelationRank p G) :
    RelationCountWitness p G (generatorRank G) (relationRank p G) := by
  exact Nat.sInf_mem hG

/-- Choose a minimal finite free pro-`p` presentation. -/
noncomputable def minimalPresentation
    (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : FiniteRelationRank p G) :
    Presentation p (generatorRank G) (relationRank p G) G :=
  Classical.choice (relation_rank_counts p G hG)

/--
The relators of a minimal finite pro-`p` presentation lie in the second
Zassenhaus term. This is the standard Frattini/minimality input, stated
separately from every arithmetic relation-rank estimate.
-/
theorem minimal_presentation_relators
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (_hProP : ProPGroup p G)
    (_hGen : FiniteGeneratorRank G)
    (hRel : FiniteRelationRank p G) :
    (minimalPresentation p G hRel).RelatorsHaveDepthleast 2 := by
  classical
  let P := minimalPresentation p G hRel
  let F := P.free.Carrier
  let qG : F →* G := P.quotientMap
  let Φ : Subgroup F := modPFrattini p F
  let C : Subgroup F := Φ.topologicalClosure
  haveI : Φ.Normal := by
    dsimp [Φ]
    infer_instance
  haveI : C.Normal := by
    exact Subgroup.is_normal_topologicalClosure Φ
  let π : F →* F ⧸ C := QuotientGroup.mk' C
  have hker_le : qG.ker ≤ C := by
    intro x hxker
    by_contra hxC
    let V := F ⧸ C
    haveI : T2Space F := t_space_disconnected F
    haveI : IsClosed (C : Set F) := by
      exact Subgroup.isClosed_topologicalClosure Φ
    haveI : T2Space V := by
      dsimp [V]
      infer_instance
    letI : IsMulCommutative V :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := C)).2
        ((le_sup_right : _root_.commutator F ≤ modPFrattini p F).trans
          Φ.le_topologicalClosure)
    letI : CommGroup V := inferInstance
    have hVpow : ∀ y : V, y ^ p = 1 := by
      intro y
      refine QuotientGroup.induction_on y ?_
      intro g
      apply (QuotientGroup.eq_one_iff (N := C) (g ^ p)).2
      exact Φ.le_topologicalClosure (pow_mod_frattini p F g)
    letI : Module (ZMod p) (Additive V) :=
      AddCommGroup.zmodModule (n := p) (by
        intro y
        induction y using Additive.rec with
        | ofMul z =>
            change Additive.ofMul (z ^ p) = 0
            simp [hVpow])
    let genV : Fin (generatorRank G) → V :=
      fun i => π (P.free.generator i)
    let H : Subgroup V := Subgroup.closure (Set.range genV)
    have hHdense : closure ((H : Subgroup V) : Set V) = Set.univ := by
      simpa [H, genV, π, V] using
        pro_dense_generators
          P.free.generator P.free.dense_generator (Hq := C)
    haveI : Finite H := by
      letI : Group.FG H := by
        dsimp [H]
        infer_instance
      have htor : Monoid.IsTorsion H := by
        intro y
        exact isOfFinOrder_iff_pow_eq_one.mpr
          ⟨p, (Fact.out : Nat.Prime p).pos, by
            apply Subtype.ext
            exact hVpow y⟩
      exact CommGroup.finite_of_fg_torsion H htor
    have hHtop : H = ⊤ := by
      apply SetLike.coe_injective
      have hHclosed : IsClosed ((H : Subgroup V) : Set V) :=
        (Set.toFinite ((H : Subgroup V) : Set V)).isClosed
      rw [← hHclosed.closure_eq, hHdense]
      rfl
    let qA : Fin (generatorRank G) → Additive V :=
      fun i => Additive.ofMul (genV i)
    let xA : Additive V := Additive.ofMul (π x)
    let W : Submodule (ZMod p) (Additive V) :=
      Submodule.span (ZMod p) (Set.range qA)
    have hxπ : π x ≠ 1 := by
      intro hx
      exact hxC ((QuotientGroup.eq_one_iff (N := C) x).mp hx)
    have hxspan : xA ∈ W.carrier := by
      have hxH : π x ∈ H := by
        rw [hHtop]
        exact Subgroup.mem_top _
      change π x ∈ Subgroup.closure (Set.range genV) at hxH
      refine Subgroup.closure_induction
        (k := Set.range genV)
        (p := fun y _hy => Additive.ofMul y ∈ W.carrier)
        ?mem ?one ?mul ?inv hxH
      · intro y hy
        rcases hy with ⟨i, rfl⟩
        exact Submodule.subset_span (R := ZMod p) ⟨i, rfl⟩
      · exact Submodule.zero_mem _
      · intro y z _hy _hz hy hz
        exact Submodule.add_mem _ hy hz
      · intro y _hy hy
        exact Submodule.neg_mem _ hy
    rcases
        (Submodule.mem_span_range_iff_exists_fun
          (R := ZMod p) (v := qA) (x := xA)).mp (by simpa [W] using hxspan) with
      ⟨c, hc⟩
    obtain ⟨a, ha⟩ : ∃ a, c a ≠ 0 := by
      by_contra h
      push Not at h
      apply hxπ
      change Additive.ofMul (π x) = Additive.ofMul 1
      simpa [xA, h] using hc.symm
    let β := {j : Fin (generatorRank G) // j ≠ a}
    let eβ : β ≃ Fin (Fintype.card β) := Fintype.equivFin β
    let smallF : Fin (Fintype.card β) → F :=
      fun i => P.free.generator ((eβ.symm i).1)
    let K₀ : Subgroup F := Subgroup.closure (Set.range smallF)
    let K : Subgroup F := K₀ ⊔ qG.ker
    let S : Subgroup V := K.map π
    let SA : AddSubgroup (Additive V) := S.toAddSubgroup
    have hqA_other {j : Fin (generatorRank G)} (hj : j ≠ a) :
        qA j ∈ SA := by
      change π (P.free.generator j) ∈ S
      refine ⟨P.free.generator j, ?_, rfl⟩
      apply (le_sup_left : K₀ ≤ K)
      exact Subgroup.subset_closure
        ⟨eβ ⟨j, hj⟩, by simp [smallF]⟩
    have hxA_S : xA ∈ SA := by
      change π x ∈ S
      exact ⟨x, (le_sup_right : qG.ker ≤ K) hxker, rfl⟩
    have hsmul_mem (r : ZMod p) {z : Additive V} (hz : z ∈ SA) :
        r • z ∈ SA := by
      rw [← ZMod.natCast_zmod_val r, Nat.cast_smul_eq_nsmul]
      exact SA.nsmul_mem hz _
    let otherSum : Additive V :=
      ∑ j ∈ (Finset.univ.erase a : Finset (Fin (generatorRank G))),
        c j • qA j
    have hother_mem : otherSum ∈ SA := by
      dsimp [otherSum]
      exact sum_mem (S := SA)
        (fun j hj => hsmul_mem (c j)
          (hqA_other ((Finset.mem_erase.mp hj).1)))
    have hsplit :
        ∑ j, c j • qA j = c a • qA a + otherSum := by
      calc
        ∑ j, c j • qA j = otherSum + c a • qA a := by
          dsimp [otherSum]
          symm
          exact Finset.sum_erase_add _ _ (Finset.mem_univ a)
        _ = c a • qA a + otherSum := add_comm _ _
    have hca : c a • qA a = xA - otherSum := by
      apply eq_sub_of_add_eq
      simpa [hsplit] using hc
    have hqa_mem : qA a ∈ SA := by
      have hqa :
          qA a = (c a)⁻¹ • (xA - otherSum) := by
        calc
          qA a = 1 • qA a := by simp
          _ = ((c a)⁻¹ * c a) • qA a := by simp [ha]
          _ = (c a)⁻¹ • (c a • qA a) := by rw [mul_smul]
          _ = (c a)⁻¹ • (xA - otherSum) := by rw [hca]
      rw [hqa]
      exact hsmul_mem _ (SA.sub_mem hxA_S hother_mem)
    have hqA_mem : ∀ j : Fin (generatorRank G), qA j ∈ SA := by
      intro j
      by_cases hj : j = a
      · subst hj
        exact hqa_mem
      · exact hqA_other hj
    have hHS : H ≤ S := by
      apply (Subgroup.closure_le _).mpr
      rintro y ⟨j, rfl⟩
      simpa [qA, SA] using hqA_mem j
    have hStop : S = ⊤ := by
      apply top_unique
      have htop_le : (⊤ : Subgroup V) ≤ S := by
        rw [← hHtop]
        exact hHS
      exact htop_le
    have hgen_mem_K_sup_C :
        ∀ j : Fin (generatorRank G), P.free.generator j ∈ K ⊔ C := by
      intro j
      have hj : π (P.free.generator j) ∈ S := by
        rw [hStop]
        exact Subgroup.mem_top _
      change P.free.generator j ∈ S.comap π at hj
      rw [show S = K.map π from rfl,
        QuotientGroup.comap_map_mk' C K] at hj
      have hle : C ⊔ K ≤ K ⊔ C :=
        sup_le le_sup_right le_sup_left
      exact hle hj
    have hKmap_top (N : OpenNormalSubgroup F) :
        K.map (QuotientGroup.mk' N.toSubgroup) = ⊤ := by
      let Q := F ⧸ N.toSubgroup
      let φ : F →* Q := QuotientGroup.mk' N.toSubgroup
      let L : Subgroup Q := K.map φ
      letI : DiscreteTopology Q :=
        pro_discrete_topology N
      letI : Finite Q :=
        pro_p_open N
      have hφcont : Continuous (fun y : F => φ y) := by
        exact pro_open_continuous N
      have hφsurj : Function.Surjective φ :=
        QuotientGroup.mk'_surjective N.toSubgroup
      have hC_le :
          C ≤ (modPFrattini p Q).comap φ := by
        change Φ.topologicalClosure ≤ (modPFrattini p Q).comap φ
        apply pro_topological_closed
        · exact mod_frattini_comap (p := p) φ
        · change IsClosed ((fun y : F => φ y) ⁻¹'
            ((modPFrattini p Q : Subgroup Q) : Set Q))
          exact (isClosed_discrete _).preimage hφcont
      have hCmap_le :
          C.map φ ≤ modPFrattini p Q :=
        (Subgroup.map_le_iff_le_comap).2 hC_le
      have hgen_image :
          ∀ j : Fin (generatorRank G),
            φ (P.free.generator j) ∈ L ⊔ modPFrattini p Q := by
        intro j
        have hj :
            φ (P.free.generator j) ∈ (K ⊔ C).map φ :=
          ⟨P.free.generator j, hgen_mem_K_sup_C j, rfl⟩
        rw [Subgroup.map_sup] at hj
        exact (sup_le_sup_left hCmap_le L) hj
      have hgenerated :
          Subgroup.closure
              (Set.range (fun j : Fin (generatorRank G) =>
                φ (P.free.generator j))) =
            ⊤ :=
        pro_generated_image P.free.generator P.free.dense_generator
          φ hφcont hφsurj
      have hsup : L ⊔ modPFrattini p Q = ⊤ := by
        apply top_unique
        rw [← hgenerated]
        exact (Subgroup.closure_le _).mpr (by
          rintro y ⟨j, rfl⟩
          exact hgen_image j)
      have hQ : IsPGroup p Q := P.free.isProP N
      have hmod_le : modPFrattini p Q ≤ _root_.frattini Q := by
        dsimp [modPFrattini]
        apply sup_le
        · dsimp [pPowerSubgroup]
          apply Subgroup.normalClosure_le_normal
          intro y hy
          rcases hy with ⟨g, rfl⟩
          exact Towers.p_group_frattini hQ g
        · rw [_root_.commutator_def]
          apply (Subgroup.commutator_le).2
          intro a _ha b _hb
          exact Towers.p_commutator_frattini hQ a b
      have hsup_frattini : L ⊔ _root_.frattini Q = ⊤ := by
        apply le_antisymm le_top
        rw [← hsup]
        exact sup_le_sup_left hmod_le L
      have hLtop : L = ⊤ := frattini_nongenerating hsup_frattini
      exact hLtop
    have hKdense : K.topologicalClosure = ⊤ := by
      apply top_unique
      intro y _hy
      by_contra hy
      rcases
          (separate_sets_disconnected
            (Γ := F)
            (C := (K.topologicalClosure : Set F)))
            K.isClosed_topologicalClosure y hy with
        ⟨N, hN⟩
      apply hN
      have hyN :
          QuotientGroup.mk' N.toSubgroup y ∈
            K.map (QuotientGroup.mk' N.toSubgroup) := by
        rw [hKmap_top N]
        exact Subgroup.mem_top _
      rcases hyN with ⟨k, hk, hkq⟩
      exact ⟨k, K.le_topologicalClosure hk, hkq⟩
    have hmapK :
        K.map qG = K₀.map qG := by
      dsimp [K]
      rw [Subgroup.map_sup]
      have hker_map : qG.ker.map qG = ⊥ := by
        apply le_antisymm
        · intro y hy
          rcases hy with ⟨z, hz, rfl⟩
          change qG z = 1
          exact hz
        · exact bot_le
      simp [hker_map]
    have hsmall_dense :
        Subgroup.topologicalClosure
            (Subgroup.closure
              (Set.range (fun i : Fin (Fintype.card β) =>
                qG (smallF i)))) =
          ⊤ := by
      have hmap_dense :
          (K.map qG).topologicalClosure = ⊤ :=
        DenseRange.topologicalClosure_map_subgroup
          P.quotientMap_continuous P.quotientMap_surjective.denseRange hKdense
      rw [hmapK] at hmap_dense
      simpa [K₀, MonoidHom.map_closure, Set.range_comp'] using hmap_dense
    have hcount :
        GeneratorCountWitness G (Fintype.card β) := by
      exact
        ⟨fun i : Fin (Fintype.card β) => qG (smallF i),
          hsmall_dense⟩
    have hle : generatorRank G ≤ Fintype.card β :=
      Nat.sInf_le hcount
    have hlt : Fintype.card β < generatorRank G := by
      simpa [β] using
        (Fintype.card_subtype_lt
          (p := fun j : Fin (generatorRank G) => j ≠ a)
          (x := a) (by simp))
    exact (not_lt_of_ge hle hlt).elim
  change ∀ i, P.relator i ∈
    (zassenhausFiltration p P.free.Carrier 2).topologicalClosure
  intro i
  rw [filtration_p_frattini]
  apply hker_le
  rw [P.kernel_eq]
  exact
    (Subgroup.normalClosure (Set.range P.relator)).le_topologicalClosure
      (Subgroup.subset_normalClosure (Set.mem_range_self i))

end ProP

end Towers
