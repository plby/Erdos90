import Towers.Group.Zassenhaus.FactoryBranchCases

/-!
# Reachable Hall-ranked residual scheduling

The unrestricted residual scheduler requests a local branch for every pair of
a symbolic factor and a numerical Hall-rank defect.  Recipe-correct inner
reduction naturally supplies branches only for tasks reached from the
collector's worklists.

This file records a restricted scheduler indexed by a reachability predicate.
Every emitted child must remain reachable, so well-founded Hall-ranked
recursion constructs residual recollections from local branches only along
the actual recursive task graph.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
A reachable Hall-ranked branch is an ordinary branch whose emitted children
remain inside the recursive task predicate.
-/
structure RRBranch
    {d n inputWeight : ℕ}
    (Reachable :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight →
        ℕ → Prop)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ) where
  branch :
    RRBrancha
      (n := n) factor rankDefect
  children_reachable :
    ∀ task ∈ branch.children.tasks,
      Reachable task.1 task.2

/--
A Hall-ranked residual scheduler whose local obligations are restricted to
reachable tasks.
-/
structure TRSchedua
    {d n inputWeight : ℕ}
    (Reachable :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight →
        ℕ → Prop) where
  branches :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (rankDefect : ℕ),
      Reachable factor rankDefect →
        RRBranch
          (n := n) Reachable factor rankDefect

namespace
  TRSchedua

/--
Run Hall-ranked well-founded recursion from branches supplied only for
reachable tasks.
-/
noncomputable def residualRecollection
    {d n inputWeight : ℕ}
    {Reachable :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight →
        ℕ → Prop}
    (scheduler :
      TRSchedua
        (n := n) Reachable)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hreachable : Reachable factor rankDefect) :
    TSRecollb
      (n := n) factor :=
  Classical.choice <|
    SPFactora.ranked_descends_induction
      (motive := fun child childRankDefect =>
        Reachable child childRankDefect →
          Nonempty
            (TSRecollb
              (n := n) child))
      (fun parent parentRankDefect ih hparent =>
        let branch := scheduler.branches parent parentRankDefect hparent
        ⟨branch.branch.recollect fun task htask =>
          Classical.choice <|
            ih task.1 task.2
              (branch.branch.children.tasks_descend task htask)
              (branch.children_reachable task htask)⟩)
      factor rankDefect hreachable

/--
Compile reachable local branches directly into a restricted scheduler.
-/
noncomputable def ofBranches
    {d n inputWeight : ℕ}
    {Reachable :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight →
        ℕ → Prop}
    (branches :
      ∀
        (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        Reachable factor rankDefect →
          RRBranch
            (n := n) Reachable factor rankDefect) :
    TRSchedua
      (n := n) Reachable where
  branches := branches

end
  TRSchedua

namespace RRBranch

/--
Compile one reachable outer-factory case, provided its emitted children
remain reachable.
-/
noncomputable def outerFactoryCase
    {d n inputWeight : ℕ}
    {Reachable :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight →
        ℕ → Prop}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      OFRoute
        (d := d) (n := n) (inputWeight := inputWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (branchCase :
      TruncatedBranchCase
        (n := n) factor rankDefect)
    (children_reachable :
      ∀ task ∈
          (RRBrancha.outerFactoryCase
            hn hH routing factor rankDefect branchCase).children.tasks,
        Reachable task.1 task.2) :
    RRBranch
      (n := n) Reachable factor rankDefect where
  branch :=
    RRBrancha.outerFactoryCase
      hn hH routing factor rankDefect branchCase
  children_reachable := children_reachable

end RRBranch

namespace
  TRSchedua

/--
Compile outer-factory cases only along a reachable ranked task graph.
-/
noncomputable def outerFactoryCases
    {d n inputWeight : ℕ}
    {Reachable :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight →
        ℕ → Prop}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      OFRoute
        (d := d) (n := n) (inputWeight := inputWeight))
    (cases :
      ∀
        (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        Reachable factor rankDefect →
          TruncatedBranchCase
            (n := n) factor rankDefect)
    (children_reachable :
      ∀
        (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ)
        (hreachable : Reachable factor rankDefect)
        (task :
          SPFactora
              (concreteBasicCommutators.{u} d) inputWeight ×
            ℕ),
        task ∈
            (RRBrancha.outerFactoryCase
              hn hH routing factor rankDefect
                (cases factor rankDefect hreachable)).children.tasks →
          Reachable task.1 task.2) :
    TRSchedua
      (n := n) Reachable :=
  ofBranches fun factor rankDefect hreachable =>
    RRBranch.outerFactoryCase
      hn hH routing factor rankDefect (cases factor rankDefect hreachable)
        (children_reachable factor rankDefect hreachable)

/--
Run well-founded residual recursion directly from reachable outer-factory
cases.
-/
noncomputable def recollect_factory_cases
    {d n inputWeight : ℕ}
    {Reachable :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight →
        ℕ → Prop}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      OFRoute
        (d := d) (n := n) (inputWeight := inputWeight))
    (cases :
      ∀
        (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        Reachable factor rankDefect →
          TruncatedBranchCase
            (n := n) factor rankDefect)
    (children_reachable :
      ∀
        (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ)
        (hreachable : Reachable factor rankDefect)
        (task :
          SPFactora
              (concreteBasicCommutators.{u} d) inputWeight ×
            ℕ),
        task ∈
            (RRBrancha.outerFactoryCase
              hn hH routing factor rankDefect
                (cases factor rankDefect hreachable)).children.tasks →
          Reachable task.1 task.2)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hreachable : Reachable factor rankDefect) :
    TSRecollb
      (n := n) factor :=
  (outerFactoryCases hn hH routing cases children_reachable)
    |>.residualRecollection factor rankDefect hreachable

end
  TRSchedua

namespace CBWorka

/--
Recollect an exact concrete outer-bracket worklist using a Hall-ranked
scheduler restricted to reachable recursive tasks.
-/
noncomputable def recollection_reachable_scheduler
    {d n inputWeight : ℕ}
    {Reachable :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight →
        ℕ → Prop}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (scheduler :
      TRSchedua
        (n := n) Reachable)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      HEWord.tree inner.word =
        .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (tasks_reachable :
      ∀ task ∈ rankedTasks packet hinputWeight inner right unchanged,
        Reachable task.1 task.2) :
    TSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight PEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet hinputWeight inner right) :=
  recollection_basic_residuals packet hinputWeight inner right
    hinnerTruncated added originalRight unchanged originalLeft hinnerTree
      hRightLeft hRightUnchanged hunchangedBasic
        (fun task htask =>
          scheduler.residualRecollection task.1 task.2
            (tasks_reachable task htask))

end CBWorka

end TCTex
end Towers
