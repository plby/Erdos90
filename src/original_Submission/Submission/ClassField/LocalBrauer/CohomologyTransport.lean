import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Tactic
import Submission.ClassField.CrossedProducts.CohomologyClass
import Submission.ClassField.LocalBrauer.CyclicH2


/-!
# Chapter IV, Section 4: transport of multiplicative second cohomology

Normalized multiplicative cocycles, their cohomology classes, and the cyclic
`H²` calculation are invariant under equivariant isomorphisms of the acting
group and coefficient group.
-/

namespace Submission.CField.LBrauer

noncomputable section

open CProduca
open groupCohomology

namespace MHTrans

universe uG uH uM uN

variable {G : Type uG} {H : Type uH} {M : Type uM} {N : Type uN}
  [Group G] [Group H] [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction H N]

/-- Transport a normalized cocycle along equivariant isomorphisms of the
acting group and coefficient group. -/
def cocycleMap (eG : G ≃* H) (eM : M ≃* N)
    (heq : ∀ (g : G) (m : M), eM (g • m) = eG g • eM m)
    (c : NMCocycl₂ (G := G) (M := M)) :
    NMCocycl₂ (G := H) (M := N) where
  toFun p := eM (c (eG.symm p.1, eG.symm p.2))
  isMulCocycle₂ := by
    intro g h j
    have hs := heq (eG.symm g) (c (eG.symm h, eG.symm j))
    rw [eG.apply_symm_apply] at hs
    calc
      eM (c (eG.symm (g * h), eG.symm j)) *
          eM (c (eG.symm g, eG.symm h)) =
        eM (c (eG.symm (g * h), eG.symm j) *
          c (eG.symm g, eG.symm h)) := (map_mul eM _ _).symm
      _ = eM ((eG.symm g • c (eG.symm h, eG.symm j)) *
          c (eG.symm g, eG.symm (h * j))) := by
        apply congrArg eM
        simpa using c.isMulCocycle₂ (eG.symm g) (eG.symm h) (eG.symm j)
      _ = eM (eG.symm g • c (eG.symm h, eG.symm j)) *
          eM (c (eG.symm g, eG.symm (h * j))) := map_mul eM _ _
      _ = g • eM (c (eG.symm h, eG.symm j)) *
          eM (c (eG.symm g, eG.symm (h * j))) := by rw [hs]
  map_one_fst g := by simp
  map_one_snd g := by simp

@[simp]
theorem cocycleMap_apply (eG : G ≃* H) (eM : M ≃* N)
    (heq : ∀ (g : G) (m : M), eM (g • m) = eG g • eM m)
    (c : NMCocycl₂ (G := G) (M := M)) (g h : H) :
    cocycleMap eG eM heq c (g, h) = eM (c (eG.symm g, eG.symm h)) :=
  rfl

private theorem symm_equivariant (eG : G ≃* H) (eM : M ≃* N)
    (heq : ∀ (g : G) (m : M), eM (g • m) = eG g • eM m) :
    ∀ (h : H) (n : N), eM.symm (h • n) = eG.symm h • eM.symm n := by
  intro h n
  apply eM.injective
  rw [eM.apply_symm_apply]
  simpa using (heq (eG.symm h) (eM.symm n)).symm

/-- Transport is an isomorphism on normalized cocycles. -/
def cocycleMulEquiv (eG : G ≃* H) (eM : M ≃* N)
    (heq : ∀ (g : G) (m : M), eM (g • m) = eG g • eM m) :
    NMCocycl₂ (G := G) (M := M) ≃*
      NMCocycl₂ (G := H) (M := N) where
  toFun := cocycleMap eG eM heq
  invFun := cocycleMap eG.symm eM.symm (symm_equivariant eG eM heq)
  left_inv c := by
    apply NMCocycl₂.ext
    rintro ⟨g, h⟩
    simp
  right_inv c := by
    apply NMCocycl₂.ext
    rintro ⟨g, h⟩
    simp
  map_mul' c d := by
    apply NMCocycl₂.ext
    rintro ⟨g, h⟩
    simp

/-- Equivariant transport preserves cohomology of normalized cocycles. -/
theorem cohomologous_cocycle (eG : G ≃* H) (eM : M ≃* N)
    (heq : ∀ (g : G) (m : M), eM (g • m) = eG g • eM m)
    {c d : NMCocycl₂ (G := G) (M := M)}
    (hcd : MHTwo.IsCohomologous c d) :
    MHTwo.IsCohomologous
      (cocycleMap eG eM heq c) (cocycleMap eG eM heq d) := by
  obtain ⟨x, hx⟩ := hcd
  refine ⟨fun h ↦ eM (x (eG.symm h)), ?_⟩
  intro g h
  have hs := heq (eG.symm g) (x (eG.symm h))
  rw [eG.apply_symm_apply] at hs
  calc
    g • eM (x (eG.symm h)) / eM (x (eG.symm (g * h))) *
        eM (x (eG.symm g)) =
      eM (eG.symm g • x (eG.symm h)) /
        eM (x (eG.symm (g * h))) * eM (x (eG.symm g)) := by rw [hs]
    _ = eM ((eG.symm g • x (eG.symm h)) /
        x (eG.symm (g * h)) * x (eG.symm g)) := by
      rw [← map_div, ← map_mul]
    _ = eM (c (eG.symm g, eG.symm h) /
        d (eG.symm g, eG.symm h)) := by
      apply congrArg eM
      simpa using hx (eG.symm g) (eG.symm h)
    _ = eM (c (eG.symm g, eG.symm h)) /
        eM (d (eG.symm g, eG.symm h)) := map_div eM _ _

/-- Equivariant isomorphisms of actions induce an isomorphism on
multiplicative second cohomology. -/
def h2Equiv (eG : G ≃* H) (eM : M ≃* N)
    (heq : ∀ (g : G) (m : M), eM (g • m) = eG g • eM m) :
    MHTwo G M ≃* MHTwo H N where
  toFun := Quotient.map (cocycleMap eG eM heq)
    (fun _ _ h ↦ cohomologous_cocycle eG eM heq h)
  invFun := Quotient.map
    (cocycleMap eG.symm eM.symm (symm_equivariant eG eM heq))
    (fun _ _ h ↦ cohomologous_cocycle eG.symm eM.symm
      (symm_equivariant eG eM heq) h)
  left_inv x := by
    induction x using Quotient.inductionOn with
    | _ c =>
        exact congrArg MHTwo.mk
          ((cocycleMulEquiv eG eM heq).left_inv c)
  right_inv x := by
    induction x using Quotient.inductionOn with
    | _ c =>
        exact congrArg MHTwo.mk
          ((cocycleMulEquiv eG eM heq).right_inv c)
  map_mul' x y := by
    induction x, y using Quotient.inductionOn₂ with
    | _ c d =>
        exact congrArg MHTwo.mk
          ((cocycleMulEquiv eG eM heq).map_mul c d)

@[simp]
theorem h_2_mk (eG : G ≃* H) (eM : M ≃* N)
    (heq : ∀ (g : G) (m : M), eM (g • m) = eG g • eM m)
    (c : NMCocycl₂ (G := G) (M := M)) :
    h2Equiv eG eM heq (MHTwo.mk c) =
      MHTwo.mk (cocycleMap eG eM heq c) :=
  rfl

end MHTrans

namespace FMAct

universe uG uM

variable (G : Type uG) (M : Type uM) [Group G] [Fintype G]
  [CommGroup M] [MulDistribMulAction G M]

/-- Elements fixed by a finite group action. -/
def invariants : Subgroup M where
  carrier := {x | ∀ g : G, g • x = x}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy g
    simp only [smul_mul', hx g, hy g]
  inv_mem' := by
    intro x hx g
    simp only [smul_inv', hx g]

omit [Fintype G] in
@[simp]
theorem mem_invariants_iff (x : M) :
    x ∈ invariants G M ↔ ∀ g : G, g • x = x :=
  Iff.rfl

/-- The norm homomorphism for a finite multiplicative action. -/
def norm : M →* invariants G M where
  toFun x := ⟨∏ g : G, g • x, by
    intro h
    change (MulDistribMulAction.toMonoidHom M h) (∏ g : G, g • x) = _
    rw [map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft h)
      (fun g : G ↦ h • g • x) (fun g : G ↦ g • x)
      (fun g ↦ (mul_smul h g x).symm) ⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change (∏ g : G, g • (x * y)) =
      (∏ g : G, g • x) * (∏ g : G, g • y)
    simp only [smul_mul', Finset.prod_mul_distrib]

@[simp]
theorem norm_coe (x : M) :
    ((norm G M x : invariants G M) : M) = ∏ g : G, g • x :=
  rfl

/-- Invariant elements modulo norms for a finite action. -/
abbrev invariantsModNorm :=
  invariants G M ⧸ (norm G M).range

end FMAct

namespace GroupH2

universe uG uM

variable {n : ℕ} [NeZero n]
  {G : Type uG} [Group G] [Fintype G]
  {M : Type uM} [CommGroup M] [MulDistribMulAction G M]

abbrev C := Multiplicative (ZMod n)

/-- Pull the original action back along a cyclic group isomorphism. -/
abbrev pulledAction (e : C (n := n) ≃* G) :
    MulDistribMulAction (C (n := n)) M :=
  MulDistribMulAction.compHom M e.toMonoidHom

abbrev pulledInvariants (e : C (n := n) ≃* G) : Subgroup M :=
  @CyclicH2.invariants n M _ (pulledAction (M := M) e)

abbrev pulledNorm (e : C (n := n) ≃* G) :
    M →* pulledInvariants (M := M) e :=
  @CyclicH2.norm n _ M _ (pulledAction (M := M) e)

abbrev pulledInvariantsMod (e : C (n := n) ≃* G) :=
  @CyclicH2.invariantsModNorm n _ M _ (pulledAction (M := M) e)

section

variable (e : C (n := n) ≃* G)

/-- Reindex `H²(G,M)` by a chosen identification of `G` with `Z/nZ`. -/
def hCyclicModel :
    MHTwo G M ≃*
      @MHTwo (C (n := n)) M _ _ (pulledAction (M := M) e) := by
  letI : MulDistribMulAction (C (n := n)) M := pulledAction e
  exact MHTrans.h2Equiv e.symm (MulEquiv.refl M) (by
    intro g m
    change g • m = e (e.symm g) • m
    rw [e.apply_symm_apply])

/-- Reindexing identifies invariants for the pulled-back cyclic action with
invariants for the original action. -/
def invariantsMulEquiv :
    pulledInvariants (M := M) e ≃* FMAct.invariants G M := by
  letI : MulDistribMulAction (C (n := n)) M := pulledAction e
  exact
    { toFun := fun x ↦ ⟨x.1, by
        intro g
        simpa [pulledAction, MulAction.compHom_smul_def] using x.2 (e.symm g) ⟩
      invFun := fun x ↦ ⟨x.1, by
        intro c
        simpa [pulledAction, MulAction.compHom_smul_def] using x.2 (e c) ⟩
      left_inv := fun x ↦ by apply Subtype.ext; rfl
      right_inv := fun x ↦ by apply Subtype.ext; rfl
      map_mul' := fun x y ↦ by apply Subtype.ext; rfl }

theorem invariants_mul_norm (x : M) :
    invariantsMulEquiv e (pulledNorm (M := M) e x) =
      FMAct.norm G M x := by
  apply Subtype.ext
  change (∏ c : C (n := n), e c • x) = ∏ g : G, g • x
  exact Fintype.prod_equiv e.toEquiv _ _ (fun _ ↦ rfl)

private theorem range_comap :
    (pulledNorm (M := M) e).range ≤
      (FMAct.norm G M).range.comap
        (invariantsMulEquiv e).toMonoidHom := by
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, (invariants_mul_norm e x).symm⟩

private theorem norm_comap_symm :
    (FMAct.norm G M).range ≤
      (pulledNorm (M := M) e).range.comap
        (invariantsMulEquiv e).symm.toMonoidHom := by
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  refine ⟨x, ?_⟩
  apply (invariantsMulEquiv e).injective
  rw [invariants_mul_norm]
  simp

/-- Reindexing preserves the quotient of invariant elements by norms. -/
def invariantsModEquiv :
    pulledInvariantsMod (M := M) e ≃*
      FMAct.invariantsModNorm G M where
  toFun := QuotientGroup.map
    (pulledNorm (M := M) e).range
    (FMAct.norm G M).range
    (invariantsMulEquiv e).toMonoidHom (range_comap e)
  invFun := QuotientGroup.map
    (FMAct.norm G M).range
    (pulledNorm (M := M) e).range
    (invariantsMulEquiv e).symm.toMonoidHom (norm_comap_symm e)
  left_inv q := by
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective (pulledNorm (M := M) e).range q
    apply congrArg (QuotientGroup.mk'
      (pulledNorm (M := M) e).range)
    exact (invariantsMulEquiv e).left_inv x
  right_inv q := by
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective (FMAct.norm G M).range q
    apply congrArg (QuotientGroup.mk' (FMAct.norm G M).range)
    exact (invariantsMulEquiv e).right_inv x
  map_mul' x y := by
    exact map_mul (QuotientGroup.map
      (pulledNorm (M := M) e).range
      (FMAct.norm G M).range
      (invariantsMulEquiv e).toMonoidHom (range_comap e)) x y

/-- **Cyclic `H²` for an arbitrary cyclic model.** A chosen isomorphism
`Z/nZ ≃ G` identifies multiplicative second cohomology for the original
`G`-action with its invariant elements modulo the original norm. -/
noncomputable def mulInvariantsMod (hn : 1 < n) :
    MHTwo G M ≃* FMAct.invariantsModNorm G M :=
  (hCyclicModel e).trans <|
    (@CyclicH2.mulInvariantsMod n _ M _
      (pulledAction (M := M) e) hn).trans <|
      invariantsModEquiv e

end

end GroupH2

end

end Submission.CField.LBrauer
