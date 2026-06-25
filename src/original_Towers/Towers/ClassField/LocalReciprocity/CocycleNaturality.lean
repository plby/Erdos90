import Towers.ClassField.Shifting.TransferBridge
import Towers.ClassField.LocalReciprocity.TateGenerator
import Towers.ClassField.CrossedProducts.CohomologyRestriction
import Towers.ClassField.LocalBrauer.CohomologyTransport

/-!
# Cocycle naturality in Milne III.3.2

The degree-minus-two Tate shift has an explicit description on a group
element `g`: it is represented by the product `prod_s c(s,g)` for a
normalized two-cocycle `c`.  This file proves the two finite-product
identities behind restriction and corestriction in Lemma III.3.2.
-/

namespace Towers.CField.LRecip

open scoped BigOperators
open Towers.CField.CProduca
open Towers.CField.LBrauer

noncomputable section

universe uG uM

variable {G : Type uG} [Group G] [Fintype G]
variable {M : Type uM} [CommGroup M] [MulDistribMulAction G M]

namespace NMCocycl₂

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The cocycle product on a group element.  This is the representative
computed by `neg_generator_inv`. -/
def cyclicProduct (c : NMCocycl₂ (G := G) (M := M)) (g : G) : M :=
  ∏ s : G, c (s, g)

@[simp]
theorem cyclicProduct_one
    (c : NMCocycl₂ (G := G) (M := M)) :
    cyclicProduct c 1 = 1 := by
  simp [cyclicProduct]

omit [Fintype G] in
/-- Product form of the cocycle identity on one left coset. -/
theorem prod_leftCoset
    (c : NMCocycl₂ (G := G) (M := M))
    (H : Subgroup G) [Fintype H] (r : G) (h : H) :
    (∏ t : H, c (r * t, h)) = r • (∏ t : H, c (t, h)) := by
  have hterm (t : H) :
      c (r * t, h) =
        (r • c (t, h)) * c (r, t * h) / c (r, t) := by
    rw [div_eq_mul_inv]
    let d := c (r, t)
    calc
      c (r * t, h) = c (r * t, h) * d * d⁻¹ := by simp
      _ = ((r • c (t, h)) * c (r, t * h)) * d⁻¹ := by
        rw [(c.isMulCocycle₂ r t h).symm]
      _ = _ := by rfl
  simp_rw [hterm]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
  have hact : (∏ t : H, r • c (t, h)) = r • ∏ t : H, c (t, h) := by
    exact (map_prod (MulDistribMulAction.toMonoidHom M r) _ _).symm
  rw [hact]
  have hperm : (∏ t : H, c (r, t * h)) = ∏ t : H, c (r, t) :=
    Fintype.prod_equiv (Equiv.mulRight h) _ _ (fun _ ↦ rfl)
  rw [hperm]
  exact mul_div_cancel_right _ _

/-- The cyclic cocycle product is fixed by the acting group. -/
theorem cyclicProduct_smul
    (c : NMCocycl₂ (G := G) (M := M)) (g a : G) :
    a • cyclicProduct c g = cyclicProduct c g := by
  let H : Subgroup G := ⊤
  letI : Fintype H := Fintype.ofFinite H
  let e : H ≃ G := Equiv.Set.univ G
  have hprod : (∏ t : H, c (a * t, g)) = a • (∏ t : H, c (t, g)) :=
    prod_leftCoset c H a ⟨g, Subgroup.mem_top g⟩
  have hleft : (∏ t : H, c (a * t, g)) = cyclicProduct c g := by
    rw [cyclicProduct]
    exact Fintype.prod_equiv (e.trans (Equiv.mulLeft a))
      (fun t : H ↦ c (a * t, g)) (fun s : G ↦ c (s, g)) (fun _ ↦ rfl)
  have hright : (∏ t : H, c (t, g)) = cyclicProduct c g := by
    rw [cyclicProduct]
    exact Fintype.prod_equiv e
      (fun t : H ↦ c (t, g)) (fun s : G ↦ c (s, g)) (fun _ ↦ rfl)
  rw [hleft, hright] at hprod
  exact hprod.symm

/-- The cyclic product packaged as a finite-action invariant. -/
def cyclicProductInvariant
    (c : NMCocycl₂ (G := G) (M := M)) (g : G) :
    FMAct.invariants G M :=
  ⟨cyclicProduct c g, cyclicProduct_smul c g⟩

/-- Cohomologous cocycles have the same cyclic-product class modulo the
finite group norm. -/
theorem cyclic_invariant_cohomologous
    {c d : NMCocycl₂ (G := G) (M := M)}
    (hcd : MHTwo.IsCohomologous c d) (g : G) :
    QuotientGroup.mk' (FMAct.norm G M).range
        (cyclicProductInvariant c g) =
      QuotientGroup.mk' (FMAct.norm G M).range
        (cyclicProductInvariant d g) := by
  change (cyclicProductInvariant c g :
      FMAct.invariantsModNorm G M) = cyclicProductInvariant d g
  rw [QuotientGroup.eq_iff_div_mem]
  obtain ⟨x, hx⟩ := hcd
  refine ⟨x g, ?_⟩
  apply Subtype.ext
  symm
  change cyclicProduct c g / cyclicProduct d g = ∏ h : G, h • x g
  rw [cyclicProduct, cyclicProduct, ← Finset.prod_div_distrib]
  calc
    ∏ h : G, c (h, g) / d (h, g) =
        ∏ h : G, (h • x g / x (h * g)) * x h := by
      apply Finset.prod_congr rfl
      intro h _
      exact (hx h g).symm
    _ = (∏ h : G, h • x g) *
        (∏ h : G, x (h * g))⁻¹ * (∏ h : G, x h) := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        Finset.prod_inv_distrib]
    _ = ∏ h : G, h • x g := by
      have hr : (∏ h : G, x (h * g)) = ∏ h : G, x h :=
        Fintype.prod_equiv (Equiv.mulRight g) _ _ (fun _ ↦ rfl)
      rw [hr]
      simp

/-- The product for the ambient group is the transversal norm of the
subgroup product.  This is the representative-level corestriction formula. -/
theorem cyclic_transversal_norm
    (c : NMCocycl₂ (G := G) (M := M))
    (H : Subgroup G) [Fintype H] [H.FiniteIndex]
    (S : H.LeftTransversal) (h : H) :
    cyclicProduct c h =
      ∏ q : G ⧸ H,
        (S.2.leftQuotientEquiv q : G) •
          ∏ t : H, c (t, h) := by
  classical
  let e : (G ⧸ H) × H ≃ G :=
    (Equiv.prodCongr S.2.leftQuotientEquiv (Equiv.refl H)).trans S.2.equiv.symm
  calc
    cyclicProduct c h =
        ∏ p : (G ⧸ H) × H,
          c ((S.2.leftQuotientEquiv p.1 : G) * p.2, h) := by
      rw [cyclicProduct]
      symm
      apply Fintype.prod_equiv e
      intro p
      rfl
    _ = ∏ q : G ⧸ H,
          ∏ t : H, c ((S.2.leftQuotientEquiv q : G) * t, h) := by
      rw [Fintype.prod_prod_type]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro q _
      exact prod_leftCoset c H (S.2.leftQuotientEquiv q) h

omit [Fintype G] in
/-- A one-coset calculation for homological restriction.  The discrepancy
between the ambient cocycle product and the transfer product is an `H`-norm. -/
theorem prod_rightCoset
    (c : NMCocycl₂ (G := G) (M := M))
    (H : Subgroup G) [Fintype H] [H.FiniteIndex]
    (q : Quotient (QuotientGroup.rightRel H)) (g : G) :
    let r := q.out
    let h := Rep.rightCosetCorrection H (r * g)
    let r' := Rep.rightCosetRep H (r * g)
    (∏ t : H, c (t * r, g)) =
      (∏ t : H, (t : G) • (c (r, g) / c (h, r'))) *
        (∏ t : H, c (t, h)) *
          ((∏ t : H, c (t, r')) / ∏ t : H, c (t, r)) := by
  dsimp only
  let r := q.out
  let h := Rep.rightCosetCorrection H (r * g)
  let r' := Rep.rightCosetRep H (r * g)
  have hrg : r * g = (h : G) * r' := by
    dsimp [h, r']
    simp [Rep.rightCosetCorrection, Rep.rightCosetRep]
  have hterm (t : H) :
      c (t * r, g) =
        ((t : G) • (c (r, g) / c (h, r'))) * c (t, h) *
          c (t * h, r') / c (t, r) := by
    have h₁ := c.isMulCocycle₂ (t : G) r g
    have h₂ := c.isMulCocycle₂ (t : G) h r'
    rw [hrg] at h₁
    rw [div_eq_mul_inv]
    have hB : c (t, (h : G) * r') =
        c (t, h) * c (t * h, r') / ((t : G) • c (h, r')) := by
      rw [div_eq_mul_inv]
      let d := (t : G) • c (h, r')
      calc
        c (t, (h : G) * r') = d⁻¹ * (d * c (t, (h : G) * r')) := by
          simp
        _ = d⁻¹ * (c (t * h, r') * c (t, h)) := by rw [← h₂]
        _ = _ := by simp [d]; ac_rfl
    let d := c (t, r)
    calc
      c (t * r, g) = c (t * r, g) * d * d⁻¹ := by simp
      _ = (((t : G) • c (r, g)) * c (t, (h : G) * r')) * d⁻¹ := by
        rw [h₁]
      _ = _ := by
        rw [hB]
        have hmapdiv : ((t : G) • (c (r, g) / c (h, r'))) =
            ((t : G) • c (r, g)) / ((t : G) • c (h, r')) :=
          map_div (MulDistribMulAction.toMonoidHom M (t : G)) _ _
        rw [hmapdiv]
        simp only [div_eq_mul_inv]
        simp [d]
        ac_rfl
  have hperm : (∏ t : H, c (t * h, r')) = ∏ t : H, c (t, r') :=
    Fintype.prod_equiv (Equiv.mulRight h) _ _ (fun _ ↦ rfl)
  calc
    (∏ t : H, c (t * r, g)) =
        ∏ t : H,
          (((t : G) • (c (r, g) / c (h, r'))) * c (t, h) *
            c (t * h, r') / c (t, r)) := by
      apply Finset.prod_congr rfl
      intro t _
      exact hterm t
    _ = _ := by
      rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
        Finset.prod_mul_distrib, hperm]
      let A := ∏ t : H, (t : G) • (c (r, g) / c (h, r'))
      let B := ∏ t : H, c (t, h)
      let C := ∏ t : H, c (t, r')
      let D := ∏ t : H, c (t, r)
      change (A * B * C) / D = A * B * (C / D)
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Restriction/transfer identity for the cocycle products.  The quotient
of the ambient product by the products on the right-coset corrections is an
`H`-norm, with an explicit norm preimage. -/
theorem cyclic_div_transfer
    (c : NMCocycl₂ (G := G) (M := M))
    (H : Subgroup G) [Fintype H] [H.FiniteIndex] (g : G) :
    cyclicProduct c g /
        ∏ q : Quotient (QuotientGroup.rightRel H),
          ∏ t : H, c (t, Rep.rightCosetCorrection H (q.out * g)) =
      ∏ t : H, (t : G) •
        (∏ q : Quotient (QuotientGroup.rightRel H),
          c (q.out, g) /
            c (Rep.rightCosetCorrection H (q.out * g),
              Rep.rightCosetRep H (q.out * g))) := by
  classical
  let Q := Quotient (QuotientGroup.rightRel H)
  let rep : Q → G := fun q ↦ q.out
  let corr : Q → H := fun q ↦ Rep.rightCosetCorrection H (q.out * g)
  let next : Q → G := fun q ↦ Rep.rightCosetRep H (q.out * g)
  let T : H.RightTransversal :=
    ⟨Set.range rep, Subgroup.isComplement_range_right Quotient.out_eq'⟩
  let e : H × Q ≃ G := by
    exact (Equiv.prodCongr (Equiv.refl H) T.2.rightQuotientEquiv).trans
      T.2.equiv.symm
  have hdecomp :
      cyclicProduct c g = ∏ q : Q, ∏ t : H, c (t * rep q, g) := by
    rw [cyclicProduct]
    calc
      (∏ s : G, c (s, g)) =
          ∏ p : H × Q, c ((p.1 : G) * rep p.2, g) := by
        symm
        apply Fintype.prod_equiv e
        intro p
        change c ((p.1 : G) * rep p.2, g) =
          c ((p.1 : G) * (T.2.rightQuotientEquiv p.2 : G), g)
        rw [Subgroup.IsComplement.rightQuotientEquiv_apply Quotient.out_eq']
      _ = _ := by rw [Fintype.prod_prod_type, Finset.prod_comm]
  rw [hdecomp]
  dsimp only [rep]
  simp_rw [prod_rightCoset c H]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  let f : Q → Q := Quotient.map (fun x : G ↦ x * g) (by
    intro a b hab
    exact QuotientGroup.rightRel_apply.mpr <| by
      simpa [mul_inv_rev, mul_assoc] using QuotientGroup.rightRel_apply.mp hab)
  let fInv : Q → Q := Quotient.map (fun x : G ↦ x * g⁻¹) (by
    intro a b hab
    exact QuotientGroup.rightRel_apply.mpr <| by
      simpa [mul_inv_rev, mul_assoc] using QuotientGroup.rightRel_apply.mp hab)
  let perm : Q ≃ Q :=
    { toFun := f
      invFun := fInv
      left_inv := by
        intro q
        induction q using Quotient.inductionOn
        simp [f, fInv, mul_assoc]
      right_inv := by
        intro q
        induction q using Quotient.inductionOn
        simp [f, fInv, mul_assoc] }
  have hnext (q : Q) : next q = rep (perm q) := by
    have hfq : f q = Quotient.mk _ (q.out * g) := by
      calc
        f q = f (Quotient.mk _ q.out) := congrArg f (Quotient.out_eq q).symm
        _ = Quotient.mk _ (q.out * g) := rfl
    change Quotient.out (Quotient.mk _ (q.out * g)) = Quotient.out (f q)
    rw [hfq]
  have hcancel :
      (∏ q : Q, ∏ t : H, c (t, next q)) =
        ∏ q : Q, ∏ t : H, c (t, rep q) := by
    apply Fintype.prod_equiv perm
    intro q
    rw [hnext]
  have hquotientProd :
      (∏ q : Q, (∏ t : H, c (t, next q)) /
        ∏ t : H, c (t, rep q)) = 1 := by
    rw [Finset.prod_div_distrib, hcancel]
    let z := ∏ q : Q, ∏ t : H, c (t, rep q)
    change z / z = 1
    exact div_self' z
  have hnormProd :
      (∏ q : Q, ∏ t : H, (t : G) •
          (c (q.out, g) / c (Rep.rightCosetCorrection H (q.out * g),
            Rep.rightCosetRep H (q.out * g)))) =
        ∏ t : H, (t : G) •
          (∏ q : Q, c (q.out, g) /
            c (Rep.rightCosetCorrection H (q.out * g),
              Rep.rightCosetRep H (q.out * g))) := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro t _
    exact (map_prod (MulDistribMulAction.toMonoidHom M (t : G)) _ _).symm
  dsimp only [next, rep] at hquotientProd
  rw [hquotientProd, mul_one]
  rw [hnormProd]
  exact mul_div_cancel_right _ _

/-- Regard an ambient cyclic product as an invariant for a subgroup. -/
def ambientCyclicInvariant
    (c : NMCocycl₂ (G := G) (M := M))
    (H : Subgroup G) [Fintype H] (g : G) :
    FMAct.invariants H M :=
  ⟨cyclicProduct c g, fun h ↦ cyclicProduct_smul c g h⟩

/-- Product of the subgroup cyclic products occurring in the transfer of
an ambient group element. -/
def transferCyclicInvariant
    (c : NMCocycl₂ (G := G) (M := M))
    (H : Subgroup G) [Fintype H] [H.FiniteIndex] (g : G) :
    FMAct.invariants H M :=
  ∏ q : Quotient (QuotientGroup.rightRel H),
    cyclicProductInvariant
      (NMCocycl₂.restrict H.subtype (by intro h x; rfl) c)
      (Rep.rightCosetCorrection H (q.out * g))

/-- The ambient cyclic product and the product attached to the transfer
have the same class modulo the subgroup norm. -/
theorem ambient_cyclic_transfer
    (c : NMCocycl₂ (G := G) (M := M))
    (H : Subgroup G) [Fintype H] [H.FiniteIndex] (g : G) :
    QuotientGroup.mk' (FMAct.norm H M).range
        (ambientCyclicInvariant c H g) =
      QuotientGroup.mk' (FMAct.norm H M).range
        (transferCyclicInvariant c H g) := by
  change (ambientCyclicInvariant c H g :
      FMAct.invariantsModNorm H M) =
    transferCyclicInvariant c H g
  rw [QuotientGroup.eq_iff_div_mem]
  let b : M :=
    ∏ q : Quotient (QuotientGroup.rightRel H),
      c (q.out, g) /
        c (Rep.rightCosetCorrection H (q.out * g),
          Rep.rightCosetRep H (q.out * g))
  refine ⟨b, ?_⟩
  apply Subtype.ext
  change ((FMAct.norm H M b :
      FMAct.invariants H M) : M) =
    ((ambientCyclicInvariant c H g /
      transferCyclicInvariant c H g :
        FMAct.invariants H M) : M)
  rw [FMAct.norm_coe]
  rw [Subgroup.coe_div]
  change (∏ t : H, (t : G) • b) =
    cyclicProduct c g / ((transferCyclicInvariant c H g :
      FMAct.invariants H M) : M)
  have htransfer :
      ((transferCyclicInvariant c H g :
        FMAct.invariants H M) : M) =
        ∏ q : Quotient (QuotientGroup.rightRel H),
          cyclicProduct
            (NMCocycl₂.restrict H.subtype
              (by intro h x; rfl) c)
            (Rep.rightCosetCorrection H (q.out * g)) := by
    simpa only [transferCyclicInvariant, cyclicProductInvariant] using
      map_prod (FMAct.invariants H M).subtype
        (fun q : Quotient (QuotientGroup.rightRel H) ↦
          cyclicProductInvariant
            (NMCocycl₂.restrict H.subtype
              (by intro h x; rfl) c)
            (Rep.rightCosetCorrection H (q.out * g))) Finset.univ
  rw [htransfer]
  exact (cyclic_div_transfer c H g).symm

/-- Forget part of the invariance from `G` to a subgroup `H`. -/
def subgroupInvariantRestriction (H : Subgroup G) [Fintype H] :
    FMAct.invariants G M →* FMAct.invariants H M where
  toFun x := ⟨x.1, fun h ↦ x.2 h⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem ambient_range_comap
    (H : Subgroup G) [Fintype H] [H.FiniteIndex] :
    (FMAct.norm G M).range ≤
      (FMAct.norm H M).range.comap
        (subgroupInvariantRestriction H) := by
  rintro _ ⟨x, rfl⟩
  let Q := Quotient (QuotientGroup.rightRel H)
  let rep : Q → G := fun q ↦ q.out
  let T : H.RightTransversal :=
    ⟨Set.range rep, Subgroup.isComplement_range_right Quotient.out_eq'⟩
  let e : H × Q ≃ G := by
    exact (Equiv.prodCongr (Equiv.refl H) T.2.rightQuotientEquiv).trans
      T.2.equiv.symm
  let z : M := ∏ q : Q, rep q • x
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change (∏ h : H, (h : G) • z) = ∏ g : G, g • x
  calc
    (∏ h : H, (h : G) • z) =
        ∏ h : H, ∏ q : Q, ((h : G) * rep q) • x := by
      apply Finset.prod_congr rfl
      intro h _
      rw [show (h : G) • z =
          ∏ q : Q, (h : G) • (rep q • x) by
        exact map_prod (MulDistribMulAction.toMonoidHom M (h : G)) _ _]
      apply Finset.prod_congr rfl
      intro q _
      exact (mul_smul (h : G) (rep q) x).symm
    _ = ∏ p : H × Q, ((p.1 : G) * rep p.2) • x := by
      rw [Fintype.prod_prod_type]
    _ = ∏ g : G, g • x := by
      apply Fintype.prod_equiv e
      intro p
      change ((p.1 : G) * rep p.2) • x =
        ((p.1 : G) * (T.2.rightQuotientEquiv p.2 : G)) • x
      rw [Subgroup.IsComplement.rightQuotientEquiv_apply Quotient.out_eq']

/-- Restriction from ambient invariants modulo the ambient norm to subgroup
invariants modulo the subgroup norm. -/
def invariantsModRestriction
    (H : Subgroup G) [Fintype H] [H.FiniteIndex] :
    FMAct.invariantsModNorm G M →*
      FMAct.invariantsModNorm H M :=
  QuotientGroup.map (FMAct.norm G M).range
    (FMAct.norm H M).range
    (subgroupInvariantRestriction H)
    (ambient_range_comap H)

@[simp]
theorem invariants_restriction_mk
    (H : Subgroup G) [Fintype H] [H.FiniteIndex]
    (x : FMAct.invariants G M) :
    invariantsModRestriction H
        (QuotientGroup.mk' (FMAct.norm G M).range x) =
      QuotientGroup.mk' (FMAct.norm H M).range
        (subgroupInvariantRestriction H x) :=
  rfl

/-- Cocycle-product form of degree-minus-two restriction: after restricting
the norm quotient from `G` to `H`, the image is the product attached to the
Verlag representatives. -/
theorem invariants_restriction_cyclic
    (c : NMCocycl₂ (G := G) (M := M))
    (H : Subgroup G) [Fintype H] [H.FiniteIndex] (g : G) :
    invariantsModRestriction H
        (QuotientGroup.mk' (FMAct.norm G M).range
          (cyclicProductInvariant c g)) =
      QuotientGroup.mk' (FMAct.norm H M).range
        (transferCyclicInvariant c H g) := by
  rw [invariants_restriction_mk]
  exact ambient_cyclic_transfer c H g

end NMCocycl₂

namespace FATrans

universe uH

variable {H : Type uH} [Group H] [Fintype H]
  [MulDistribMulAction H M]

/-- Reindex finite-action invariants along an equivariant group
isomorphism, leaving the coefficient element unchanged. -/
def invariantsMulGroup
    (e : G ≃* H) (heq : ∀ g : G, ∀ x : M, g • x = e g • x) :
    FMAct.invariants G M ≃* FMAct.invariants H M where
  toFun x := ⟨x.1, fun h ↦ by
    rw [← e.apply_symm_apply h, ← heq]
    exact x.2 (e.symm h)⟩
  invFun x := ⟨x.1, fun g ↦ by
    rw [heq]
    exact x.2 (e g)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem invariants_group_norm
    (e : G ≃* H) (heq : ∀ g : G, ∀ x : M, g • x = e g • x)
    (x : M) :
    invariantsMulGroup e heq (FMAct.norm G M x) =
      FMAct.norm H M x := by
  apply Subtype.ext
  change (∏ g : G, g • x) = ∏ h : H, h • x
  exact Fintype.prod_equiv e.toEquiv _ _ (fun g ↦ heq g x)

private theorem norm_range_comap
    (e : G ≃* H) (heq : ∀ g : G, ∀ x : M, g • x = e g • x) :
    (FMAct.norm G M).range ≤
      (FMAct.norm H M).range.comap
      (invariantsMulGroup e heq) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨x, (invariants_group_norm e heq x).symm⟩

private theorem range_comap_symm
    (e : G ≃* H) (heq : ∀ g : G, ∀ x : M, g • x = e g • x) :
    (FMAct.norm H M).range ≤
      (FMAct.norm G M).range.comap
      (invariantsMulGroup e heq).symm := by
  rintro _ ⟨x, rfl⟩
  refine ⟨x, ?_⟩
  apply (invariantsMulGroup e heq).injective
  rw [invariants_group_norm]
  simp

/-- Reindex invariants modulo norms along an equivariant group
isomorphism. -/
def invariantsModGroup
    (e : G ≃* H) (heq : ∀ g : G, ∀ x : M, g • x = e g • x) :
    FMAct.invariantsModNorm G M ≃*
      FMAct.invariantsModNorm H M where
  toFun := QuotientGroup.map (FMAct.norm G M).range
    (FMAct.norm H M).range
    (invariantsMulGroup e heq)
    (norm_range_comap e heq)
  invFun := QuotientGroup.map (FMAct.norm H M).range
    (FMAct.norm G M).range
    (invariantsMulGroup e heq).symm
    (range_comap_symm e heq)
  left_inv q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (FMAct.norm G M).range q
    rfl
  right_inv q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (FMAct.norm H M).range q
    rfl
  map_mul' x y := by
    exact map_mul (QuotientGroup.map (FMAct.norm G M).range
      (FMAct.norm H M).range
      (invariantsMulGroup e heq)
      (norm_range_comap e heq)) x y

@[simp]
theorem invariants_mod_mk
    (e : G ≃* H) (heq : ∀ g : G, ∀ x : M, g • x = e g • x)
    (x : FMAct.invariants G M) :
    invariantsModGroup e heq
        (QuotientGroup.mk' (FMAct.norm G M).range x) =
      QuotientGroup.mk' (FMAct.norm H M).range
        (invariantsMulGroup e heq x) := by
  exact QuotientGroup.map_mk' (FMAct.norm G M).range
    (FMAct.norm H M).range
    (invariantsMulGroup e heq)
    (norm_range_comap e heq) x

end FATrans

end

end Towers.CField.LRecip
