import Towers.FieldTheory.CentralEmbeddingPresentation
import Towers.FieldTheory.CentralEmbeddingPullback
import Towers.FieldTheory.CentralEmbeddingDescent
import Towers.ClassField.CohomologyOps.ShortComplexMap
import Towers.ClassField.LocalBrauer.CyclicH2
import Towers.ClassField.LocalBrauer.CohomologyTransport
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.GroupTheory.SemidirectProduct


/-!
# Relative reductions for tame central embedding problems

The prescribed lifts of tame inertia and Frobenius generate a subgroup that
still maps onto the prescribed local quotient.  For a kernel of prime order,
either that subgroup meets the kernel trivially and gives a splitting, or it
contains the kernel and is the whole extension group.
-/

noncomputable section

namespace Towers
namespace TBluepr

universe u v w

open Towers.CField.CProduca
open Towers.CField.LBrauer
open CategoryTheory
open CategoryTheory.Limits
open Towers.CField.COps

attribute [local instance] Units.mulDistribMulActionRight

/-- Integer powers, regarded as a homomorphism from the multiplicative copy
of `Z`.  This is convenient when presenting an extension with cyclic
quotient as a quotient of a semidirect product. -/
def integerPowersHom {G : Type*} [Group G] (g : G) :
    Multiplicative ℤ →* G where
  toFun n := g ^ n.toAdd
  map_one' := by simp
  map_mul' a b := by
    change g ^ (a.toAdd + b.toAdd) = g ^ a.toAdd * g ^ b.toAdd
    rw [zpow_add]

/-- The distinguished element `1` generates the cyclic multiplicative copy
of `ZMod n`. -/
theorem cyclic_zpowers_top
    (n : ℕ) [NeZero n] :
    Subgroup.zpowers (CyclicH2.generator (n := n)) = ⊤ := by
  apply top_unique
  intro z _
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨(z.toAdd.val : ℤ), ?_⟩
  apply Multiplicative.ext
  change (z.toAdd.val : ℤ) • (1 : ZMod n) = z.toAdd
  simp

/-- A group equivalence transports the assertion that one element generates
the whole group. -/
theorem zpowers_top_equiv
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G)
    (hx : Subgroup.zpowers x = ⊤) :
    Subgroup.zpowers (e x) = ⊤ := by
  apply top_unique
  intro y _
  have hy : e.symm y ∈ Subgroup.zpowers x := by
    rw [hx]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k, ?_⟩
  calc
    (e x) ^ k = e (x ^ k) := (map_zpow e x k).symm
    _ = e (e.symm y) := by rw [hk]
    _ = y := e.apply_symm_apply y

/-- Extend a homomorphism from a normal subgroup across a cyclic quotient.
The conjugation identity and the single relation on a lift of the quotient
generator are exactly the relations in the corresponding metacyclic
presentation. -/
theorem hom_normal_cyclic
    {Q H : Type*} [Group Q] [Group H]
    (N : Subgroup Q) [N.Normal]
    (y : Q) (f : ℕ) (_hf : 0 < f)
    (horder : orderOf (QuotientGroup.mk' N y) = f)
    (hgen : Subgroup.zpowers (QuotientGroup.mk' N y) = ⊤)
    (fn : N →* H) (Y : H)
    (hconj : ∀ (k : ℤ) (n : N),
      fn (MulAut.conjNormal (y ^ k) n) =
        Y ^ k * fn n * (Y ^ k)⁻¹)
    (hpow : Y ^ f = fn ⟨y ^ f, by
      apply (QuotientGroup.eq_one_iff (y ^ f)).mp
      change QuotientGroup.mk' N (y ^ f) = 1
      rw [map_pow, ← horder]
      exact pow_orderOf_eq_one _⟩) :
    ∃ F : Q →* H, F.comp N.subtype = fn ∧ F y = Y := by
  let Z := Multiplicative ℤ
  let yp : Z →* Q := integerPowersHom y
  let Yp : Z →* H := integerPowersHom Y
  let action : Z →* MulAut N := (MulAut.conjNormal).comp yp
  let P := N ⋊[action] Z
  let p : P →* Q := SemidirectProduct.lift N.subtype yp (by
    intro k
    ext n
    exact MulAut.conjNormal_apply (y ^ k.toAdd) n)
  let F₀ : P →* H := SemidirectProduct.lift fn Yp (by
    intro k
    ext n
    exact hconj k.toAdd n)
  have hpSurj : Function.Surjective p := by
    intro q
    have hqbar : QuotientGroup.mk' N q ∈
        Subgroup.zpowers (QuotientGroup.mk' N y) := by
      rw [hgen]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hqbar
    have hnmem : q * (y ^ k)⁻¹ ∈ N := by
      apply (QuotientGroup.eq_one_iff (q * (y ^ k)⁻¹)).mp
      change QuotientGroup.mk' N (q * (y ^ k)⁻¹) = 1
      rw [map_mul, map_inv, map_zpow, hk]
      simp
    let n : N := ⟨q * (y ^ k)⁻¹, hnmem⟩
    let z : Z := Multiplicative.ofAdd k
    refine ⟨⟨n, z⟩, ?_⟩
    change (n : Q) * y ^ k = q
    simp [n, mul_assoc]
  have hker : p.ker ≤ F₀.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    let k : ℤ := a.right.toAdd
    have hpk : (f : ℤ) ∣ k := by
      rw [← horder]
      apply orderOf_dvd_iff_zpow_eq_one.mpr
      have hpa : (a.left : Q) * y ^ k = 1 := ha
      have hy : y ^ k = (a.left : Q)⁻¹ :=
        eq_inv_of_mul_eq_one_right hpa
      calc
        (QuotientGroup.mk' N y) ^ k =
            QuotientGroup.mk' N (y ^ k) := (map_zpow _ y k).symm
        _ = QuotientGroup.mk' N ((a.left : Q)⁻¹) := by rw [hy]
        _ = 1 := by simp
    obtain ⟨t, ht⟩ := hpk
    have hpa : (a.left : Q) * y ^ k = 1 := ha
    have hleft : (a.left : Q) = (y ^ k)⁻¹ :=
      eq_inv_of_mul_eq_one_left hpa
    have hyright : y ^ k = (a.left : Q)⁻¹ :=
      eq_inv_of_mul_eq_one_right hpa
    have hykN : y ^ k ∈ N := by
      rw [hyright]
      exact N.inv_mem a.left.property
    have hyfN : y ^ f ∈ N := by
      apply (QuotientGroup.eq_one_iff (y ^ f)).mp
      change QuotientGroup.mk' N (y ^ f) = 1
      rw [map_pow, ← horder]
      exact pow_orderOf_eq_one _
    let yf : N := ⟨y ^ f, hyfN⟩
    have hpow' : Y ^ (f : ℤ) = fn yf := by
      simpa [yf] using hpow
    have hYk : Y ^ k = fn ⟨y ^ k, hykN⟩ := by
      calc
        Y ^ k = Y ^ ((f : ℤ) * t) := by rw [ht]
        _ = (Y ^ (f : ℤ)) ^ t := zpow_mul Y (f : ℤ) t
        _ = (fn yf) ^ t := by rw [hpow']
        _ = fn (yf ^ t) := (map_zpow fn yf t).symm
        _ = fn ⟨y ^ k, hykN⟩ := by
          congr 1
          apply Subtype.ext
          change (y ^ f) ^ t = y ^ k
          rw [← zpow_natCast, ← zpow_mul, ← ht]
    change fn a.left * Y ^ k = 1
    rw [show fn a.left = (fn ⟨y ^ k, hykN⟩)⁻¹ by
        rw [← map_inv]
        congr 1
        apply Subtype.ext
        exact hleft]
    rw [hYk]
    exact inv_mul_cancel _
  let F : Q →* H :=
    (p.liftOfSurjective hpSurj) ⟨F₀, hker⟩
  have hFp : F.comp p = F₀ :=
    MonoidHom.liftOfRightInverse_comp
      (f := p)
      (f_inv := Function.surjInv hpSurj)
      (Function.rightInverse_surjInv hpSurj)
      (g := ⟨F₀, hker⟩)
  refine ⟨F, ?_, ?_⟩
  · ext n
    have hpInl : p (SemidirectProduct.inl n) = (n : Q) := by
      exact SemidirectProduct.lift_inl N.subtype yp _ n
    have hFInl : F₀ (SemidirectProduct.inl n) = fn n := by
      exact SemidirectProduct.lift_inl fn Yp _ n
    change F (n : Q) = fn n
    calc
      F (n : Q) = F (p (SemidirectProduct.inl n)) := by rw [hpInl]
      _ = F₀ (SemidirectProduct.inl n) :=
        DFunLike.congr_fun hFp (SemidirectProduct.inl n)
      _ = fn n := hFInl
  · let oneZ : Z := Multiplicative.ofAdd (1 : ℤ)
    have hpInr : p (SemidirectProduct.inr oneZ) = y := by
      calc
        p (SemidirectProduct.inr oneZ) = yp oneZ :=
          SemidirectProduct.lift_inr N.subtype yp _ _
        _ = y := by simp [yp, oneZ, integerPowersHom]
    have hFInr : F₀ (SemidirectProduct.inr oneZ) = Y := by
      calc
        F₀ (SemidirectProduct.inr oneZ) = Yp oneZ :=
          SemidirectProduct.lift_inr fn Yp _ _
        _ = Y := by simp [Yp, oneZ, integerPowersHom]
    calc
      F y = F (p (SemidirectProduct.inr oneZ)) := by rw [hpInr]
      _ = F₀ (SemidirectProduct.inr oneZ) :=
        DFunLike.congr_fun hFp (SemidirectProduct.inr oneZ)
      _ = Y := hFInr

/-- Two homomorphisms out of a group with cyclic quotient agree when they
agree on the normal subgroup and on one lift of a quotient generator. -/
theorem hom_ext_cyclic
    {Q H : Type*} [Group Q] [Group H]
    (N : Subgroup Q) [N.Normal] (y : Q)
    (hgen : Subgroup.zpowers (QuotientGroup.mk' N y) = ⊤)
    (f g : Q →* H)
    (hN : f.comp N.subtype = g.comp N.subtype)
    (hy : f y = g y) :
    f = g := by
  ext q
  have hqbar : QuotientGroup.mk' N q ∈
      Subgroup.zpowers (QuotientGroup.mk' N y) := by
    rw [hgen]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hqbar
  have hnmem : q * (y ^ k)⁻¹ ∈ N := by
    apply (QuotientGroup.eq_one_iff (q * (y ^ k)⁻¹)).mp
    change QuotientGroup.mk' N (q * (y ^ k)⁻¹) = 1
    rw [map_mul, map_inv, map_zpow, hk]
    simp
  let n : N := ⟨q * (y ^ k)⁻¹, hnmem⟩
  have hq : (n : Q) * y ^ k = q := by
    simp [n, mul_assoc]
  have hn : f (n : Q) = g (n : Q) := by
    have hn' := DFunLike.congr_fun hN n
    exact hn'
  have hfdecomp : f ((n : Q) * y ^ k) =
      f (n : Q) * (f y) ^ k := by
    calc
      f ((n : Q) * y ^ k) = f (n : Q) * f (y ^ k) := map_mul _ _ _
      _ = f (n : Q) * (f y) ^ k := by rw [map_zpow]
  have hgdecomp : g ((n : Q) * y ^ k) =
      g (n : Q) * (g y) ^ k := by
    calc
      g ((n : Q) * y ^ k) = g (n : Q) * g (y ^ k) := map_mul _ _ _
      _ = g (n : Q) * (g y) ^ k := by rw [map_zpow]
  calc
    f q = f ((n : Q) * y ^ k) := congrArg f hq.symm
    _ = f (n : Q) * (f y) ^ k := hfdecomp
    _ = g (n : Q) * (g y) ^ k := by rw [hn, hy]
    _ = g ((n : Q) * y ^ k) := hgdecomp.symm
    _ = g q := congrArg g hq

/-- Intertwining conjugation by one element automa intertwines every
integer power of that conjugation. -/
theorem monoid_normal_zpow
    {Q : Type u} {T : Type v} [Group Q] [Group T]
    (N : Subgroup Q) [N.Normal]
    (fn : N →* T) (y : Q) (Y : T)
    (hconj : ∀ n : N,
      fn (MulAut.conjNormal y n) = Y * fn n * Y⁻¹) :
    ∀ (k : ℤ) (n : N),
      fn (MulAut.conjNormal (y ^ k) n) =
        Y ^ k * fn n * (Y ^ k)⁻¹ := by
  have hconjInv (n : N) :
      fn (MulAut.conjNormal y⁻¹ n) = Y⁻¹ * fn n * Y := by
    let n' : N := MulAut.conjNormal y⁻¹ n
    have h := hconj n'
    have hn : MulAut.conjNormal y n' = n := by
      apply Subtype.ext
      simp [n']
    rw [hn] at h
    calc
      fn n' = Y⁻¹ * (Y * fn n' * Y⁻¹) * Y := by group
      _ = Y⁻¹ * fn n * Y := by rw [h]
  intro k n
  induction k using Int.induction_on generalizing n with
  | zero => simp
  | succ m ih =>
      have hsource :
          MulAut.conjNormal (y ^ ((m : ℤ) + 1)) n =
            MulAut.conjNormal (y ^ (m : ℤ))
              (MulAut.conjNormal y n) := by
        apply Subtype.ext
        rw [zpow_add_one]
        simp only [MulAut.conjNormal_apply]
        group
      rw [hsource, ih, hconj, zpow_add_one]
      group
  | pred m ih =>
      have hsource :
          MulAut.conjNormal (y ^ (-(m : ℤ) - 1)) n =
            MulAut.conjNormal (y ^ (-(m : ℤ)))
              (MulAut.conjNormal y⁻¹ n) := by
        apply Subtype.ext
        rw [zpow_sub_one]
        simp only [MulAut.conjNormal_apply]
        group
      rw [hsource, ih, hconjInv, zpow_sub_one]
      group

/-- The quotient by the preimage of a normal subgroup is canonically the
quotient of the target by that subgroup. -/
noncomputable def quotientComapSurjective
    {Q G : Type*} [Group Q] [Group G]
    (q : Q →* G) (hq : Function.Surjective q)
    (I : Subgroup G) [I.Normal] :
    Q ⧸ I.comap q ≃* G ⧸ I := by
  let qI : Q →* G ⧸ I := (QuotientGroup.mk' I).comp q
  have hqI : Function.Surjective qI := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective I z
    obtain ⟨x, rfl⟩ := hq g
    exact ⟨x, rfl⟩
  have hker : I.comap q = qI.ker := by
    ext x
    simp [qI, MonoidHom.mem_ker]
  exact QuotientGroup.liftEquiv (I.comap q) hqI hker

@[simp]
theorem comap_surjective_mk
    {Q G : Type*} [Group Q] [Group G]
    (q : Q →* G) (hq : Function.Surjective q)
    (I : Subgroup G) [I.Normal] (x : Q) :
    quotientComapSurjective q hq I
        (QuotientGroup.mk' (I.comap q) x) =
      QuotientGroup.mk' I (q x) :=
  rfl

/-- A fixed root of the power relation on a lift of a cyclic generator gives
a semilinear realization of the whole cyclic central extension. -/
theorem cyclic_semidirect_root
    {Q : Type u} {G : Type v} {M : Type w}
    [Group Q] [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (phi : q.ker →* M)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (n : ℕ) [NeZero n] (x : Q)
    (horder : orderOf (q x) = n)
    (hgen : Subgroup.zpowers (QuotientGroup.mk' q.ker x) = ⊤)
    (eta : M) (hetaFixed : ∀ g : G, g • eta = eta)
    (hetaPow : eta ^ n = phi ⟨x ^ n, by
      rw [MonoidHom.mem_ker, map_pow, ← horder, pow_orderOf_eq_one]⟩) :
    ∃ lift : Q →* M ⋊[MulDistribMulAction.toMulAut G M] G,
      SemidirectProduct.rightHom.comp lift = q ∧
        (∀ z : q.ker,
          lift z.1 = SemidirectProduct.inl (phi z)) ∧
        lift x = ⟨eta, q x⟩ := by
  let N : Subgroup Q := q.ker
  let target := M ⋊[MulDistribMulAction.toMulAut G M] G
  let fn : N →* target := SemidirectProduct.inl.comp phi
  let Y : target := ⟨eta, q x⟩
  have hquotOrder : orderOf (QuotientGroup.mk' N x) = n := by
    let e := QuotientGroup.quotientKerEquivOfSurjective q hq
    calc
      orderOf (QuotientGroup.mk' N x) =
          orderOf (e (QuotientGroup.mk' N x)) :=
        (e.orderOf_eq _).symm
      _ = orderOf (q x) := by rfl
      _ = n := horder
  have hYpowNat : ∀ m : ℕ, Y ^ m = ⟨eta ^ m, (q x) ^ m⟩ := by
    intro m
    induction m with
    | zero => simp [Y]
    | succ m ih =>
        rw [pow_succ, ih]
        apply SemidirectProduct.ext
        · change eta ^ m * ((q x) ^ m • eta) = eta ^ (m + 1)
          calc
            eta ^ m * ((q x) ^ m • eta) = eta ^ m * eta := by
              rw [hetaFixed]
            _ = eta ^ (m + 1) := (pow_succ eta m).symm
        · change (q x) ^ m * q x = (q x) ^ (m + 1)
          exact (pow_succ (q x) m).symm
  have hconj : ∀ (k : ℤ) (z : N),
      fn (MulAut.conjNormal (x ^ k) z) =
        Y ^ k * fn z * (Y ^ k)⁻¹ := by
    intro k z
    have hzcentral := hcentral z.property
    have hsource : MulAut.conjNormal (x ^ k) z = z := by
      apply Subtype.ext
      change x ^ k * (z : Q) * (x ^ k)⁻¹ = z
      have hzcomm : x ^ k * (z : Q) = (z : Q) * x ^ k :=
        Subgroup.mem_center_iff.mp hzcentral (x ^ k)
      rw [hzcomm]
      group
    have htarget : Commute Y (SemidirectProduct.inl (phi z)) := by
      have hl : Commute (SemidirectProduct.inl eta : target)
          (SemidirectProduct.inl (phi z)) := by
        exact (Commute.all eta (phi z)).map SemidirectProduct.inl
      have hr : Commute (SemidirectProduct.inr (q x) : target)
          (SemidirectProduct.inl (phi z)) := by
        rw [Commute]
        apply SemidirectProduct.ext
        · simp [hfixed]
        · simp
      rw [show Y = SemidirectProduct.inl eta *
          SemidirectProduct.inr (q x) from
        SemidirectProduct.mk_eq_inl_mul_inr (q x) eta]
      exact Commute.mul_left hl hr
    rw [hsource]
    change SemidirectProduct.inl (phi z) =
      Y ^ k * SemidirectProduct.inl (phi z) * (Y ^ k)⁻¹
    rw [(htarget.zpow_left k).eq]
    simp
  have hpow : Y ^ n = fn ⟨x ^ n, by
      apply (QuotientGroup.eq_one_iff (x ^ n)).mp
      change QuotientGroup.mk' N (x ^ n) = 1
      rw [map_pow, ← hquotOrder, pow_orderOf_eq_one]⟩ := by
    rw [hYpowNat]
    apply SemidirectProduct.ext
    · change eta ^ n = phi ⟨x ^ n, _⟩
      exact hetaPow
    · change (q x) ^ n = 1
      rw [← horder, pow_orderOf_eq_one]
  obtain ⟨lift, hliftN, hliftY⟩ :=
    hom_normal_cyclic
      N x n (NeZero.pos n) hquotOrder hgen fn Y hconj hpow
  refine ⟨lift, ?_, ?_, ?_⟩
  · apply hom_ext_cyclic N x hgen
    · rw [MonoidHom.comp_assoc, hliftN]
      ext z
      change 1 = q z
      exact z.property.symm
    · change SemidirectProduct.rightHom (lift x) = q x
      rw [hliftY]
      rfl
  · intro z
    change (lift.comp N.subtype) z = SemidirectProduct.inl (phi z)
    rw [hliftN]
    rfl
  · exact hliftY

/-- A fixed root for a cyclic inertia lift gives a semilinear lift of the
full preimage of inertia, with values in the semidirect product for the
ambient quotient group. -/
theorem inertia_preimage_semidirect
    {Q : Type u} {G : Type v} {M : Type w}
    [Group Q] [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (phi : q.ker →* M)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (I : Subgroup G) [I.Normal]
    (n : ℕ) [NeZero n]
    (eI : Multiplicative (ZMod n) ≃* I)
    (x : Q)
    (hx : q x = I.subtype (eI (CyclicH2.generator (n := n))))
    (eta : M)
    (hetaFixed :
      letI : MulDistribMulAction I M :=
        (inferInstance : MulDistribMulAction G M).compHom M I.subtype
      ∀ i : I, i • eta = eta)
    (hetaPow : eta ^ n = phi ⟨x ^ n, by
      rw [MonoidHom.mem_ker, map_pow, hx]
      change I.subtype (eI (CyclicH2.generator (n := n)) ^ n) = 1
      calc
        I.subtype (eI (CyclicH2.generator (n := n)) ^ n) =
            I.subtype (eI ((CyclicH2.generator (n := n)) ^ n)) := by
              exact congrArg I.subtype
                (map_pow eI (CyclicH2.generator (n := n)) n).symm
        _ = I.subtype (1 : I) := by
              congr 1
              rw [← map_one eI]
              congr 1
              apply Multiplicative.ext
              simp [CyclicH2.generator]
        _ = 1 := map_one I.subtype⟩) :
    let P := centralExtensionPreimage q I
    ∃ fn : P →* M ⋊[MulDistribMulAction.toMulAut G M] G,
      SemidirectProduct.rightHom.comp fn = q.comp P.subtype ∧
        (∀ z : q.ker,
          fn ⟨z.1, by
            change q z.1 ∈ I
            rw [z.property]
            exact I.one_mem⟩ =
            SemidirectProduct.inl (phi z)) ∧
        fn ⟨x, by
          change q x ∈ I
          rw [hx]
          exact (eI (CyclicH2.generator (n := n))).property⟩ =
            ⟨eta, q x⟩ := by
  let P := centralExtensionPreimage q I
  let p : P →* I := centralPreimageProjection q I
  have hp : Function.Surjective p :=
    preimage_projection_surjective q hq I
  have hpcentral : p.ker ≤ Subgroup.center P :=
    extension_preimage_projection q I hcentral
  let eK : q.ker ≃* p.ker :=
    extensionPreimageProjection q I
  let phiP : p.ker →* M := phi.comp eK.symm.toMonoidHom
  let iAction : MulDistribMulAction I M :=
    (inferInstance : MulDistribMulAction G M).compHom M I.subtype
  letI : MulDistribMulAction I M := iAction
  have hfixedP (i : I) (z : p.ker) : i • phiP z = phiP z := by
    exact hfixed i.1 (eK.symm z)
  let xP : P := ⟨x, by
    change q x ∈ I
    rw [hx]
    exact (eI (CyclicH2.generator (n := n))).property⟩
  have hpx : p xP = eI (CyclicH2.generator (n := n)) := by
    apply Subtype.ext
    exact hx
  have hporder : orderOf (p xP) = n := by
    rw [hpx, eI.orderOf_eq]
    simp [CyclicH2.generator]
  have hpgenI : Subgroup.zpowers (p xP) = ⊤ := by
    rw [hpx]
    exact zpowers_top_equiv eI
      (CyclicH2.generator (n := n))
      (cyclic_zpowers_top n)
  have hpgen : Subgroup.zpowers (QuotientGroup.mk' p.ker xP) = ⊤ := by
    let ep := QuotientGroup.quotientKerEquivOfSurjective p hp
    have h := zpowers_top_equiv ep.symm (p xP) hpgenI
    have heq : ep.symm (p xP) = QuotientGroup.mk' p.ker xP := by
      apply ep.injective
      rw [ep.apply_symm_apply]
      rfl
    rwa [heq] at h
  have hetaPowP : eta ^ n = phiP ⟨xP ^ n, by
      rw [MonoidHom.mem_ker, map_pow, ← hporder, pow_orderOf_eq_one]⟩ := by
    exact hetaPow
  obtain ⟨liftI, hliftIRight, hliftIKernel, hliftIX⟩ :=
    cyclic_semidirect_root
      p hp hpcentral phiP hfixedP n xP hporder hpgen eta hetaFixed hetaPowP
  let mapIG :
      M ⋊[MulDistribMulAction.toMulAut I M] I →*
        M ⋊[MulDistribMulAction.toMulAut G M] G :=
    SemidirectProduct.map (MonoidHom.id M) I.subtype (by
      intro i
      ext m
      rfl)
  let fn : P →* M ⋊[MulDistribMulAction.toMulAut G M] G :=
    mapIG.comp liftI
  refine ⟨fn, ?_, ?_, ?_⟩
  · ext a
    have ha := DFunLike.congr_fun hliftIRight a
    change I.subtype (liftI a).right = q a.1
    exact congrArg Subtype.val ha
  · intro z
    let zP : p.ker := eK z
    have hz := hliftIKernel zP
    change mapIG (liftI (eK z)) = SemidirectProduct.inl (phi z)
    rw [hz]
    rw [SemidirectProduct.map_inl]
    change SemidirectProduct.inl (phi (eK.symm (eK z))) =
      SemidirectProduct.inl (phi z)
    rw [eK.symm_apply_apply]
  · change mapIG (liftI xP) = ⟨eta, q x⟩
    rw [hliftIX]
    apply SemidirectProduct.ext
    · rfl
    · change I.subtype (p xP) = q x
      rw [hpx]
      exact hx.symm

/-- An additive representation acts multiplicatively on the multiplicative
type tag of its underlying additive group. -/
@[reducible]
def representationMultiplicativeAction
    {G : Type u} [Group G]
    (A : Rep.{v} ℤ G) : MulDistribMulAction G (Multiplicative A) where
  smul g x := Multiplicative.ofAdd (A.ρ g x.toAdd)
  one_smul x := by
    apply Multiplicative.toAdd.injective
    change A.ρ 1 x.toAdd = x.toAdd
    rw [map_one]
    rfl
  mul_smul g h x := by
    apply Multiplicative.toAdd.injective
    change A.ρ (g * h) x.toAdd = A.ρ g (A.ρ h x.toAdd)
    rw [map_mul]
    rfl
  smul_one g := by
    apply Multiplicative.toAdd.injective
    exact map_zero (A.ρ g)
  smul_mul g x y := by
    apply Multiplicative.toAdd.injective
    exact map_add (A.ρ g) x.toAdd y.toAdd

@[simp]
theorem representation_multiplicative_smul
    {G : Type u} [Group G] (A : Rep.{v} ℤ G)
    (g : G) (x : Multiplicative A) :
    letI : MulDistribMulAction G (Multiplicative A) :=
      representationMultiplicativeAction A
    g • x = Multiplicative.ofAdd (A.ρ g x.toAdd) :=
  rfl

/-- A morphism of integral representations, written multiplicatively on
the underlying additive groups. -/
def representationHomMultiplicative
    {G : Type} [Group G] {A B : Rep ℤ G} (f : A ⟶ B) :
    Multiplicative A →* Multiplicative B where
  toFun x := Multiplicative.ofAdd (f.hom x.toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    exact map_zero f.hom
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    exact map_add f.hom x.toAdd y.toAdd

theorem representation_hom_equivariant
    {G : Type} [Group G] {A B : Rep ℤ G} (f : A ⟶ B)
    (g : G) (x : Multiplicative A) :
    letI : MulDistribMulAction G (Multiplicative A) :=
      representationMultiplicativeAction A
    letI : MulDistribMulAction G (Multiplicative B) :=
      representationMultiplicativeAction B
    representationHomMultiplicative f (g • x) =
      g • representationHomMultiplicative f x := by
  apply Multiplicative.toAdd.injective
  change f.hom (A.ρ g x.toAdd) = B.ρ g (f.hom x.toAdd)
  exact Rep.hom_comm_apply f g x.toAdd

/-- The representation obtained by multiplicatively tagging an integral
representation and then converting back is canonically isomorphic to the
original representation. -/
noncomputable def representationRepIso
    {G : Type} [Group G] (A : Rep ℤ G) :
    letI : MulDistribMulAction G (Multiplicative A) :=
      representationMultiplicativeAction A
    Rep.ofMulDistribMulAction G (Multiplicative A) ≅ A := by
  letI : Module ℤ A := A.hV2
  letI : MulDistribMulAction G (Multiplicative A) :=
    representationMultiplicativeAction A
  let eRep :
      (Rep.ofMulDistribMulAction G (Multiplicative A)).ρ.Equiv A.ρ :=
    Representation.Equiv.mk
      ((AddEquiv.additiveMultiplicative A).toIntLinearEquiv
        (modM := AddCommGroup.toIntModule _)
        (modM₂ := A.hV2)) (by
          intro g
          apply LinearMap.ext
          intro x
          rfl)
  exact Rep.mkIso eRep

/-- Every ordinary degree-two cohomology class has a normalized
multiplicative representative. -/
theorem MHTwo.group_cohomology_surj
    {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M] :
    Function.Surjective
      (MHTwo.toGroupCohomology :
        MHTwo G M →
          groupCohomology.H2 (Rep.ofMulDistribMulAction G M)) := by
  intro z
  induction z using groupCohomology.H2_induction_on with
  | h x =>
      let f : G × G → M := Additive.toMul ∘ x
      have hf : groupCohomology.IsMulCocycle₂ f :=
        groupCohomology.isMulCocycle₂_of_mem_cocycles₂
          (G := G) (M := M) x x.property
      let c : NMCocycl₂ (G := G) (M := M) :=
        NMCocycl₂.normalize f hf
      refine ⟨MHTwo.mk c, ?_⟩
      change groupCohomology.H2π (Rep.ofMulDistribMulAction G M)
          (groupCohomology.cocyclesOfIsMulCocycle₂ c.isMulCocycle₂) =
        groupCohomology.H2π (Rep.ofMulDistribMulAction G M) x
      rw [groupCohomology.H2π_eq_iff]
      have hboundary :=
        (groupCohomology.coboundariesOfIsMulCoboundary₂
          (NMCocycl₂.normalize_div_coboundary₂ f hf)).property
      convert hboundary using 1

set_option maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the large search space in this proof.
/-- An ordinary degree-two class vanishes if a multiplicative detector kills
every normalized multiplicative representative. -/
theorem h_multiplicative_detector
    {G : Type} [Group G] (A B : Rep ℤ G) (f : A ⟶ B)
    (hdetector :
      letI : MulDistribMulAction G (Multiplicative A) :=
        representationMultiplicativeAction A
      letI : MulDistribMulAction G (Multiplicative B) :=
        representationMultiplicativeAction B
      ∀ x : MHTwo G (Multiplicative A),
        MHTwo.mapCoefficientsHom
            (representationHomMultiplicative f)
            (representation_hom_equivariant f) x = 1 →
          x = 1)
    (y : groupCohomology A 2)
    (hy : ((groupCohomology.functor ℤ G 2).map f) y = 0) :
    y = 0 := by
  letI : Module ℤ A := A.hV2
  letI : Module ℤ B := B.hV2
  letI : MulDistribMulAction G (Multiplicative A) :=
    representationMultiplicativeAction A
  letI : MulDistribMulAction G (Multiplicative B) :=
    representationMultiplicativeAction B
  let tagA := Rep.ofMulDistribMulAction G (Multiplicative A)
  let tagB := Rep.ofMulDistribMulAction G (Multiplicative B)
  let eA : tagA ≅ A := representationRepIso A
  let eB : tagB ≅ B := representationRepIso B
  let F := groupCohomology.functor ℤ G 2
  let fTag : tagA ⟶ tagB :=
    MHTwo.coefficientRepHom
      (representationHomMultiplicative f)
      (representation_hom_equivariant f)
  have hsquare : fTag ≫ eB.hom = eA.hom ≫ f := by
    apply Rep.Hom.ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl
  let yTag : groupCohomology tagA 2 := (F.mapIso eA).inv y
  obtain ⟨x, hx⟩ :=
    MHTwo.group_cohomology_surj
      (G := G) (M := Multiplicative A) yTag
  have hxTo : (F.map eA.hom)
      (MHTwo.toGroupCohomology x) = y := by
    rw [hx]
    dsimp [yTag]
    have hcat : (F.map eA.inv) ≫ (F.map eA.hom) = 𝟙 (F.obj A) :=
      (F.mapIso eA).inv_hom_id
    have happ := congrArg
      (fun h : F.obj A ⟶ F.obj A ↦ h.hom y) hcat
    simpa [F] using happ
  have hxmap : MHTwo.mapCoefficientsHom
      (representationHomMultiplicative f)
      (representation_hom_equivariant f) x = 1 := by
    apply (MHTwo.group_cohomology_zero _).mp
    rw [MHTwo.cohomology_coefficients_hom]
    have hinj : Function.Injective (F.map eB.hom) :=
      (ModuleCat.mono_iff_injective (F.map eB.hom)).mp inferInstance
    apply hinj
    calc
      (F.map eB.hom) ((F.map fTag)
            (MHTwo.toGroupCohomology x)) =
          (F.map (fTag ≫ eB.hom))
            (MHTwo.toGroupCohomology x) := by
              rw [F.map_comp]
              rfl
      _ = (F.map (eA.hom ≫ f))
            (MHTwo.toGroupCohomology x) := by rw [hsquare]
      _ = (F.map f) ((F.map eA.hom)
            (MHTwo.toGroupCohomology x)) := by
              rw [F.map_comp]
              rfl
      _ = 0 := by rw [hxTo]; exact hy
      _ = (F.map eB.hom) 0 := (map_zero (F.map eB.hom).hom).symm
  have hxone := hdetector x hxmap
  have hone : MHTwo.toGroupCohomology
      (1 : MHTwo G (Multiplicative A)) = 0 :=
    MHTwo.group_cohomology_one
  calc
    y = (F.map eA.hom) (MHTwo.toGroupCohomology x) := hxTo.symm
    _ = (F.map eA.hom) 0 := by rw [hxone, hone]; rfl
    _ = 0 := map_zero (F.map eA.hom).hom

universe uG uH uM uN uP uQ

/-- Equivariant transport commutes with a coefficient homomorphism when the
two coefficient squares commute. -/
theorem MHTrans.htwo_mulequiv_mapcoeffshom
    {G : Type uG} {H : Type uH}
    {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}
    [Group G] [Group H]
    [CommGroup M] [CommGroup N] [CommGroup P] [CommGroup Q]
    [MulDistribMulAction G M] [MulDistribMulAction H N]
    [MulDistribMulAction G P] [MulDistribMulAction H Q]
    (eG : G ≃* H) (eM : M ≃* N) (eP : P ≃* Q)
    (heM : ∀ g m, eM (g • m) = eG g • eM m)
    (heP : ∀ g p, eP (g • p) = eG g • eP p)
    (f : M →* P) (hf : ∀ g m, f (g • m) = g • f m)
    (k : N →* Q) (hk : ∀ h n, k (h • n) = h • k n)
    (hsquare : ∀ m, eP (f m) = k (eM m))
    (x : MHTwo G M) :
    MHTrans.h2Equiv eG eP heP
        (MHTwo.mapCoefficientsHom f hf x) =
      MHTwo.mapCoefficientsHom k hk
        (MHTrans.h2Equiv eG eM heM x) := by
  induction x using Quotient.inductionOn with
  | _ c =>
      apply congrArg MHTwo.mk
      ext p
      exact hsquare (c (eG.symm p.1, eG.symm p.2))

/-- The multiplicative group underlying Mathlib's additive invariant
representation is the usual subgroup of multiplicative invariants. -/
noncomputable def representationInvariantsEquiv
    {G M : Type} [Group G] [Fintype G]
    [CommGroup M] [MulDistribMulAction G M]
    (H : Subgroup G) [H.Normal] :
    Multiplicative
        ((Rep.ofMulDistribMulAction G M).quotientToInvariants H) ≃*
      FMAct.invariants H M where
  toFun x := ⟨x.toAdd.1.toMul, fun h ↦ by
    exact congrArg Additive.toMul (x.toAdd.2 h)⟩
  invFun x := Multiplicative.ofAdd
    ⟨Additive.ofMul x.1, fun h ↦ congrArg Additive.ofMul (x.2 h)⟩
  left_inv x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

/-- Units of a subgroup fixed field are exactly the field units fixed by
that subgroup. -/
noncomputable def fixedMulInvariants
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (H : Subgroup Gal(L/K)) :
    (IntermediateField.fixedField H)ˣ ≃*
      FMAct.invariants H Lˣ where
  toFun a := ⟨Units.map (algebraMap (IntermediateField.fixedField H) L) a,
    fun h ↦ by
      apply Units.ext
      exact a.1.2 h⟩
  invFun x := by
    let a : IntermediateField.fixedField H :=
      ⟨(x.1 : Lˣ), by
        rw [IntermediateField.mem_fixedField_iff]
        intro sigma hsigma
        exact congrArg Units.val (x.2 ⟨sigma, hsigma⟩)⟩
    have ha0 : a ≠ 0 := by
      intro ha
      have := congrArg
        (fun z : IntermediateField.fixedField H ↦ (z : L)) ha
      exact x.1.ne_zero (by simp [a] at this)
    exact Units.mk0 a ha0
  left_inv a := by
    apply Units.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    rfl

/-- The quotient-invariant coefficient module, multiplicatively presented,
is the unit group of the subgroup fixed field. -/
noncomputable def invariantsFixedEquiv
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal] :
    Multiplicative
        ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H) ≃*
      (IntermediateField.fixedField H)ˣ :=
  (representationInvariantsEquiv
      (G := Gal(L/K)) (M := Lˣ) H).trans
    (fixedMulInvariants (K := K) (L := L) H).symm

@[simp]
theorem invariants_fixed_coe
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal]
    (x : Multiplicative
      ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H)) :
    ((((invariantsFixedEquiv H x :
        (IntermediateField.fixedField H)ˣ) :
          IntermediateField.fixedField H) : L)) =
      (((Rep.toAdditive (M := Gal(L/K)) (G := Lˣ) x.toAdd.1).toMul : Lˣ) : L) := by
  rfl

@[simp]
theorem fixed_units_invariants
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal]
    (x : Multiplicative
      ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H)) :
    fixedMulInvariants H
        (invariantsFixedEquiv H x) =
      representationInvariantsEquiv H x := by
  exact (fixedMulInvariants H).apply_symm_apply _

theorem invariants_restrict_coe
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal]
    (sigma : Gal(L/K)) (a : (IntermediateField.fixedField H)ˣ) :
    (fixedMulInvariants H
        (Units.map ((AlgEquiv.restrictNormalHom
          (IntermediateField.fixedField H)) sigma) a)).1 =
      sigma • (fixedMulInvariants H a).1 := by
  apply Units.ext
  change
    (((AlgEquiv.restrictNormalHom
        (IntermediateField.fixedField H)) sigma (a :
          IntermediateField.fixedField H) :
            IntermediateField.fixedField H) : L) =
      sigma (((a : IntermediateField.fixedField H) : L))
  exact AlgEquiv.restrictNormalHom_apply
    (IntermediateField.fixedField H) sigma (a :
      IntermediateField.fixedField H)

set_option synthInstance.maxHeartbeats 200000 in
-- Extra heartbeats are needed for the typeclass search in this proof.
/-- The fixed-field coefficient equivalence intertwines the quotient action
with restriction of Galois automorphisms to the fixed field. -/
theorem invariants_fixed_equivariant
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal]
    (g : Gal(L/K) ⧸ H)
    (x : Multiplicative
      ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H)) :
    letI : MulDistribMulAction (Gal(L/K) ⧸ H)
        (Multiplicative
          ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H)) :=
      representationMultiplicativeAction
        ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H)
    invariantsFixedEquiv H (g • x) =
      IsGalois.normalAutEquivQuotient H g •
        invariantsFixedEquiv H x := by
  letI : MulDistribMulAction (Gal(L/K) ⧸ H)
      (Multiplicative
        ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H)) :=
    representationMultiplicativeAction
      ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants H)
  induction g using QuotientGroup.induction_on with
  | _ sigma =>
      apply (fixedMulInvariants
        (K := K) (L := L) H).injective
      apply Subtype.ext
      rw [IsGalois.normalAutEquivQuotient_apply]
      rw [AlgEquiv.smul_units_def]
      rw [invariants_restrict_coe
        (K := K) (L := L) H sigma]
      rw [fixed_units_invariants]
      rw [fixed_units_invariants]
      rw [representation_multiplicative_smul]
      simp only []
      rfl

/-- Noether's Hilbert-90 argument for any finite group acting faithfully by
field automorphisms.  The usual Galois-group statement is this theorem for
the tautological action of `Gal(L/K)`. -/
theorem isMulCoboundary₁_of_faithful_field_action
    {G F : Type} [Group G] [Finite G] [Field F]
    [MulSemiringAction G F] [FaithfulSMul G F]
    (f : G → Fˣ) (hf : groupCohomology.IsMulCocycle₁ f) :
    groupCohomology.IsMulCoboundary₁ f := by
  letI : Fintype G := Fintype.ofFinite G
  let coefficients : G →₀ F :=
    Finsupp.equivFunOnFinite.symm (fun g ↦ (f g : F))
  let actionFunctions : G → F → F := fun g ↦
    MulSemiringAction.toRingHom G F g
  let aux : F → F :=
    Finsupp.linearCombination F actionFunctions coefficients
  have hlinear : LinearIndependent F actionFunctions := by
    apply LinearIndependent.comp (ι' := G)
      (linearIndependent_monoidHom F F)
      (fun g ↦ (MulSemiringAction.toRingHom G F g).toMonoidHom)
    intro g h hgh
    apply toRingHom_injective G F
    apply RingHom.ext
    intro x
    exact DFunLike.congr_fun hgh x
  have haux : aux ≠ 0 := by
    have hcoeff := linearIndependent_iff.mp hlinear coefficients
    intro hzero
    have hcoeffZero := hcoeff hzero
    have hone := DFunLike.congr_fun hcoeffZero 1
    change (f 1 : F) = 0 at hone
    exact Units.ne_zero (f 1) hone
  obtain ⟨z, hz⟩ : ∃ z : F, aux z ≠ 0 :=
    not_forall.mp (fun hall ↦ haux (funext hall))
  have hauxApply : aux z = ∑ g, (f g : F) * g • z := by
    simp [aux, actionFunctions, coefficients,
      Finsupp.linearCombination, Finsupp.sum_fintype]
  refine ⟨(Units.mk0 (aux z) hz)⁻¹, ?_⟩
  intro g
  simp only [groupCohomology.IsMulCocycle₁,     div_inv_eq_mul, Units.ext_iff,
    Units.val_mul, Units.coe_smul, Units.val_inv_eq_inv_val,
    Units.val_mk0] at hf ⊢
  rw [hauxApply]
  have hsumNe : (∑ h, (f h : F) * h • z) ≠ 0 := by
    rw [← hauxApply]
    exact hz
  have hgSumNe : g • (∑ h, (f h : F) * h • z) ≠ 0 :=
    (smul_ne_zero_iff_ne g).2 hsumNe
  rw [smul_inv'']
  apply (inv_mul_eq_iff_eq_mul₀ hgSumNe).2
  simp_rw [Finset.smul_sum, smul_mul', Finset.sum_mul, mul_assoc,
    mul_comm _ (f _ : F), ← mul_assoc, ← hf g]
  exact eq_comm.mp (Fintype.sum_bijective (fun i ↦ g * i)
    (Group.mulLeft_bijective g) _ _ (fun i ↦ by
      rw [mul_smul]))

/-- The cohomological form of Noether's Hilbert 90 for a faithful finite
group action on a field. -/
theorem h_faithful_action
    {G F : Type} [Group G] [Finite G] [Field F]
    [MulSemiringAction G F] [FaithfulSMul G F] :
    IsZero (groupCohomology.H1 (Rep.ofMulDistribMulAction G Fˣ)) := by
  have hzero : ∀ x : groupCohomology.H1
      (Rep.ofMulDistribMulAction G Fˣ), x = 0 := by
    intro x
    induction x using groupCohomology.H1_induction_on with
    | h c =>
        exact (groupCohomology.H1π_eq_zero_iff _).2 (by
          refine (groupCohomology.coboundariesOfIsMulCoboundary₁ ?_).2
          let fc : G → Fˣ := fun g ↦ Additive.toMul (c.1 g)
          have hfc : groupCohomology.IsMulCocycle₁ fc := by
            exact groupCohomology.isMulCocycle₁_of_mem_cocycles₁
              (G := G) (M := Fˣ) c.1 c.2
          obtain ⟨beta, hbeta⟩ :=
            isMulCoboundary₁_of_faithful_field_action fc hfc
          exact ⟨beta, hbeta⟩)
  letI : Subsingleton (groupCohomology.H1
      (Rep.ofMulDistribMulAction G Fˣ)) :=
    ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Vanishing of normalized multiplicative `H²` implies vanishing of the
ordinary degree-two group cohomology used by inflation--restriction. -/
theorem h_multiplicative_subsingleton
    {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
    [Subsingleton (MHTwo G M)]
    (x : groupCohomology.H2 (Rep.ofMulDistribMulAction G M)) :
    x = 0 := by
  obtain ⟨y, rfl⟩ :=
    MHTwo.group_cohomology_surj (G := G) (M := M) x
  have hy : y = 1 := Subsingleton.elim _ _
  rw [hy]
  exact (MHTwo.group_cohomology_zero 1).2 rfl

/-- Elementwise degree-two inflation--restriction: if the restriction of a
class is zero and `H¹` of the normal subgroup vanishes, the class is inflated
from the quotient. -/
theorem inflation_preimage_restriction
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (H : Subgroup G) [H.Normal]
    (x : groupCohomology A 2)
    (hH1 : IsZero (groupCohomology (Rep.res H.subtype A) 1))
    (hx : restrictionCochainsMap A H 2 x = 0) :
    ∃ y : groupCohomology (A.quotientToInvariants H) 2,
      cochainsShortInflation A H 2 y = x := by
  let hlower : ∀ j : ℕ, 0 < j → j < 2 →
      IsZero (groupCohomology (Rep.res H.subtype A) j) := by
    intro j hj hj2
    have : j = 1 := by omega
    subst j
    exact hH1
  have hexact := restrictionCochainsShort A H 2 (by omega) hlower
  have hxker : x ∈ LinearMap.ker
      (restrictionCochainsMap A H 2).hom := by
    exact hx
  have hrange : LinearMap.range (cochainsShortInflation A H 2).hom =
      LinearMap.ker (restrictionCochainsMap A H 2).hom := by
    simpa [restrictionCochainsComplex] using hexact.moduleCat_range_eq_ker
  rw [← hrange] at hxker
  exact hxker

/-- A degree-two class vanishes when inflation--restriction descends it to a
quotient class which, in turn, comes from a coefficient representation with
vanishing degree-two cohomology.

Unlike a blanket vanishing assumption on the quotient `H²`, this statement is
suited to tame local fields: only the quotient class descended from the given
obstruction has to come from the unit representation of the unramified fixed
field. -/
theorem inflation_restriction_lift
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (H : Subgroup G) [H.Normal]
    (x : groupCohomology A 2)
    (hH1 : IsZero (groupCohomology (Rep.res H.subtype A) 1))
    (hrestriction : restrictionCochainsMap A H 2 x = 0)
    (B : Rep k (G ⧸ H))
    (f : B ⟶ A.quotientToInvariants H)
    (hB2 : ∀ z : groupCohomology B 2, z = 0)
    (hlift : ∀ y : groupCohomology (A.quotientToInvariants H) 2,
      cochainsShortInflation A H 2 y = x →
        ∃ z : groupCohomology B 2,
          groupCohomology.map (MonoidHom.id (G ⧸ H)) f 2 z = y) :
    x = 0 := by
  obtain ⟨y, hy⟩ :=
    inflation_preimage_restriction
      A H x hH1 hrestriction
  obtain ⟨z, hz⟩ := hlift y hy
  have hz0 : z = 0 := hB2 z
  have hy0 : y = 0 := by
    rw [← hz, hz0, map_zero]
  rw [hy0, map_zero] at hy
  exact hy.symm

/-- A coefficient detector on the quotient can replace the false assertion
that all quotient `H²` vanishes.  Naturality of inflation transports the
detected class to the original group, where injectivity of inflation for the
target coefficients forces it to vanish. -/
theorem inflation_restriction_detector
    {k G : Type u} [CommRing k] [Group G]
    (A B : Rep k G) (H : Subgroup G) [H.Normal]
    (f : A ⟶ B) (x : groupCohomology A 2)
    (hH1A : IsZero (groupCohomology (Rep.res H.subtype A) 1))
    (hrestriction : restrictionCochainsMap A H 2 x = 0)
    (hH1B : IsZero (groupCohomology (Rep.res H.subtype B) 1))
    (hdetector : ∀ y : groupCohomology (A.quotientToInvariants H) 2,
      groupCohomology.map (MonoidHom.id (G ⧸ H))
          ((Rep.quotientToInvariantsFunctor k H).map f) 2 y = 0 →
        y = 0)
    (hfx : groupCohomology.map (MonoidHom.id G) f 2 x = 0) :
    x = 0 := by
  obtain ⟨y, hy⟩ :=
    inflation_preimage_restriction
      A H x hH1A hrestriction
  let yf := groupCohomology.map (MonoidHom.id (G ⧸ H))
    ((Rep.quotientToInvariantsFunctor k H).map f) 2 y
  have hinflatedYf : cochainsShortInflation B H 2 yf = 0 := by
    have hnat := congrArg (fun g ↦ g y)
      ((groupCohomology.infNatTrans (k := k) H 2).naturality f)
    have hnat' : cochainsShortInflation B H 2 yf =
        groupCohomology.map (MonoidHom.id G) f 2
          (cochainsShortInflation A H 2 y) := by
      simpa [yf] using hnat
    rw [hnat', hy, hfx]
  have hinflationB : Function.Injective (cochainsShortInflation B H 2) := by
    have hmono := inflation_mono B H 2 (by omega)
      (fun j hj hj2 ↦ by
        have : j = 1 := by omega
        subst j
        exact hH1B)
    exact (ModuleCat.mono_iff_injective
      (cochainsShortInflation B H 2)).mp hmono
  have hyf : yf = 0 := by
    apply hinflationB
    calc
      cochainsShortInflation B H 2 yf = 0 := hinflatedYf
      _ = cochainsShortInflation B H 2 0 := by
        symm
        exact map_zero (cochainsShortInflation B H 2).hom
  have hy0 : y = 0 := hdetector y hyf
  rw [hy0, map_zero] at hy
  exact hy.symm

set_option maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the large search space in this proof.
/-- Multiplicative `H²` form of the quotient-detector argument. -/
theorem MHTwo.eq_oneinflation_restricdetecto
    {G M N : Type} [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    (H : Subgroup G) [H.Normal]
    (x : MHTwo G M)
    (f : M →* N) (hf : ∀ g : G, ∀ m : M, f (g • m) = g • f m)
    (hH1M : IsZero (groupCohomology
      (Rep.res H.subtype (Rep.ofMulDistribMulAction G M)) 1))
    (hH1N : IsZero (groupCohomology
      (Rep.res H.subtype (Rep.ofMulDistribMulAction G N)) 1))
    (hdetector : ∀ y : groupCohomology
        ((Rep.ofMulDistribMulAction G M).quotientToInvariants H) 2,
      ((groupCohomology.functor ℤ (G ⧸ H) 2).map
          ((Rep.quotientToInvariantsFunctor ℤ H).map
            (MHTwo.coefficientRepHom f hf))) y = 0 →
        y = 0)
    (hrestriction :
      letI : MulDistribMulAction H M :=
        (inferInstance : MulDistribMulAction G M).compHom M H.subtype
      MHTwo.restrictionHom H.subtype (fun _ _ ↦ rfl) x = 1)
    (hmap : MHTwo.mapCoefficientsHom f hf x = 1) :
    x = 1 := by
  let A := Rep.ofMulDistribMulAction G M
  let B := Rep.ofMulDistribMulAction G N
  let fRep : A ⟶ B := MHTwo.coefficientRepHom f hf
  let y := MHTwo.toGroupCohomology x
  have hyRestriction : restrictionCochainsMap A H 2 y = 0 := by
    letI : MulDistribMulAction H M :=
      (inferInstance : MulDistribMulAction G M).compHom M H.subtype
    change restriction A H 2 y = 0
    rw [← MHTwo.group_cohomology_restricsubgrou H x,
      hrestriction]
    exact MHTwo.group_cohomology_one
  have hyMap : groupCohomology.map (MonoidHom.id G) fRep 2 y = 0 := by
    rw [← MHTwo.cohomology_coefficients_hom f hf x,
      hmap]
    exact MHTwo.group_cohomology_one
  have hy : y = 0 := by
    apply inflation_restriction_detector
      A B H fRep y hH1M hyRestriction hH1N
    · simpa [A, B, fRep] using hdetector
    · exact hyMap
  exact (MHTwo.group_cohomology_zero x).mp hy

/-- Inflation--restriction kills a multiplicative degree-two class once its
restriction to a normal subgroup is trivial, degree-one cohomology of that
subgroup vanishes, and degree-two cohomology of the quotient invariants
vanishes. -/
theorem MHTwo.eq_one_inflatirestric
    {G M : Type} [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (H : Subgroup G) [H.Normal]
    (x : MHTwo G M)
    (hH1 : IsZero (groupCohomology
      (Rep.res H.subtype (Rep.ofMulDistribMulAction G M)) 1))
    (hquot : ∀ z : groupCohomology
      ((Rep.ofMulDistribMulAction G M).quotientToInvariants H) 2, z = 0)
    (hx :
      letI : MulDistribMulAction H M :=
        (inferInstance : MulDistribMulAction G M).compHom M H.subtype
      MHTwo.restrictionHom H.subtype (fun _ _ ↦ rfl) x = 1) :
    x = 1 := by
  letI : MulDistribMulAction H M :=
    (inferInstance : MulDistribMulAction G M).compHom M H.subtype
  let A := Rep.ofMulDistribMulAction G M
  let y := MHTwo.toGroupCohomology x
  have hyRestriction : restrictionCochainsMap A H 2 y = 0 := by
    change restriction A H 2 y = 0
    rw [← MHTwo.group_cohomology_restricsubgrou H x,
      hx]
    exact MHTwo.group_cohomology_one
  obtain ⟨z, hz⟩ :=
    inflation_preimage_restriction
      A H y hH1 hyRestriction
  have hz0 : z = 0 := hquot z
  rw [hz0, map_zero] at hz
  exact (MHTwo.group_cohomology_zero x).mp hz.symm

/-- Restriction along a group equivalence detects multiplicative
degree-two cohomology classes. -/
theorem MHTwo.eq_onerestrict_mulequiv
    {G H M : Type*} [Group G] [Group H] [CommGroup M]
    [MulDistribMulAction G M] [MulDistribMulAction H M]
    (e : H ≃* G)
    (hsmul : ∀ h : H, ∀ m : M, h • m = e h • m)
    (x : MHTwo G M)
    (hx : MHTwo.restrictionHom e.toMonoidHom hsmul x = 1) :
    x = 1 := by
  let hinv : ∀ g : G, ∀ m : M, g • m = e.symm g • m := by
    intro g m
    simpa using (hsmul (e.symm g) m).symm
  have hleft (z : MHTwo G M) :
      MHTwo.restrictionHom e.symm.toMonoidHom hinv
          (MHTwo.restrictionHom e.toMonoidHom hsmul z) = z := by
    induction z using Quotient.inductionOn with
    | _ c =>
        change MHTwo.mk
            (NMCocycl₂.restrict e.symm.toMonoidHom hinv
              (NMCocycl₂.restrict e.toMonoidHom hsmul c)) =
          MHTwo.mk c
        apply congrArg MHTwo.mk
        ext p
        change c (e (e.symm p.1), e (e.symm p.2)) = c p
        rw [e.apply_symm_apply p.1, e.apply_symm_apply p.2]
  calc
    x = MHTwo.restrictionHom e.symm.toMonoidHom hinv
          (MHTwo.restrictionHom e.toMonoidHom hsmul x) :=
      (hleft x).symm
    _ = MHTwo.restrictionHom e.symm.toMonoidHom hinv 1 := by
      rw [hx]
    _ = 1 := map_one _

/-- Triviality after restricting along a parametrization of a subgroup by
an equivalent group is exactly triviality on that subgroup. -/
theorem MHTwo.subgrourestric_eqone_mulequiv
    {G C M : Type*} [Group G] [Group C] [CommGroup M]
    [MulDistribMulAction G M]
    (I : Subgroup G) (e : C ≃* I)
    (x : MHTwo G M)
    (hx :
      letI : MulDistribMulAction I M :=
        (inferInstance : MulDistribMulAction G M).compHom M I.subtype
      letI : MulDistribMulAction C M :=
        (inferInstance : MulDistribMulAction I M).compHom M e.toMonoidHom
      MHTwo.restrictionHom
        (I.subtype.comp e.toMonoidHom) (fun _ _ ↦ rfl) x = 1) :
    letI : MulDistribMulAction I M :=
      (inferInstance : MulDistribMulAction G M).compHom M I.subtype
    MHTwo.restrictionHom I.subtype (fun _ _ ↦ rfl) x = 1 := by
  letI : MulDistribMulAction I M :=
    (inferInstance : MulDistribMulAction G M).compHom M I.subtype
  letI : MulDistribMulAction C M :=
    (inferInstance : MulDistribMulAction I M).compHom M e.toMonoidHom
  apply MHTwo.eq_onerestrict_mulequiv
    e (fun _ _ ↦ rfl)
  rw [MHTwo.restrictionHom_comp
    (f := I.subtype) (g := e.toMonoidHom)
    (hf := fun _ _ ↦ rfl) (hg := fun _ _ ↦ rfl)
    (hfg := fun _ _ ↦ rfl)]
  exact hx

/-- The mapped obstruction of a central extension vanishes once
inflation--restriction reduces it to a quotient with vanishing degree-two
cohomology. -/
theorem mapped_obstruction_restriction
    {Q G M : Type} [Group Q] [Group G] [CommGroup M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    [MulDistribMulAction G M]
    (phi : q.ker →* M)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (H : Subgroup G) [H.Normal]
    (hH1 : IsZero (groupCohomology
      (Rep.res H.subtype (Rep.ofMulDistribMulAction G M)) 1))
    (hquot : ∀ z : groupCohomology
      ((Rep.ofMulDistribMulAction G M).quotientToInvariants H) 2, z = 0)
    (hrestriction :
      letI : CommGroup q.ker :=
        centralExtensionComm q hcentral
      letI : MulDistribMulAction G q.ker :=
        trivialDistribAction G q.ker
      letI : MulDistribMulAction H M :=
        (inferInstance : MulDistribMulAction G M).compHom M H.subtype
      MHTwo.restrictionHom H.subtype (fun _ _ ↦ rfl)
        (MHTwo.mapCoefficientsHom phi
          (fun g z ↦ (hfixed g z).symm)
          (extensionObstructionClass q hq hcentral)) = 1) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    MHTwo.mapCoefficientsHom phi
        (fun g z ↦ (hfixed g z).symm)
        (extensionObstructionClass q hq hcentral) = 1 := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  apply MHTwo.eq_one_inflatirestric
    H _ hH1 hquot
  exact hrestriction

/-- A semilinear realization of a central extension trivializes its mapped
factor set.  Concretely, a lift to `M ⋊ G` supplies the one-cochain given by
the first coordinate of the lifted normalized section. -/
theorem mapped_semidirect_lift
    {Q : Type u} {G : Type v} {M : Type w}
    [Group Q] [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (phi : q.ker →* M)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (lift : Q →*
      M ⋊[MulDistribMulAction.toMulAut G M] G)
    (hlift : SemidirectProduct.rightHom.comp lift = q)
    (hkernel : ∀ z : q.ker,
      lift z.1 = SemidirectProduct.inl (phi z)) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    MHTwo.mapCoefficientsHom phi
        (fun g z ↦ (hfixed g z).symm)
        (extensionObstructionClass q hq hcentral) = 1 := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  let c := (centralExtensionSet q hq hcentral).normalizedMulCocycle
    (fun _ _ ↦ rfl)
  let d := NMCocycl₂.mapCoefficients phi
    (fun g z ↦ (hfixed g z).symm) c
  let s : G → Q := normalizedSurjInv q hq
  let b : G → M := fun g ↦ (lift (s g)).left
  have hs (g : G) : q (s g) = g :=
    normalized_surj_maps q hq g
  have hliftRight (x : Q) : (lift x).right = q x := by
    have h := DFunLike.congr_fun hlift x
    exact h
  have hsection (g h : G) :
      s g * s h =
        ((centralExtensionSet q hq hcentral (g, h) : q.ker) : Q) *
          s (g * h) := by
    change s g * s h =
      (s g * s h * (s (g * h))⁻¹) * s (g * h)
    group
  have hb (g h : G) :
      b g * (g • b h) = phi (c (g, h)) * b (g * h) := by
    have heq := congrArg lift (hsection g h)
    have hleft := congrArg SemidirectProduct.left heq
    simp only [map_mul, SemidirectProduct.mul_left] at hleft
    rw [hkernel] at hleft
    simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      map_one, MulAut.one_apply] at hleft
    rw [hliftRight, hs] at hleft
    change b g * g • b h = phi (c (g, h)) * b (g * h) at hleft
    exact hleft
  change MHTwo.mk d = 1
  rw [show (1 : MHTwo G M) = MHTwo.mk 1 from rfl,
    MHTwo.mk_eq_iff]
  refine ⟨b, ?_⟩
  intro g h
  change g • b h / b (g * h) * b g = d (g, h) / 1
  rw [div_one]
  change g • b h / b (g * h) * b g = phi (c (g, h))
  have hmul := hb g h
  calc
    g • b h / b (g * h) * b g =
        (b g * (g • b h)) / b (g * h) := by
          simp only [div_eq_mul_inv]
          ac_rfl
    _ = phi (c (g, h)) := by
          rw [hmul]
          simp

/-- A semilinear lift of the pullback extension over a subgroup kills the
coefficient-valued restriction of the original central obstruction. -/
theorem mapped_semidirect_pullback
    {Q G H M : Type} [Group Q] [Group G] [Group H] [CommGroup M]
    [MulDistribMulAction H M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (f : H →* G)
    (phi : q.ker →* M)
    (hfixed : ∀ h : H, ∀ z : q.ker, h • phi z = phi z)
    (lift : CentralExtensionPullback q f →*
      M ⋊[MulDistribMulAction.toMulAut H M] H)
    (hlift : SemidirectProduct.rightHom.comp lift =
      extensionPullbackProjection q f)
    (hkernel : ∀ z : q.ker,
      lift
          ⟨(1, z.1), by
            change f 1 = q z.1
            rw [map_one, z.property]⟩ =
        SemidirectProduct.inl (phi z)) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    letI : MulDistribMulAction H q.ker :=
      trivialDistribAction H q.ker
    MHTwo.mapCoefficientsHom phi
        (fun h z ↦ (hfixed h z).symm)
        (MHTwo.restrictionHom f (fun _ _ ↦ rfl)
          (extensionObstructionClass q hq hcentral)) = 1 := by
  let p := extensionPullbackProjection q f
  let hp : Function.Surjective p :=
    central_pullback_projection q hq f
  let hpc : p.ker ≤ Subgroup.center (CentralExtensionPullback q f) :=
    extension_pullback_projection q f hcentral
  let e := centralExtensionPullback q f
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : CommGroup p.ker :=
    centralExtensionComm p hpc
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction H q.ker :=
    trivialDistribAction H q.ker
  letI : MulDistribMulAction H p.ker :=
    trivialDistribAction H p.ker
  have hpzero := mapped_semidirect_lift
    p hp hpc (phi.comp e.toMonoidHom) (fun h z ↦ hfixed h (e z))
      lift hlift (fun z ↦ by
        have hz : e.symm (e z) = z := e.symm_apply_apply z
        rw [← hz]
        exact hkernel (e z))
  rw [← pullback_mapped_obstruction
    q hq hcentral f phi hfixed]
  exact hpzero

/-- Extend a semilinear lift over a normal subgroup across a cyclic quotient.
The output trivializes the mapped central obstruction.  In the local tame
application the normal subgroup is the preimage of inertia, and `Y` is a
semilinear Frobenius lift. -/
theorem mapped_obstruction_lift
    {Q : Type u} {G : Type v} {M : Type w}
    [Group Q] [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (phi : q.ker →* M)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (N : Subgroup Q) [N.Normal]
    (y : Q) (f : ℕ) (hf : 0 < f)
    (horder : orderOf (QuotientGroup.mk' N y) = f)
    (hgen : Subgroup.zpowers (QuotientGroup.mk' N y) = ⊤)
    (fn : N →* M ⋊[MulDistribMulAction.toMulAut G M] G)
    (hfnRight : SemidirectProduct.rightHom.comp fn = q.comp N.subtype)
    (hkerN : q.ker ≤ N)
    (hfnKernel : ∀ z : q.ker,
      fn ⟨z.1, hkerN z.property⟩ = SemidirectProduct.inl (phi z))
    (Y : M ⋊[MulDistribMulAction.toMulAut G M] G)
    (hYRight : SemidirectProduct.rightHom Y = q y)
    (hconj : ∀ (k : ℤ) (n : N),
      fn (MulAut.conjNormal (y ^ k) n) =
        Y ^ k * fn n * (Y ^ k)⁻¹)
    (hpow : Y ^ f = fn ⟨y ^ f, by
      apply (QuotientGroup.eq_one_iff (y ^ f)).mp
      change QuotientGroup.mk' N (y ^ f) = 1
      rw [map_pow, ← horder]
      exact pow_orderOf_eq_one _⟩) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    MHTwo.mapCoefficientsHom phi
        (fun g z ↦ (hfixed g z).symm)
        (extensionObstructionClass q hq hcentral) = 1 := by
  obtain ⟨lift, hliftN, hliftY⟩ :=
    hom_normal_cyclic
      N y f hf horder hgen fn Y hconj hpow
  have hliftRight : SemidirectProduct.rightHom.comp lift = q := by
    apply hom_ext_cyclic N y hgen
    · rw [MonoidHom.comp_assoc, hliftN]
      exact hfnRight
    · change SemidirectProduct.rightHom (lift y) = q y
      rw [hliftY]
      exact hYRight
  apply mapped_semidirect_lift
    q hq hcentral phi hfixed lift hliftRight
  intro z
  change (lift.comp N.subtype) ⟨z.1, hkerN z.property⟩ =
    SemidirectProduct.inl (phi z)
  rw [hliftN]
  exact hfnKernel z

/-- A fixed-root lift over the inertia preimage and one compatible
semilinear Frobenius element solve the full central obstruction.  Conjugation
for all Frobenius powers is derived from the single-generator condition. -/
theorem mapped_obstruction_semilinear
    {Q : Type u} {G : Type v} {M : Type w}
    [Group Q] [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (phi : q.ker →* M)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (I : Subgroup G) [I.Normal]
    (n : ℕ) [NeZero n]
    (eI : Multiplicative (ZMod n) ≃* I)
    (x : Q)
    (hx : q x = I.subtype (eI (CyclicH2.generator (n := n))))
    (eta : M)
    (hetaFixed :
      letI : MulDistribMulAction I M :=
        (inferInstance : MulDistribMulAction G M).compHom M I.subtype
      ∀ i : I, i • eta = eta)
    (hetaPow : eta ^ n = phi ⟨x ^ n, by
      rw [MonoidHom.mem_ker, map_pow, hx]
      change I.subtype (eI (CyclicH2.generator (n := n)) ^ n) = 1
      calc
        I.subtype (eI (CyclicH2.generator (n := n)) ^ n) =
            I.subtype (eI ((CyclicH2.generator (n := n)) ^ n)) := by
              exact congrArg I.subtype
                (map_pow eI (CyclicH2.generator (n := n)) n).symm
        _ = I.subtype (1 : I) := by
              congr 1
              rw [← map_one eI]
              congr 1
              apply Multiplicative.ext
              simp [CyclicH2.generator]
        _ = 1 := map_one I.subtype⟩)
    (y : Q) (f : ℕ) (hf : 0 < f)
    (horder : orderOf
      (QuotientGroup.mk' (I.comap q) y) = f)
    (hgen : Subgroup.zpowers
      (QuotientGroup.mk' (I.comap q) y) = ⊤)
    (hfrobenius :
      ∀ fn : I.comap q →*
          M ⋊[MulDistribMulAction.toMulAut G M] G,
      SemidirectProduct.rightHom.comp fn =
            q.comp (I.comap q).subtype →
        (∀ z : q.ker,
          fn ⟨z.1, by
            change q z.1 ∈ I
            rw [z.property]
            exact I.one_mem⟩ = SemidirectProduct.inl (phi z)) →
        fn ⟨x, by
          change q x ∈ I
          rw [hx]
          exact (eI (CyclicH2.generator (n := n))).property⟩ =
            ⟨eta, q x⟩ →
        ∃ Y : M ⋊[MulDistribMulAction.toMulAut G M] G,
          SemidirectProduct.rightHom Y = q y ∧
          (∀ a : I.comap q,
            fn (MulAut.conjNormal y a) = Y * fn a * Y⁻¹) ∧
          Y ^ f = fn ⟨y ^ f, by
            apply (QuotientGroup.eq_one_iff (y ^ f)).mp
            change QuotientGroup.mk' (I.comap q) (y ^ f) = 1
            rw [map_pow, ← horder]
            exact pow_orderOf_eq_one _⟩) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    MHTwo.mapCoefficientsHom phi
        (fun g z ↦ (hfixed g z).symm)
        (extensionObstructionClass q hq hcentral) = 1 := by
  let P := I.comap q
  obtain ⟨fn, hfnRight, hfnKernel, hfnX⟩ :=
    inertia_preimage_semidirect
      q hq hcentral phi hfixed I n eI x hx eta hetaFixed hetaPow
  obtain ⟨Y, hYRight, hYConj, hYpow⟩ :=
    hfrobenius fn hfnRight hfnKernel hfnX
  have hkerP : q.ker ≤ P := by
    intro z hz
    change q z ∈ I
    rw [hz]
    exact I.one_mem
  apply mapped_obstruction_lift
    q hq hcentral phi hfixed P y f hf horder hgen fn hfnRight
      hkerP hfnKernel Y hYRight
  · exact monoid_normal_zpow P fn y Y hYConj
  · exact hYpow

/-- The cyclic parameter of a central factor set is the order power of the
chosen lift of the cyclic generator. -/
theorem cyclic_parameter_coe
    {Q : Type u} {G : Type v} [Group Q] [Group G]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (n : ℕ) [NeZero n]
    (e : Multiplicative (ZMod n) ≃* G) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    letI : MulDistribMulAction (Multiplicative (ZMod n)) q.ker :=
      trivialDistribAction (Multiplicative (ZMod n)) q.ker
    let c := NMCocycl₂.restrict e.toMonoidHom
      (fun _ _ => rfl)
      ((centralExtensionSet q hq hcentral).normalizedMulCocycle
        (fun _ _ => rfl))
    ((CyclicH2.parameter c : q.ker) : Q) =
      normalizedSurjInv q hq (e (CyclicH2.generator (n := n))) ^ n := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction (Multiplicative (ZMod n)) q.ker :=
    trivialDistribAction (Multiplicative (ZMod n)) q.ker
  let cG := (centralExtensionSet q hq hcentral).normalizedMulCocycle
    (fun _ _ => rfl)
  let c := NMCocycl₂.restrict e.toMonoidHom
    (fun _ _ => rfl) cG
  let gen : Multiplicative (ZMod n) := CyclicH2.generator (n := n)
  let s : G → Q := normalizedSurjInv q hq
  let P : ℕ → q.ker := fun k =>
    ∏ i ∈ Finset.range k, c (gen ^ i, gen)
  have hsection (a b : G) :
      s a * s b = (centralExtensionSet q hq hcentral (a, b) : Q) *
        s (a * b) := by
    change normalizedSurjInv q hq a * normalizedSurjInv q hq b =
      (normalizedSurjInv q hq a * normalizedSurjInv q hq b *
        (normalizedSurjInv q hq (a * b))⁻¹) *
          normalizedSurjInv q hq (a * b)
    group
  have hpow (k : ℕ) :
      s (e gen) ^ k =
        (P k : Q) * s (e (gen ^ k)) := by
    induction k with
    | zero =>
        simp [P, s, normalized_surj_inv]
    | succ k ih =>
        rw [pow_succ, ih]
        calc
          ((P k : Q) * s (e (gen ^ k))) * s (e gen) =
              (P k : Q) * (s (e (gen ^ k)) * s (e gen)) := by group
          _ = (P k : Q) *
              ((centralExtensionSet q hq hcentral
                    (e (gen ^ k), e gen) : q.ker) : Q) *
                  s (e (gen ^ (k + 1))) := by
                rw [hsection]
                simp only [map_mul, pow_succ]
                group
          _ = (P (k + 1) : Q) * s (e (gen ^ (k + 1))) := by
                rw [show P (k + 1) = P k * c (gen ^ k, gen) by
                  simp [P, Finset.prod_range_succ]]
                rfl
  have hgenPow : gen ^ n = 1 := by
    apply Multiplicative.ext
    simp [gen, CyclicH2.generator]
  have hpowN :
      s (e gen) ^ n = (P n : Q) := by
    simpa [hgenPow, s, normalized_surj_inv] using hpow n
  let finEquiv : Fin n ≃ Multiplicative (ZMod n) :=
    { toFun := fun i => Multiplicative.ofAdd (i : ZMod n)
      invFun := fun g => ⟨g.toAdd.val, g.toAdd.val_lt⟩
      left_inv := fun i => by
        apply Fin.ext
        simp [ZMod.val_natCast_of_lt i.isLt]
      right_inv := fun g => by
        simp }
  have hfin (i : Fin n) : finEquiv i = gen ^ (i : ℕ) := by
    apply Multiplicative.ext
    change ((i : ℕ) : ZMod n) = (i : ℕ) • (1 : ZMod n)
    simp
  have hparameter : CyclicH2.parameter c = P n := by
    calc
      CyclicH2.parameter c =
          ∏ g : Multiplicative (ZMod n), c (g, gen) := by
            rfl
      _ = ∏ i : Fin n, c (finEquiv i, gen) :=
        (Fintype.prod_equiv finEquiv _ _ (fun _ => rfl)).symm
      _ = ∏ i : Fin n, c (gen ^ (i : ℕ), gen) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [hfin]
      _ = ∏ i ∈ Finset.range n, c (gen ^ i, gen) :=
        Fin.prod_univ_eq_prod_range
          (fun i : ℕ => c (gen ^ i, gen)) n
      _ = P n := rfl
  change ((CyclicH2.parameter c : q.ker) : Q) = s (e gen) ^ n
  rw [hparameter]
  exact hpowN.symm

/-- For a cyclic quotient, the coefficient-field obstruction vanishes once
the order power of one chosen lift is a norm. -/
theorem cyclic_mapped_lift
    {Q : Type u} {G : Type v} {M : Type w}
    [Group Q] [Group G] [CommGroup M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (e : Multiplicative (ZMod n) ≃* G)
    [MulDistribMulAction (Multiplicative (ZMod n)) M]
    (phi : q.ker →* M)
    (hfixed : ∀ g : Multiplicative (ZMod n), ∀ z : q.ker,
      g • phi z = phi z)
    (x : Q)
    (hx : q x = e (CyclicH2.generator (n := n)))
    (hnorm :
      let xpow : q.ker := ⟨x ^ n, by
        rw [MonoidHom.mem_ker, map_pow, hx]
        calc
          e (CyclicH2.generator (n := n)) ^ n =
              e (CyclicH2.generator (n := n) ^ n) :=
            (map_pow e (CyclicH2.generator (n := n)) n).symm
          _ = e 1 := by
            congr 1
            apply Multiplicative.ext
            simp [CyclicH2.generator]
          _ = 1 := map_one e⟩
      ∃ z : M, phi xpow =
        (CyclicH2.norm (n := n) (M := M) z : M)) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    letI : MulDistribMulAction (Multiplicative (ZMod n)) q.ker :=
      trivialDistribAction (Multiplicative (ZMod n)) q.ker
    let c := NMCocycl₂.restrict e.toMonoidHom
      (fun _ _ => rfl)
      ((centralExtensionSet q hq hcentral).normalizedMulCocycle
        (fun _ _ => rfl))
    MHTwo.mapCoefficientsHom phi
        (fun g z => (hfixed g z).symm) (MHTwo.mk c) = 1 := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction (Multiplicative (ZMod n)) q.ker :=
    trivialDistribAction (Multiplicative (ZMod n)) q.ker
  let cG := (centralExtensionSet q hq hcentral).normalizedMulCocycle
    (fun _ _ => rfl)
  let c := NMCocycl₂.restrict e.toMonoidHom
    (fun _ _ => rfl) cG
  let d := NMCocycl₂.mapCoefficients phi
    (fun g z => (hfixed g z).symm) c
  let gen : Multiplicative (ZMod n) := CyclicH2.generator (n := n)
  have hgenPow : gen ^ n = 1 := by
    apply Multiplicative.ext
    simp [gen, CyclicH2.generator]
  let xpow : q.ker := ⟨x ^ n, by
    rw [MonoidHom.mem_ker, map_pow, hx]
    rw [← map_pow, hgenPow, map_one]⟩
  obtain ⟨z, hz⟩ := hnorm
  have hz' : phi xpow =
      (CyclicH2.norm (n := n) (M := M) z : M) := by
    simpa [xpow] using hz
  let k : q.ker := centralExtensionCoordinate q hq x
  let s : G → Q := normalizedSurjInv q hq
  have hxks : (k : Q) * s (e gen) = x := by
    change (centralExtensionCoordinate q hq x : Q) *
      normalizedSurjInv q hq (e gen) = x
    rw [← hx]
    exact central_extension_section q hq x
  have hcomm : Commute (k : Q) (s (e gen)) := by
    exact (Subgroup.mem_center_iff.mp (hcentral k.property) (s (e gen))).symm
  have hxpowParameter :
      xpow = k ^ n * CyclicH2.parameter c := by
    apply Subtype.ext
    change x ^ n = (k : Q) ^ n *
      ((CyclicH2.parameter c : q.ker) : Q)
    calc
      x ^ n = ((k : Q) * s (e gen)) ^ n := by rw [hxks]
      _ = (k : Q) ^ n * s (e gen) ^ n := hcomm.mul_pow n
      _ = (k : Q) ^ n *
          ((CyclicH2.parameter c : q.ker) : Q) := by
            rw [cyclic_parameter_coe q hq hcentral n e]
  have hmappedParameter :
      CyclicH2.parameter d = phi (CyclicH2.parameter c) := by
    simp [d, CyclicH2.parameter]
  have hnormK :
      (CyclicH2.norm (n := n) (M := M) (phi k) : M) =
        phi k ^ n := by
    rw [CyclicH2.norm_coe]
    simp only [hfixed]
    simp
  have hphiPow :
      phi xpow = phi k ^ n * phi (CyclicH2.parameter c) := by
    rw [hxpowParameter, map_mul, map_pow]
  have hparameterNorm :
      CyclicH2.parameter d =
        (CyclicH2.norm (n := n) (M := M) (z / phi k) : M) := by
    rw [hmappedParameter]
    calc
      phi (CyclicH2.parameter c) = phi xpow / phi k ^ n := by
        rw [hphiPow]
        exact (mul_div_cancel_left (phi k ^ n)
          (phi (CyclicH2.parameter c))).symm
      _ = (CyclicH2.norm (n := n) (M := M) z : M) /
          (CyclicH2.norm (n := n) (M := M) (phi k) : M) := by
        rw [hz', hnormK]
      _ = (CyclicH2.norm (n := n) (M := M) (z / phi k) : M) := by
        exact congrArg Subtype.val
          (map_div (CyclicH2.norm (n := n) (M := M)) z (phi k)).symm
  have hdCoboundary : groupCohomology.IsMulCoboundary₂ d :=
    CyclicH2.isMulCoboundary₂_of_parameter_eq_norm hn d
      (z / phi k) hparameterNorm
  change MHTwo.mk d = 1
  rw [show (1 : MHTwo (Multiplicative (ZMod n)) M) =
    MHTwo.mk 1 from rfl, MHTwo.mk_eq_iff]
  simpa [MHTwo.IsCohomologous] using hdCoboundary

/-- The cyclic trivialization above can be chosen inside a stable coefficient
subgroup.  In the local application this subgroup is the valuation-unit
subgroup, so the later descent to the unramified quotient remains
unit-valued. -/
theorem cyclic_mapped_cochain
    {Q : Type u} {G : Type v} {M : Type w}
    [Group Q] [Group G] [CommGroup M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (e : Multiplicative (ZMod n) ≃* G)
    [MulDistribMulAction (Multiplicative (ZMod n)) M]
    (phi : q.ker →* M)
    (hfixed : ∀ g : Multiplicative (ZMod n), ∀ z : q.ker,
      g • phi z = phi z)
    (U : Subgroup M)
    (hstable : ∀ g : Multiplicative (ZMod n), ∀ m : M,
      m ∈ U → g • m ∈ U)
    (hphiU : ∀ z : q.ker, phi z ∈ U)
    (x : Q)
    (hx : q x = e (CyclicH2.generator (n := n)))
    (z : M) (hzU : z ∈ U)
    (hnorm :
      let xpow : q.ker := ⟨x ^ n, by
        rw [MonoidHom.mem_ker, map_pow, hx]
        calc
          e (CyclicH2.generator (n := n)) ^ n =
              e (CyclicH2.generator (n := n) ^ n) :=
            (map_pow e (CyclicH2.generator (n := n)) n).symm
          _ = e 1 := by
            congr 1
            apply Multiplicative.ext
            simp [CyclicH2.generator]
          _ = 1 := map_one e⟩
      phi xpow = (CyclicH2.norm (n := n) (M := M) z : M)) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    letI : MulDistribMulAction (Multiplicative (ZMod n)) q.ker :=
      trivialDistribAction (Multiplicative (ZMod n)) q.ker
    let c := NMCocycl₂.restrict e.toMonoidHom
      (fun _ _ ↦ rfl)
      ((centralExtensionSet q hq hcentral).normalizedMulCocycle
        (fun _ _ ↦ rfl))
    let d := NMCocycl₂.mapCoefficients phi
      (fun g a ↦ (hfixed g a).symm) c
    ∃ b : Multiplicative (ZMod n) → M,
      (∀ g, b g ∈ U) ∧
        ∀ g h, g • b h / b (g * h) * b g = d (g, h) := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction (Multiplicative (ZMod n)) q.ker :=
    trivialDistribAction (Multiplicative (ZMod n)) q.ker
  let cG := (centralExtensionSet q hq hcentral).normalizedMulCocycle
    (fun _ _ ↦ rfl)
  let c := NMCocycl₂.restrict e.toMonoidHom
    (fun _ _ ↦ rfl) cG
  let d := NMCocycl₂.mapCoefficients phi
    (fun g a ↦ (hfixed g a).symm) c
  let gen : Multiplicative (ZMod n) := CyclicH2.generator (n := n)
  have hgenPow : gen ^ n = 1 := by
    apply Multiplicative.ext
    simp [gen, CyclicH2.generator]
  let xpow : q.ker := ⟨x ^ n, by
    rw [MonoidHom.mem_ker, map_pow, hx]
    rw [← map_pow, hgenPow, map_one]⟩
  have hz' : phi xpow =
      (CyclicH2.norm (n := n) (M := M) z : M) := by
    simpa [xpow] using hnorm
  let k : q.ker := centralExtensionCoordinate q hq x
  let s : G → Q := normalizedSurjInv q hq
  have hxks : (k : Q) * s (e gen) = x := by
    change (centralExtensionCoordinate q hq x : Q) *
      normalizedSurjInv q hq (e gen) = x
    rw [← hx]
    exact central_extension_section q hq x
  have hcomm : Commute (k : Q) (s (e gen)) := by
    exact (Subgroup.mem_center_iff.mp (hcentral k.property) (s (e gen))).symm
  have hxpowParameter :
      xpow = k ^ n * CyclicH2.parameter c := by
    apply Subtype.ext
    change x ^ n = (k : Q) ^ n *
      ((CyclicH2.parameter c : q.ker) : Q)
    calc
      x ^ n = ((k : Q) * s (e gen)) ^ n := by rw [hxks]
      _ = (k : Q) ^ n * s (e gen) ^ n := hcomm.mul_pow n
      _ = (k : Q) ^ n *
          ((CyclicH2.parameter c : q.ker) : Q) := by
            rw [cyclic_parameter_coe q hq hcentral n e]
  have hmappedParameter :
      CyclicH2.parameter d = phi (CyclicH2.parameter c) := by
    simp [d, CyclicH2.parameter]
  have hnormK :
      (CyclicH2.norm (n := n) (M := M) (phi k) : M) =
        phi k ^ n := by
    rw [CyclicH2.norm_coe]
    simp only [hfixed]
    simp
  have hphiPow :
      phi xpow = phi k ^ n * phi (CyclicH2.parameter c) := by
    rw [hxpowParameter, map_mul, map_pow]
  have hparameterNorm :
      CyclicH2.parameter d =
        (CyclicH2.norm (n := n) (M := M) (z / phi k) : M) := by
    rw [hmappedParameter]
    calc
      phi (CyclicH2.parameter c) = phi xpow / phi k ^ n := by
        rw [hphiPow]
        exact (mul_div_cancel_left (phi k ^ n)
          (phi (CyclicH2.parameter c))).symm
      _ = (CyclicH2.norm (n := n) (M := M) z : M) /
          (CyclicH2.norm (n := n) (M := M) (phi k) : M) := by
        rw [hz', hnormK]
      _ = (CyclicH2.norm (n := n) (M := M) (z / phi k) : M) := by
        exact congrArg Subtype.val
          (map_div (CyclicH2.norm (n := n) (M := M)) z (phi k)).symm
  apply CyclicH2.mul_coboundary₂_cochain_mem_subgroup
    hn U hstable d
  · intro g h
    exact hphiU (c (g, h))
  · exact U.div_mem hzU (hphiU k)
  · exact hparameterNorm

/-- A fixed `n`th root of the lift power supplies the norm required by the
cyclic obstruction criterion. -/
theorem mapped_fixed_root
    {Q : Type u} {G : Type v} {M : Type w}
    [Group Q] [Group G] [CommGroup M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (e : Multiplicative (ZMod n) ≃* G)
    [MulDistribMulAction (Multiplicative (ZMod n)) M]
    (phi : q.ker →* M)
    (hfixed : ∀ g : Multiplicative (ZMod n), ∀ z : q.ker,
      g • phi z = phi z)
    (x : Q)
    (hx : q x = e (CyclicH2.generator (n := n)))
    (eta : M)
    (hetaFixed : ∀ g : Multiplicative (ZMod n), g • eta = eta)
    (hetaPow :
      let xpow : q.ker := ⟨x ^ n, by
        rw [MonoidHom.mem_ker, map_pow, hx]
        calc
          e (CyclicH2.generator (n := n)) ^ n =
              e (CyclicH2.generator (n := n) ^ n) :=
            (map_pow e (CyclicH2.generator (n := n)) n).symm
          _ = e 1 := by
            congr 1
            apply Multiplicative.ext
            simp [CyclicH2.generator]
          _ = 1 := map_one e⟩
      eta ^ n = phi xpow) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    letI : MulDistribMulAction (Multiplicative (ZMod n)) q.ker :=
      trivialDistribAction (Multiplicative (ZMod n)) q.ker
    let c := NMCocycl₂.restrict e.toMonoidHom
      (fun _ _ => rfl)
      ((centralExtensionSet q hq hcentral).normalizedMulCocycle
        (fun _ _ => rfl))
    MHTwo.mapCoefficientsHom phi
        (fun g z => (hfixed g z).symm) (MHTwo.mk c) = 1 := by
  apply cyclic_mapped_lift
    q hq hcentral n hn e phi hfixed x hx
  refine ⟨eta, ?_⟩
  rw [← hetaPow, CyclicH2.norm_coe]
  simp only [hetaFixed]
  simp

/-- The coefficient-valued central obstruction restricts trivially to a
cyclic subgroup when a chosen lift of its generator has a fixed root of its
order power.  The proof applies the cyclic criterion to the pullback central
extension over that subgroup. -/
theorem mapped_restriction_root
    {Q : Type u} {G : Type v} {M : Type w}
    [Group Q] [Group G] [CommGroup M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (f : Multiplicative (ZMod n) →* G)
    [MulDistribMulAction (Multiplicative (ZMod n)) M]
    (phi : q.ker →* M)
    (hfixed : ∀ g : Multiplicative (ZMod n), ∀ z : q.ker,
      g • phi z = phi z)
    (x : Q)
    (hx : q x = f (CyclicH2.generator (n := n)))
    (eta : M)
    (hetaFixed : ∀ g : Multiplicative (ZMod n), g • eta = eta)
    (hetaPow :
      let xpow : q.ker := ⟨x ^ n, by
        rw [MonoidHom.mem_ker, map_pow, hx]
        calc
          f (CyclicH2.generator (n := n)) ^ n =
              f (CyclicH2.generator (n := n) ^ n) :=
            (map_pow f (CyclicH2.generator (n := n)) n).symm
          _ = f 1 := by
            congr 1
            apply Multiplicative.ext
            simp [CyclicH2.generator]
          _ = 1 := map_one f⟩
      eta ^ n = phi xpow) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    letI : MulDistribMulAction (Multiplicative (ZMod n)) q.ker :=
      trivialDistribAction (Multiplicative (ZMod n)) q.ker
    MHTwo.mapCoefficientsHom phi
        (fun g z ↦ (hfixed g z).symm)
        (MHTwo.restrictionHom f (fun _ _ ↦ rfl)
          (extensionObstructionClass q hq hcentral)) = 1 := by
  let C := Multiplicative (ZMod n)
  let p := extensionPullbackProjection q f
  let hp : Function.Surjective p :=
    central_pullback_projection q hq f
  let hpc : p.ker ≤ Subgroup.center (CentralExtensionPullback q f) :=
    extension_pullback_projection q f hcentral
  let e := centralExtensionPullback q f
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : CommGroup p.ker :=
    centralExtensionComm p hpc
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction C q.ker :=
    trivialDistribAction C q.ker
  letI : MulDistribMulAction C p.ker :=
    trivialDistribAction C p.ker
  let gen : C := CyclicH2.generator (n := n)
  let xp : CentralExtensionPullback q f := ⟨(gen, x), hx.symm⟩
  have hxp : p xp = (MulEquiv.refl C) gen := rfl
  have hetaPow' :
      let xpow : p.ker := ⟨xp ^ n, by
        rw [MonoidHom.mem_ker, map_pow, hxp]
        apply Multiplicative.ext
        simp [gen, CyclicH2.generator]⟩
      eta ^ n = (phi.comp e.toMonoidHom) xpow := by
    simpa [xp, e] using hetaPow
  have hpzero :=
    mapped_fixed_root
      (Q := CentralExtensionPullback q f) (G := C) (M := M)
      (q := p) (hq := hp) (hcentral := hpc)
      (n := n) hn (e := MulEquiv.refl C)
      (phi := phi.comp e.toMonoidHom)
      (hfixed := fun g z ↦ hfixed g (e z))
      (x := xp) (hx := hxp) (eta := eta)
      (hetaFixed := hetaFixed) (hetaPow := hetaPow')
  rw [← pullback_mapped_obstruction
    q hq hcentral f phi hfixed]
  simpa [extensionObstructionClass] using hpzero

/-- A primitive root whose order is the order of a chosen lift contains an
`n`th root of the image of that lift's `n`th power.  This is the elementary
root-of-unity calculation used for tame inertia. -/
theorem fixed_lift_pow
    {Q : Type u} {G : Type v} {F : Type w}
    [Group Q] [Finite Q] [Group G] [Finite G] [Field F]
    {H : Type*} [Group H] [MulDistribMulAction H Fˣ]
    (q : Q →* G) (n : ℕ) (x : Q)
    (horder : orderOf (q x) = n)
    (phi : q.ker →* Fˣ) (hphi : Function.Injective phi)
    (zeta : Fˣ) (hzeta : IsPrimitiveRoot zeta (orderOf x))
    (hzetaFixed : ∀ h : H, h • zeta = zeta) :
    let xpow : q.ker := ⟨x ^ n, by
      rw [MonoidHom.mem_ker, map_pow, ← horder, pow_orderOf_eq_one]⟩
    ∃ eta : Fˣ, (∀ h : H, h • eta = eta) ∧ eta ^ n = phi xpow := by
  let xpow : q.ker := ⟨x ^ n, by
    rw [MonoidHom.mem_ker, map_pow, ← horder, pow_orderOf_eq_one]⟩
  have hnDvd : n ∣ orderOf x := by
    rw [← horder]
    exact orderOf_map_dvd q x
  have hnPos : 0 < n := by
    rw [← horder]
    exact (isOfFinOrder_of_finite (q x)).orderOf_pos
  have hn0 : n ≠ 0 := hnPos.ne'
  let d := orderOf x / n
  have hxOrderPos : 0 < orderOf x :=
    (isOfFinOrder_of_finite x).orderOf_pos
  have hnLe : n ≤ orderOf x := Nat.le_of_dvd hxOrderPos hnDvd
  have hdPos : 0 < d := Nat.div_pos hnLe hnPos
  letI : NeZero d := ⟨hdPos.ne'⟩
  have hzetaPow : IsPrimitiveRoot (zeta ^ n) d := by
    exact hzeta.pow_of_dvd hn0 hnDvd
  have hxpowOrder : orderOf xpow = d := by
    change orderOf (⟨x ^ n, _⟩ : q.ker) = d
    rw [Subgroup.orderOf_mk, orderOf_pow_of_dvd hn0 hnDvd]
  have htargetOrder : orderOf (phi xpow) = d := by
    rw [orderOf_injective phi hphi xpow, hxpowOrder]
  have htargetPow : (phi xpow) ^ d = 1 := by
    rw [← htargetOrder]
    exact pow_orderOf_eq_one (phi xpow)
  have htargetMem : phi xpow ∈ rootsOfUnity d F :=
    (mem_rootsOfUnity' d (phi xpow)).2 (congrArg Units.val htargetPow)
  obtain ⟨a, _ha, ha⟩ :=
    hzetaPow.eq_pow_of_mem_rootsOfUnity htargetMem
  refine ⟨zeta ^ a, ?_, ?_⟩
  · intro h
    rw [smul_pow', hzetaFixed]
  · change (zeta ^ a) ^ n = phi xpow
    calc
      (zeta ^ a) ^ n = zeta ^ (a * n) := (pow_mul zeta a n).symm
      _ = zeta ^ (n * a) := by rw [Nat.mul_comm]
      _ = (zeta ^ n) ^ a := pow_mul zeta n a
      _ = phi xpow := ha

/-- Primitive roots in the inertia-fixed coefficient field kill the
restriction of a finite central obstruction to the cyclic inertia group. -/
theorem mapped_primitive_root
    {Q : Type u} {G : Type v} {F : Type w}
    [Group Q] [Finite Q] [Group G] [Finite G] [Field F]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (f : Multiplicative (ZMod n) →* G)
    [MulDistribMulAction (Multiplicative (ZMod n)) Fˣ]
    (phi : q.ker →* Fˣ) (hphi : Function.Injective phi)
    (hfixed : ∀ g : Multiplicative (ZMod n), ∀ z : q.ker,
      g • phi z = phi z)
    (x : Q)
    (hx : q x = f (CyclicH2.generator (n := n)))
    (horder : orderOf (q x) = n)
    (zeta : Fˣ) (hzeta : IsPrimitiveRoot zeta (orderOf x))
    (hzetaFixed : ∀ g : Multiplicative (ZMod n), g • zeta = zeta) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    letI : MulDistribMulAction (Multiplicative (ZMod n)) q.ker :=
      trivialDistribAction (Multiplicative (ZMod n)) q.ker
    MHTwo.mapCoefficientsHom phi
        (fun g z ↦ (hfixed g z).symm)
        (MHTwo.restrictionHom f (fun _ _ ↦ rfl)
          (extensionObstructionClass q hq hcentral)) = 1 := by
  obtain ⟨eta, hetaFixed, hetaPow⟩ :=
    fixed_lift_pow q n x horder phi hphi
      zeta hzeta hzetaFixed
  apply mapped_restriction_root
    q hq hcentral n hn f phi hfixed x hx eta hetaFixed
  simpa using hetaPow

/-- A primitive root fixed by a cyclic inertia subgroup kills the mapped
central obstruction on the inertia subgroup itself. -/
theorem mapped_restriction_primitive
    {Q G F : Type} [Group Q] [Finite Q] [Group G] [Finite G] [Field F]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (I : Subgroup G)
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (eI : Multiplicative (ZMod n) ≃* I)
    [MulDistribMulAction G Fˣ]
    (phi : q.ker →* Fˣ) (hphi : Function.Injective phi)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (x : Q)
    (hx : q x = I.subtype (eI (CyclicH2.generator (n := n))))
    (horder : orderOf (q x) = n)
    (zeta : Fˣ) (hzeta : IsPrimitiveRoot zeta (orderOf x))
    (hzetaFixed :
      letI : MulDistribMulAction I Fˣ :=
        (inferInstance : MulDistribMulAction G Fˣ).compHom Fˣ I.subtype
      ∀ i : I, i • zeta = zeta) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    letI : MulDistribMulAction I Fˣ :=
      (inferInstance : MulDistribMulAction G Fˣ).compHom Fˣ I.subtype
    MHTwo.restrictionHom I.subtype (fun _ _ ↦ rfl)
      (MHTwo.mapCoefficientsHom phi
        (fun g z ↦ (hfixed g z).symm)
        (extensionObstructionClass q hq hcentral)) = 1 := by
  let C := Multiplicative (ZMod n)
  let f : C →* G := I.subtype.comp eI.toMonoidHom
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction I q.ker :=
    trivialDistribAction I q.ker
  letI : MulDistribMulAction C q.ker :=
    trivialDistribAction C q.ker
  letI : MulDistribMulAction I Fˣ :=
    (inferInstance : MulDistribMulAction G Fˣ).compHom Fˣ I.subtype
  letI : MulDistribMulAction C Fˣ :=
    (inferInstance : MulDistribMulAction I Fˣ).compHom Fˣ eI.toMonoidHom
  let obstruction := extensionObstructionClass q hq hcentral
  let mapped := MHTwo.mapCoefficientsHom phi
    (fun g z ↦ (hfixed g z).symm) obstruction
  have hxC :
      MHTwo.mapCoefficientsHom phi
          (fun c z ↦ (hfixed (f c) z).symm)
          (MHTwo.restrictionHom f (fun _ _ ↦ rfl)
            obstruction) = 1 := by
    exact mapped_primitive_root
      q hq hcentral n hn f phi hphi
      (fun c z ↦ hfixed (f c) z) x hx horder zeta hzeta
      (fun c ↦ hzetaFixed (eI c))
  have hxMappedC :
      MHTwo.restrictionHom f (fun _ _ ↦ rfl) mapped = 1 := by
    rw [MHTwo.restriction_hom_coefficients
      (r := f) (hM := fun _ _ ↦ rfl) (hN := fun _ _ ↦ rfl)
      (f := phi) (fG := fun g z ↦ (hfixed g z).symm)
      (fH := fun c z ↦ (hfixed (f c) z).symm)]
    exact hxC
  exact MHTwo.subgrourestric_eqone_mulequiv
    I eI mapped hxMappedC

/-- The full local tame reduction: primitive-root control kills inertia,
Hilbert 90 permits inflation from the unramified quotient, and vanishing on
that quotient kills the mapped central obstruction. -/
theorem mapped_inflation_restriction
    {Q G F : Type} [Group Q] [Finite Q] [Group G] [Finite G] [Field F]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (I : Subgroup G) [I.Normal]
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (eI : Multiplicative (ZMod n) ≃* I)
    [MulSemiringAction G F] [FaithfulSMul G F]
    (phi : q.ker →* Fˣ) (hphi : Function.Injective phi)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (x : Q)
    (hx : q x = I.subtype (eI (CyclicH2.generator (n := n))))
    (horder : orderOf (q x) = n)
    (zeta : Fˣ) (hzeta : IsPrimitiveRoot zeta (orderOf x))
    (hzetaFixed :
      letI : MulDistribMulAction I Fˣ :=
        (inferInstance : MulDistribMulAction G Fˣ).compHom Fˣ I.subtype
      ∀ i : I, i • zeta = zeta)
    (hquot : ∀ z : groupCohomology
      ((Rep.ofMulDistribMulAction G Fˣ).quotientToInvariants I) 2,
        z = 0) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    MHTwo.mapCoefficientsHom phi
        (fun g z ↦ (hfixed g z).symm)
        (extensionObstructionClass q hq hcentral) = 1 := by
  let iAction : MulSemiringAction I F :=
    MulSemiringAction.compHom (R := F) I.subtype
  letI : MulSemiringAction I F := iAction
  let iFaithful : @FaithfulSMul I F iAction.toSMul :=
    { eq_of_smul_eq_smul := fun {a b} hab ↦ by
        apply Subtype.ext
        exact FaithfulSMul.eq_of_smul_eq_smul
          (M := G) (α := F) hab }
  letI : @FaithfulSMul I F iAction.toSMul := iFaithful
  have hH1 : IsZero (groupCohomology
      (Rep.res I.subtype (Rep.ofMulDistribMulAction G Fˣ)) 1) := by
    change IsZero (groupCohomology.H1
      (Rep.ofMulDistribMulAction I Fˣ))
    exact h_faithful_action (G := I) (F := F)
  apply mapped_obstruction_restriction
    q hq hcentral phi hfixed I hH1 hquot
  exact mapped_restriction_primitive
    q hq hcentral I n hn eI phi hphi hfixed x hx horder
      zeta hzeta hzetaFixed

/-- The subgroup generated by two lifts maps onto a quotient generated by
their images. -/
theorem pair_restriction_surjective
    {Q G : Type u} [Group Q] [Group G]
    (q : Q →* G) (x y : Q)
    (hgen : Subgroup.closure ({q x, q y} : Set G) = ⊤) :
    Function.Surjective
      (q.comp (Subgroup.closure ({x, y} : Set Q)).subtype) := by
  let H : Subgroup Q := Subgroup.closure ({x, y} : Set Q)
  have hmap : H.map q = ⊤ := by
    calc
      H.map q = Subgroup.closure (q '' ({x, y} : Set Q)) := by
        exact MonoidHom.map_closure q ({x, y} : Set Q)
      _ = Subgroup.closure ({q x, q y} : Set G) := by
        congr 1
        ext z
        simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
        aesop
      _ = ⊤ := hgen
  intro g
  have hg : g ∈ H.map q := by rw [hmap]; exact Subgroup.mem_top g
  obtain ⟨z, hzH, rfl⟩ := hg
  exact ⟨⟨z, hzH⟩, rfl⟩

/-- If the subgroup generated by two lifts meets the kernel trivially, its
surjection to the quotient supplies a splitting of the original map. -/
theorem splitting_comap_bot
    {Q G : Type u} [Group Q] [Group G]
    (q : Q →* G) (x y : Q)
    (hgen : Subgroup.closure ({q x, q y} : Set G) = ⊤)
    (hker : (Subgroup.closure ({x, y} : Set Q)).comap q.ker.subtype = ⊥) :
    ∃ s : G →* Q, q.comp s = MonoidHom.id G := by
  let H : Subgroup Q := Subgroup.closure ({x, y} : Set Q)
  let r : H →* G := q.comp H.subtype
  have hrSurj : Function.Surjective r :=
    pair_restriction_surjective q x y hgen
  have hrInj : Function.Injective r := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext z
    constructor
    · intro hz
      have hzker : (z : Q) ∈ q.ker := by
        exact hz
      have hzcomap : (⟨z, hzker⟩ : q.ker) ∈ H.comap q.ker.subtype := z.property
      rw [hker] at hzcomap
      have hkone : (⟨z, hzker⟩ : q.ker) = 1 := by
        simpa using hzcomap
      exact Subtype.ext
        (congrArg (fun k : q.ker => (k : Q)) hkone)
    · intro hz
      have hz' : z = 1 := Subgroup.mem_bot.mp hz
      rw [hz']
      exact map_one r
  let e : H ≃* G := MulEquiv.ofBijective r ⟨hrInj, hrSurj⟩
  let s : G →* Q := H.subtype.comp e.symm.toMonoidHom
  refine ⟨s, ?_⟩
  ext g
  change r (e.symm g) = g
  exact e.apply_symm_apply g

/-- If the subgroup generated by lifts contains the entire kernel and maps
onto the quotient, then it is the whole extension group. -/
theorem pair_closure_top
    {Q G : Type u} [Group Q] [Group G]
    (q : Q →* G) (x y : Q)
    (hgen : Subgroup.closure ({q x, q y} : Set G) = ⊤)
    (hker : q.ker ≤ Subgroup.closure ({x, y} : Set Q)) :
    Subgroup.closure ({x, y} : Set Q) = ⊤ := by
  let H : Subgroup Q := Subgroup.closure ({x, y} : Set Q)
  have hrSurj : Function.Surjective (q.comp H.subtype) :=
    pair_restriction_surjective q x y hgen
  apply top_unique
  intro z _
  obtain ⟨h, hh⟩ := hrSurj (q z)
  change q (h : Q) = q z at hh
  have hdiff : z * (h : Q)⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hh]
    exact mul_inv_cancel _
  have hdiffH : z * (h : Q)⁻¹ ∈ H := hker hdiff
  have hhH : (h : Q) ∈ H := h.property
  have hprod : (z * (h : Q)⁻¹) * (h : Q) ∈ H := H.mul_mem hdiffH hhH
  simpa [mul_assoc] using hprod

/-- Prime-kernel dichotomy for a pair of prescribed lifts: either they give
a splitting already, or they generate the entire extension group. -/
theorem splitting_or_top
    {Q G : Type u} [Group Q] [Group G]
    (q : Q →* G) (x y : Q)
    (hgen : Subgroup.closure ({q x, q y} : Set G) = ⊤)
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card q.ker = p) :
    (∃ s : G →* Q, q.comp s = MonoidHom.id G) ∨
      Subgroup.closure ({x, y} : Set Q) = ⊤ := by
  let H : Subgroup Q := Subgroup.closure ({x, y} : Set Q)
  let J : Subgroup q.ker := H.comap q.ker.subtype
  letI : Fact (Nat.card q.ker).Prime := ⟨hcard ▸ hp⟩
  rcases J.eq_bot_or_eq_top_of_prime_card with hJ | hJ
  · exact Or.inl
      (splitting_comap_bot q x y hgen hJ)
  · right
    apply pair_closure_top q x y hgen
    intro z hz
    let zk : q.ker := ⟨z, hz⟩
    have hzJ : zk ∈ J := by rw [hJ]; exact Subgroup.mem_top zk
    exact hzJ

end TBluepr
end Towers
