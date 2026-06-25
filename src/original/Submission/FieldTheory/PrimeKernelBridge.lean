import Submission.FieldTheory.CentralEmbeddingDecomposition
import Submission.FieldTheory.CentralEmbeddingObstruction
import Submission.FieldTheory.CentralEmbeddingRealization
import Submission.FieldTheory.CentralEmbeddingRelative
import Submission.NumberTheory.Locals.RamificationGroups
import Submission.NumberTheory.Locals.LocalUnramifiedDecomposition
import Submission.ClassField.LocalBrauer.SpectralNormData

/-!
# Prime-kernel reduction for tame local central obstructions

This file isolates the group-theoretic part of the local argument used in the
rational tame `3` embedding problem.  A chosen inertia generator and arithmetic
Frobenius generate the decomposition group.  For a central extension with
prime-order kernel, prescribed lifts of those two elements therefore either
split the local extension already or generate its whole pullback.
-/

namespace Submission
namespace TBluepr

universe uQ uG uM uT uF

open Submission.NumberTheory.Milne
open Submission.CField.CProduca
open Submission.CField.LBrauer
open IsLocalRing ValuativeRel
open scoped Pointwise commutatorElement

noncomputable section

attribute [local instance] rationalIntegerGaloisAction

set_option maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the large search space in this proof.
/-- The ambient generation theorem for inertia and Frobenius, expressed
inside the decomposition group itself. -/
theorem frob_generate_subtype
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]
    [FiniteDimensional ℚ L] [IsGalois ℚ L]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime]
    [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (tau : P.inertia Gal(L/ℚ))
    (htau : Subgroup.closure ({tau} : Set (P.inertia Gal(L/ℚ))) = ⊤)
    (sigma : Gal(L/ℚ))
    (hsigma : IsArithFrobAt ℤ sigma P) :
    let D := MulAction.stabilizer Gal(L/ℚ) P
    let tauD : D :=
      ⟨tau, Ideal.inertia_le_stabilizer P tau.property⟩
    let sigmaD : D :=
      ⟨sigma,
        arith_frob_decomposition P sigma hsigma⟩
    Subgroup.closure ({tauD, sigmaD} : Set D) = ⊤ := by
  let D := MulAction.stabilizer Gal(L/ℚ) P
  let tauD : D :=
    ⟨tau, Ideal.inertia_le_stabilizer P tau.property⟩
  let sigmaD : D :=
    ⟨sigma,
      arith_frob_decomposition P sigma hsigma⟩
  let H : Subgroup D := Subgroup.closure ({tauD, sigmaD} : Set D)
  have hambient :
      Subgroup.closure ({(tau : Gal(L/ℚ)), sigma} : Set Gal(L/ℚ)) = D :=
    arith_frob_generate
      hq P tau htau sigma hsigma
  have himage : D.subtype '' ({tauD, sigmaD} : Set D) =
      ({(tau : Gal(L/ℚ)), sigma} : Set Gal(L/ℚ)) := by
    ext z
    simp [tauD, sigmaD, eq_comm]
  have hmap : H.map D.subtype = D := by
    calc
      H.map D.subtype =
          Subgroup.closure (D.subtype '' ({tauD, sigmaD} : Set D)) := by
            exact MonoidHom.map_closure D.subtype ({tauD, sigmaD} : Set D)
      _ = Subgroup.closure
          ({(tau : Gal(L/ℚ)), sigma} : Set Gal(L/ℚ)) := by
            rw [himage]
      _ = D := hambient
  apply top_unique
  intro z _
  have hz : (z : Gal(L/ℚ)) ∈ H.map D.subtype := by
    rw [hmap]
    exact z.property
  obtain ⟨w, hwH, hw⟩ := hz
  have hwz : w = z := by
    apply Subtype.ext
    exact hw
  simpa [hwz] using hwH

set_option maxHeartbeats 1000000 in
-- Extra heartbeats are needed for the large search space in this proof.
/-- For a prime-kernel central extension, a tame pair whose images generate
the quotient either already gives a vanishing mapped obstruction, or the pair
generates the entire extension.  In the second branch the supplied tame
relation is retained for the subsequent local realization argument. -/
theorem mapped_obstruction_generates
    {Q G : Type u} {M : Type v} [Group Q] [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (phi : q.ker →* M)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (x y : Q)
    (hgen : Subgroup.closure ({q x, q y} : Set G) = ⊤)
    (residueCard : ℕ)
    (htame : x ^ (residueCard - 1) * ⁅x, y⁆ = 1)
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card q.ker = p) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    MHTwo.mapCoefficientsHom phi
        (fun g z ↦ (hfixed g z).symm)
        (extensionObstructionClass q hq hcentral) = 1 ∨
      (Subgroup.closure ({x, y} : Set Q) = ⊤ ∧
        x ^ (residueCard - 1) * ⁅x, y⁆ = 1) := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  rcases splitting_or_top
      q x y hgen p hp hcard with hsplit | htop
  · left
    obtain ⟨s, hs⟩ := hsplit
    have htrivial :=
      set_trivial_splitting
        q hq hcentral s hs
    have hobstruction :
        extensionObstructionClass q hq hcentral = 1 :=
      (set_trivial_obstruction
        q hq hcentral).1 htrivial
    rw [hobstruction, map_one]
  · exact Or.inr ⟨htop, htame⟩

/-- A presentation-level form of the prime-kernel dichotomy.  If the mapped
local obstruction is not already trivial, the prescribed tame inertia and
Frobenius lifts make the abstract tame presentation surject onto the entire
pullback extension. -/
theorem mapped_presentation_surjective
    {Q G : Type u} {M : Type v} [Group Q] [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (phi : q.ker →* M)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (x y : Q)
    (hgen : Subgroup.closure ({q x, q y} : Set G) = ⊤)
    (residueCard : ℕ)
    (htame : x ^ (residueCard - 1) * ⁅x, y⁆ = 1)
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card q.ker = p) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    MHTwo.mapCoefficientsHom phi
          (fun g z ↦ (hfixed g z).symm)
          (extensionObstructionClass q hq hcentral) = 1 ∨
      Function.Surjective
        (tamePresentationLift residueCard x y htame) := by
  rcases mapped_obstruction_generates
      q hq hcentral phi hfixed x y hgen residueCard htame p hp hcard with
    hzero | ⟨hpair, _⟩
  · exact Or.inl hzero
  · right
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    intro z _
    have hle : Subgroup.closure ({x, y} : Set Q) ≤
        (tamePresentationLift residueCard x y htame).range := by
      rw [Subgroup.closure_le]
      intro a ha
      rcases ha with (rfl | rfl)
      · exact ⟨(tameLocalPresentation residueCard).of
          (tameLocalInertia residueCard), by simp⟩
      · exact ⟨(tameLocalPresentation residueCard).of
          (tameFrobeniusGenerator residueCard), by simp⟩
    rw [hpair] at hle
    exact hle (Subgroup.mem_top z)

set_option maxHeartbeats 3000000 in
-- Extra heartbeats are needed for the large search space in this proof.
set_option synthInstance.maxHeartbeats 1000000 in
/-- In the nonsplit branch of the prime-kernel dichotomy, the killed tame
relation is not merely formal: the whole pullback group occurs as the Galois
group of a finite extension of the given local field.  This is the local
realization needed to turn a Koch relator into a weak solution of the
completed embedding problem. -/
theorem mapped_obstruction_realization
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [CharZero K]
    {Q G : Type u} {M : Type v}
    [Group Q] [Finite Q] [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (hQ : IsPGroup 3 Q)
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (phi : q.ker →* M)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (x y : Q)
    (hgen : Subgroup.closure ({q x, q y} : Set G) = ⊤)
    (htame : x ^ (localResidueCard K - 1) * ⁅x, y⁆ = 1)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (hcard : Nat.card q.ker = 3) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    MHTwo.mapCoefficientsHom phi
          (fun g z ↦ (hfixed g z).symm)
          (extensionObstructionClass q hq hcentral) = 1 ∨
      ∃ (N : Type u) (_ : Field N) (_ : Algebra K N)
          (_ : FiniteDimensional K N) (_ : IsGalois K N),
        Nonempty (Q ≃* Gal(N/K)) := by
  rcases mapped_obstruction_generates
      q hq hcentral phi hfixed x y hgen (localResidueCard K) htame
        3 Nat.prime_three hcard with hzero | ⟨hpair, _⟩
  · exact Or.inl hzero
  · right
    have hconj : y * x * y⁻¹ = x ^ localResidueCard K :=
      (tame_relation_conjugation x y
        (one_local_card K).le).1 htame
    obtain ⟨zeta, hzeta, b, hb, a, ha, hirr, hGal, action, hbij⟩ :=
      tame_pair_realization
        K hQ x y hcoprime hconj
    let H : Subgroup Q := Subgroup.closure ({x, y} : Set Q)
    have hxH : x ∈ H :=
      Subgroup.subset_closure (Set.mem_insert x {y})
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    letI : I.Normal := tame_inertia_closure
      x y (localResidueCard K) hcoprime hconj
    let f := Nat.card (H ⧸ I)
    let e := orderOf x
    letI : NeZero f := ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
    letI : NeZero e := ⟨(orderOf_pos x).ne'⟩
    let eI : Multiplicative (ZMod e) ≃* I :=
      (tameZMod x).trans
        (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxH)).symm
    letI : CommGroup I :=
      eI.symm.toMonoidHom.commGroupOfInjective eI.symm.injective
    letI : MulDistribMulAction Gal(canonicalUnramifiedLevel K f/K) I :=
      tameInertiaAction K x y hcoprime hconj
    letI : Fact (Irreducible (tameKummerPolynomial (orderOf x) a)) :=
      ⟨hirr⟩
    let eAction : H ≃* Gal(TameKummerAdjoin e a/K) :=
      MulEquiv.ofBijective action hbij
    let eTop : H ≃* Q :=
      (MulEquiv.subgroupCongr hpair).trans Subgroup.topEquiv
    exact ⟨TameKummerAdjoin e a, inferInstance,
      inferInstance, inferInstance, hGal,
      ⟨eTop.symm.trans eAction⟩⟩

/-- The preimage of a cyclic inertia group is generated by the central kernel
and one chosen lift of an inertia generator.  Consequently, to verify that a
semilinear Frobenius element conjugates a homomorphism correctly on the whole
preimage, it is enough to check the central kernel and that one lift. -/
theorem inertia_preimage_conjugation
    {Q : Type uQ} {G : Type uG} {T : Type uT}
    [Group Q] [Group G] [Group T]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (I : Subgroup G) [I.Normal]
    (n : ℕ) [NeZero n]
    (eI : Multiplicative (ZMod n) ≃* I)
    (x y : Q)
    (hx : q x = I.subtype (eI (CyclicH2.generator (n := n))))
    (fn : I.comap q →* T) (Y : T)
    (hkernel : ∀ z : q.ker,
      Commute Y (fn ⟨z.1, by
        change q z.1 ∈ I
        rw [z.property]
        exact I.one_mem⟩))
    (hxconj :
      fn (MulAut.conjNormal y
          (⟨x, by
            change q x ∈ I
            rw [hx]
            exact (eI (CyclicH2.generator (n := n))).property⟩ :
            I.comap q)) =
        Y * fn (⟨x, by
          change q x ∈ I
          rw [hx]
          exact (eI (CyclicH2.generator (n := n))).property⟩ : I.comap q) * Y⁻¹) :
    ∀ a : I.comap q,
      fn (MulAut.conjNormal y a) = Y * fn a * Y⁻¹ := by
  let P : Subgroup Q := I.comap q
  let p : P →* I :=
    (q.comp P.subtype).codRestrict I (fun a ↦ a.property)
  have hp : Function.Surjective p := by
    intro i
    obtain ⟨a, ha⟩ := hq (i : G)
    have haP : a ∈ P := by
      change q a ∈ I
      rw [ha]
      exact i.property
    refine ⟨⟨a, haP⟩, ?_⟩
    apply Subtype.ext
    exact ha
  let xP : P := ⟨x, by
    change q x ∈ I
    rw [hx]
    exact (eI (CyclicH2.generator (n := n))).property⟩
  have hpx : p xP = eI (CyclicH2.generator (n := n)) := by
    apply Subtype.ext
    exact hx
  have hpgen : Subgroup.zpowers (p xP) = ⊤ := by
    rw [hpx]
    exact zpowers_top_equiv eI
      (CyclicH2.generator (n := n))
      (cyclic_zpowers_top n)
  intro a
  have haPow : p a ∈ Subgroup.zpowers (p xP) := by
    rw [hpgen]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haPow
  have hzker : (a : Q) * (x ^ k)⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow]
    have hk' : q (a : Q) = q x ^ k := by
      have hkval := congrArg Subtype.val hk
      simpa [p, xP] using hkval.symm
    rw [hk']
    exact mul_inv_cancel _
  let z : q.ker := ⟨(a : Q) * (x ^ k)⁻¹, hzker⟩
  let zP : P := ⟨z.1, by
    change q z.1 ∈ I
    rw [z.property]
    exact I.one_mem⟩
  have hadecomp : a = zP * xP ^ k := by
    apply Subtype.ext
    change (a : Q) = ((a : Q) * (x ^ k)⁻¹) * x ^ k
    group
  have hzconj :
      fn (MulAut.conjNormal y zP) = Y * fn zP * Y⁻¹ := by
    have hzcentral : y * (z : Q) * y⁻¹ = (z : Q) := by
      have hzcomm : y * (z : Q) = (z : Q) * y :=
        Subgroup.mem_center_iff.mp (hcentral z.property) y
      rw [hzcomm]
      group
    rw [show MulAut.conjNormal y zP = zP by
      apply Subtype.ext
      exact hzcentral]
    have hzP : zP = ⟨z.1, by
        change q z.1 ∈ I
        rw [z.property]
        exact I.one_mem⟩ := Subtype.ext rfl
    rw [hzP]
    rw [(hkernel z).eq]
    group
  have hxconjPow : ∀ m : ℤ,
      fn (MulAut.conjNormal y (xP ^ m)) =
        Y * fn (xP ^ m) * Y⁻¹ := by
    intro m
    have hxconj' :
        fn (MulAut.conjNormal y xP) = Y * fn xP * Y⁻¹ := by
      simpa only using hxconj
    calc
      fn (MulAut.conjNormal y (xP ^ m)) =
          fn ((MulAut.conjNormal y xP) ^ m) := by rw [map_zpow]
      _ = (fn (MulAut.conjNormal y xP)) ^ m := by rw [map_zpow]
      _ = (Y * fn xP * Y⁻¹) ^ m := by rw [hxconj']
      _ = Y * (fn xP) ^ m * Y⁻¹ := by
        simpa only [MulAut.conj_apply] using
          (map_zpow (MulAut.conj Y) (fn xP) m).symm
      _ = Y * fn (xP ^ m) * Y⁻¹ := by rw [map_zpow]
  rw [hadecomp, map_mul, map_mul, hzconj, hxconjPow]
  rw [map_mul]
  group

/-- In a central extension, the preimage of a cyclic subgroup is generated
by the central kernel and any lift of a generator.  In particular every
element of that preimage commutes with the chosen lift. -/
theorem inertia_preimage_commutes
    {Q : Type uQ} {G : Type uG} [Group Q] [Group G]
    (q : Q →* G) (_hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (I : Subgroup G)
    (n : ℕ) [NeZero n]
    (eI : Multiplicative (ZMod n) ≃* I)
    (x : Q)
    (hx : q x = I.subtype (eI (CyclicH2.generator (n := n)))) :
    ∀ a : I.comap q, Commute (a : Q) x := by
  let P : Subgroup Q := I.comap q
  let p : P →* I :=
    (q.comp P.subtype).codRestrict I (fun a ↦ a.property)
  have hpgen : Subgroup.zpowers (p ⟨x, by
      change q x ∈ I
      rw [hx]
      exact (eI (CyclicH2.generator (n := n))).property⟩) = ⊤ := by
    have hegen :
        Subgroup.zpowers (eI (CyclicH2.generator (n := n))) = ⊤ :=
      zpowers_top_equiv eI
        (CyclicH2.generator (n := n))
        (cyclic_zpowers_top n)
    simpa [p, P, hx] using hegen
  intro a
  have haPow : p a ∈ Subgroup.zpowers
      (p ⟨x, by
        change q x ∈ I
        rw [hx]
        exact (eI (CyclicH2.generator (n := n))).property⟩) := by
    rw [hpgen]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haPow
  have hzker : (a : Q) * (x ^ k)⁻¹ ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow]
    have hk' : q (a : Q) = q x ^ k := by
      have hkval := congrArg Subtype.val hk
      simpa [p, P] using hkval.symm
    rw [hk']
    exact mul_inv_cancel _
  have hzcomm : Commute ((a : Q) * (x ^ k)⁻¹) x :=
    (Subgroup.mem_center_iff.mp (hcentral hzker) x).symm
  have hxpow : Commute (x ^ k) x := (Commute.refl x).zpow_left k
  have hadecomp : (a : Q) = ((a : Q) * (x ^ k)⁻¹) * x ^ k := by
    group
  rw [hadecomp]
  exact hzcomm.mul_left hxpow

/-- If a homomorphism on the preimage of cyclic inertia sends the chosen
inertia lift to an element whose left coordinate is inertia-fixed, then the
left coordinate of every image is inertia-fixed. -/
theorem preimage_semidirect_fixed
    {Q : Type uQ} {G : Type uG} {M : Type uM}
    [Group Q] [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (I : Subgroup G)
    (n : ℕ) [NeZero n]
    (eI : Multiplicative (ZMod n) ≃* I)
    (x : Q)
    (hx : q x = I.subtype (eI (CyclicH2.generator (n := n))))
    (eta : M) (hetaI : ∀ i : I, i.1 • eta = eta)
    (fn : I.comap q →*
      M ⋊[MulDistribMulAction.toMulAut G M] G)
    (hfnRight : SemidirectProduct.rightHom.comp fn =
      q.comp (I.comap q).subtype)
    (hfnX : fn ⟨x, by
        change q x ∈ I
        rw [hx]
        exact (eI (CyclicH2.generator (n := n))).property⟩ =
      ⟨eta, q x⟩) :
    ∀ a : I.comap q, ∀ i : I, i.1 • (fn a).left = (fn a).left := by
  let xP : I.comap q := ⟨x, by
    change q x ∈ I
    rw [hx]
    exact (eI (CyclicH2.generator (n := n))).property⟩
  intro a
  have hcommQ : Commute (a : Q) x :=
    inertia_preimage_commutes q hq hcentral I n eI x hx a
  have hcommP : Commute a xP := by
    rw [Commute]
    apply Subtype.ext
    exact hcommQ.eq
  have hcommTarget : Commute (fn a) (fn xP) := hcommP.map fn
  have hgenFixed :
      (eI (CyclicH2.generator (n := n)) : I).1 • (fn a).left =
        (fn a).left := by
    have heq := hcommTarget.eq
    rw [show fn xP = ⟨eta, q x⟩ from hfnX] at heq
    have haI : q (a : Q) ∈ I := a.property
    have hleft := congrArg
      (fun z : M ⋊[MulDistribMulAction.toMulAut G M] G => z.left) heq
    simp only [SemidirectProduct.mul_left] at hleft
    have hrightA := DFunLike.congr_fun hfnRight a
    change (fn a).right = q (a : Q) at hrightA
    rw [hrightA] at hleft
    change (fn a).left * (q (a : Q) • eta) =
      eta * (q x • (fn a).left) at hleft
    rw [hetaI ⟨q (a : Q), haI⟩] at hleft
    have hcancel : eta * (fn a).left =
        eta * (q x • (fn a).left) := by
      rw [mul_comm eta (fn a).left]
      exact hleft
    have hqx : q x • (fn a).left = (fn a).left := by
      exact (mul_left_cancel hcancel).symm
    simpa [hx] using hqx
  letI : MulDistribMulAction I M :=
    (inferInstance : MulDistribMulAction G M).compHom M I.subtype
  let stabilizer : Subgroup I := MulAction.stabilizer I (fn a).left
  have hgenMem : eI (CyclicH2.generator (n := n)) ∈ stabilizer := by
    exact hgenFixed
  have htop : stabilizer = ⊤ := by
    apply top_unique
    intro i _
    have hi : i ∈ Subgroup.zpowers
        (eI (CyclicH2.generator (n := n))) := by
      rw [zpowers_top_equiv eI
        (CyclicH2.generator (n := n))
        (cyclic_zpowers_top n)]
      exact Subgroup.mem_top i
    exact (Subgroup.zpowers_le.mpr hgenMem) hi
  intro i
  have hi : i ∈ stabilizer := by rw [htop]; exact Subgroup.mem_top i
  exact hi

/-- An element fixed by a normal subgroup and by one lift of a generator of
the cyclic quotient is fixed by the whole group. -/
theorem fixed_normal_generator
    {G : Type uG} {M : Type uM} [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (I : Subgroup G) [I.Normal]
    (y : G)
    (hgen : Subgroup.zpowers (QuotientGroup.mk' I y) = ⊤)
    (c : M)
    (hI : ∀ i : I, i.1 • c = c)
    (hy : y • c = c) :
    ∀ g : G, g • c = c := by
  let stabilizer : Subgroup G := MulAction.stabilizer G c
  have hIle : I ≤ stabilizer := fun i hi ↦ hI ⟨i, hi⟩
  have hyMem : y ∈ stabilizer := hy
  intro g
  have hgbar : QuotientGroup.mk' I g ∈
      Subgroup.zpowers (QuotientGroup.mk' I y) := by
    rw [hgen]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgbar
  have hdiff : g * (y ^ k)⁻¹ ∈ I := by
    apply (QuotientGroup.eq_one_iff (g * (y ^ k)⁻¹)).mp
    change QuotientGroup.mk' I (g * (y ^ k)⁻¹) = 1
    rw [map_mul, map_inv, map_zpow, hk]
    exact mul_inv_cancel _
  have hdiffMem : g * (y ^ k)⁻¹ ∈ stabilizer := hIle hdiff
  have hypowMem : y ^ k ∈ stabilizer :=
    (Subgroup.zpowers_le.mpr hyMem)
      (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  have hgMem : (g * (y ^ k)⁻¹) * y ^ k ∈ stabilizer :=
    stabilizer.mul_mem hdiffMem hypowMem
  simpa [mul_assoc] using hgMem

/-- A coefficient fixed by inertia gives the correct semilinear conjugation
law for a Frobenius lift as soon as Frobenius raises the chosen inertia
radical by the residue-cardinality power. -/
theorem preimage_semidirect_conjugation
    {Q : Type uQ} {G : Type uG} {M : Type uM}
    [Group Q] [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (phi : q.ker →* M)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (I : Subgroup G) [I.Normal]
    (n : ℕ) [NeZero n]
    (eI : Multiplicative (ZMod n) ≃* I)
    (x y : Q)
    (hx : q x = I.subtype (eI (CyclicH2.generator (n := n))))
    (r : ℕ) (hconj : y * x * y⁻¹ = x ^ r)
    (eta : M)
    (hetaI : ∀ i : I, i.1 • eta = eta)
    (hetaFrob : q y • eta = eta ^ r)
    (fn : I.comap q →* M ⋊[MulDistribMulAction.toMulAut G M] G)
    (hfnKernel : ∀ z : q.ker,
      fn ⟨z.1, by
        change q z.1 ∈ I
        rw [z.property]
        exact I.one_mem⟩ = SemidirectProduct.inl (phi z))
    (hfnX : fn ⟨x, by
        change q x ∈ I
        rw [hx]
        exact (eI (CyclicH2.generator (n := n))).property⟩ =
      ⟨eta, q x⟩)
    (b : M) (hbI : ∀ i : I, i.1 • b = b) :
    let Y : M ⋊[MulDistribMulAction.toMulAut G M] G := ⟨b, q y⟩
    ∀ a : I.comap q,
      fn (MulAut.conjNormal y a) = Y * fn a * Y⁻¹ := by
  let Y : M ⋊[MulDistribMulAction.toMulAut G M] G := ⟨b, q y⟩
  apply inertia_preimage_conjugation
    q hq hcentral I n eI x y hx fn Y
  · intro z
    rw [hfnKernel z]
    rw [Commute]
    apply SemidirectProduct.ext
    · simp [Y, hfixed, mul_comm]
    · simp [Y]
  · let xP : I.comap q := ⟨x, by
      change q x ∈ I
      rw [hx]
      exact (eI (CyclicH2.generator (n := n))).property⟩
    have hsource : MulAut.conjNormal y xP = xP ^ r := by
      apply Subtype.ext
      exact hconj
    rw [hsource, map_pow, show fn xP = ⟨eta, q x⟩ from hfnX]
    let X : M ⋊[MulDistribMulAction.toMulAut G M] G := ⟨eta, q x⟩
    have hetaX : q x • eta = eta := by
      rw [hx]
      exact hetaI (eI (CyclicH2.generator (n := n)))
    have hbX : q x • b = b := by
      rw [hx]
      exact hbI (eI (CyclicH2.generator (n := n)))
    have hetaXPow (m : ℕ) : (q x) ^ m • eta = eta := by
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ, mul_smul, hetaX, ih]
    have hbXPow (m : ℕ) : (q x) ^ m • b = b := by
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ, mul_smul, hbX, ih]
    have hpowX (m : ℕ) : X ^ m = ⟨eta ^ m, (q x) ^ m⟩ := by
      induction m with
      | zero =>
          apply SemidirectProduct.ext <;> simp [X]
      | succ m ih =>
          rw [pow_succ, ih]
          apply SemidirectProduct.ext
          · change eta ^ m * ((q x) ^ m • eta) = eta ^ (m + 1)
            rw [hetaXPow]
            exact (pow_succ eta m).symm
          · exact (pow_succ (q x) m).symm
    have hconjMap : q y * q x * (q y)⁻¹ = (q x) ^ r := by
      simpa only [map_mul, map_inv, map_pow] using congrArg q hconj
    have hbConj : (q y * q x) • ((q y)⁻¹ • b) = b := by
      rw [← mul_smul]
      rw [hconjMap, hbXPow]
    change X ^ r = Y * X * Y⁻¹
    rw [hpowX]
    apply SemidirectProduct.ext
    · dsimp [Y, X]
      change eta ^ r = b * (q y • eta) *
          ((q y * q x) • ((q y)⁻¹ • b⁻¹))
      simp only [smul_inv']
      rw [hetaFrob, hbConj]
      calc
        eta ^ r = eta ^ r * (b * b⁻¹) := by simp
        _ = b * eta ^ r * b⁻¹ := by ac_rfl
    · dsimp [Y, X]
      exact hconjMap.symm

/-- The natural power of a semidirect-product element has left coordinate
equal to the corresponding cyclic action norm. -/
theorem semidirect_mk_pow
    {G : Type uG} {M : Type uM} [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (b : M) (g : G) (f : ℕ) :
    (⟨b, g⟩ : M ⋊[MulDistribMulAction.toMulAut G M] G) ^ f =
      ⟨∏ k ∈ Finset.range f, g ^ k • b, g ^ f⟩ := by
  induction f with
  | zero =>
      apply SemidirectProduct.ext <;> simp
  | succ f ih =>
      rw [pow_succ, ih]
      apply SemidirectProduct.ext
      · change (∏ k ∈ Finset.range f, g ^ k • b) * (g ^ f • b) =
          ∏ k ∈ Finset.range (f + 1), g ^ k • b
        rw [Finset.prod_range_succ]
      · exact (pow_succ g f).symm

/-- A finite-order element of a semidirect product has detector-zero left
coordinate whenever the detector is invariant under the acting group.

For the tame local application, `M` is the multiplicative group of the
coefficient field and `ord` is its normalized additive valuation, written
multiplicatively.  This is the small calculation which shows that the right
hand side of the final unramified norm equation is a unit. -/
theorem semidirect_detector_pow
    {G : Type uG} {M : Type uM} [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (ord : M →* Multiplicative ℤ)
    (hord : ∀ g : G, ∀ m : M, ord (g • m) = ord m)
    (b : M) (g : G) (n : ℕ) (hn : 0 < n)
    (hpow : (⟨b, g⟩ :
      M ⋊[MulDistribMulAction.toMulAut G M] G) ^ n = 1) :
    ord b = 1 := by
  have hleft :
      ∏ k ∈ Finset.range n, g ^ k • b = 1 := by
    have h := congrArg
      (fun z : M ⋊[MulDistribMulAction.toMulAut G M] G => z.left) hpow
    rw [semidirect_mk_pow] at h
    exact h
  have hordPow : ord b ^ n = 1 := by
    calc
      ord b ^ n = ∏ _k ∈ Finset.range n, ord b := by
        rw [Finset.prod_const, Finset.card_range]
      _ = ∏ k ∈ Finset.range n, ord (g ^ k • b) := by
        apply Finset.prod_congr rfl
        intro k _
        rw [hord]
      _ = ord (∏ k ∈ Finset.range n, g ^ k • b) := by
        rw [map_prod]
      _ = 1 := by rw [hleft, map_one]
  apply Multiplicative.toAdd.injective
  have hz : (n : ℤ) * (ord b).toAdd = 0 := by
    have := congrArg Multiplicative.toAdd hordPow
    simpa [nsmul_eq_mul] using this
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  change (ord b).toAdd = 0
  exact (mul_eq_zero.mp hz).resolve_left hnz

set_option maxHeartbeats 4000000 in
-- Extra heartbeats are needed for the large search space in this proof.
/-- Norm-equation form of the tame semilinear criterion.  Once inertia has
been lifted by a fixed radical, the only remaining datum is a coefficient
whose cyclic Frobenius norm is the left coordinate of the prescribed
Frobenius power. -/
theorem mapped_obstruction_equation
    {Q : Type uQ} {G : Type uG} {M : Type uM}
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
    (hetaI : ∀ i : I, i.1 • eta = eta)
    (hetaPow : eta ^ n = phi ⟨x ^ n, by
      rw [MonoidHom.mem_ker, map_pow, hx]
      change I.subtype (eI (CyclicH2.generator (n := n)) ^ n) = 1
      rw [← map_pow]
      have hgen : (CyclicH2.generator (n := n)) ^ n = 1 := by
        apply Multiplicative.ext
        simp [CyclicH2.generator]
      rw [hgen, map_one, map_one]⟩)
    (y : Q) (r : ℕ) (hconj : y * x * y⁻¹ = x ^ r)
    (hetaFrob : q y • eta = eta ^ r)
    (f : ℕ) (hf : 0 < f)
    (horder : orderOf (QuotientGroup.mk' (I.comap q) y) = f)
    (hgen : Subgroup.zpowers (QuotientGroup.mk' (I.comap q) y) = ⊤)
    (hnorm :
      ∀ fn : I.comap q →*
          M ⋊[MulDistribMulAction.toMulAut G M] G,
        SemidirectProduct.rightHom.comp fn = q.comp (I.comap q).subtype →
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
        ∃ b : M, (∀ i : I, i.1 • b = b) ∧
          (∏ k ∈ Finset.range f, (q y) ^ k • b) =
            (fn ⟨y ^ f, by
              apply (QuotientGroup.eq_one_iff (y ^ f)).mp
              change QuotientGroup.mk' (I.comap q) (y ^ f) = 1
              rw [map_pow, ← horder, pow_orderOf_eq_one]⟩).left) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    MHTwo.mapCoefficientsHom phi
        (fun g z ↦ (hfixed g z).symm)
        (extensionObstructionClass q hq hcentral) = 1 := by
  apply mapped_obstruction_semilinear
    q hq hcentral phi hfixed I n eI x hx eta hetaI hetaPow y f hf
      horder hgen
  intro fn hfnRight hfnKernel hfnX
  obtain ⟨b, hbI, hbNorm⟩ := hnorm fn hfnRight hfnKernel hfnX
  let Y : M ⋊[MulDistribMulAction.toMulAut G M] G := ⟨b, q y⟩
  refine ⟨Y, rfl, ?_, ?_⟩
  · exact preimage_semidirect_conjugation
      q hq hcentral phi hfixed I n eI x y hx r hconj eta hetaI
        hetaFrob fn hfnKernel hfnX b hbI
  · rw [show Y ^ f =
        ⟨∏ k ∈ Finset.range f, (q y) ^ k • b, (q y) ^ f⟩ by
      exact semidirect_mk_pow b (q y) f]
    apply SemidirectProduct.ext
    · exact hbNorm
    · have hright := DFunLike.congr_fun hfnRight
          (⟨y ^ f, by
            apply (QuotientGroup.eq_one_iff (y ^ f)).mp
            change QuotientGroup.mk' (I.comap q) (y ^ f) = 1
            rw [map_pow, ← horder, pow_orderOf_eq_one]⟩ : I.comap q)
      change (q y) ^ f =
        (fn (⟨y ^ f, by
          apply (QuotientGroup.eq_one_iff (y ^ f)).mp
          change QuotientGroup.mk' (I.comap q) (y ^ f) = 1
          rw [map_pow, ← horder, pow_orderOf_eq_one]⟩ : I.comap q)).right
      simpa using hright.symm

set_option maxHeartbeats 2000000 in
-- The finite central-extension argument expands several quotient constructions.
/-- Relative tame local vanishing reduced to the ordinary unramified norm
criterion.

The `hnormSurj` hypothesis is the local-class-field-theory input: a
`G`-fixed element of detector value zero is a norm from the inertia-fixed
field.  All remaining facts needed by
`mapped_obstruction_equation`
are forced by finiteness, the central cyclic inertia preimage, and the tame
conjugation relation. -/
theorem mapped_obstruction_surjective
    {Q : Type uQ} {G : Type uG} {M : Type uM}
    [Group Q] [Finite Q] [Group G] [CommGroup M]
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
    (hetaI : ∀ i : I, i.1 • eta = eta)
    (hetaPow : eta ^ n = phi ⟨x ^ n, by
      rw [MonoidHom.mem_ker, map_pow, hx]
      change I.subtype (eI (CyclicH2.generator (n := n)) ^ n) = 1
      rw [← map_pow]
      have hgen : (CyclicH2.generator (n := n)) ^ n = 1 := by
        apply Multiplicative.ext
        simp [CyclicH2.generator]
      rw [hgen, map_one, map_one]⟩)
    (y : Q) (r : ℕ) (hconj : y * x * y⁻¹ = x ^ r)
    (hetaFrob : q y • eta = eta ^ r)
    (f : ℕ) (hf : 0 < f)
    (horder : orderOf (QuotientGroup.mk' (I.comap q) y) = f)
    (hgen : Subgroup.zpowers (QuotientGroup.mk' (I.comap q) y) = ⊤)
    (ord : M →* Multiplicative ℤ)
    (hord : ∀ g : G, ∀ m : M, ord (g • m) = ord m)
    (hnormSurj : ∀ c : M,
      (∀ g : G, g • c = c) → ord c = 1 →
        ∃ b : M, (∀ i : I, i.1 • b = b) ∧
          (∏ k ∈ Finset.range f, (q y) ^ k • b) = c) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    MHTwo.mapCoefficientsHom phi
        (fun g z ↦ (hfixed g z).symm)
        (extensionObstructionClass q hq hcentral) = 1 := by
  apply mapped_obstruction_equation
    q hq hcentral phi hfixed I n eI x hx eta hetaI hetaPow y r hconj
      hetaFrob f hf horder hgen
  intro fn hfnRight hfnKernel hfnX
  let a : I.comap q := ⟨y ^ f, by
    apply (QuotientGroup.eq_one_iff (y ^ f)).mp
    change QuotientGroup.mk' (I.comap q) (y ^ f) = 1
    rw [map_pow, ← horder, pow_orderOf_eq_one]⟩
  let c : M := (fn a).left
  have hcI : ∀ i : I, i.1 • c = c := by
    exact preimage_semidirect_fixed
      q hq hcentral I n eI x hx eta hetaI fn hfnRight hfnX a
  have hconjFn :=
    preimage_semidirect_conjugation
      q hq hcentral phi hfixed I n eI x y hx r hconj eta hetaI
        hetaFrob fn hfnKernel hfnX (1 : M) (by intro i; simp)
  have haConj : MulAut.conjNormal y a = a := by
    apply Subtype.ext
    dsimp [a]
    group
  have hcy : q y • c = c := by
    have h := hconjFn a
    rw [haConj] at h
    have hleft := congrArg
      (fun z : M ⋊[MulDistribMulAction.toMulAut G M] G => z.left) h
    change c = (1 : M) * (q y • c) * _ at hleft
    simpa using hleft.symm
  have hgenG : Subgroup.zpowers (QuotientGroup.mk' I (q y)) = ⊤ := by
    let e := quotientComapSurjective q hq I
    have he := zpowers_top_equiv e
      (QuotientGroup.mk' (I.comap q) y) hgen
    change Subgroup.zpowers
      (e (QuotientGroup.mk' (I.comap q) y)) = ⊤ at he
    rw [comap_surjective_mk] at he
    exact he
  have hcG : ∀ g : G, g • c = c :=
    fixed_normal_generator I (q y) hgenG c hcI hcy
  have hcOrder : ord c = 1 := by
    let m := orderOf a
    have hm : 0 < m := (isOfFinOrder_of_finite a).orderOf_pos
    have hpowA : a ^ m = 1 := by
      exact pow_orderOf_eq_one a
    have hpowFn : (fn a) ^ m = 1 := by
      rw [← map_pow, hpowA, map_one]
    exact semidirect_detector_pow
      ord hord c (fn a).right m hm (by simpa [c] using hpowFn)
  exact hnormSurj c hcG hcOrder

/-- Prime-to-residue-characteristic roots of unity are fixed by inertia, and
an element acting as arithmetic Frobenius on the residue field raises them
to the residue-cardinality power.  This is the elementary Teichmuller
uniqueness bridge needed after passing to a completion. -/
theorem integral_inertia_fixed
    {B F G : Type u} [CommRing B] [IsDomain B] [IsLocalRing B]
    [Field F] [Algebra B F]
    [Group G] [MulSemiringAction G B] [MulSemiringAction G F]
    [MulDistribMulAction G Fˣ]
    (hcompat : ∀ g : G, ∀ b : B,
      algebraMap B F (g • b) = g • algebraMap B F b)
    (hcompatUnits : ∀ g : G, ∀ z : Fˣ,
      ((g • z : Fˣ) : F) = g • (z : F))
    (n : ℕ) (hn : IsUnit (n : B))
    (z : Bˣ) (hz : (z : B) ^ n = 1)
    (y : G) (r : ℕ)
    (hyResidue : IsLocalRing.residue B (y • (z : B)) =
      IsLocalRing.residue B ((z : B) ^ r)) :
    let zF : Fˣ := Units.map (algebraMap B F) z
    (∀ i : (IsLocalRing.maximalIdeal B).inertia G,
      i.1 • zF = zF) ∧ y • zF = zF ^ r := by
  let zF : Fˣ := Units.map (algebraMap B F) z
  have inertiaFixed : ∀ i : (IsLocalRing.maximalIdeal B).inertia G,
      i.1 • zF = zF := by
    intro i
    have hpow : (i.1 • (z : B)) ^ n = 1 := by
      calc
        (i.1 • (z : B)) ^ n = i.1 • ((z : B) ^ n) :=
          ((MulSemiringAction.toRingEquiv G B i.1).map_pow (z : B) n).symm
        _ = 1 := by rw [hz, smul_one]
    have hres : IsLocalRing.residue B (i.1 • (z : B)) =
        IsLocalRing.residue B (z : B) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact i.property (z : B)
    have heq : i.1 • (z : B) = (z : B) :=
      Submission.NumberTheory.Milne.residue_nat_cast
        hn hpow hz hres
    apply Units.ext
    rw [hcompatUnits]
    change i.1 • algebraMap B F (z : B) = algebraMap B F (z : B)
    rw [← hcompat, heq]
  refine ⟨inertiaFixed, ?_⟩
  have hpowY : (y • (z : B)) ^ n = 1 := by
    calc
      (y • (z : B)) ^ n = y • ((z : B) ^ n) :=
        ((MulSemiringAction.toRingEquiv G B y).map_pow (z : B) n).symm
      _ = 1 := by rw [hz, smul_one]
  have hpowR : ((z : B) ^ r) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]
  have heqY : y • (z : B) = (z : B) ^ r :=
    Submission.NumberTheory.Milne.residue_nat_cast
      hn hpowY hpowR hyResidue
  apply Units.ext
  rw [hcompatUnits]
  change y • algebraMap B F (z : B) = algebraMap B F (z : B) ^ r
  rw [← hcompat, heqY, map_pow]

/-- The root chosen to trivialize cyclic inertia can be chosen equivariantly
for a Frobenius element.  If Frobenius raises one ambient primitive root to
its `r`th power, it does the same to the root of the lift power produced by
the cyclic obstruction calculation. -/
theorem fixed_frobenius_lift
    {Q : Type uQ} {G : Type uG} {F : Type uF}
    [Group Q] [Finite Q] [Group G] [Finite G]
    [Field F] [MulDistribMulAction G Fˣ]
    (q : Q →* G) (n : ℕ) (x : Q)
    (horder : orderOf (q x) = n)
    (phi : q.ker →* Fˣ) (hphi : Function.Injective phi)
    (I : Subgroup G) (y : G) (r : ℕ)
    (zeta : Fˣ) (hzeta : IsPrimitiveRoot zeta (orderOf x))
    (hzetaI : ∀ i : I, i.1 • zeta = zeta)
    (hzetaY : y • zeta = zeta ^ r) :
    let xpow : q.ker := ⟨x ^ n, by
      rw [MonoidHom.mem_ker, map_pow, ← horder, pow_orderOf_eq_one]⟩
    ∃ eta : Fˣ,
      (∀ i : I, i.1 • eta = eta) ∧
      eta ^ n = phi xpow ∧
      y • eta = eta ^ r := by
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
  have hzetaPow : IsPrimitiveRoot (zeta ^ n) d :=
    hzeta.pow_of_dvd hn0 hnDvd
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
  refine ⟨zeta ^ a, ?_, ?_, ?_⟩
  · intro i
    rw [smul_pow', hzetaI]
  · change (zeta ^ a) ^ n = phi xpow
    calc
      (zeta ^ a) ^ n = zeta ^ (a * n) := (pow_mul zeta a n).symm
      _ = zeta ^ (n * a) := by rw [Nat.mul_comm]
      _ = (zeta ^ n) ^ a := pow_mul zeta n a
      _ = phi xpow := ha
  · calc
      y • zeta ^ a = (y • zeta) ^ a := smul_pow' y zeta a
      _ = (zeta ^ r) ^ a := by rw [hzetaY]
      _ = zeta ^ (r * a) := (pow_mul zeta r a).symm
      _ = zeta ^ (a * r) := by rw [Nat.mul_comm]
      _ = (zeta ^ a) ^ r := pow_mul zeta a r

/-- Tame local vanishing from the two concrete arithmetic inputs used in the
completed number-field application: Teichmuller control of a primitive root
and norm-surjectivity from the inertia-fixed field. -/
theorem mapped_obstruction_primitive
    {Q : Type uQ} {G : Type uG} {F : Type uF}
    [Group Q] [Finite Q] [Group G] [Finite G]
    [Field F] [MulDistribMulAction G Fˣ]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (phi : q.ker →* Fˣ) (hphi : Function.Injective phi)
    (hfixed : ∀ g : G, ∀ z : q.ker, g • phi z = phi z)
    (I : Subgroup G) [I.Normal]
    (n : ℕ) [NeZero n]
    (eI : Multiplicative (ZMod n) ≃* I)
    (x : Q)
    (hx : q x = I.subtype (eI (CyclicH2.generator (n := n))))
    (horderX : orderOf (q x) = n)
    (y : Q) (r : ℕ) (hconj : y * x * y⁻¹ = x ^ r)
    (zeta : Fˣ) (hzeta : IsPrimitiveRoot zeta (orderOf x))
    (hzetaI : ∀ i : I, i.1 • zeta = zeta)
    (hzetaY : q y • zeta = zeta ^ r)
    (f : ℕ) (hf : 0 < f)
    (horder : orderOf (QuotientGroup.mk' (I.comap q) y) = f)
    (hgen : Subgroup.zpowers (QuotientGroup.mk' (I.comap q) y) = ⊤)
    (ord : Fˣ →* Multiplicative ℤ)
    (hord : ∀ g : G, ∀ m : Fˣ, ord (g • m) = ord m)
    (hnormSurj : ∀ c : Fˣ,
      (∀ g : G, g • c = c) → ord c = 1 →
        ∃ b : Fˣ, (∀ i : I, i.1 • b = b) ∧
          (∏ k ∈ Finset.range f, (q y) ^ k • b) = c) :
    letI : CommGroup q.ker :=
      centralExtensionComm q hcentral
    letI : MulDistribMulAction G q.ker :=
      trivialDistribAction G q.ker
    MHTwo.mapCoefficientsHom phi
        (fun g z ↦ (hfixed g z).symm)
        (extensionObstructionClass q hq hcentral) = 1 := by
  obtain ⟨eta, hetaI, hetaPow, hetaY⟩ :=
    fixed_frobenius_lift
      q n x horderX phi hphi I (q y) r zeta hzeta hzetaI hzetaY
  apply mapped_obstruction_surjective
    q hq hcentral phi hfixed I n eI x hx eta hetaI
      (by simpa using hetaPow) y r hconj hetaY f hf horder hgen
      ord hord hnormSurj

/-- Embed units of a fixed field into the ambient field. -/
noncomputable def fixedUnitAmbient
    (K F : Type u) [Field K] [Field F] [Algebra K F]
    (I : Subgroup Gal(F/K)) : (IntermediateField.fixedField I)ˣ →* Fˣ :=
  Units.map (IntermediateField.fixedField I).val.toMonoidHom

/-- A unit embedded from the fixed field is fixed by the subgroup. -/
theorem fixed_unit_ambient
    (K F : Type u) [Field K] [Field F] [Algebra K F]
    (I : Subgroup Gal(F/K))
    (b : (IntermediateField.fixedField I)ˣ) (i : I) :
    i.1 • fixedUnitAmbient K F I b =
      fixedUnitAmbient K F I b := by
  apply Units.ext
  change i.1 (((b : IntermediateField.fixedField I) : F)) =
    ((b : IntermediateField.fixedField I) : F)
  exact (IntermediateField.mem_fixedField_iff I
    ((b : IntermediateField.fixedField I) : F)).1
      (b : IntermediateField.fixedField I).property i i.property

/-- If one element generates the quotient by a normal subgroup, the field
norm from the fixed field is the orbit product over its powers. -/
theorem galois_fixed_product
    (K F : Type u) [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    (I : Subgroup Gal(F/K)) [I.Normal]
    (y : Gal(F/K)) (f : ℕ)
    (horder : orderOf (QuotientGroup.mk' I y) = f)
    (hgen : Subgroup.zpowers (QuotientGroup.mk' I y) = ⊤)
    (b : (IntermediateField.fixedField I)ˣ) :
    algebraMap K F (Algebra.norm K (b : IntermediateField.fixedField I)) =
      ((∏ k ∈ Finset.range f, y ^ k •
        fixedUnitAmbient K F I b : Fˣ) : F) := by
  classical
  unfold fixedUnitAmbient
  let E := IntermediateField.fixedField I
  let e : Gal(F/K) ⧸ I ≃* Gal(E/K) := IsGalois.normalAutEquivQuotient I
  have hinj : Set.InjOn
      (fun k : ℕ ↦ (QuotientGroup.mk' I y) ^ k)
      (Finset.range f) := by
    intro m hm n hn hmn
    have hm_lt : m < f := Finset.mem_range.mp hm
    have hn_lt : n < f := Finset.mem_range.mp hn
    have hmod := (pow_inj_mod (x := QuotientGroup.mk' I y)).mp hmn
    rw [horder, Nat.mod_eq_of_lt hm_lt, Nat.mod_eq_of_lt hn_lt] at hmod
    exact hmod
  have himage : Finset.image
      (fun k : ℕ ↦ (QuotientGroup.mk' I y) ^ k)
      (Finset.range f) = Finset.univ := by
    have himageZ : Finset.image
        (fun k : ℕ ↦ (QuotientGroup.mk' I y) ^ k)
        (Finset.range f) =
          ((Subgroup.zpowers (QuotientGroup.mk' I y) :
            Subgroup (Gal(F/K) ⧸ I)) : Set (Gal(F/K) ⧸ I)).toFinset := by
      calc
        Finset.image (fun k : ℕ ↦ (QuotientGroup.mk' I y) ^ k)
            (Finset.range f) =
            Finset.image (fun k : ℕ ↦ (QuotientGroup.mk' I y) ^ k)
              (Finset.range (orderOf (QuotientGroup.mk' I y))) := by
                rw [horder]
        _ = ((Subgroup.zpowers (QuotientGroup.mk' I y) :
              Subgroup (Gal(F/K) ⧸ I)) : Set (Gal(F/K) ⧸ I)).toFinset :=
          image_range_orderOf
    ext z
    constructor
    · intro _
      exact Finset.mem_univ z
    · intro _
      apply (Finset.ext_iff.mp himageZ z).mpr
      apply Set.mem_toFinset.mpr
      rw [hgen]
      exact Subgroup.mem_top z
  have hnormProd :
      algebraMap K E (Algebra.norm K (b : E)) =
        ∏ z : Gal(F/K) ⧸ I, (e z) (b : E) :=
    calc
      algebraMap K E (Algebra.norm K (b : E)) =
          ∏ sigma : Gal(E/K), sigma (b : E) :=
        Algebra.norm_eq_prod_automorphisms K (b : E)
      _ = ∏ z : Gal(F/K) ⧸ I, (e z) (b : E) :=
        (Equiv.prod_comp e.toEquiv
          (fun sigma : Gal(E/K) ↦ sigma (b : E))).symm
  change ((algebraMap K E (Algebra.norm K (b : E)) : E) : F) = _
  rw [hnormProd]
  change E.val (∏ z : Gal(F/K) ⧸ I, (e z) (b : E)) = _
  rw [map_prod]
  rw [← himage, Finset.prod_image hinj]
  rw [show ((∏ k ∈ Finset.range f, y ^ k • Units.map
      (IntermediateField.fixedField I).val.toMonoidHom b : Fˣ) : F) =
      ∏ k ∈ Finset.range f, ((y ^ k • Units.map
        (IntermediateField.fixedField I).val.toMonoidHom b : Fˣ) : F) by
    change (Units.coeHom F) (∏ k ∈ Finset.range f, y ^ k • Units.map
      (IntermediateField.fixedField I).val.toMonoidHom b) = _
    rw [map_prod]
    rfl]
  apply Finset.prod_congr rfl
  intro k _hk
  rw [show (QuotientGroup.mk' I y) ^ k =
      QuotientGroup.mk' I (y ^ k) by rw [map_pow]]
  dsimp only [e]
  change E.val (((IsGalois.normalAutEquivQuotient I)
    (↑(y ^ k) : Gal(F/K) ⧸ I)) (b : E)) = _
  rw [IsGalois.normalAutEquivQuotient_apply]
  calc
    E.val (((AlgEquiv.restrictNormalHom E) (y ^ k)) (b : E)) =
        (y ^ k) ((b : E) : F) :=
      AlgEquiv.restrictNormalHom_apply E (y ^ k) (b : E)
    _ = (y ^ k) ((Units.map E.val.toMonoidHom b : Fˣ) : F) := rfl
    _ = ((y ^ k • Units.map E.val.toMonoidHom b : Fˣ) : F) :=
      (Units.coe_smul (y ^ k) (Units.map E.val.toMonoidHom b)).symm

/-- Transport a unit backwards across an equality of intermediate fields. -/
noncomputable def intermediateFieldUnit
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    {E₁ E₂ : IntermediateField K F} (h : E₁ = E₂) : E₂ˣ →* E₁ˣ :=
  Units.map (IntermediateField.equivOfEq h).symm.toMonoidHom

/-- Transporting an intermediate-field unit across equality preserves its
field norm. -/
theorem norm_intermediate_unit
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F]
    {E₁ E₂ : IntermediateField K F} (h : E₁ = E₂) (b : E₂ˣ) :
    Algebra.norm K ((intermediateFieldUnit h b : E₁ˣ) : E₁) =
      Algebra.norm K (b : E₂) := by
  let e : E₁ ≃ₐ[K] E₂ := IntermediateField.equivOfEq h
  have hb : e ((intermediateFieldUnit h b : E₁ˣ) : E₁) = (b : E₂) := by
    change e (e.symm (b : E₂)) = (b : E₂)
    exact e.apply_symm_apply (b : E₂)
  calc
    Algebra.norm K ((intermediateFieldUnit h b : E₁ˣ) : E₁) =
        Algebra.norm K
          (e ((intermediateFieldUnit h b : E₁ˣ) : E₁)) :=
      (Algebra.norm_eq_of_algEquiv e
        ((intermediateFieldUnit h b : E₁ˣ) : E₁)).symm
    _ = Algebra.norm K (b : E₂) := by rw [hb]

/-- Galoisness transports across equality of intermediate fields. -/
theorem galois_intermediate_field
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F]
    {E₁ E₂ : IntermediateField K F} [IsGalois K E₁]
    (h : E₁ = E₂) : IsGalois K E₂ :=
  IsGalois.of_algEquiv (IntermediateField.equivOfEq h)

set_option maxHeartbeats 2000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- The residue-algebra and integral-model instance search is deeply nested.
/-- Package the residue algebra and unit norm theorem into local norm data. -/
noncomputable def unramified_data_model
    (K L U : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    [CommRing U]
    [Algebra (Valuation.integer (ValuativeRel.valuation K)) U]
    [Algebra U L]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K)) U L]
    [IsIntegralClosure U (Valuation.integer (ValuativeRel.valuation K)) L]
    [Module.Finite (Valuation.integer (ValuativeRel.valuation K)) U]
    [Algebra.FormallyUnramified
      (Valuation.integer (ValuativeRel.valuation K)) U]
    [IsLocalRing U]
    [IsLocalHom
      (algebraMap (Valuation.integer (ValuativeRel.valuation K)) U)] :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L :=
      spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : IsNonarchimedeanLocalField L :=
      FLExt.nonarchimedeanLocalField K L
    ∃ hResidueAlgebra : Algebra
        (ResidueField (Valuation.integer (ValuativeRel.valuation K)))
        (ResidueField (Valuation.integer (ValuativeRel.valuation L))),
      letI : Algebra
          (ResidueField (Valuation.integer (ValuativeRel.valuation K)))
          (ResidueField (Valuation.integer (ValuativeRel.valuation L))) :=
        hResidueAlgebra
      UnramifiedUnitData K L
        (FLExt.integerUnitNorm K L) :=
  FLExt.residue_unramified_model
    K L U

set_option maxHeartbeats 2000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- The residue-algebra and integral-model instance search is deeply nested.
/-- A base-field unit of order zero is a field norm from an extension with
a formally unramified integral model. -/
theorem unit_integral_model
    (K L U : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    [CommRing U]
    [Algebra (Valuation.integer (ValuativeRel.valuation K)) U]
    [Algebra U L]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K)) U L]
    [IsIntegralClosure U (Valuation.integer (ValuativeRel.valuation K)) L]
    [Module.Finite (Valuation.integer (ValuativeRel.valuation K)) U]
    [Algebra.FormallyUnramified
      (Valuation.integer (ValuativeRel.valuation K)) U]
    [IsLocalRing U]
    [IsLocalHom
      (algebraMap (Valuation.integer (ValuativeRel.valuation K)) U)]
    (a : Kˣ) (ha : localUnitOrder K (Additive.ofMul a) = 0) :
    ∃ b : Lˣ, Units.map (Algebra.norm K) b = a := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  obtain ⟨hResidueAlgebra, hUnitNorm⟩ :=
    FLExt.residue_unramified_model
      K L U
  letI := hResidueAlgebra
  have hLocalNorm :=
    FLExt.unramified_data_unit
      K L hResidueAlgebra hUnitNorm
  obtain ⟨aInt, haInt⟩ :=
    integer_order_zero K a ha
  obtain ⟨bInt, hbNorm⟩ :=
    unramified_integer_norm K L
      (FLExt.integerUnitNorm K L) hLocalNorm aInt
  let b : Lˣ := Units.map
    (Valuation.integer (ValuativeRel.valuation L)).subtype.toMonoidHom bInt
  refine ⟨b, ?_⟩
  apply Units.ext
  change Algebra.norm K
    (((bInt : (Valuation.integer (ValuativeRel.valuation L))ˣ) :
      Valuation.integer (ValuativeRel.valuation L)) : L) = (a : K)
  rw [hbNorm]
  exact congrArg Units.val haInt

set_option maxHeartbeats 2000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- Fixed-field norm calculations require the full local-field instance tower.
/-- In a finite Galois extension of nonarchimedean local fields, a unit of
the base field is a norm from the inertia-fixed field.  The norm is written
as the orbit product of any element whose image generates the quotient by
inertia.

This is the arithmetic input required by
`mapped_obstruction_surjective`; it is
proved from the intrinsic maximal-unramified characterization of the
inertia-fixed field and unit-norm surjectivity for a formally unramified
integral model. -/
theorem inertia_equation_model
    (K F B : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [NontriviallyNormedField F] [NormedAlgebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    [IsUltrametricDist F] [ValuativeRel F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [IsNonarchimedeanLocalField F]
    [CommRing B]
    [IsDomain B]
    [IsDiscreteValuationRing B]
    [HenselianLocalRing B]
    [Algebra (Valuation.integer (ValuativeRel.valuation K)) B]
    [Algebra B F]
    [IsFractionRing B F]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K))
      B F]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K)) K F]
    [IsIntegralClosure
      B
      (Valuation.integer (ValuativeRel.valuation K)) F]
    [MulSemiringAction Gal(F/K) B]
    [SMulDistribClass Gal(F/K) B F] :
    let G := Gal(F/K)
    let P := IsLocalRing.maximalIdeal B
    let I := P.inertia G
    ∀ (hI : I.Normal),
      letI : I.Normal := hI
      ∀ (y : G) (f : ℕ),
        0 < f →
        orderOf (QuotientGroup.mk' I y) = f →
        Subgroup.zpowers (QuotientGroup.mk' I y) = ⊤ →
        ∀ c : Fˣ,
          (∀ g : G, g • c = c) →
          localOrderHom F c = 1 →
          ∃ b : Fˣ, (∀ i : I, i.1 • b = b) ∧
            (∏ k ∈ Finset.range f, y ^ k • b) = c := by
  dsimp only
  let G := Gal(F/K)
  let A := Valuation.integer (ValuativeRel.valuation K)
  letI : Module.Finite A B := IsIntegralClosure.finite A K F B
  letI : IsGaloisGroup G A B :=
    IsGaloisGroup.of_isFractionRing G A B K F
  letI : IsDiscreteValuationRing A :=
    discrete_valuation_ring K
  letI : HenselianLocalRing A :=
    integer_henselian_ring K
  letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).2 <| by
      intro a b hab
      apply FaithfulSMul.algebraMap_injective A K
      apply (algebraMap K F).injective
      rw [← IsScalarTower.algebraMap_apply A K F a,
        ← IsScalarTower.algebraMap_apply A K F b,
        IsScalarTower.algebraMap_apply A B F a,
        IsScalarTower.algebraMap_apply A B F b]
      exact congrArg (algebraMap B F) hab
  letI : IsLocalHom (algebraMap A B) :=
    Algebra.IsIntegral.isLocalHom A B
  let P := IsLocalRing.maximalIdeal B
  let I := P.inertia G
  intro hI
  letI : I.Normal := hI
  intro y f _hf horder hgen c hc hord
  let Efix := inertiaFixedField (K := K) (L := F) P
  let U := maximalUnramifiedSubalgebra A B
  let E := fractionFieldSubalgebra A B K F U
  have hFixE : Efix = E :=
    inertia_fraction_subalgebra
      (A := A) (B := B) (K := K) (L := F)
  let algUE : Algebra U E :=
    fractionIntermediateSubalgebra A B K F U
  letI : SMul U E := algUE.toSMul
  letI : Algebra U E := algUE
  letI : Module.Finite A U := maximal_subalgebra_finite A B
  letI : Algebra.FormallyUnramified A U :=
    maximal_subalgebra_formally A B
  letI : IsDiscreteValuationRing U :=
    subalgebra_discrete_valuation A B
  letI : IsLocalRing U :=
    subalgebra_ring_integral A B U
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).2 <| by
      intro a b hab
      apply FaithfulSMul.algebraMap_injective A B
      exact congrArg Subtype.val hab
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  letI : IsFractionRing U E :=
    fraction_intermediate_subalgebra A B K F U
  letI : IsScalarTower A U E := IsScalarTower.of_algebraMap_eq' <| by
    ext a
    change algebraMap A F a = algebraMap B F (algebraMap A B a)
    exact IsScalarTower.algebraMap_apply A B F a
  letI : IsIntegralClosure U A E :=
    IsIntegralClosure.of_isIntegrallyClosed U A E
  letI : FiniteDimensional K E := by
    exact Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
  letI : IsGalois K Efix := IsGalois.of_fixedField_normal_subgroup I
  letI : IsGalois K E :=
    galois_intermediate_field hFixE
  have hcBase : (c : F) ∈ Set.range (algebraMap K F) :=
    (IsGalois.mem_range_algebraMap_iff_fixed (c : F)).2 (fun g ↦ by
      exact congrArg Units.val (hc g))
  obtain ⟨a, ha⟩ := hcBase
  have ha0 : a ≠ 0 := by
    intro ha0
    have hc0 : (c : F) = 0 := by simpa [ha0] using ha.symm
    exact c.ne_zero hc0
  let aUnit : Kˣ := Units.mk0 a ha0
  have haUnit : Units.map (algebraMap K F) aUnit = c := by
    apply Units.ext
    exact ha
  have hordF : localUnitOrder F (Additive.ofMul c) = 0 := by
    have h := congrArg Multiplicative.toAdd hord
    simpa [localOrderHom] using h
  have hvalF : ValuativeRel.valuation F (c : F) = 1 := by
    apply le_antisymm
    · have hle : localUnitOrder F (0 : Additive Fˣ) ≤
          localUnitOrder F (Additive.ofMul c) := by simp [hordF]
      simpa using
        (local_order_valuation F (1 : Fˣ) c).1 hle
    · have hle : localUnitOrder F (Additive.ofMul c) ≤
          localUnitOrder F (0 : Additive Fˣ) := by simp [hordF]
      simpa using
        (local_order_valuation F c (1 : Fˣ)).1 hle
  have hnormF : ‖(c : F)‖₊ = 1 := by
    rw [← NormedField.valuation_apply]
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation F)
      (NormedField.valuation (K := F))).eq_one_iff_eq_one.mp hvalF
  have hnormK : ‖a‖₊ = 1 := by
    calc
      ‖a‖₊ = ‖algebraMap K F a‖₊ := (nnnorm_algebraMap' F a).symm
      _ = ‖(c : F)‖₊ := congrArg nnnorm ha
      _ = 1 := hnormF
  have hvalK : ValuativeRel.valuation K a = 1 := by
    apply (ValuativeRel.isEquiv (ValuativeRel.valuation K)
      (NormedField.valuation (K := K))).eq_one_iff_eq_one.mpr
    simpa only [NormedField.valuation_apply] using hnormK
  have hordK : localUnitOrder K (Additive.ofMul aUnit) = 0 := by
    apply le_antisymm
    · have hle : localUnitOrder K (Additive.ofMul aUnit) ≤
          localUnitOrder K (0 : Additive Kˣ) := by
        apply (local_order_valuation K aUnit (1 : Kˣ)).2
        simpa [aUnit] using hvalK.ge
      simpa using hle
    · have hle : localUnitOrder K (0 : Additive Kˣ) ≤
          localUnitOrder K (Additive.ofMul aUnit) := by
        apply (local_order_valuation K (1 : Kˣ) aUnit).2
        simpa [aUnit] using hvalK.le
      simpa using hle
  obtain ⟨bE, hbNorm⟩ :=
    unit_integral_model K E U aUnit hordK
  let bFix : Efixˣ := intermediateFieldUnit hFixE bE
  let b : Fˣ := fixedUnitAmbient K F I bFix
  refine ⟨b, ?_, ?_⟩
  · exact fixed_unit_ambient K F I bFix
  · have hprodMap :
        algebraMap K F (Algebra.norm K (bFix : Efix)) =
          ((∏ k ∈ Finset.range f, y ^ k • b : Fˣ) : F) := by
      exact galois_fixed_product
        K F I y f horder hgen bFix
    apply Units.ext
    change ((∏ k ∈ Finset.range f, y ^ k • b : Fˣ) : F) = (c : F)
    rw [← hprodMap]
    have hnormTransfer :
        Algebra.norm K (bFix : Efix) = Algebra.norm K (bE : E) := by
      exact norm_intermediate_unit hFixE bE
    rw [hnormTransfer]
    have hbNormVal : Algebra.norm K (bE : E) = (aUnit : K) :=
      congrArg Units.val hbNorm
    rw [hbNormVal]
    exact congrArg Units.val haUnit

set_option maxHeartbeats 2000000 in
-- Elaboration and instance synthesis each need an explicit local budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- The spectral integral model creates a large local-field instance search.
/-- The canonical spectral-integer specialization of
`inertia_equation_model`. -/
theorem inertia_fixed_equation
    (K F : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [NontriviallyNormedField F] [NormedAlgebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    [IsUltrametricDist F] [ValuativeRel F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    [IsNonarchimedeanLocalField F]
    [Algebra (Valuation.integer (ValuativeRel.valuation K))
      (Valuation.integer (NormedField.valuation (K := F)))]
    [Algebra (Valuation.integer (NormedField.valuation (K := F))) F]
    [IsFractionRing (Valuation.integer (NormedField.valuation (K := F))) F]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K))
      (Valuation.integer (NormedField.valuation (K := F))) F]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K)) K F]
    [IsIntegralClosure
      (Valuation.integer (NormedField.valuation (K := F)))
      (Valuation.integer (ValuativeRel.valuation K)) F]
    [MulSemiringAction Gal(F/K)
      (Valuation.integer (NormedField.valuation (K := F)))]
    [SMulDistribClass Gal(F/K)
      (Valuation.integer (NormedField.valuation (K := F))) F] :
    let G := Gal(F/K)
    let B := Valuation.integer (NormedField.valuation (K := F))
    let P := IsLocalRing.maximalIdeal B
    let I := P.inertia G
    ∀ (hI : I.Normal),
      letI : I.Normal := hI
      ∀ (y : G) (f : ℕ),
        0 < f →
        orderOf (QuotientGroup.mk' I y) = f →
        Subgroup.zpowers (QuotientGroup.mk' I y) = ⊤ →
        ∀ c : Fˣ,
          (∀ g : G, g • c = c) →
          localOrderHom F c = 1 →
          ∃ b : Fˣ, (∀ i : I, i.1 • b = b) ∧
            (∏ k ∈ Finset.range f, y ^ k • b) = c := by
  let B := Valuation.integer (NormedField.valuation (K := F))
  have hBF : Valuation.integer (ValuativeRel.valuation F) = B := by
    ext x
    simp only [B, Valuation.mem_integer_iff]
    rw [← (ValuativeRel.valuation F).vle_one_iff,
      ← (NormedField.valuation (K := F)).vle_one_iff]
  letI : IsDiscreteValuationRing B :=
    hBF ▸ discrete_valuation_ring F
  letI : HenselianLocalRing B :=
    hBF ▸ integer_henselian_ring F
  exact inertia_equation_model
    K F B

end

end TBluepr
end Submission
