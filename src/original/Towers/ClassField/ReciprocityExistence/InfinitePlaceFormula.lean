import Towers.ClassField.BrauerLocalization.ArchimedeanData
import Towers.ClassField.LocalReciprocity.CyclicCase
import Towers.ClassField.LocalReciprocity.GaloisInvariantsQuotient
import Towers.ClassField.Reciprocity.CompletionArtinHom
import Towers.ClassField.ReciprocityExistence.InfiniteIdeleShapiro
import Towers.ClassField.ReciprocityExistence.LocalNormalization
import Towers.ClassField.BrauerLocalization.InfiniteNaturality

open scoped IsMulCommutative

/-!
# The infinite-place cup coordinate in Theorem VII.8.1

At an archimedean place the decomposition group has order one or two.  This
makes both normalizations occurring in the local comparison rigid: a local
norm-residue equivalence is unique, and so is an additive Brauer invariant
whose image is the standard two-torsion subgroup of `Q/Z`.
-/

namespace Towers.CField.RExist

open AbsoluteValue NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LFTheory
open Towers.CField.LClass
open Towers.CField.LRecip
open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.ICohomo
open Towers.CField.NIndex
open Towers.CField.HNorm
open Towers.CField.BLoc

noncomputable section

universe u

/-- The cyclic `H²` parameter of the literal invariant-character cup is
the class of its invariant coefficient modulo norms. -/
theorem cyclic_cup_parameter
    {n : ℕ} [NeZero n]
    {G M : Type u} [CommGroup G] [Fintype G]
    [CommGroup M] [MulDistribMulAction G M]
    (hn : 1 < n) (e : Multiplicative (ZMod n) ≃* G)
    (x : M) (hx : ∀ g : G, g • x = x) :
    GroupH2.mulInvariantsMod (M := M) e hn
        (invariantCharacterCup x hx
          (universeTransportedCharacter n G e)) =
      QuotientGroup.mk' (FMAct.norm G M).range ⟨x, hx⟩ := by
  let piG : FMAct.invariants G M := ⟨x, hx⟩
  let pi : GroupH2.pulledInvariants (M := M) e :=
    (GroupH2.invariantsMulEquiv e).symm piG
  have hcup := invariant_universe_transported
    n G M e pi
  have hcup' :
      invariantCharacterCup x hx
          (universeTransportedCharacter n G e) =
        universeTransportedCarry n G M e pi := by
    simpa [pi, piG] using hcup
  rw [hcup', universe_transported_carry hn e pi]
  rfl

/-- The two-torsion subgroup of `Q/Z` has a unique nonzero element. -/
theorem invariant_torsion_ne
    {x y : LocalInvariant} (hx2 : 2 • x = 0) (hy2 : 2 • y = 0)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) : x = y := by
  let xt : localInvariantTorsion 2 := ⟨x, hx2⟩
  let yt : localInvariantTorsion 2 := ⟨y, hy2⟩
  let q := (torsionZMod 2).symm
  rcases zmod_or_one (q xt) with hxt | hxt <;>
    rcases zmod_or_one (q yt) with hyt | hyt
  · exact (hx0 (congrArg Subtype.val
      (q.injective (hxt.trans (map_zero q).symm)))).elim
  · exact (hx0 (congrArg Subtype.val
      (q.injective (hxt.trans (map_zero q).symm)))).elim
  · exact (hy0 (congrArg Subtype.val
      (q.injective (hyt.trans (map_zero q).symm)))).elim
  · exact congrArg Subtype.val (q.injective (hxt.trans hyt.symm))

/-- A rational character of a cyclic group of order two is either zero or
the normalized injective character. -/
theorem rational_character_cases
    {G : Type u} [CommGroup G]
    (e : Multiplicative (ZMod 2) ≃* G)
    (chi : RationalCharacter G) :
    chi = 0 ∨
      chi = universeTransportedCharacter 2 G e := by
  let s : G := e (Multiplicative.ofAdd (1 : ZMod 2))
  let psi := universeTransportedCharacter 2 G e
  have hsne : s ≠ 1 := by
    intro hs
    have h := e.injective (hs.trans (map_one e).symm)
    norm_num [s] at h
  have hcases (g : G) : g = 1 ∨ g = s := by
    rcases zmod_or_one (e.symm g).toAdd with h | h
    · left
      apply e.symm.injective
      simpa using h
    · right
      apply e.symm.injective
      simpa [s] using h
  by_cases hchi : chi (Additive.ofMul s) = 0
  · left
    ext g
    change chi (Additive.ofMul g) = 0
    rcases hcases g with hg | hg
    · rw [hg]
      simp
    · rw [hg, hchi]
  · right
    ext g
    change chi (Additive.ofMul g) = psi (Additive.ofMul g)
    rcases hcases g with hg | hg
    · rw [hg]
      simp
    · rw [hg]
      have hs2 : s * s = 1 := by
        calc
          s * s = e (Multiplicative.ofAdd (1 : ZMod 2) *
              Multiplicative.ofAdd (1 : ZMod 2)) := (map_mul e _ _).symm
          _ = e 1 := by congr
          _ = 1 := map_one e
      have hchi2 : 2 • chi (Additive.ofMul s) = 0 := by
        rw [two_nsmul, ← map_add]
        change chi (Additive.ofMul (s * s)) = 0
        rw [hs2]
        simp
      have hpsi2 : 2 • psi (Additive.ofMul s) = 0 := by
        rw [two_nsmul, ← map_add]
        change psi (Additive.ofMul (s * s)) = 0
        rw [hs2]
        simp
      have hpsi : psi (Additive.ofMul s) ≠ 0 := by
        intro hzero
        have hinj := universe_transported_injective
          2 G e
        have h : Additive.ofMul s = 0 := hinj (by simpa using hzero)
        exact hsne (congrArg Additive.toMul h)
      exact invariant_torsion_ne
        hchi2 hpsi2 hchi hpsi

/-- Cupping with the zero character gives the trivial multiplicative
cohomology class. -/
theorem invariant_cup_zero
    {G M : Type u} [CommGroup G] [CommGroup M]
    [MulDistribMulAction G M]
    (x : M) (hx : ∀ g : G, g • x = x) :
    invariantCharacterCup x hx (0 : RationalCharacter G) = 1 := by
  rw [invariantCharacterCup]
  change MHTwo.mk _ = MHTwo.mk 1
  congr 1
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  change x ^ rationalBoundaryExponent
      (0 : RationalCharacter G) g h = 1
  have hlift (j : G) :
      rationalCharacterLift (0 : RationalCharacter G) j = 0 := by
    rw [rationalCharacterLift]
    change ((AddCircle.equivIco (1 : ℚ) 0
      (0 : AddCircle (1 : ℚ))).1 : ℚ) = 0
    simpa [rationalCharacterLift] using
      rational_character_lift (0 : RationalCharacter G)
  have hexp : rationalBoundaryExponent
      (0 : RationalCharacter G) g h = 0 := by
    have hq : ((rationalBoundaryExponent
        (0 : RationalCharacter G) g h : ℤ) : ℚ) = 0 := by
      rw [rational_boundary_spec]
      rw [hlift, hlift, hlift]
      ring
    exact_mod_cast hq
  simp only [hexp, zpow_zero]

/-- Abstract order-two form of the archimedean character formula.  The
only arithmetic input is the identification of invariant coefficients
modulo the action norm with the field norm quotient. -/
theorem cup_invariant_formula
    {G M A : Type u} [CommGroup G] [Fintype G]
    [CommGroup M] [MulDistribMulAction G M] [CommGroup A]
    (e : Multiplicative (ZMod 2) ≃* G)
    (embed : A →* M) (fixed : ∀ a g, g • embed a = embed a)
    (N : Subgroup A)
    (q : (FMAct.invariants G M ⧸
        (FMAct.norm G M).range) ≃* (A ⧸ N))
    (hq : ∀ a, q (QuotientGroup.mk' (FMAct.norm G M).range
        ⟨embed a, fixed a⟩) = QuotientGroup.mk' N a)
    (artin : (A ⧸ N) ≃* G)
    (F : MHTwo G M →* Multiplicative LocalInvariant)
    (hFinj : Function.Injective F)
    (hFtwo : ∀ z, 2 • (F z).toAdd = 0)
    (a : A) (chi : RationalCharacter G) :
    (F (invariantCharacterCup (embed a) (fixed a) chi)).toAdd =
      chi (Additive.ofMul (artin (QuotientGroup.mk' N a))) := by
  let psi := universeTransportedCharacter 2 G e
  let cup := invariantCharacterCup (embed a) (fixed a) psi
  let y := artin (QuotientGroup.mk' N a)
  rcases rational_character_cases e chi with hchi | hchi
  · subst chi
    rw [invariant_cup_zero]
    simp
  · rw [hchi]
    change (F cup).toAdd = psi (Additive.ofMul y)
    have hparameter :
        GroupH2.mulInvariantsMod (M := M) e (by omega)
            cup =
          QuotientGroup.mk' (FMAct.norm G M).range
            ⟨embed a, fixed a⟩ := by
      exact cyclic_cup_parameter (by omega) e (embed a) (fixed a)
    by_cases hy : y = 1
    · have haq : QuotientGroup.mk' N a = 1 := by
        apply artin.injective
        simpa [y] using hy
      have hcup : cup = 1 := by
        apply (GroupH2.mulInvariantsMod
          (M := M) e (by omega)).injective
        rw [hparameter, map_one]
        apply q.injective
        rw [hq, map_one, haq]
      rw [hcup, map_one, hy]
      simp
    · have hcup : cup ≠ 1 := by
        intro hcup
        have hparamOne :
            QuotientGroup.mk' (FMAct.norm G M).range
                ⟨embed a, fixed a⟩ = 1 := by
          rw [← hparameter, hcup, map_one]
        have haq : QuotientGroup.mk' N a = 1 := by
          rw [← hq]
          simpa using congrArg q hparamOne
        apply hy
        change artin (QuotientGroup.mk' N a) = 1
        rw [haq, map_one]
      have hFne : (F cup).toAdd ≠ 0 := by
        intro hzero
        apply hcup
        apply hFinj
        apply Multiplicative.toAdd.injective
        simpa using hzero
      have hpsine : psi (Additive.ofMul y) ≠ 0 := by
        intro hzero
        have hinj := universe_transported_injective
          2 G e
        have hy0 : Additive.ofMul y = 0 := hinj (by simpa using hzero)
        exact hy (congrArg Additive.toMul hy0)
      have hy2 : y * y = 1 := by
        rcases zmod_or_one
            (e.symm y).toAdd with hy0 | hy1
        · have : y = 1 := by
            apply e.symm.injective
            simpa using hy0
          exact (hy this).elim
        · have hys : y = e (Multiplicative.ofAdd (1 : ZMod 2)) := by
            apply e.symm.injective
            simpa using hy1
          rw [hys]
          calc
            e (Multiplicative.ofAdd (1 : ZMod 2)) *
                e (Multiplicative.ofAdd (1 : ZMod 2)) =
              e (Multiplicative.ofAdd (1 : ZMod 2) *
                Multiplicative.ofAdd (1 : ZMod 2)) := (map_mul e _ _).symm
            _ = e 1 := by congr
            _ = 1 := map_one e
      have hpsiTwo : 2 • psi (Additive.ofMul y) = 0 := by
        rw [two_nsmul, ← map_add]
        change psi (Additive.ofMul (y * y)) = 0
        rw [hy2]
        simp
      exact invariant_torsion_ne
        (hFtwo cup) hpsiTwo hFne hpsine

/-- The corresponding formula when the local decomposition group is
trivial. -/
theorem subsingleton_cup_formula
    {G M A : Type u} [CommGroup G] [Subsingleton G]
    [CommGroup M] [MulDistribMulAction G M] [CommGroup A]
    (embed : A →* M) (fixed : ∀ a g, g • embed a = embed a)
    (artin : A →* G)
    (F : MHTwo G M →* Multiplicative LocalInvariant)
    (a : A) (chi : RationalCharacter G) :
    (F (invariantCharacterCup (embed a) (fixed a) chi)).toAdd =
      chi (Additive.ofMul (artin a)) := by
  have hchi : chi = 0 := by
    ext g
    change chi (Additive.ofMul g) = 0
    rw [Subsingleton.elim g 1]
    simp
  rw [hchi, invariant_cup_zero, map_one]
  rfl

set_option maxHeartbeats 5000000 in
-- The archimedean cup comparison unfolds local invariants and transported Galois actions.
set_option synthInstance.maxHeartbeats 1000000 in
-- Both the real/complex completion tower and its local Galois group are synthesized here.
/-- Proposition III.3.6 at an infinite completion, in the multiplicative
crossed-product presentation used by the global idèle cup. -/
theorem archimedeanCupFormula
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (inv : Additive (BrauerGroup v.1.Completion) →+ LocalInvariant)
    (hinv : ArchimedeanBrauerInvariant K v inv)
    (a : v.1.Completionˣ) (chi : RationalCharacter Gal(L/K)) :
    let hwv := infinite_lies_comap v w.1 w.2
    letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    letI : Module.Finite v.1.Completion w.1.1.Completion :=
      infinite_completion_module (K := K) (L := L) v w
    letI : IsGalois v.1.Completion w.1.1.Completion :=
      infiniteHasseGalois K L v w
    let decomp : absoluteValueDecomposition v.1 w.1.1 ≃*
        Gal(w.1.1.Completion/v.1.Completion) :=
      infiniteDecompositionGroup v w.1
    letI : IsMulCommutative
        Gal(w.1.1.Completion/v.1.Completion) := by
      refine ⟨⟨fun sigma tau => decomp.symm.injective ?_⟩⟩
      simpa only [map_mul] using
        mul_comm (decomp.symm sigma) (decomp.symm tau)
    letI : CommGroup Gal(w.1.1.Completion/v.1.Completion) :=
      inferInstance
    inv (Additive.ofMul
        (((CProduc.hRelativeBrauer
            v.1.Completion w.1.1.Completion
            (invariantCharacterCup
              (Units.map (algebraMap v.1.Completion
                w.1.1.Completion) a)
              (fun sigma => by
                apply Units.ext
                exact sigma.commutes a)
              (chi.comp
                ((absoluteValueDecomposition v.1 w.1.1).subtype.comp
                  decomp.symm.toMonoidHom).toAdditive))) :
          relativeBrauerGroup v.1.Completion w.1.1.Completion) :
        BrauerGroup v.1.Completion)) =
      chi (Additive.ofMul (infiniteGlobalArtin v w a)) := by
  let hwv := infinite_lies_comap v w.1 w.2
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  let D := absoluteValueDecomposition v.1 w.1.1
  let H := Gal(w.1.1.Completion/v.1.Completion)
  let decomp : D ≃* H := infiniteDecompositionGroup v w.1
  letI : IsMulCommutative H := by
    refine ⟨⟨fun sigma tau ↦ decomp.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decomp.symm sigma) (decomp.symm tau)
  letI : CommGroup H := inferInstance
  let intoGlobal : H →* Gal(L/K) :=
    D.subtype.comp decomp.symm.toMonoidHom
  let localChi : RationalCharacter H := chi.comp intoGlobal.toAdditive
  let embed : v.1.Completionˣ →* w.1.1.Completionˣ :=
    Units.map (algebraMap v.1.Completion w.1.1.Completion)
  have fixed (b : v.1.Completionˣ) (g : H) : g • embed b = embed b :=
    multiplicative_base_fixed
      v.1.Completion w.1.1.Completion b g
  let F : MHTwo H w.1.1.Completionˣ →*
      Multiplicative LocalInvariant :=
    inv.toMultiplicative.comp
      ((relativeBrauerGroup v.1.Completion
          w.1.1.Completion).subtype.comp
        (CProduc.hRelativeBrauer
          v.1.Completion w.1.1.Completion).toMonoidHom)
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply (CProduc.hRelativeBrauer
      v.1.Completion w.1.1.Completion).injective
    apply Subtype.ext
    apply hinv.1
    exact congrArg Multiplicative.toAdd hxy
  have hDcases : Nat.card D = 1 ∨ Nat.card D = 2 := by
    have hstabilizer : D = MulAction.stabilizer Gal(L/K) w.1 := by
      change absoluteValueDecomposition v.1 w.1.1 = _
      rw [absolute_decomposition_stabilizer]
      ext sigma
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
      constructor
      · intro h
        apply InfinitePlace.ext
        exact fun x ↦ DFunLike.congr_fun h x
      · intro h
        exact congrArg (fun z : InfinitePlace L ↦ z.1) h
    rw [hstabilizer]
    exact InfinitePlace.nat_card_stabilizer_eq_one_or_two K w.1
  have hcard : Nat.card H = 1 ∨ Nat.card H = 2 := by
    have h := Nat.card_congr decomp.toEquiv
    omega
  let artinLocal :
      (v.1.Completionˣ ⧸ normSubgroup v.1.Completion
        w.1.1.Completion) ≃* H :=
    (infinitePlaceArtin v w).trans decomp
  have hglobalArtin :
      intoGlobal (artinLocal (QuotientGroup.mk'
        (normSubgroup v.1.Completion w.1.1.Completion) a)) =
        infiniteGlobalArtin v w a := by
    change D.subtype
        (decomp.symm (decomp
          (infinitePlaceArtin v w
            (QuotientGroup.mk'
              (normSubgroup v.1.Completion w.1.1.Completion) a)))) =
      D.subtype
        (infinitePlaceArtin v w
          (QuotientGroup.mk'
            (normSubgroup v.1.Completion w.1.1.Completion) a))
    rw [decomp.symm_apply_apply]
  rcases hcard with hcard | hcard
  · letI : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hcard).1
    have hlocal := subsingleton_cup_formula
      embed fixed
      (artinLocal.toMonoidHom.comp
        (QuotientGroup.mk' (normSubgroup v.1.Completion
          w.1.1.Completion))) F a localChi
    change (F (invariantCharacterCup (embed a) (fixed a)
      localChi)).toAdd = _
    calc
      _ = localChi (Additive.ofMul
          (artinLocal (QuotientGroup.mk'
            (normSubgroup v.1.Completion w.1.1.Completion) a))) := hlocal
      _ = chi (Additive.ofMul
          (infiniteGlobalArtin v w a)) := by
        change chi (Additive.ofMul
          (intoGlobal (artinLocal (QuotientGroup.mk'
            (normSubgroup v.1.Completion w.1.1.Completion) a)))) = _
        rw [hglobalArtin]
  · have hvreal : InfinitePlace.IsReal v := by
      by_contra hv
      have hvcomplex : InfinitePlace.IsComplex v :=
        InfinitePlace.not_isReal_iff_isComplex.mp hv
      letI : IsAlgClosed v.1.Completion :=
        alg_closed_ring
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            hvcomplex).symm
      have hsurj : Function.Surjective
          (algebraMap v.1.Completion w.1.1.Completion) :=
        IsAlgClosed.algebraMap_bijective_of_isIntegral.2
      have hsub : Subsingleton H := by
        constructor
        intro sigma tau
        ext x
        obtain ⟨b, rfl⟩ := hsurj x
        rw [sigma.commutes, tau.commutes]
      have hone : Nat.card H = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩
      omega
    have hFtwo (z : MHTwo H w.1.1.Completionˣ) :
        2 • (F z).toAdd = 0 := by
      have hzrange : (F z).toAdd ∈ Set.range inv := by
        refine ⟨Additive.ofMul
          (((CProduc.hRelativeBrauer
              v.1.Completion w.1.1.Completion z :
            relativeBrauerGroup v.1.Completion w.1.1.Completion) :
              BrauerGroup v.1.Completion)), ?_⟩
        rfl
      change (F z).toAdd ∈ {x : LocalInvariant | 2 • x = 0}
      rw [← hinv.2.1 hvreal]
      exact hzrange
    letI : IsCyclic H :=
      isCyclic_of_card_dvd_prime (p := 2) (by rw [hcard])
    let e : Multiplicative (ZMod 2) ≃* H := by
      apply mulEquivOfCyclicCardEq
      simpa using hcard.symm
    have hlocal := cup_invariant_formula e embed fixed
      (normSubgroup v.1.Completion w.1.1.Completion)
      (galoisInvariantsUniverse
        v.1.Completion w.1.1.Completion)
      (galois_invariants_universe
        v.1.Completion w.1.1.Completion)
      artinLocal F hFinj hFtwo a localChi
    change (F (invariantCharacterCup (embed a) (fixed a)
      localChi)).toAdd = _
    calc
      _ = localChi (Additive.ofMul
          (artinLocal (QuotientGroup.mk'
            (normSubgroup v.1.Completion w.1.1.Completion) a))) := hlocal
      _ = chi (Additive.ofMul
          (infiniteGlobalArtin v w a)) := by
        change chi (Additive.ofMul
          (intoGlobal (artinLocal (QuotientGroup.mk'
            (normSubgroup v.1.Completion w.1.1.Completion) a)))) = _
        rw [hglobalArtin]

set_option maxHeartbeats 3000000 in
-- Relabelling the cup unfolds the chosen-place stabilizer and completion comparison.
set_option synthInstance.maxHeartbeats 1000000 in
-- The dependent stabilizer action requires the completion algebra instances simultaneously.
/-- Relabelling the local archimedean cup by the chosen-place stabilizer
gives the literal stabilizer cup produced by infinite-place Shapiro. -/
theorem infinite_stabilizer_cup
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v)
    (a : v.1.Completionˣ) (chi : RationalCharacter Gal(L/K)) :
    let hwv := infinite_lies_comap v w.1 w.2
    let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
    letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    letI : Module.Finite v.1.Completion w.1.1.Completion :=
      infinite_completion_module (K := K) (L := L) v w
    letI : IsGalois v.1.Completion w.1.1.Completion :=
      infiniteHasseGalois K L v w
    let decomp := infiniteCompletionStabilizer
      (K := K) (L := L) v w
    letI : IsMulCommutative
        Gal(w.1.1.Completion/v.1.Completion) := by
      refine ⟨⟨fun sigma tau ↦ decomp.symm.injective ?_⟩⟩
      simpa only [map_mul] using
        mul_comm (decomp.symm sigma) (decomp.symm tau)
    letI : MulDistribMulAction (CompletionPlaceStabilizer v.1 w0)
        w.1.1.Completionˣ :=
      completionDistribAction v.1 w0
    let intoGlobal : Gal(w.1.1.Completion/v.1.Completion) →* Gal(L/K) :=
      (CompletionPlaceStabilizer v.1 w0).subtype.comp
        decomp.symm.toMonoidHom
    infinite2Stabilizer
        (K := K) (L := L) v w
        (invariantCharacterCup
          (Units.map (algebraMap v.1.Completion w.1.1.Completion) a)
          (multiplicative_base_fixed
            v.1.Completion w.1.1.Completion a)
          (chi.comp intoGlobal.toAdditive)) =
      invariantCharacterCup
        (Units.map
          (completionLies v.1 w.1.1 hwv).toMonoidHom a)
        (fun h => by
          apply Units.ext
          change stabilizerRingHom v.1 w0 h
              (algebraMap v.1.Completion w.1.1.Completion a) =
            algebraMap v.1.Completion w.1.1.Completion a
          let eh : Gal(w.1.1.Completion/v.1.Completion) := decomp h
          change eh (algebraMap v.1.Completion w.1.1.Completion a) =
            algebraMap v.1.Completion w.1.1.Completion a
          exact eh.commutes a)
        (chi.comp
          (CompletionPlaceStabilizer v.1 w0).subtype.toAdditive) := by
  let hwv := infinite_lies_comap v w.1 w.2
  let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  let decomp := infiniteCompletionStabilizer
    (K := K) (L := L) v w
  letI : IsMulCommutative
      Gal(w.1.1.Completion/v.1.Completion) := by
    refine ⟨⟨fun sigma tau ↦ decomp.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decomp.symm sigma) (decomp.symm tau)
  letI : MulDistribMulAction (CompletionPlaceStabilizer v.1 w0)
      w.1.1.Completionˣ :=
    completionDistribAction v.1 w0
  let intoGlobal : Gal(w.1.1.Completion/v.1.Completion) →* Gal(L/K) :=
    (CompletionPlaceStabilizer v.1 w0).subtype.comp
      decomp.symm.toMonoidHom
  dsimp only
  unfold infinite2Stabilizer
  rw [invariant_cup_restriction]
  have hchar :
      (chi.comp intoGlobal.toAdditive).comp
          decomp.toMonoidHom.toAdditive =
        chi.comp
          (CompletionPlaceStabilizer v.1 w0).subtype.toAdditive := by
    ext t
    simp [intoGlobal, decomp]
  rw [hchar]
  rfl

set_option maxHeartbeats 3000000 in
-- Comparing the two degree-two classes unfolds the resized completion representation.
set_option synthInstance.maxHeartbeats 1000000 in
-- The absolute and relative Brauer transports synthesize their completion fields together.
/-- The chosen-completion comparison at an infinite place represents the
same absolute Brauer class as the original local multiplicative `H²` class. -/
theorem infinite_multiplicative_2
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (data : BData K)
    (v : InfinitePlace K) :
    let completion := completionChoice K L
    let w := completion.infiniteUpper v
    let hwv := infinite_lies_comap v w.1 w.2
    let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
    letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
    letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    letI : Module.Finite v.1.Completion w.1.1.Completion :=
      infinite_completion_module (K := K) (L := L) v w
    letI : IsGalois v.1.Completion w.1.1.Completion :=
      infiniteHasseGalois K L v w
    ∀ x : MHTwo Gal(w.1.1.Completion/v.1.Completion)
        w.1.1.Completionˣ,
      data.placeInvariant.invariant (.inr v)
          (localBrauerInclusion K L completion (.inr v)
            ((resizedChosen2
                K L completion (.inr v)).symm
              ((uliftHasseNorm
                  (K := K) (L := L) v.1 w0).symm
                ((infiniteHStabilizer
                    (K := K) (L := L) v w)
                  (multiplicativeLiftAdditive x))))) =
        data.placeInvariant.invariant (.inr v)
          (Additive.ofMul
            (((CProduc.hRelativeBrauer
                v.1.Completion w.1.1.Completion x :
              relativeBrauerGroup v.1.Completion w.1.1.Completion) :
              BrauerGroup v.1.Completion))) := by
  let completion := completionChoice K L
  let w := completion.infiniteUpper v
  let hwv := infinite_lies_comap v w.1 w.2
  let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
  letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  dsimp only
  intro x
  have hcoordinate :
      (resizedChosen2
          K L completion (.inr v)).symm
          ((uliftHasseNorm
              (K := K) (L := L) v.1 w0).symm
            ((infiniteHStabilizer
                (K := K) (L := L) v w)
              (multiplicativeLiftAdditive x))) =
        (relativeBrauer2
          v.1.Completion w.1.1.Completion).symm
            (multiplicativeLiftAdditive x) := by
    change (relativeBrauer2
        v.1.Completion w.1.1.Completion).symm
      ((infiniteHStabilizer
          (K := K) (L := L) v w).symm
        ((uliftHasseNorm
            (K := K) (L := L) v.1 w0)
          ((uliftHasseNorm
              (K := K) (L := L) v.1 w0).symm
            ((infiniteHStabilizer
                (K := K) (L := L) v w)
              (multiplicativeLiftAdditive x))))) = _
    rw [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  rw [hcoordinate]
  change data.placeInvariant.invariant (.inr v)
      (Additive.ofMul
        ((((relativeBrauer2
            v.1.Completion w.1.1.Completion).symm
          (multiplicativeLiftAdditive x)).toMul :
            relativeBrauerGroup v.1.Completion w.1.1.Completion) :
          BrauerGroup v.1.Completion)) = _
  rw [resized_multiplicative_2]

set_option maxHeartbeats 15000000 in
-- The global cup coordinate combines Shapiro, completion transport, and the local formula.
set_option synthInstance.maxHeartbeats 1000000 in
-- Its dependent infinite-place tower requires a deeper local Galois instance search.
set_option maxRecDepth 100000 in
/-- The infinite coordinate of the literal global idèle cup satisfies the
canonical archimedean local character formula. -/
theorem infinite_cup_invariant
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (data : BData K)
    (v : InfinitePlace K)
    (a : IdeleGroup (NumberField.RingOfIntegers K) K)
    (chi : RationalCharacter Gal(L/K)) :
    data.placeInvariant.invariant (.inr v)
        (multiplicativeIdeleCup K L chi
          (Additive.ofMul a) (.inr v)) =
      chi (Additive.ofMul
        (infiniteGlobalArtin v
          ((completionChoice K L).infiniteUpper v)
          (MulEquiv.piUnits a.1 v))) := by
  let completion := completionChoice K L
  let w := completion.infiniteUpper v
  let hwv := infinite_lies_comap v w.1 w.2
  let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
  letI : Fact v.1.IsNontrivial := ⟨infinite_place_nontrivial v⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v.1) :=
    places_above_pretransitive v
  let decomp := infiniteCompletionStabilizer
    (K := K) (L := L) v w
  letI : IsMulCommutative
      Gal(w.1.1.Completion/v.1.Completion) := by
    refine ⟨⟨fun sigma tau ↦ decomp.symm.injective ?_⟩⟩
    simpa only [map_mul] using
      mul_comm (decomp.symm sigma) (decomp.symm tau)
  letI : MulDistribMulAction (CompletionPlaceStabilizer v.1 w0)
      w.1.1.Completionˣ := completionDistribAction v.1 w0
  let intoGlobal : Gal(w.1.1.Completion/v.1.Completion) →* Gal(L/K) :=
    (CompletionPlaceStabilizer v.1 w0).subtype.comp
      decomp.symm.toMonoidHom
  let localA : v.1.Completionˣ := MulEquiv.piUnits a.1 v
  let localCup : MHTwo
      Gal(w.1.1.Completion/v.1.Completion) w.1.1.Completionˣ :=
    invariantCharacterCup
      (Units.map (algebraMap v.1.Completion w.1.1.Completion) localA)
      (multiplicative_base_fixed
        v.1.Completion w.1.1.Completion localA)
      (chi.comp intoGlobal.toAdditive)
  let coordinate := resizedHDecomposition
    (K := K) (L := L)
    (globalMultiplicative2 K L a chi) (.inr v)
  have hshapiro := global_multiplicative_shapiro
    (K := K) (L := L) v a chi
  have hstabilizer := infinite_stabilizer_cup
    K L v w localA chi
  have hlocalRelabel :=
    infinite_stabilizer_multiplicative
      (K := K) (L := L) v w localCup
  have hchosen :
      resizedPlaceStabilizer
          (K := K) (L := L) completion (.inr v) coordinate =
        (uliftHasseNorm
          (K := K) (L := L) v.1 w0).symm
          ((infiniteHStabilizer
            (K := K) (L := L) v w)
            (multiplicativeLiftAdditive localCup)) := by
    change uliftCompletionUnits
        (K := K) (L := L) v.1 w0 coordinate = _
    rw [hshapiro]
    apply (uliftHasseNorm
      (K := K) (L := L) v.1 w0).injective
    rw [AddEquiv.apply_symm_apply, hlocalRelabel]
    have hcup :
        invariantCharacterCup
            (infiniteChosenMonoid
              (K := K) (L := L) v w
              (ideleExtensionMonoid (K := K) (L := L) a))
            (fun h => by
              rw [← chosen_monoid_equivariant
                (K := K) (L := L) v w h]
              exact congrArg
                (infiniteChosenMonoid
                  (K := K) (L := L) v w)
                (global_multiplicative_fixed K L a h))
            (chi.comp
              (CompletionPlaceStabilizer v.1 w0).subtype.toAdditive) =
          infinite2Stabilizer
            (K := K) (L := L) v w localCup := by
      rw [hstabilizer]
      congr 1
      exact chosen_monoid_extension
        (K := K) (L := L) v w a
    rw [hcup]
    obtain ⟨c, hc⟩ := MHTwo.exists_mk_eq
      (infinite2Stabilizer
        (K := K) (L := L) v w localCup)
    rw [← hc]
    change groupCohomology.map
        (MonoidHom.id (CompletionPlaceStabilizer v.1 w0))
        (uliftIsoHasse
          (K := K) (L := L) v.1 w0).hom 2
        (normalizedCocycleU c) =
      normalizedCocycleU c
    rw [normalizedCocycleU,
      groupCohomology.H2π_comp_map_apply]
    congr 1
  have hrelative :
      completionRelativeBrauer
          (K := K) (L := L) completion (.inr v) coordinate =
        (resizedChosen2
            K L completion (.inr v)).symm
          ((uliftHasseNorm
              (K := K) (L := L) v.1 w0).symm
            ((infiniteHStabilizer
                (K := K) (L := L) v w)
              (multiplicativeLiftAdditive localCup))) := by
    change (resizedChosen2
        K L completion (.inr v)).symm
      (resizedPlaceStabilizer
        (K := K) (L := L) completion (.inr v) coordinate) = _
    rw [hchosen]
  rw [global_multiplicative_infinite]
  rw [hrelative]
  rw [infinite_multiplicative_2
    K L data v localCup]
  exact archimedeanCupFormula K L v w
    (data.placeInvariant.invariant (.inr v))
    (data.placeInvariant.infinite_isCanonical v) localA chi

/-- The axiomatic normalization used in Theorem VII.8.1 determines an
archimedean Brauer invariant uniquely. -/
theorem archimedean_brauer_unique
    (K : Type u) [Field K] [NumberField K]
    (v : InfinitePlace K)
    (f g : Additive
        (BrauerGroup (placeCompletion K (.inr v))) →+ LocalInvariant)
    (hf : ArchimedeanBrauerInvariant K v f)
    (hg : ArchimedeanBrauerInvariant K v g) :
    f = g := by
  apply DFunLike.ext _ _
  intro x
  classical
  by_cases hv : InfinitePlace.IsReal v
  · have hfx : 2 • f x = 0 := by
      have : f x ∈ Set.range f := ⟨x, rfl⟩
      simpa [hf.2.1 hv] using this
    have hgx : 2 • g x = 0 := by
      have : g x ∈ Set.range g := ⟨x, rfl⟩
      simpa [hg.2.1 hv] using this
    let fx : localInvariantTorsion 2 := ⟨f x, hfx⟩
    let gx : localInvariantTorsion 2 := ⟨g x, hgx⟩
    let e := (torsionZMod 2).symm
    rcases zmod_or_one (e fx) with hfx0 | hfx1 <;>
      rcases zmod_or_one (e gx) with hgx0 | hgx1
    · exact congrArg Subtype.val (e.injective (hfx0.trans hgx0.symm))
    · have hx0 : x = 0 := by
        apply hf.1
        rw [map_zero]
        exact congrArg Subtype.val
          (e.injective (hfx0.trans (map_zero e).symm))
      subst x
      simp
    · have hx0 : x = 0 := by
        apply hg.1
        rw [map_zero]
        exact congrArg Subtype.val
          (e.injective (hgx0.trans (map_zero e).symm))
      subst x
      simp
    · exact congrArg Subtype.val (e.injective (hfx1.trans hgx1.symm))
  · have hc : InfinitePlace.IsComplex v :=
      InfinitePlace.not_isReal_iff_isComplex.mp hv
    have hfr := hf.2.2 hc
    have hgr := hg.2.2 hc
    have hfx : f x = 0 := by
      have : f x ∈ Set.range f := ⟨x, rfl⟩
      simpa [hfr] using this
    have hgx : g x = 0 := by
      have : g x ∈ Set.range g := ⟨x, rfl⟩
      simpa [hgr] using this
    rw [hfx, hgx]

end

end Towers.CField.RExist
