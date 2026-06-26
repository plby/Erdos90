import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.RingTheory.SimpleRing.Congr
import Submission.ClassField.ReciprocityExistence.PlaceCompletion
import Submission.ClassField.LocalBrauer.RealBrauerGroup
import Submission.ClassField.LocalBrauer.LocalInvariantTorsion

/-!
# Archimedean invariant data for Theorem VIII.4.2

This file constructs the canonical invariants at all archimedean places.  A
finite-dimensional universe shrink extends the real central-simple-algebra
classification to arbitrary completion universes; this yields the real
Brauer equivalence with `ZMod 2` without assuming a pre-existing Brauer-group
transport functor.
-/

namespace Submission.CField.BLoc

open NumberField
open Submission.CField.BGroups
open Submission.CField.LBrauer
open Submission.CField.RExist
open scoped Quaternion

noncomputable section

universe u v

/-- The real central-simple-algebra classification is independent of the
universe containing the algebra.  We shrink a finite-dimensional algebra to
`Type`, apply the small-universe computation of the real Brauer group, and
transport the resulting algebra equivalence back. -/
theorem hamilton_any_universe
    (A : Type u) [Ring A] [Algebra ℝ A] [IsSimpleRing A]
    [Algebra.IsCentral ℝ A] [Module.Finite ℝ A] :
    (∃ n : ℕ, n ≠ 0 ∧
      Nonempty (A ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ)) ∨
    (∃ n : ℕ, n ≠ 0 ∧
      Nonempty (A ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℍ[ℝ])) := by
  letI : Small.{0} A := Module.Finite.small ℝ A
  letI : IsSimpleRing (Shrink.{0} A) :=
    IsSimpleRing.of_ringEquiv (Shrink.ringEquiv A).symm inferInstance
  letI : Algebra.IsCentral ℝ (Shrink.{0} A) := by
    constructor
    intro x hx
    have hx' : (Shrink.algEquiv ℝ A x) ∈ Subalgebra.center ℝ A :=
      (MulEquivClass.apply_mem_center_iff (Shrink.algEquiv ℝ A)).mpr hx
    obtain ⟨r, hr⟩ := (Algebra.IsCentral.center_eq_bot ℝ A).le hx'
    refine ⟨r, (Shrink.algEquiv ℝ A).injective ?_⟩
    simpa using hr
  rcases simple_matrix_hamilton
      (Shrink.{0} A) with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact Or.inl ⟨n, hn, ⟨(Shrink.algEquiv ℝ A).symm.trans e⟩⟩
  · exact Or.inr ⟨n, hn, ⟨(Shrink.algEquiv ℝ A).symm.trans e⟩⟩

/-- Hamilton's quaternion algebra transported to a field ring-equivalent to
`R`.  `ULift` keeps the carrier in the same universe as the base field, as
required by the current same-universe Brauer-group multiplication. -/
noncomputable def realHamiltonCSA
    (E : Type u) [Field E] (e : E ≃+* ℝ) : CSA.{u, u} E := by
  letI : Algebra E ℝ := RingHom.toAlgebra e.toRingHom
  let eER : E ≃ₐ[E] ℝ :=
    AlgEquiv.ofRingEquiv (f := e) (fun x ↦ by
      change e x = e x
      rfl)
  letI : Module.Finite E ℝ := Module.Finite.equiv eER.toLinearEquiv
  letI : Module.Finite E ℍ[ℝ] := Module.Finite.trans ℝ ℍ[ℝ]
  letI : Algebra.IsCentral E ℍ[ℝ] := by
    constructor
    intro x hx
    have hxR : x ∈ Subalgebra.center ℝ ℍ[ℝ] := hx
    obtain ⟨r, hr⟩ := (Algebra.IsCentral.center_eq_bot ℝ ℍ[ℝ]).le hxR
    refine ⟨e.symm r, ?_⟩
    calc
      algebraMap E ℍ[ℝ] (e.symm r) =
          algebraMap ℝ ℍ[ℝ] (e (e.symm r)) := rfl
      _ = algebraMap ℝ ℍ[ℝ] r := by rw [e.apply_symm_apply]
      _ = x := hr
  letI : IsSimpleRing (ULift.{u} ℍ[ℝ]) :=
    IsSimpleRing.of_ringEquiv
      (ULift.ringEquiv (R := ℍ[ℝ])).symm inferInstance
  letI : Algebra.IsCentral E (ULift.{u} ℍ[ℝ]) := by
    constructor
    intro x hx
    have hx' : (ULift.algEquiv (R := E) (A := ℍ[ℝ]) x) ∈
        Subalgebra.center E ℍ[ℝ] :=
      (MulEquivClass.apply_mem_center_iff
        (ULift.algEquiv (R := E) (A := ℍ[ℝ]))).mpr hx
    obtain ⟨r, hr⟩ := (Algebra.IsCentral.center_eq_bot E ℍ[ℝ]).le hx'
    refine ⟨r, (ULift.algEquiv (R := E) (A := ℍ[ℝ])).injective ?_⟩
    simpa using hr
  exact centralSimpleCSA E (ULift.{u} ℍ[ℝ])

/-- Over a field ring-equivalent to `R`, every central simple algebra is
Brauer-equivalent either to the base field or to transported Hamilton
quaternions. -/
theorem simple_equivalent_hamilton
    (E : Type u) [Field E] (e : E ≃+* ℝ)
    (A : Type u) [Ring A] [Algebra E A] [IsSimpleRing A]
    [Algebra.IsCentral E A] [Module.Finite E A] :
    IsBrauerEquivalent (centralSimpleCSA E A) (baseFieldCSA E) ∨
      IsBrauerEquivalent (centralSimpleCSA E A)
        (realHamiltonCSA E e) := by
  letI : Algebra ℝ E := RingHom.toAlgebra e.symm.toRingHom
  letI : Algebra ℝ A :=
    RingHom.toAlgebra'
      (((algebraMap E A).comp e.symm.toRingHom) : ℝ →+* A)
      (fun r x ↦ Algebra.commutes (e.symm r) x)
  letI : IsScalarTower ℝ E A := IsScalarTower.of_algebraMap_eq' rfl
  let eRE : ℝ ≃ₐ[ℝ] E :=
    AlgEquiv.ofRingEquiv (f := e.symm) (fun _ ↦ rfl)
  letI : Module.Finite ℝ E := Module.Finite.equiv eRE.toLinearEquiv
  letI : Module.Finite ℝ A := Module.Finite.trans E A
  letI : Algebra.IsCentral ℝ A := by
    constructor
    intro x hx
    have hxE : x ∈ Subalgebra.center E A := hx
    obtain ⟨y, hy⟩ := (Algebra.IsCentral.center_eq_bot E A).le hxE
    refine ⟨e y, ?_⟩
    calc
      algebraMap ℝ A (e y) = algebraMap E A (e.symm (e y)) := rfl
      _ = algebraMap E A y := by rw [e.symm_apply_apply]
      _ = x := hy
  rcases hamilton_any_universe A with
      ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  · left
    letI : Algebra E ℝ := RingHom.toAlgebra e.toRingHom
    let fE : A ≃ₐ[E] Matrix (Fin n) (Fin n) ℝ :=
      AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun x ↦ by
        calc
          f (algebraMap E A x) = f (algebraMap ℝ A (e x)) := by
            congr 1
            exact congrArg (algebraMap E A) (e.symm_apply_apply x).symm
          _ = algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) (e x) :=
            f.commutes (e x)
          _ = algebraMap E (Matrix (Fin n) (Fin n) ℝ) x := by rfl)
    let eRE' : ℝ ≃ₐ[E] E :=
      AlgEquiv.ofRingEquiv (f := e.symm) (fun x ↦ e.symm_apply_apply x)
    exact brauer_equivalent_matrix E _ n hn
      (fE.trans eRE'.mapMatrix)
  · right
    letI : Algebra E ℝ := RingHom.toAlgebra e.toRingHom
    let fE : A ≃ₐ[E] Matrix (Fin n) (Fin n) ℍ[ℝ] :=
      AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun x ↦ by
        calc
          f (algebraMap E A x) = f (algebraMap ℝ A (e x)) := by
            congr 1
            exact congrArg (algebraMap E A) (e.symm_apply_apply x).symm
          _ = algebraMap ℝ (Matrix (Fin n) (Fin n) ℍ[ℝ]) (e x) :=
            f.commutes (e x)
          _ = algebraMap E (Matrix (Fin n) (Fin n) ℍ[ℝ]) x := by rfl)
    refine ⟨1, n, one_ne_zero, hn, ?_⟩
    change Nonempty (Matrix (Fin 1) (Fin 1) A ≃ₐ[E]
      Matrix (Fin n) (Fin n) (realHamiltonCSA E e))
    dsimp only [realHamiltonCSA]
    refine ⟨?_⟩
    change Matrix (Fin 1) (Fin 1) A ≃ₐ[E]
      Matrix (Fin n) (Fin n) (ULift.{u} ℍ[ℝ])
    exact (matrixFinAlg E A).trans <|
      fE.trans (ULift.algEquiv (R := E) (A := ℍ[ℝ])).symm.mapMatrix

/-- The transported Hamilton class remains nontrivial.  The proof transports
any hypothetical matrix presentation back to the ordinary real Hamilton
algebra, contradicting `hamilton_brauer_ne`. -/
theorem real_hamilton_brauer
    (E : Type u) [Field E] (e : E ≃+* ℝ) :
    brauerClass E (realHamiltonCSA E e) ≠
      (1 : BrauerGroup E) := by
  intro h
  letI : Algebra E ℝ := RingHom.toAlgebra e.toRingHom
  obtain ⟨n, hn, ⟨f⟩⟩ :=
    (brauer_alg_matrix E
      (realHamiltonCSA E e)).1 h
  dsimp only [realHamiltonCSA] at f
  change ULift.{u} ℍ[ℝ] ≃ₐ[E] Matrix (Fin n) (Fin n) E at f
  letI : Algebra ℝ E := RingHom.toAlgebra e.symm.toRingHom
  let fR : ULift.{u} ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin n) (Fin n) E :=
    AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun r ↦ by
      calc
        f (algebraMap ℝ (ULift.{u} ℍ[ℝ]) r) =
            f (algebraMap E (ULift.{u} ℍ[ℝ]) (e.symm r)) := by
              congr 1
              apply ULift.down_injective
              change algebraMap ℝ ℍ[ℝ] r =
                algebraMap ℝ ℍ[ℝ] (e (e.symm r))
              rw [e.apply_symm_apply]
        _ = algebraMap E (Matrix (Fin n) (Fin n) E) (e.symm r) :=
          f.commutes (e.symm r)
        _ = algebraMap ℝ (Matrix (Fin n) (Fin n) E) r := by rfl)
  let eER : E ≃ₐ[ℝ] ℝ :=
    AlgEquiv.ofRingEquiv (f := e) (fun r ↦ by
      change e (e.symm r) = r
      exact e.apply_symm_apply r)
  let small : ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (ULift.algEquiv (R := ℝ) (A := ℍ[ℝ])).symm |>.trans <|
      fR.trans eER.mapMatrix
  apply hamilton_brauer_ne
  rw [brauer_alg_matrix]
  exact ⟨n, hn, ⟨small⟩⟩

/-- Every Brauer class over a field ring-equivalent to `R` is either the
identity or the transported Hamilton class. -/
theorem real_or_hamilton
    (E : Type u) [Field E] (e : E ≃+* ℝ) (x : BrauerGroup E) :
    x = 1 ∨ x = brauerClass E (realHamiltonCSA E e) := by
  induction x using Quotient.inductionOn with
  | _ A =>
      rcases
          simple_equivalent_hamilton
            E e A with hA | hA
      · left
        change brauerClass E A = brauerClass E (baseFieldCSA E)
        exact (brauer_class E A (baseFieldCSA E)).2 hA
      · right
        exact (brauer_class E A
          (realHamiltonCSA E e)).2 hA

/-- Every element of `ZMod 2` is represented by `0` or `1`. -/
theorem zmod_or_one (a : ZMod 2) :
    a = 0 ∨ a = 1 := by
  have hlt := a.val_lt
  have ha : a.val = 0 ∨ a.val = 1 := by omega
  rcases ha with ha | ha
  · left
    apply ZMod.val_injective
    simpa using ha
  · right
    apply ZMod.val_injective
    simpa using ha

/-- The transported Hamilton class has order two. -/
theorem real_hamilton_self
    (E : Type u) [Field E] (e : E ≃+* ℝ) :
    brauerClass E (realHamiltonCSA E e) *
        brauerClass E (realHamiltonCSA E e) = 1 := by
  let h := brauerClass E (realHamiltonCSA E e)
  rcases real_or_hamilton E e (h * h) with
      hsq | hsq
  · exact hsq
  · change h * h = h at hsq
    have heq : h = 1 := by
      calc
        h = h⁻¹ * (h * h) := by simp
        _ = h⁻¹ * h := by rw [hsq]
        _ = 1 := by simp
    exact (real_hamilton_brauer E e heq).elim

/-- The coordinate homomorphism which sends the base-field Brauer class to
`0` and the transported Hamilton class to `1` in `ZMod 2`. -/
noncomputable def realBrauerZ
    (E : Type u) [Field E] (e : E ≃+* ℝ) :
    BrauerGroup E →* Multiplicative (ZMod 2) := by
  classical
  exact
    { toFun := fun x ↦
        if x = 1 then Multiplicative.ofAdd 0 else Multiplicative.ofAdd 1
      map_one' := by simp
      map_mul' := fun x y ↦ by
        let h := brauerClass E (realHamiltonCSA E e)
        have hne : h ≠ 1 := real_hamilton_brauer E e
        have hsq : h * h = 1 :=
          real_hamilton_self E e
        rcases real_or_hamilton E e x with rfl | rfl <;>
          rcases real_or_hamilton E e y with rfl | rfl <;>
          simp only [h, hne, hsq, ofAdd_zero, mul_one, one_mul, if_false,
            if_true]
        change (0 : ZMod 2) = 1 + 1
        decide }

/-- The two-class coordinate homomorphism is bijective. -/
theorem real_z_bijective
    (E : Type u) [Field E] (e : E ≃+* ℝ) :
    Function.Bijective (realBrauerZ E e) := by
  constructor
  · intro x y hxy
    let h := brauerClass E (realHamiltonCSA E e)
    have hne : h ≠ 1 := real_hamilton_brauer E e
    have hone : 1 ≠ h := Ne.symm hne
    rcases real_or_hamilton E e x with rfl | rfl <;>
      rcases real_or_hamilton E e y with rfl | rfl <;>
    all_goals try rfl
    all_goals
      exfalso
      have hz := congrArg Multiplicative.toAdd hxy
      norm_num [realBrauerZ, h, hne, hone] at hz
  · intro z
    rcases zmod_or_one z.toAdd with hz | hz
    · refine ⟨1, ?_⟩
      change (realBrauerZ E e 1).toAdd = z.toAdd
      simp [realBrauerZ, hz]
    · refine ⟨brauerClass E (realHamiltonCSA E e), ?_⟩
      change (realBrauerZ E e
        (brauerClass E (realHamiltonCSA E e))).toAdd = z.toAdd
      simp [realBrauerZ, hz,
        real_hamilton_brauer E e]

/-- The Brauer group of any field ring-equivalent to `R`, in any universe,
is additively equivalent to `ZMod 2`. -/
noncomputable def realZRing
    (E : Type u) [Field E] (e : E ≃+* ℝ) :
    Additive (BrauerGroup E) ≃+ ZMod 2 :=
  MulEquiv.toAdditiveLeft <|
    MulEquiv.ofBijective (realBrauerZ E e)
      (real_z_bijective E e)

/-- Algebraic closedness transports across a ring equivalence even when the
two fields live in different universes.  Mathlib's same-universe theorem is
not general enough for an arbitrary number-field completion. -/
theorem alg_closed_ring
    {F : Type u} {E : Type v} [Field F] [Field E]
    (e : F ≃+* E) [IsAlgClosed F] : IsAlgClosed E := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : (p.map e.symm.toRingHom).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hp)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    (p.map e.symm.toRingHom) hpe
  refine ⟨e x, ?_⟩
  rw [Polynomial.IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

/-- The invariant at a complex place is the zero homomorphism. -/
def complexPlaceInvariant
    (K : Type u) [Field K] [NumberField K]
    (v : InfinitePlace K) :
    Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K (.inr v))) →+
      LocalInvariant := 0

/-- The zero invariant has the required canonical properties at a complex
place because its Brauer group is trivial. -/
theorem complex_invariant_canonical
    (K : Type u) [Field K] [NumberField K]
    (v : InfinitePlace K) (hv : InfinitePlace.IsComplex v) :
    ArchimedeanBrauerInvariant K v
      (complexPlaceInvariant K v) := by
  letI : IsAlgClosed v.Completion :=
    alg_closed_ring
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
  letI : Subsingleton
      (BrauerGroup (Submission.CField.RExist.placeCompletion K (.inr v))) := by
    change Subsingleton (BrauerGroup v.Completion)
    exact brauer_subsingleton_closed v.Completion
  constructor
  · intro x y _
    exact Subsingleton.elim x y
  constructor
  · intro hvreal
    exact (InfinitePlace.not_isComplex_iff_isReal.mpr hvreal hv).elim
  · intro _
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      simp [complexPlaceInvariant]
    · intro hz
      have hz0 : z = 0 := by simpa using hz
      subst z
      exact ⟨0, map_zero _⟩

/-- The canonical map from `ZMod n` has exactly the `n`-torsion of `Q/Z` as
its range. -/
theorem range_zmod_invariant (n : ℕ) [NeZero n] :
    Set.range (zmodLocalInvariant n) = {x | n • x = 0} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change n • zmodLocalInvariant n z = 0
    rw [← map_nsmul]
    simp
  · intro hx
    let xt : localInvariantTorsion n := ⟨x, hx⟩
    obtain ⟨z, hz⟩ := (zmod_torsion_bijective n).2 xt
    refine ⟨z, ?_⟩
    exact congrArg Subtype.val hz

/-- Given an additive identification of the Brauer group of a real
completion with `ZMod 2`, compose it with the standard inclusion into
`Q/Z`. -/
noncomputable def realInvariantAdd
    (K : Type u) [Field K] [NumberField K]
    (v : InfinitePlace K)
    (e : Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K (.inr v))) ≃+
      ZMod 2) :
    Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K (.inr v))) →+
      LocalInvariant :=
  (zmodLocalInvariant 2).comp e.toAddMonoidHom

/-- Any such identification gives the canonical real-place invariant. -/
theorem real_invariant_canonical
    (K : Type u) [Field K] [NumberField K]
    (v : InfinitePlace K) (hv : InfinitePlace.IsReal v)
    (e : Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K (.inr v))) ≃+
      ZMod 2) :
    ArchimedeanBrauerInvariant K v
      (realInvariantAdd K v e) := by
  constructor
  · exact (zmod_invariant_injective 2).comp e.injective
  constructor
  · intro _
    rw [← range_zmod_invariant 2]
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨e b, rfl⟩
    · rintro ⟨z, rfl⟩
      refine ⟨e.symm z, ?_⟩
      simp [realInvariantAdd]
  · intro hcomplex
    exact (InfinitePlace.not_isComplex_iff_isReal.mpr hv hcomplex).elim

/-- The additive `ZMod 2` coordinate on the Brauer group of a real
completion. -/
noncomputable def realPlaceBrauer
    (K : Type u) [Field K] [NumberField K]
    (v : InfinitePlace K) (hv : InfinitePlace.IsReal v) :
    Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K (.inr v))) ≃+
      ZMod 2 := by
  change Additive (BrauerGroup v.Completion) ≃+ ZMod 2
  exact realZRing v.Completion
    (InfinitePlace.Completion.ringEquivRealOfIsReal hv)

/-- The canonical invariant at a real infinite place. -/
noncomputable def realPlaceInvariant
    (K : Type u) [Field K] [NumberField K]
    (v : InfinitePlace K) (hv : InfinitePlace.IsReal v) :
    Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K (.inr v))) →+
      LocalInvariant :=
  realInvariantAdd K v
    (realPlaceBrauer K v hv)

/-- The constructed real-place invariant has the standard image and is
injective. -/
theorem real_place_canonical
    (K : Type u) [Field K] [NumberField K]
    (v : InfinitePlace K) (hv : InfinitePlace.IsReal v) :
    ArchimedeanBrauerInvariant K v
      (realPlaceInvariant K v hv) :=
  real_invariant_canonical K v hv
    (realPlaceBrauer K v hv)

/-- The canonical invariant at an arbitrary infinite place, selected by the
real/complex dichotomy. -/
noncomputable def archimedeanPlaceInvariant
    (K : Type u) [Field K] [NumberField K]
    (v : InfinitePlace K) :
    Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K (.inr v))) →+
      LocalInvariant := by
  classical
  exact if hv : InfinitePlace.IsReal v then
      realPlaceInvariant K v hv
    else
      complexPlaceInvariant K v

/-- The selected invariant is canonical at every infinite place. -/
theorem archimedean_invariant_canonical
    (K : Type u) [Field K] [NumberField K]
    (v : InfinitePlace K) :
    ArchimedeanBrauerInvariant K v
      (archimedeanPlaceInvariant K v) := by
  classical
  by_cases hv : InfinitePlace.IsReal v
  · simpa [archimedeanPlaceInvariant, hv] using
      real_place_canonical K v hv
  · have hc : InfinitePlace.IsComplex v :=
      InfinitePlace.not_isReal_iff_isComplex.mp hv
    simpa [archimedeanPlaceInvariant, hv] using
      complex_invariant_canonical K v hc

/-- Unconditional local-invariant data at every number-field place. -/
noncomputable def placeInvariantData
    (K : Type u) [Field K] [NumberField K] :
    PIData K where
  invariant
    | .inl P => finitePlaceInvariant K P
    | .inr v => archimedeanPlaceInvariant K v
  finite_eq _ := rfl
  infinite_isCanonical v :=
    archimedean_invariant_canonical K v

end

end Submission.CField.BLoc
