import Towers.FieldTheory.FiniteDefect.AmbientSeparation
import Towers.Group.FinitePRelator.ShadowCorrespondence


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Towers
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PCShadow
open PRFact
open PRQuotie
open RCFact
open RSCorr
open TFFact

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
An actual surjective continuous finite `3`-group quotient of the actual initial
Galois group.
-/
abbrev InitialKochQuotient :=
  QShadow 3 initialGaloisGroup

/--
Pull an actual finite `3`-group quotient of the actual initial Galois group
back along the initial Koch quotient map.  The pullback automa kills
the displayed tame Koch relators because the initial Koch quotient kills them.
-/
def initialKochPullback
    (D : KRData)
    (S : InitialKochQuotient) :
    D.ThreeRelatorQuotient :=
  RSCorr.QShadow.pullbackAlongPresented
    (relator := D.fiveRelatorFamily.relator)
    D.fiveRelatorPresented
    S

/--
The pulled-back finite quotient map is the original finite quotient map
composed with the initial Koch quotient map.
-/
lemma initial_three_pullback
    (D : KRData)
    (S : InitialKochQuotient) :
    (D.initialKochPullback S).map =
      S.map.comp initialKochQuotient := rfl

/--
The desired finite quotient Koch theorem turns the initial Koch quotient into a
finite-`3` universal five-relator quotient.
-/
def fiveUniversalTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    D.fiveRelatorPresented.FiniteThreeUniversal
      D.fiveRelatorFamily :=
  D.factorization_theorem_statement.mp
    hfactor

/--
The finite-`3` universality theorem in the generic `p`-relator language.
-/
def fivePresentedTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    D.fiveRelatorPresented.FinitePUniversal 3 :=
  (D.fiveRelatorPresented.three_universal_p
      D.fiveRelatorFamily).mp
    (D.fiveUniversalTheorem hfactor)

/--
Under the desired theorem, descend one actual finite `3`-group tame-relator
quotient of the initial free pro-`3` group to an actual finite `3`-group
quotient of the actual initial Galois group.
-/
def relatorDescendTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (S : D.ThreeRelatorQuotient) :
    InitialKochQuotient :=
  RSCorr.RQShadow.descendAlongPresented
    D.fiveRelatorPresented
    D.five_presented_topological
    (D.fivePresentedTheorem hfactor)
    S

/--
The descended quotient from the actual initial Galois group pulls back to the
original finite tame-relator quotient map.
-/
lemma descend_theorem_comp
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (S : D.ThreeRelatorQuotient) :
    (D.relatorDescendTheorem hfactor S).map.comp
        initialKochQuotient =
      S.map := by
  exact RSCorr.RQShadow.descendAlongComp
    D.fiveRelatorPresented
    D.five_presented_topological
    (D.fivePresentedTheorem hfactor)
    S

/--
The descended finite quotient map from the actual initial Galois group is
continuous.
-/
lemma descend_theorem_continuous
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (S : D.ThreeRelatorQuotient) :
    Continuous (D.relatorDescendTheorem hfactor S).map := by
  exact (D.relatorDescendTheorem hfactor S).toShadow.map_continuous

/--
The descended finite quotient map from the actual initial Galois group is
surjective.
-/
lemma descend_theorem_surjective
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (S : D.ThreeRelatorQuotient) :
    Function.Surjective
      (D.relatorDescendTheorem hfactor S).map := by
  exact (D.relatorDescendTheorem hfactor S).map_surjective

/--
The descended finite quotient map is the unique homomorphism from the actual
initial Galois group whose pullback is the original finite tame-relator
quotient map.
-/
lemma descend_theorem_unique
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (S : D.ThreeRelatorQuotient)
    (β : initialGaloisGroup →* S.Target)
    (hβ : β.comp initialKochQuotient = S.map) :
    β = (D.relatorDescendTheorem hfactor S).map := by
  exact
    RSCorr.RQShadow.descend_along_unique
    D.fiveRelatorPresented
    D.five_presented_topological
    (D.fivePresentedTheorem hfactor)
    S
    β
    hβ

/--
The named theorem-level factor of one finite tame-relator quotient is the same
map as its packaged descended finite quotient of the actual initial Galois
group.
-/
lemma descend_theorem_factor
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (S : D.ThreeRelatorQuotient) :
    (D.relatorDescendTheorem hfactor S).map =
      D.relatorFactorTheorem
        hfactor
        S.map
        S.toRShadow.toShadow.map_continuous
        S.toRShadow.toShadow.target_p_group
        S.toRShadow.relator_killed := by
  exact (D.descend_theorem_unique
    hfactor
    S
    (D.relatorFactorTheorem
      hfactor
      S.map
      S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group
      S.toRShadow.relator_killed)
    (D.relator_theorem_comp
      hfactor
      S.map
      S.toRShadow.toShadow.map_continuous
      S.toRShadow.toShadow.target_p_group
      S.toRShadow.relator_killed)).symm

/--
Descending a pulled-back finite quotient of the actual initial Galois group
recovers its original quotient map.
-/
lemma descend_theorem_pullback
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (S : InitialKochQuotient) :
    (D.relatorDescendTheorem hfactor
      (D.initialKochPullback S)).map =
      S.map := by
  exact RSCorr.QShadow.descend_along_presented
    D.fiveRelatorPresented
    D.five_presented_topological
    (D.fivePresentedTheorem hfactor)
    S

/--
Pulling back the descended finite quotient of one finite tame-relator quotient
recovers its original quotient map.
-/
lemma pullback_descend_theorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (S : D.ThreeRelatorQuotient) :
    (D.initialKochPullback
      (D.relatorDescendTheorem hfactor S)).map =
      S.map := by
  exact RSCorr.RQShadow.pullback_descend_along
    D.fiveRelatorPresented
    D.five_presented_topological
    (D.fivePresentedTheorem hfactor)
    S

/--
One actual finite tame-relator quotient of the initial free pro-`3` group is a
pullback from the actual initial Galois group when its same finite `3` target
admits a continuous surjective quotient map from the latter with the expected
pullback.
-/
def InitialKochPullback
    (D : KRData)
    (S : D.ThreeRelatorQuotient) :
    Prop :=
  ∃ β : initialGaloisGroup →* S.Target,
    Continuous β ∧ Function.Surjective β ∧
      β.comp initialKochQuotient = S.map

/--
Every actual finite tame-relator quotient of the initial free pro-`3` group is
a pullback from an actual finite `3` quotient of the actual initial Galois
group.
-/
def AllQuotientsPullbacks
    (D : KRData) :
    Prop :=
  ∀ S : D.ThreeRelatorQuotient,
    D.InitialKochPullback S

/--
If one finite tame-relator quotient is a pullback from a finite quotient map of
the actual initial Galois group, then its kernel contains the initial Koch
kernel.
-/
lemma initial_koch_pullback
    (D : KRData)
    (S : D.ThreeRelatorQuotient)
    (hpullback : D.InitialKochPullback S) :
    initialKochQuotient.ker ≤ S.map.ker := by
  rcases hpullback with ⟨β, _hβcontinuous, _hβsurjective, hβ⟩
  intro x hx
  apply MonoidHom.mem_ker.mpr
  have hβx := DFunLike.congr_fun hβ x
  change β (initialKochQuotient x) = S.map x at hβx
  rw [MonoidHom.mem_ker.mp hx] at hβx
  exact hβx.symm.trans (map_one _)

/--
The desired finite quotient Koch theorem is exactly the statement that every
actual finite `3`-group tame-relator quotient of the initial free pro-`3` group
comes by pullback from an actual finite `3` quotient of the actual initial
Galois group.
-/
lemma fin_factorization_pullbacks
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.AllQuotientsPullbacks := by
  constructor
  · intro hfactor S
    exact ⟨(D.relatorDescendTheorem hfactor S).map,
      D.descend_theorem_continuous hfactor S,
      D.descend_theorem_surjective hfactor S,
      D.descend_theorem_comp
        hfactor
        S⟩
  · intro hpullback P _hPGroup _hPTopology _hPDiscrete _hPFinite α hα hP hkill
    let S : D.ThreeRelatorQuotient :=
      RQShadow.relatorShadowRange
        (RShadow.ofMap α hα hP hkill)
    have hS : initialKochQuotient.ker ≤ S.map.ker :=
      D.initial_koch_pullback
        S
        (hpullback S)
    simpa [S, RQShadow.relator_shadow_range] using hS

end KRData

end TBluepr
end Towers
