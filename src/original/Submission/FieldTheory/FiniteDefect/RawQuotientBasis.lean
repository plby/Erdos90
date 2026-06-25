import Submission.FieldTheory.FiniteDefect.QuotientBasis


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PCShadow
open PRFact
open PRQuotie
open RSFact
open TFFact

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
A quotient-valued refinement of the canonical raw Zassenhaus factor cone:
each raw relator stage is required to be an actual surjective finite `3`
quotient of the actual initial Galois group.
-/
structure CSCone
    (D : KRData)
    extends D.CRCone where
  factor_surjective :
    ∀ n : ℕ, Function.Surjective (toCRCone.factor n)

namespace CSCone

/--
A quotient-valued raw Zassenhaus factor cone is determined by its underlying
continuous factor cone.
-/
lemma ext
    (D : KRData)
    (C E : D.CSCone)
    (hcone :
      C.toCRCone = E.toCRCone) :
    C = E := by
  cases C
  cases E
  cases hcone
  rfl

/--
There is at most one quotient-valued raw Zassenhaus factor cone.
-/
lemma subsingleton
    (D : KRData) :
    Subsingleton D.CSCone := by
  constructor
  intro C E
  apply CSCone.ext D C E
  exact (CRCone.subsingleton D).elim _ _

/--
The quotient-valued raw Zassenhaus cone is compatible with the canonical
transition maps between raw relator stages.
-/
lemma transition_comp_factor
    (D : KRData)
    (C : D.CSCone)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (D.ZassenhausRelatorTransition hnm).comp
        (C.factor m) =
      C.factor n := by
  exact CRCone.transition_comp_factor
    D
    C.toCRCone
    hnm

/--
Deeper factors in a quotient-valued raw Zassenhaus cone have smaller kernels.
-/
lemma factor_kernel
    (D : KRData)
    (C : D.CSCone)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (C.factor m).ker ≤ (C.factor n).ker := by
  exact ker_factors_through
    (C.factor m)
    (C.factor n)
    ⟨D.ZassenhausRelatorTransition hnm,
      C.transition_comp_factor D hnm⟩

/--
Each factor in a quotient-valued raw Zassenhaus cone is a topological quotient
map from the actual initial Galois group onto its finite discrete target.
-/
lemma factor_quotient
    (D : KRData)
    (C : D.CSCone)
    (n : ℕ) :
    Topology.IsQuotientMap (C.factor n) := by
  exact RCFact.surjective_t_space
    (C.factor n)
    (C.factor_surjective n)
    (C.factor_continuous n)

/--
Package one factor of a quotient-valued raw Zassenhaus cone as an actual
finite `3` quotient shadow of the actual initial Galois group.
-/
def toQShadow
    (D : KRData)
    (C : D.CSCone)
    (n : ℕ) :
    InitialKochQuotient where
  toShadow := {
    Target := (D.ZassenhausRelatorQuotient n).Target
    map := C.factor n
    map_continuous := C.factor_continuous n
    target_p_group :=
      (D.ZassenhausRelatorQuotient n).toRShadow.toShadow.target_p_group
  }
  map_surjective := C.factor_surjective n

/--
The quotient shadow attached to a raw Zassenhaus cone remembers the cone
factor itself as its quotient map.
-/
@[simp]
lemma quotient_shadow
    (D : KRData)
    (C : D.CSCone)
    (n : ℕ) :
    (C.toQShadow D n).map = C.factor n := rfl

/--
The quotient shadow attached to a raw Zassenhaus cone pulls back along the
actual Koch quotient map to the original raw relator quotient map.
-/
lemma quotient_shadow_comp
    (D : KRData)
    (C : D.CSCone)
    (n : ℕ) :
    (C.toQShadow D n).map.comp initialKochQuotient =
      (D.ZassenhausRelatorQuotient n).map := by
  exact C.factor_comp_map n

/--
The raw Zassenhaus transition maps are quotient maps between the quotient
shadows attached to any quotient-valued raw Zassenhaus cone.
-/
lemma transition_comp_shadow
    (D : KRData)
    (C : D.CSCone)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (D.ZassenhausRelatorTransition hnm).comp
        (C.toQShadow D m).map =
      (C.toQShadow D n).map := by
  exact C.transition_comp_factor D hnm

/--
The desired finite quotient Koch theorem constructs the unique
quotient-valued raw Zassenhaus factor cone.
-/
def kochFactorizationTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    D.CSCone where
  toCRCone := {
    factor := fun n =>
      (D.descendedShadowTheorem
        hfactor n).map
    factor_continuous := fun n =>
      (D.descendedShadowTheorem
        hfactor n).toShadow.map_continuous
    factor_comp_map := fun n =>
      D.descended_shadow_theorem
        hfactor
        n
  }
  factor_surjective := fun n =>
    (D.descendedShadowTheorem
      hfactor n).map_surjective

/--
The quotient-valued raw Zassenhaus cone from the theorem has the same
underlying continuous cone as the earlier canonical construction.
-/
lemma theorem_cone_existing
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    (kochFactorizationTheorem D
      hfactor).toCRCone =
      D.continuousKochFactorization
        hfactor := by
  exact (CRCone.subsingleton D).elim _ _

/--
Any quotient-valued raw Zassenhaus factor cone proves the desired finite
quotient Koch theorem.
-/
lemma koch_theorem_nonempty
    (D : KRData)
    (hcone : Nonempty D.CSCone) :
    D.KochFactorizationTheorem := by
  rcases hcone with ⟨C⟩
  exact D.fin_koch_cone
    ⟨C.toCRCone⟩

/--
The desired finite quotient Koch theorem is equivalent to saying that the raw
canonical Zassenhaus relator tower is already an actual quotient tower of the
actual initial Galois group.
-/
lemma factorization_theorem_nonempty
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      Nonempty D.CSCone := by
  constructor
  · intro hfactor
    exact ⟨kochFactorizationTheorem D hfactor⟩
  · exact koch_theorem_nonempty D

/--
Under the desired theorem, every quotient-valued raw Zassenhaus cone has the
same factor maps as the descended raw quotient shadows.
-/
lemma factor_descended_theorem
    (D : KRData)
    (C : D.CSCone)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    C.factor n =
      (D.descendedShadowTheorem
        hfactor n).map := by
  apply MonoidHom.ext
  intro y
  rcases initial_quotient_surjective y with ⟨x, rfl⟩
  have hcone := congrArg
    (fun φ : initialKochFree.Carrier →*
        (D.ZassenhausRelatorQuotient n).Target => φ x)
    (C.factor_comp_map n)
  have hdesc := congrArg
    (fun φ : initialKochFree.Carrier →*
        (D.ZassenhausRelatorQuotient n).Target => φ x)
    (D.descended_shadow_theorem
      hfactor
      n)
  exact hcone.trans hdesc.symm

/--
Every quotient-valued raw Zassenhaus cone gives a kernel-cofinal finite `3`
quotient family of the actual initial Galois group.
-/
lemma quotient_shadow_cofinal
    (D : KRData)
    (C : D.CSCone) :
    CofinalShadowFamily (C.toQShadow D) := by
  let hfactor : D.KochFactorizationTheorem :=
    koch_theorem_nonempty D ⟨C⟩
  intro S
  rcases D.zassenhaus_fin_koch
      hfactor
      S with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  change (C.factor n).ker ≤ S.map.ker
  rw [C.factor_descended_theorem D hfactor n]
  exact hn

/--
Every actual finite `3` quotient of the actual initial Galois group is a
surjective continuous quotient of one factor in any quotient-valued raw
Zassenhaus cone.
-/
lemma factor_surje_conti
    (D : KRData)
    (C : D.CSCone)
    (S : InitialKochQuotient) :
    ∃ n : ℕ,
      SFThroug (C.factor n) S.map := by
  rcases C.quotient_shadow_cofinal D S with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  exact surjectively_continuously_factors
    (C.factor n)
    S.map
    (C.factor_quotient D n)
    S.toShadow.map_continuous
    S.map_surjective
    hn

/--
A finite family of actual finite `3` quotients of the actual initial Galois
group is dominated by one sufficiently deep factor in any quotient-valued raw
Zassenhaus cone.
-/
lemma surjec_conti_famil
    (D : KRData)
    (C : D.CSCone)
    (𝒮 : Finset InitialKochQuotient) :
    ∃ n : ℕ,
      ∀ S ∈ 𝒮,
        SFThroug (C.factor n) S.map := by
  classical
  induction 𝒮 using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      intro S hS
      simp at hS
  | @insert S 𝒮 hSnotmem ih =>
      rcases
        C.factor_surje_conti
          D
          S with
        ⟨m, hm⟩
      rcases ih with ⟨n, hn⟩
      refine ⟨max n m, ?_⟩
      intro T hT
      rw [Finset.mem_insert] at hT
      rcases hT with rfl | hT
      · exact surjectively_continuously_factors
          (C.factor (max n m))
          T.map
          (C.factor_quotient D (max n m))
          T.toShadow.map_continuous
          T.map_surjective
          ((C.factor_kernel D (Nat.le_max_right n m)).trans
            (ker_surjectively_through (C.factor m) T.map hm))
      · have hTfactor := hn T hT
        exact surjectively_continuously_factors
          (C.factor (max n m))
          T.map
          (C.factor_quotient D (max n m))
          T.toShadow.map_continuous
          T.map_surjective
          ((C.factor_kernel D (Nat.le_max_left n m)).trans
            (ker_surjectively_through (C.factor n) T.map hTfactor))

/--
The common kernel of the quotient shadows attached to a quotient-valued raw
Zassenhaus cone.
-/
def ShadowFamilyKernel
    (D : KRData)
    (C : D.CSCone) :
    Subgroup initialGaloisGroup :=
  shadowFamilyKernel (C.toQShadow D)

/--
Every quotient-valued raw Zassenhaus cone detects exactly the full finite `3`
residual kernel of the actual initial Galois group.
-/
lemma shadow_family_residual
    (D : KRData)
    (C : D.CSCone) :
    C.ShadowFamilyKernel D =
      residualKernel 3 initialGaloisGroup := by
  exact shadow_family_cofinal
    (C.toQShadow D)
    (C.quotient_shadow_cofinal D)

/--
Because the actual initial Galois group is residually finite `3`, every
quotient-valued raw Zassenhaus cone has trivial common kernel.
-/
lemma shadow_family_bot
    (D : KRData)
    (C : D.CSCone) :
    C.ShadowFamilyKernel D = ⊥ := by
  rw [C.shadow_family_residual D]
  exact initial_galois_residually

/--
The desired finite quotient Koch theorem is equivalent to existence of a raw
canonical quotient cone whose finite quotient shadows separate the actual
initial Galois group.
-/
lemma theorem_cone_trivial
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∃ C : D.CSCone,
        C.ShadowFamilyKernel D = ⊥ := by
  constructor
  · intro hfactor
    let C := kochFactorizationTheorem D hfactor
    exact ⟨C, C.shadow_family_bot D⟩
  · rintro ⟨C, _⟩
    exact koch_theorem_nonempty D ⟨C⟩

end CSCone

end KRData

end TBluepr
end Submission
