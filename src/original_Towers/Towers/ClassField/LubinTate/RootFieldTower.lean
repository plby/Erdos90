import Towers.ClassField.LubinTate.RootFieldAdic

/-!
# The finite Lubin--Tate root-field tower

Summary I.3.7 arranges the finite Lubin--Tate extensions into a compatible
tower by choosing primitive torsion points `pi_n` with
`f(pi_(n+1)) = pi_n`.  The individual distinguished root fields were
constructed in `LubinTateRootField`; this file supplies their canonical
successive embeddings and proves the degree of each step.
-/

namespace Towers.CField.LTate

noncomputable section

open Polynomial
open Towers.CField.FGroups

universe u v w

/-- Applying `f` once before a reduced iterate advances its level by one. -/
theorem reduced_lubin_tate
    {R : Type*} [CommSemiring R] (f : R[X]) (n : ℕ) (x : R) :
    (reducedLubinIterate f n).eval (f.eval x) =
      (reducedLubinIterate f (n + 1)).eval x := by
  rw [reduced_iterate_eval, reduced_iterate_eval]
  rw [Function.iterate_succ_apply]

/-- A zero of one compositional iterate remains a zero at the next level
when the polynomial fixes zero. -/
theorem iterate_comp_x
    {R : Type*} [CommSemiring R] (f : R[X])
    (hf0 : f.coeff 0 = 0) (n : ℕ) (x : R)
    (hx : (f.comp^[n] X).eval x = 0) :
    (f.comp^[n + 1] X).eval x = 0 := by
  rw [Polynomial.iterate_comp_eval] at hx ⊢
  rw [Function.iterate_succ_apply', hx]
  simpa only [← Polynomial.coeff_zero_eq_eval_zero] using hf0

namespace LTDatum

variable {A : Type u} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]
  (D : LTDatum A)
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]

/-- The image of the level-`n + 2` distinguished root under `f` is a root
of the preceding reduced level polynomial. -/
theorem aeval_reduced_f (n : ℕ) :
    Polynomial.aeval
        (Polynomial.aeval (D.root K (n + 1))
          (D.f.map (algebraMap A K)))
        (D.reducedPolynomial K n) = 0 := by
  let E := D.RootField K (n + 1)
  let fE : E[X] :=
    (D.f.map (algebraMap A K)).map (algebraMap K E)
  have hredmap (m : ℕ) :
      (D.reducedPolynomial K m).map (algebraMap K E) =
        reducedLubinIterate fE m := by
    calc
      (D.reducedPolynomial K m).map (algebraMap K E) =
          (reducedLubinIterate
            (D.f.map (algebraMap A K)) m).map (algebraMap K E) := by
        rw [reducedPolynomial, lubin_tate_iterate]
      _ = reducedLubinIterate fE m := by
        simpa only [fE] using lubin_tate_iterate
          (algebraMap K E) (D.f.map (algebraMap A K)) m
  simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  change Polynomial.eval
      (Polynomial.eval (D.root K (n + 1)) fE)
      ((D.reducedPolynomial K n).map (algebraMap K E)) = 0
  rw [hredmap]
  rw [reduced_lubin_tate]
  have hroot := D.aeval_root K (n + 1)
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    hredmap] at hroot
  exact hroot

/-- The successive field embedding in Summary I.3.7.  It sends the
distinguished level-`n + 1` root to `f` evaluated at the distinguished
level-`n + 2` root. -/
noncomputable def rootAlgHom (n : ℕ) :
    D.RootField K n →ₐ[K] D.RootField K (n + 1) :=
  AdjoinRoot.liftAlgHom (D.reducedPolynomial K n)
    (Algebra.ofId K (D.RootField K (n + 1)))
    (Polynomial.aeval (D.root K (n + 1))
      (D.f.map (algebraMap A K)))
    (D.aeval_reduced_f K n)

@[simp]
theorem root_alg_hom (n : ℕ) :
    D.rootAlgHom K n (D.root K n) =
      Polynomial.aeval (D.root K (n + 1))
        (D.f.map (algebraMap A K)) := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Every successive root-field map is injective, so the finite levels form
an honest ascending tower of fields. -/
theorem root_alg_injective (n : ℕ) :
    Function.Injective (D.rootAlgHom K n) :=
  (D.rootAlgHom K n).injective

/-- The canonical embedding from any distinguished finite level into every
higher one, obtained by composing the successive maps. -/
noncomputable def rootFieldAlg {n m : ℕ} (h : n ≤ m) :
    D.RootField K n →ₐ[K] D.RootField K m :=
  Nat.leRecOn (C := fun r ↦ D.RootField K n →ₐ[K] D.RootField K r) h
    (fun {r} i ↦ (D.rootAlgHom K r).comp i)
    (AlgHom.id K (D.RootField K n))

@[simp]
theorem root_alg_refl (n : ℕ) :
    D.rootFieldAlg K (Nat.le_refl n) =
      AlgHom.id K (D.RootField K n) := by
  rw [rootFieldAlg, Nat.leRecOn_self]

/-- Recursion formula for the embeddings between arbitrary finite levels. -/
theorem root_alg_step {n m : ℕ} (h : n ≤ m) :
    D.rootFieldAlg K (Nat.le.step h) =
      (D.rootAlgHom K m).comp (D.rootFieldAlg K h) := by
  simp only [rootFieldAlg]
  rw [Nat.leRecOn_succ h]

@[simp]
theorem root_alg_succ (n : ℕ) :
    D.rootFieldAlg K (Nat.le_succ n) =
      D.rootAlgHom K n := by
  simp only [rootFieldAlg]
  rw [Nat.leRecOn_succ']
  exact AlgHom.comp_id _

/-- Every map in the distinguished finite root-field system is injective. -/
theorem alg_hom_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (D.rootFieldAlg K h) :=
  (D.rootFieldAlg K h).injective

/-- Consecutive distinguished Lubin--Tate root fields have relative degree
`q`, as displayed in Summary I.3.7. -/
theorem finrank_root_succ (n : ℕ) :
    let i := D.rootAlgHom K n
    letI : Algebra (D.RootField K n) (D.RootField K (n + 1)) :=
      i.toRingHom.toAlgebra
    Module.finrank (D.RootField K n) (D.RootField K (n + 1)) = D.q := by
  let i := D.rootAlgHom K n
  letI : Algebra (D.RootField K n) (D.RootField K (n + 1)) :=
    i.toRingHom.toAlgebra
  letI : IsScalarTower K (D.RootField K n) (D.RootField K (n + 1)) :=
    IsScalarTower.of_algHom i
  have htower := Module.finrank_mul_finrank K
    (D.RootField K n) (D.RootField K (n + 1))
  rw [D.finrank_rootField K n, D.finrank_rootField K (n + 1)] at htower
  have hfactor_ne : (D.q - 1) * D.q ^ n ≠ 0 := by
    exact Nat.ne_of_gt (Nat.mul_pos
      (Nat.sub_pos_of_lt D.one_lt_q)
      (pow_pos (Nat.zero_lt_of_lt D.one_lt_q) n))
  apply mul_left_cancel₀ hfactor_ne
  calc
    (D.q - 1) * D.q ^ n *
          Module.finrank (D.RootField K n) (D.RootField K (n + 1)) =
        (D.q - 1) * D.q ^ (n + 1) := htower
    _ = (D.q - 1) * D.q ^ n * D.q := by
      rw [pow_succ, mul_assoc]

section CoherentAlgebraicClosureEmbedding

variable (Omega : Type w) [Field Omega] [Algebra K Omega]
  [IsAlgClosure K Omega]

/-- Any embedding of one distinguished root field into an algebraic closure
extends across the next map in the root-field tower. -/
theorem root_alg_commuting
    (n : ℕ) (e : D.RootField K n →ₐ[K] Omega) :
    ∃ e' : D.RootField K (n + 1) →ₐ[K] Omega,
      e'.comp (D.rootAlgHom K n) = e := by
  let i := D.rootAlgHom K n
  letI : Algebra (D.RootField K n) (D.RootField K (n + 1)) :=
    i.toRingHom.toAlgebra
  letI : IsScalarTower K (D.RootField K n) (D.RootField K (n + 1)) :=
    IsScalarTower.of_algHom i
  letI : Module.Finite (D.RootField K n) (D.RootField K (n + 1)) :=
    Module.Finite.of_restrictScalars_finite K _ _
  letI : Algebra.IsAlgebraic (D.RootField K n) (D.RootField K (n + 1)) :=
    Algebra.IsAlgebraic.of_finite _ _
  letI : IsAlgClosed Omega := IsAlgClosure.isAlgClosed K
  obtain ⟨e', he'⟩ :=
    IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (K := K) (L := D.RootField K n) (M := Omega)
      (E := D.RootField K (n + 1)) e
  refine ⟨e', ?_⟩
  simpa only [i] using he'

/-- A coherent choice of embeddings of all distinguished finite root fields
into one algebraic closure.  The successor case is chosen using the extension
lemma, so it extends the preceding embedding by construction. -/
noncomputable def coherentAlgHom :
    (n : ℕ) → D.RootField K n →ₐ[K] Omega
  | 0 => by
      letI : IsAlgClosed Omega := IsAlgClosure.isAlgClosed K
      exact IsAlgClosed.lift
  | n + 1 => Classical.choose
      (D.root_alg_commuting K Omega n
        (coherentAlgHom n))

/-- The chosen root-field embeddings commute with every successor map. -/
theorem coherent_alg_succ (n : ℕ) :
    (D.coherentAlgHom K Omega (n + 1)).comp
        (D.rootAlgHom K n) =
      D.coherentAlgHom K Omega n := by
  rw [coherentAlgHom]
  exact Classical.choose_spec
    (D.root_alg_commuting K Omega n
      (D.coherentAlgHom K Omega n))

/-- The compatible primitive Lubin--Tate torsion point at finite level `n` in
the fixed algebraic closure. -/
noncomputable def coherentTorsionRoot (n : ℕ) : Omega :=
  D.coherentAlgHom K Omega n (D.root K n)

/-- The coherent primitive roots satisfy Milne's recursion
`f(pi_(n+2)) = pi_(n+1)`. -/
theorem aeval_f_coherent (n : ℕ) :
    Polynomial.aeval (D.coherentTorsionRoot K Omega (n + 1))
        (D.f.map (algebraMap A K)) =
      D.coherentTorsionRoot K Omega n := by
  let e := D.coherentAlgHom K Omega (n + 1)
  have hcomm := DFunLike.congr_fun
    (D.coherent_alg_succ K Omega n) (D.root K n)
  change e (D.rootAlgHom K n (D.root K n)) =
    D.coherentAlgHom K Omega n (D.root K n) at hcomm
  rw [D.root_alg_hom K n] at hcomm
  rw [coherentTorsionRoot, coherentTorsionRoot]
  rw [← hcomm]
  exact Polynomial.aeval_algHom_apply e
    (D.root K (n + 1)) (D.f.map (algebraMap A K))

end CoherentAlgebraicClosureEmbedding

section AmbientTower

variable (Omega : Type*) [Field Omega] [Algebra K Omega]

/-- The full set of level-`n + 1` Lubin--Tate torsion roots in a common
ambient extension field.  By `RootValuation`, in the local-field setting
these roots automa lie in the open unit ball used by Milne. -/
def torsionRootSet (n : ℕ) : Set Omega :=
  {x | Polynomial.aeval x (D.torsionPolynomial K n) = 0}

omit [IsFractionRing A K] in
/-- The full torsion iterate remains monic after extension to the base
fraction field. -/
theorem torsionPolynomial_monic (n : ℕ) :
    (D.torsionPolynomial K n).Monic := by
  rw [torsionPolynomial]
  apply Polynomial.Monic.map
  apply monic_iterate_x D.f_monic
  rw [D.f_natDegree]
  exact Nat.ne_of_gt (Nat.zero_lt_of_lt D.one_lt_q)

omit [IsFractionRing A K] in
/-- The full torsion zero locus is the union of the preceding iterate's
zero locus and the roots of the reduced Eisenstein factor. -/
theorem torsion_set_union (n : ℕ) :
    D.torsionRootSet K Omega n =
      (((D.f.comp^[n] X).map (algebraMap A K)).rootSet Omega) ∪
        ((D.reducedPolynomial K n).rootSet Omega) := by
  have hprevMonic :
      ((D.f.comp^[n] X).map (algebraMap A K)).Monic := by
    apply Polynomial.Monic.map
    apply monic_iterate_x D.f_monic
    rw [D.f_natDegree]
    exact Nat.ne_of_gt (Nat.zero_lt_of_lt D.one_lt_q)
  ext x
  rw [torsionRootSet, Set.mem_setOf_eq, D.torsionPolynomial_factor K n,
    map_mul]
  simp only [mul_eq_zero, Set.mem_union]
  rw [hprevMonic.mem_rootSet,
    (D.reducedPolynomial_monic K n).mem_rootSet]

/-- The level-`n + 1` torsion roots are contained in the next level. -/
theorem torsion_set_mono (n : ℕ) :
    D.torsionRootSet K Omega n ⊆ D.torsionRootSet K Omega (n + 1) := by
  let fOmega : Omega[X] :=
    (D.f.map (algebraMap A K)).map (algebraMap K Omega)
  have hmap (m : ℕ) :
      (D.torsionPolynomial K m).map (algebraMap K Omega) =
        fOmega.comp^[m + 1] X := by
    calc
      (D.torsionPolynomial K m).map (algebraMap K Omega) =
          ((D.f.map (algebraMap A K)).comp^[m + 1] X).map
            (algebraMap K Omega) := by
        rw [torsionPolynomial, iterate_x]
      _ = fOmega.comp^[m + 1] X := by
        simpa only [fOmega] using iterate_x
          (algebraMap K Omega) (D.f.map (algebraMap A K)) (m + 1)
  intro x hx
  change Polynomial.aeval x (D.torsionPolynomial K (n + 1)) = 0
  change Polynomial.aeval x (D.torsionPolynomial K n) = 0 at hx
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    hmap] at hx ⊢
  apply iterate_comp_x fOmega
  · simp only [fOmega, Polynomial.coeff_map]
    simpa using D.lubinTateSeries.1
  · exact hx

/-- The concrete finite-level field `K_{pi,n+1}` inside a common ambient
extension: adjoining all roots of the level torsion polynomial. -/
def torsionLevelField (n : ℕ) : IntermediateField K Omega :=
  IntermediateField.adjoin K (D.torsionRootSet K Omega n)

/-- The common-ambient field generated by the primitive roots of the reduced
level polynomial.  Splitting-field uniqueness identifies this with the
abstract distinguished root field. -/
def reducedTorsionField (n : ℕ) : IntermediateField K Omega :=
  IntermediateField.adjoin K
    ((D.reducedPolynomial K n).rootSet Omega)

omit [IsFractionRing A K] in
/-- Every primitive root is a torsion point at the corresponding full level,
so the reduced-root field is contained in Milne's full torsion field. -/
theorem reduced_torsion_level (n : ℕ) :
    D.reducedTorsionField K Omega n ≤
      D.torsionLevelField K Omega n := by
  apply IntermediateField.adjoin.mono
  intro x hx
  change Polynomial.aeval x (D.torsionPolynomial K n) = 0
  rw [D.torsionPolynomial_factor K n, map_mul]
  rw [(D.reducedPolynomial_monic K n).mem_rootSet] at hx
  rw [hx, mul_zero]

/-- Consecutive concrete finite levels form an ascending field tower. -/
theorem torsion_mono_succ (n : ℕ) :
    D.torsionLevelField K Omega n ≤
      D.torsionLevelField K Omega (n + 1) :=
  IntermediateField.adjoin.mono K (D.torsionRootSet K Omega n)
    (D.torsionRootSet K Omega (n + 1))
    (D.torsion_set_mono K Omega n)

/-- The concrete finite Lubin--Tate levels are monotone in their index. -/
theorem torsion_level_mono :
    Monotone (D.torsionLevelField K Omega) :=
  monotone_nat_of_le_succ (D.torsion_mono_succ K Omega)

/-- Milne's infinite Lubin--Tate extension `K_pi`, constructed in the common
ambient field as the supremum of its finite torsion levels. -/
def infiniteTorsionField : IntermediateField K Omega :=
  ⨆ n, D.torsionLevelField K Omega n

/-- The first displayed assertion of Summary I.3.7: `K_pi` is exactly the
directed union of the finite fields `K_{pi,n}`. -/
theorem coe_i_union :
    (D.infiniteTorsionField K Omega : Set Omega) =
      ⋃ n, (D.torsionLevelField K Omega n : Set Omega) := by
  exact IntermediateField.coe_iSup_of_directed
    (D.torsion_level_mono K Omega).directed_le

/-- Elementwise form of the directed-union description of `K_pi`. -/
theorem infinite_torsion_field (x : Omega) :
    x ∈ D.infiniteTorsionField K Omega ↔
      ∃ n, x ∈ D.torsionLevelField K Omega n := by
  rw [← SetLike.mem_coe, D.coe_i_union K Omega,
    Set.mem_iUnion]
  rfl

end AmbientTower

section LocalAmbientTower

open scoped NormedField

variable (K : Type v) (Omega : Type w)
  [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [ProperSpace K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsDiscreteValuationRing
    (Valuation.integer (NormedField.valuation (K := K)))]
  [Field Omega] [Algebra K Omega] [IsAlgClosure K Omega]

set_option maxHeartbeats 3000000 in
-- The induction repeatedly instantiates the spectral splitting theorem at a
-- different finite root field and transports it through the tower embeddings.
/-- The full level-`n + 1` torsion polynomial splits in the distinguished
root field at that level. -/
theorem torsion_splits_field
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi})) :
    ∀ n : ℕ,
      ((D.torsionPolynomial K n).map
        (algebraMap K (D.RootField K n))).Splits := by
  intro n
  induction n with
  | zero =>
      rw [D.torsionPolynomial_factor K 0, Polynomial.map_mul]
      apply Polynomial.Splits.mul
      · simp
      · exact (D.field_splits_separable K hfield 0).1
  | succ n ih =>
      rw [D.torsionPolynomial_factor K (n + 1), Polynomial.map_mul]
      apply Polynomial.Splits.mul
      · have hmap := ih.map (D.rootAlgHom K n).toRingHom
        rw [Polynomial.map_map] at hmap
        have hcomp :
            (D.rootAlgHom K n).toRingHom.comp
                (algebraMap K (D.RootField K n)) =
              algebraMap K (D.RootField K (n + 1)) := by
          ext x
          exact (D.rootAlgHom K n).commutes x
        rw [hcomp] at hmap
        simpa only [torsionPolynomial] using hmap
      · exact (D.field_splits_separable K hfield (n + 1)).1

set_option maxHeartbeats 2000000 in
-- Constructing both splitting-field instances unfolds the deep spectral
-- local-field instance telescope used by `field_splits_separable`.
/-- In a common algebraic closure, the distinguished abstract root field is
canonically isomorphic up to splitting-field uniqueness to the field generated
by all primitive roots of the reduced level polynomial. -/
noncomputable def reducedTorsionLevel
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    D.RootField K n ≃ₐ[K] D.reducedTorsionField K Omega n := by
  let p := D.reducedPolynomial K n
  let E := D.RootField K n
  let T := D.reducedTorsionField K Omega n
  have hsplitsE : (p.map (algebraMap K E)).Splits :=
    (D.field_splits_separable K hfield n).1
  have hroot : D.root K n ∈ p.rootSet E := by
    exact (D.reducedPolynomial_monic K n).mem_rootSet.mpr
      (D.aeval_root K n)
  have hadjoinE : IntermediateField.adjoin K (p.rootSet E) = ⊤ := by
    apply top_unique
    rw [← D.adjoin_root_top K n]
    exact IntermediateField.adjoin.mono K {D.root K n} (p.rootSet E)
      (Set.singleton_subset_iff.mpr hroot)
  letI : p.IsSplittingField K E :=
    isSplittingField_iff_intermediateField.mpr ⟨hsplitsE, hadjoinE⟩
  letI : p.IsSplittingField K T := by
    change p.IsSplittingField K
      (IntermediateField.adjoin K (p.rootSet Omega))
    exact IntermediateField.adjoin_rootSet_isSplittingField
      ((IsAlgClosure.isAlgClosed K).splits _)
  exact (Polynomial.IsSplittingField.algEquiv E p).trans
    (Polynomial.IsSplittingField.algEquiv T p).symm

set_option maxHeartbeats 3000000 in
-- This transports full-iterate splitting across the splitting-field
-- equivalence and then uses the root-membership characterization in `Omega`.
/-- In an algebraic closure, adjoining all level torsion points gives exactly
the field generated by the primitive roots of the reduced Eisenstein factor. -/
theorem torsion_level_reduced
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    D.torsionLevelField K Omega n =
      D.reducedTorsionField K Omega n := by
  let E := D.RootField K n
  let T := D.reducedTorsionField K Omega n
  let e := D.reducedTorsionLevel K Omega hfield n
  have hsplitsE :
      ((D.torsionPolynomial K n).map (algebraMap K E)).Splits :=
    D.torsion_splits_field K hfield n
  have hsplitsT :
      ((D.torsionPolynomial K n).map (algebraMap K T)).Splits := by
    have hmap := hsplitsE.map e.toRingEquiv.toRingHom
    rw [Polynomial.map_map] at hmap
    have hcomp :
        e.toRingEquiv.toRingHom.comp (algebraMap K E) =
          algebraMap K T := by
      apply RingHom.ext
      intro x
      exact e.commutes x
    rw [hcomp] at hmap
    exact hmap
  apply le_antisymm
  · rw [torsionLevelField, IntermediateField.adjoin_le_iff]
    intro x hx
    have hxroot : x ∈ (D.torsionPolynomial K n).rootSet Omega :=
      (D.torsionPolynomial_monic K n).mem_rootSet.mpr hx
    exact ((IntermediateField.splits_iff_mem
      ((IsAlgClosure.isAlgClosed K).splits
        ((D.torsionPolynomial K n).map (algebraMap K Omega)))).mp
          hsplitsT) x hxroot
  · exact D.reduced_torsion_level K Omega n

omit [CompleteSpace K] [ProperSpace K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The coherently chosen primitive point is a zero of the reduced
Eisenstein factor defining its level. -/
theorem aeval_reduced_coherent
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (n : ℕ) :
    Polynomial.aeval (D.coherentTorsionRoot K Omega n)
        (D.reducedPolynomial K n) = 0 := by
  let e := D.coherentAlgHom K Omega n
  calc
    Polynomial.aeval (e (D.root K n)) (D.reducedPolynomial K n) =
        e (Polynomial.aeval (D.root K n)
          (D.reducedPolynomial K n)) :=
      Polynomial.aeval_algHom_apply e (D.root K n)
        (D.reducedPolynomial K n)
    _ = 0 := by rw [D.aeval_root K n, map_zero]

omit [CompleteSpace K] [ProperSpace K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The coherently chosen primitive point belongs to the full finite torsion
zero locus. -/
theorem coherent_torsion_set
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (n : ℕ) :
    D.coherentTorsionRoot K Omega n ∈ D.torsionRootSet K Omega n := by
  rw [torsionRootSet, Set.mem_setOf_eq,
    D.torsionPolynomial_factor K n, map_mul]
  rw [D.aeval_reduced_coherent K Omega n, mul_zero]

set_option maxHeartbeats 3000000 in
-- The degree comparison unfolds the local splitting-field construction used
-- to identify the concrete torsion level with the reduced root field.
/-- The field range of the coherent level embedding is exactly Milne's
concrete finite torsion field in the chosen algebraic closure. -/
theorem coherent_alg_range
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    (D.coherentAlgHom K Omega n).fieldRange =
      D.torsionLevelField K Omega n := by
  let e := D.coherentAlgHom K Omega n
  let T := D.torsionLevelField K Omega n
  let eT : D.RootField K n ≃ₐ[K] T :=
    (D.reducedTorsionLevel K Omega hfield n).trans
      (IntermediateField.equivOfEq
        (D.torsion_level_reduced
          K Omega hfield n).symm)
  letI : Module.Finite K T := Module.Finite.equiv eT.toLinearEquiv
  have hrange_adjoin : e.fieldRange =
      IntermediateField.adjoin K {D.coherentTorsionRoot K Omega n} := by
    calc
      e.fieldRange = (⊤ : IntermediateField K (D.RootField K n)).map e :=
        AlgHom.fieldRange_eq_map e
      _ = (IntermediateField.adjoin K {D.root K n}).map e := by
        rw [D.adjoin_root_top K n]
      _ = IntermediateField.adjoin K {D.coherentTorsionRoot K Omega n} := by
        rw [IntermediateField.adjoin_map, Set.image_singleton]
        rfl
  have hrange_le : e.fieldRange ≤ T := by
    rw [hrange_adjoin]
    apply IntermediateField.adjoin.mono
    rw [Set.singleton_subset_iff]
    exact D.coherent_torsion_set K Omega n
  let eRange : D.RootField K n ≃ₐ[K] e.fieldRange :=
    AlgEquiv.ofInjectiveField e
  apply IntermediateField.eq_of_le_of_finrank_eq hrange_le
  exact eRange.toLinearEquiv.finrank_eq.symm.trans
    eT.toLinearEquiv.finrank_eq

set_option maxHeartbeats 3000000 in
-- The equality with the full torsion field unfolds the full-iterate splitting
-- argument above, in addition to the reduced splitting-field equivalence.
/-- The concrete ambient finite torsion field is algebraically equivalent to
the distinguished abstract root field. -/
noncomputable def rootTorsionLevel
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    D.RootField K n ≃ₐ[K] D.torsionLevelField K Omega n :=
  (AlgEquiv.ofInjectiveField
    (D.coherentAlgHom K Omega n)).trans
    (IntermediateField.equivOfEq
      (D.coherent_alg_range K Omega hfield n))

/-- The coherent abstract-to-concrete equivalences commute with the successor
embedding and the inclusion of consecutive ambient torsion fields. -/
theorem torsion_level_succ
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    (IntermediateField.inclusion
        (D.torsion_mono_succ K Omega n)).comp
        (D.rootTorsionLevel
          K Omega hfield n).toAlgHom =
      (D.rootTorsionLevel
          K Omega hfield (n + 1)).toAlgHom.comp
        (D.rootAlgHom K n) := by
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  change D.coherentAlgHom K Omega n x =
    D.coherentAlgHom K Omega (n + 1)
      (D.rootAlgHom K n x)
  exact (DFunLike.congr_fun
    (D.coherent_alg_succ K Omega n) x).symm

/-- A chosen primitive level-`n + 1` Lubin--Tate torsion point in the common
algebraic closure.  It is the distinguished root in the abstract `AdjoinRoot`
model, transported through splitting-field uniqueness. -/
noncomputable def torsionLevelPrimitive
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    D.torsionLevelField K Omega n :=
  D.rootTorsionLevel K Omega hfield n (D.root K n)

@[simp]
theorem coe_torsion_primitive
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    ((D.torsionLevelPrimitive K Omega hfield n :
      D.torsionLevelField K Omega n) : Omega) =
      D.coherentTorsionRoot K Omega n := rfl

/-- The concrete primitive torsion points inherit the coherent recursion from
the chosen algebraic-closure embeddings. -/
theorem aeval_f_primitive
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    Polynomial.aeval
        ((D.torsionLevelPrimitive K Omega hfield (n + 1) :
          D.torsionLevelField K Omega (n + 1)) : Omega)
        (D.f.map (algebraMap
          (Valuation.integer (NormedField.valuation (K := K))) K)) =
      ((D.torsionLevelPrimitive K Omega hfield n :
        D.torsionLevelField K Omega n) : Omega) := by
  rw [D.coe_torsion_primitive K Omega hfield,
    D.coe_torsion_primitive K Omega hfield]
  exact D.aeval_f_coherent K Omega n

/-- The chosen ambient primitive point is a zero of the reduced Eisenstein
factor defining its level. -/
theorem aeval_reduced_primitive
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    Polynomial.aeval
        ((D.torsionLevelPrimitive K Omega hfield n :
          D.torsionLevelField K Omega n) : Omega)
        (D.reducedPolynomial K n) = 0 := by
  rw [D.coe_torsion_primitive K Omega hfield]
  exact D.aeval_reduced_coherent K Omega n

/-- The chosen primitive point is, in particular, a point of Milne's full
level-`n + 1` torsion zero locus. -/
theorem torsion_primitive_set
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    ((D.torsionLevelPrimitive K Omega hfield n :
      D.torsionLevelField K Omega n) : Omega) ∈
      D.torsionRootSet K Omega n := by
  rw [torsionRootSet, Set.mem_setOf_eq,
    D.torsionPolynomial_factor K n, map_mul]
  rw [D.aeval_reduced_primitive
    K Omega hfield n, mul_zero]

/-- The chosen primitive torsion point generates the complete concrete finite
level over `K`. -/
theorem adjoin_primitive_top
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    IntermediateField.adjoin K
        {D.torsionLevelPrimitive K Omega hfield n} = ⊤ := by
  let e := D.rootTorsionLevel K Omega hfield n
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy : y ∈ IntermediateField.adjoin K {D.root K n} := by
    rw [D.adjoin_root_top K n]
    trivial
  have hmap : e y ∈
      (IntermediateField.adjoin K {D.root K n}).map e.toAlgHom :=
    (IntermediateField.map_mem_map
      (IntermediateField.adjoin K {D.root K n}) e.toAlgHom).2 hy
  rw [IntermediateField.adjoin_map, Set.image_singleton] at hmap
  exact hmap

/-- An automorphism of a concrete finite torsion level is determined by its
value on the chosen primitive torsion point. -/
theorem torsion_level_ext
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ)
    {σ τ : D.torsionLevelField K Omega n ≃ₐ[K]
      D.torsionLevelField K Omega n}
    (h : σ (D.torsionLevelPrimitive K Omega hfield n) =
      τ (D.torsionLevelPrimitive K Omega hfield n)) :
    σ = τ := by
  let e := D.rootTorsionLevel K Omega hfield n
  apply (AlgEquiv.autCongr e).symm.injective
  apply AlgEquiv.ext
  intro x
  have hhom : ((AlgEquiv.autCongr e).symm σ).toAlgHom =
      ((AlgEquiv.autCongr e).symm τ).toAlgHom := by
    apply AdjoinRoot.algHom_ext
    simpa only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
      AlgEquiv.apply_symm_apply, torsionLevelPrimitive, e] using
        congrArg e.symm h
  exact DFunLike.congr_fun hhom x

set_option maxHeartbeats 2000000 in
-- This reuses the same splitting-field equivalence and its spectral instance
-- telescope, then transports the already computed abstract root-field degree.
/-- The primitive-root field in the common algebraic closure has Milne's
finite-level degree `(q - 1) * q^n`. -/
theorem finrank_reduced_torsion
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    Module.finrank K (D.reducedTorsionField K Omega n) =
      (D.q - 1) * D.q ^ n := by
  rw [← D.finrank_rootField K n]
  let e := D.reducedTorsionLevel K Omega hfield n
  exact e.toLinearEquiv.finrank_eq.symm

set_option maxHeartbeats 3000000 in
-- Rewriting the ambient full level to the primitive splitting field unfolds
-- the same spectral splitting argument as the preceding equality theorem.
/-- The actual finite torsion field in the common algebraic closure has the
degree asserted in Theorem I.3.6(a). -/
theorem finrank_torsion_level
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    Module.finrank K (D.torsionLevelField K Omega n) =
      (D.q - 1) * D.q ^ n := by
  rw [D.torsion_level_reduced K Omega hfield n]
  exact D.finrank_reduced_torsion K Omega hfield n

end LocalAmbientTower

end LTDatum

end

end Towers.CField.LTate
