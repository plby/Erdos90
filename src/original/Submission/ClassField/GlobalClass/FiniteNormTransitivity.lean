import Mathlib.RingTheory.Norm.Transitivity
import Submission.ClassField.NormIndex.IdeleExtensionMap
import Submission.ClassField.NormIndex.IdeleTowerLocal
import Submission.ClassField.NormIndex.IdeleTowerPlaces
import Submission.ClassField.GlobalClass.Transitivity

/-!
# Finite-idèle norm transitivity without a Galois hypothesis

The idèle norm of Chapter V is defined for every finite extension, but the
first tower theorem was proved through Galois-coordinate maps.  Norm
limitation needs the source's unrestricted tower.  Here the same completed
norms are reindexed by literal upper primes and their extension maps are
compared directly on the dense global field; no Galois action is used.
-/

namespace Submission.CField.GClass

open IsDedekindDomain NumberField
open Submission.CField.Ideles
open Submission.CField.NIndex

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  RingOfIntegers K

/-- Reindex a dependent family along an equivalence. -/
private def reindexDependent {α β : Type*} (P : β → Sort*) (e : α ≃ β)
    (f : (a : α) → P (e a)) (b : β) : P b :=
  e.apply_symm_apply b ▸ f (e.symm b)

private theorem reindexDependent_apply {α β : Type*} (P : β → Sort*)
    (e : α ≃ β) (f : (a : α) → P (e a)) (a : α) :
    reindexDependent P e f (e a) = f a := by
  change Equiv.piCongrLeft P e f (e a) = f a
  exact Equiv.piCongrLeft_apply_apply P e f a

/-- The semilocal factor embedding, reindexed by its literal upper prime.
Unlike the Galois-coordinate embedding, this is defined for every finite
extension. -/
noncomputable def literalExtensionHom
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (Q : PlacesAbovePrime K L P) :
    P.adicCompletion K →+* Q.1.adicCompletion L :=
  reindexDependent
    (fun Q : PlacesAbovePrime K L P ↦
      P.adicCompletion K →+* Q.1.adicCompletion L)
    (upperPlacesAbove
      (K := K) (L := L) P)
    (fun q ↦ factorExtensionHom (K := K) (L := L) P q) Q

private theorem literal_extension_ring
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (q : UpperPrimeFactors (K := K) (L := L) P) :
    literalExtensionHom (K := K) (L := L) P
        (upperPlacesAbove
          (K := K) (L := L) P q) =
      factorExtensionHom (K := K) (L := L) P q :=
  reindexDependent_apply _ _ _ q

set_option maxRecDepth 100000 in
/-- The literal-prime embedding agrees with the global field embeddings. -/
theorem literal_comp_embedding
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (Q : PlacesAbovePrime K L P) (x : K) :
    literalExtensionHom (K := K) (L := L) P Q
        (FinitePlace.embedding P x) =
      FinitePlace.embedding Q.1 (algebraMap K L x) := by
  let e := upperPlacesAbove
    (K := K) (L := L) P
  obtain ⟨q, rfl⟩ := e.surjective Q
  rw [literal_extension_ring]
  exact ring_comp_embedding
    (K := K) (L := L) P q x

/-- The literal-prime embedding is continuous. -/
theorem literal_extension_continuous
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (Q : PlacesAbovePrime K L P) :
    Continuous (literalExtensionHom
      (K := K) (L := L) P Q) := by
  let e := upperPlacesAbove
    (K := K) (L := L) P
  obtain ⟨q, rfl⟩ := e.surjective Q
  rw [literal_extension_ring]
  exact factor_extension_continuous
    (K := K) (L := L) P q

set_option maxHeartbeats 2000000 in
-- The two compositions are determined by their values on the dense base field.
/-- Literal finite-completion embeddings are transitive in every finite
number-field tower. -/
theorem literal_extension_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    (P : HeightOneSpectrum (OK K))
    (Q : PlacesAbovePrime K E P)
    (R : PlacesAbovePrime E L Q.1) :
    (literalExtensionHom (K := E) (L := L) Q.1 R).comp
        (literalExtensionHom (K := K) (L := E) P Q) =
      literalExtensionHom (K := K) (L := L) P
        ((placesAboveTower K E L P).symm ⟨Q, R⟩) := by
  apply DFunLike.ext _ _
  intro z
  exact congrFun
    ((P.denseRange_algebraMap K).equalizer
      ((literal_extension_continuous Q.1 R).comp
        (literal_extension_continuous P Q))
      (literal_extension_continuous P
        ((placesAboveTower K E L P).symm ⟨Q, R⟩))
      (funext fun x ↦ by
        change literalExtensionHom (K := E) (L := L) Q.1 R
            (literalExtensionHom (K := K) (L := E) P Q
              (FinitePlace.embedding P x)) =
          literalExtensionHom (K := K) (L := L) P
            ((placesAboveTower K E L P).symm ⟨Q, R⟩)
              (FinitePlace.embedding P x)
        rw [literal_comp_embedding,
          literal_comp_embedding,
          literal_comp_embedding,
          ← IsScalarTower.algebraMap_apply K E L]
        rfl)) z

/-- The completed norm, reindexed by the literal upper prime. -/
noncomputable def finiteLiteralNorm
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (Q : PlacesAbovePrime K L P) :
    (Q.1.adicCompletion L)ˣ →* (P.adicCompletion K)ˣ :=
  reindexDependent
    (fun Q : PlacesAbovePrime K L P ↦
      (Q.1.adicCompletion L)ˣ →* (P.adicCompletion K)ˣ)
    (upperPlacesAbove
      (K := K) (L := L) P)
    (fun q ↦ finiteCompletionNorm (K := K) (L := L) P q) Q

private theorem literal_norm_equiv
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (q : UpperPrimeFactors (K := K) (L := L) P) :
    finiteLiteralNorm (K := K) (L := L) P
        (upperPlacesAbove
          (K := K) (L := L) P q) =
      finiteCompletionNorm (K := K) (L := L) P q :=
  reindexDependent_apply _ _ _ q

set_option maxRecDepth 100000 in
/-- A literal-prime norm is the algebra norm for the corresponding literal
completion embedding. -/
theorem literal_norm_algebra
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (Q : PlacesAbovePrime K L P) :
    letI : Algebra (P.adicCompletion K) (Q.1.adicCompletion L) :=
      (literalExtensionHom (K := K) (L := L) P Q).toAlgebra
    finiteLiteralNorm (K := K) (L := L) P Q =
      Units.map (Algebra.norm (P.adicCompletion K)) := by
  let e := upperPlacesAbove
    (K := K) (L := L) P
  obtain ⟨q, rfl⟩ := e.surjective Q
  rw [literal_norm_equiv,
    literal_extension_ring]
  rfl

set_option maxHeartbeats 2000000 in
-- Four finite-dimensional completion-module instances must be aligned.
set_option maxRecDepth 100000 in
/-- Completed norms are transitive at a literal prime in an arbitrary
finite tower. -/
theorem literal_norm_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    (P : HeightOneSpectrum (OK K))
    (Q : PlacesAbovePrime K E P)
    (R : PlacesAbovePrime E L Q.1)
    (z : (R.1.adicCompletion L)ˣ) :
    finiteLiteralNorm (K := K) (L := L) P
        ((placesAboveTower K E L P).symm ⟨Q, R⟩) z =
      finiteLiteralNorm (K := K) (L := E) P Q
        (finiteLiteralNorm (K := E) (L := L) Q.1 R z) := by
  let RKL := (placesAboveTower K E L P).symm ⟨Q, R⟩
  let fKE := literalExtensionHom (K := K) (L := E) P Q
  let fEL := literalExtensionHom (K := E) (L := L) Q.1 R
  let fKL := literalExtensionHom (K := K) (L := L) P RKL
  letI : Algebra (P.adicCompletion K) (Q.1.adicCompletion E) :=
    fKE.toAlgebra
  letI : Algebra (Q.1.adicCompletion E) (R.1.adicCompletion L) :=
    fEL.toAlgebra
  letI : Algebra (P.adicCompletion K) (R.1.adicCompletion L) :=
    fKL.toAlgebra
  letI : Module.Free (P.adicCompletion K) (Q.1.adicCompletion E) :=
    Module.Free.of_divisionRing _ _
  letI : Module.Free (Q.1.adicCompletion E) (R.1.adicCompletion L) :=
    Module.Free.of_divisionRing _ _
  letI : Module.Free (P.adicCompletion K) (R.1.adicCompletion L) :=
    Module.Free.of_divisionRing _ _
  letI : IsScalarTower (P.adicCompletion K) (Q.1.adicCompletion E)
      (R.1.adicCompletion L) := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (literal_extension_trans P Q R).symm
  rw [literal_norm_algebra,
    literal_norm_algebra,
    literal_norm_algebra]
  apply Units.ext
  exact (Algebra.norm_norm
    (R := P.adicCompletion K)
    (S := Q.1.adicCompletion E)
    (A := R.1.adicCompletion L)).symm

/-- The original finite idèle norm coordinate is the product of the
literal-prime norms. -/
theorem idele_prod_literal
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (x : FiniteIdeles (OK L) L) :
    finiteNorm (K := K) (L := L) P x =
      ∏ Q : PlacesAbovePrime K L P,
        finiteLiteralNorm (K := K) (L := L) P Q (x.1 Q.1) := by
  let e := upperPlacesAbove
    (K := K) (L := L) P
  change (∏ q : UpperPrimeFactors (K := K) (L := L) P,
      finiteCompletionNorm (K := K) (L := L) P q
        (x.1 (upperPrime (K := K) (L := L) P q))) = _
  calc
    _ = ∏ q : UpperPrimeFactors (K := K) (L := L) P,
        finiteLiteralNorm (K := K) (L := L) P (e q)
          (x.1 (e q).1) := by
      apply Finset.prod_congr rfl
      intro q _
      exact DFunLike.congr_fun
        (literal_norm_equiv P q) _ |>.symm
    _ = _ := e.prod_comp (fun Q ↦
      finiteLiteralNorm (K := K) (L := L) P Q (x.1 Q.1))

set_option maxHeartbeats 2000000 in
-- Reindexing the dependent product exposes the local norm-tower identity.
set_option maxRecDepth 100000 in
/-- Transitivity of the finite component of the idèle norm for every finite
number-field tower. -/
theorem idele_trans_arbitrary
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    (x : FiniteIdeles (OK L) L) :
    finiteIdeleNorm (K := K) (L := L) x =
      finiteIdeleNorm (K := K) (L := E)
        (finiteIdeleNorm (K := E) (L := L) x) := by
  apply RestrictedProduct.ext
  intro P
  change finiteNorm (K := K) (L := L) P x =
    finiteNorm (K := K) (L := E) P
      (finiteIdeleNorm (K := E) (L := L) x)
  rw [idele_prod_literal,
    idele_prod_literal]
  let e := placesAboveTower K E L P
  calc
    (∏ R : PlacesAbovePrime K L P,
        finiteLiteralNorm (K := K) (L := L) P R (x.1 R.1)) =
        ∏ QR : Σ Q : PlacesAbovePrime K E P,
            PlacesAbovePrime E L Q.1,
          finiteLiteralNorm (K := K) (L := L) P (e.symm QR)
            (x.1 QR.2.1) := by
      exact (e.symm.prod_comp (fun R ↦
        finiteLiteralNorm (K := K) (L := L) P R (x.1 R.1))).symm
    _ = ∏ Q : PlacesAbovePrime K E P,
        ∏ R : PlacesAbovePrime E L Q.1,
          finiteLiteralNorm (K := K) (L := L) P (e.symm ⟨Q, R⟩)
            (x.1 R.1) := Fintype.prod_sigma _
    _ = ∏ Q : PlacesAbovePrime K E P,
        ∏ R : PlacesAbovePrime E L Q.1,
          finiteLiteralNorm (K := K) (L := E) P Q
            (finiteLiteralNorm (K := E) (L := L) Q.1 R
              (x.1 R.1)) := by
      apply Finset.prod_congr rfl
      intro Q _
      apply Finset.prod_congr rfl
      intro R _
      exact literal_norm_trans P Q R (x.1 R.1)
    _ = ∏ Q : PlacesAbovePrime K E P,
        finiteLiteralNorm (K := K) (L := E) P Q
          (∏ R : PlacesAbovePrime E L Q.1,
            finiteLiteralNorm (K := E) (L := L) Q.1 R
              (x.1 R.1)) := by
      apply Finset.prod_congr rfl
      intro Q _
      rw [map_prod]
    _ = ∏ Q : PlacesAbovePrime K E P,
        finiteLiteralNorm (K := K) (L := E) P Q
          ((finiteIdeleNorm (K := E) (L := L) x).1 Q.1) := by
      apply Finset.prod_congr rfl
      intro Q _
      rw [finite_idele_norm,
        idele_prod_literal]

/-- The concrete idèle norm is transitive in every finite number-field
tower. -/
theorem norm_trans_arbitrary
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L] :
    ideleNorm (K := K) (L := L) =
      (ideleNorm (K := K) (L := E)).comp
        (ideleNorm (K := E) (L := L)) := by
  apply MonoidHom.ext
  intro x
  apply Prod.ext
  · exact DFunLike.congr_fun
      (infinite_idele_trans (K := K) (E := E) (L := L)) x.1
  · exact idele_trans_arbitrary (K := K) (E := E) (L := L) x.2

/-- The unrestricted concrete norm theorem supplies the transitivity bridge
used by Theorem VIII.4.8. -/
theorem transitivityIdeleBridge :
    TransitivityIdeleBridge.{u} := by
  intro K E L _ _ _ _ _ _ _ _ _ _ _
  exact norm_trans_arbitrary (K := K) (E := E) (L := L)

/-- The containment half of norm limitation is now unconditional. -/
theorem normContainmentBridge :
    NormContainmentBridge.{u} :=
  containment_bridge_transitivity
    transitivityIdeleBridge

/-- Consequently the full norm limitation theorem now retains only Milne's
corestriction/index comparison. -/
theorem norm_transitivity_index
    (hindex : IndexBridge.{u}) :
    MaximalSubextensionEquality.{u} :=
  containment_index normContainmentBridge hindex

end

end Submission.CField.GClass
