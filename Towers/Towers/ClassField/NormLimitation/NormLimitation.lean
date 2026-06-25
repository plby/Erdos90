import Towers.ClassField.NormLimitation.NormLimitationBridge
import Towers.ClassField.GlobalClass.Existential
import Towers.ClassField.GlobalClass.FiniteNormTransitivity

/-!
# Norm limitation in the form used by Lemma VII.9.4

For an abelian extension `L/K'`, arbitrary-tower norm transitivity identifies
the image under `Nm_{K'/K}` of its norm group with `Nm_{L/K}(C_L)`.
The existential form of Theorem VIII.4.8 then realizes this image as a
finite abelian norm group over `K`.
-/

namespace Towers.CField.NLimita

open NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.GClass

noncomputable section

universe u

noncomputable local instance extensionNumberField
    {K' : Type u} [Field K'] [NumberField K']
    (L : FASubext K') : NumberField L.1 :=
  NumberField.of_module_finite K' L.1

/-- The existential form of norm limitation supplies exactly the bridge
used in Lemma VII.9.4. -/
theorem limitation_bridge_global
    (h48 : ExistentialNormLimitation.{u}) :
    NormLimitationBridge.{u} := by
  intro K K' _ _ _ _ _ _ L
  let E := L.1
  letI : Algebra K E :=
    ((algebraMap K' E).comp (algebraMap K K')).toAlgebra
  letI : IsScalarTower K K' E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : FiniteDimensional K E := FiniteDimensional.trans K K' E
  obtain ⟨M, hM⟩ := h48 K E
  refine ⟨M, ?_⟩
  rw [hM, idele_class_range]
  have htrans : canonicalIdeleNorm (K := K) (L := E) =
      (canonicalIdeleNorm (K := K) (L := K')).comp
        (canonicalIdeleNorm (K := K') (L := E)) :=
    canonical_idele_trans
      (norm_trans_arbitrary (K := K) (E := K') (L := E))
  rw [htrans, MonoidHom.range_comp]

/-- Lemma VII.9.4 now follows from Lemma 9.1 and the existential Norm
Limitation Theorem, with no additional arithmetic hypotheses. -/
theorem normLimitationStatement
    (h91 : (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V))
    (h48 : ExistentialNormLimitation.{u}) :
    (∀ (K K' : Type u) [Field K] [NumberField K]
          [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
          (U : Subgroup (IdeleClassGroup (NumberField.RingOfIntegers K) K)),
          IsOpen (U : Set (IdeleClassGroup (NumberField.RingOfIntegers K) K)) → U.FiniteIndex →
          IdeleNormGroup K'
            (U.comap (canonicalIdeleNorm (K := K) (L := K'))) →
          IdeleNormGroup K U) :=
  limitation_statement_bridges h91
    (limitation_bridge_global h48)

end

end Towers.CField.NLimita
