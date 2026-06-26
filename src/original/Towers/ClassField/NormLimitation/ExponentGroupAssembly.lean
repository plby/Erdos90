import Towers.ClassField.NormLimitation.SubgroupQuotientMap
import Towers.ClassField.NormLimitation.FiniteQuotients
import Towers.ClassField.NormLimitation.ExistenceInterface
import Towers.ClassField.NormLimitation.CoreDefinitions
import Towers.ClassField.NormLimitation.OpenCoreStatement
import Towers.ClassField.NormLimitation.KummerCoreStatement

/-!
# Chapter VII, Section 9, Lemma 9.3

This is the exponent-`p` case of the existence theorem.  An open subgroup
`V` contains the classes of all idèles which are units away from a suitable
finite set `S`; if `C_K / V` is killed by `p`, it also contains every `p`th
power.  Kummer theory constructs a norm group inside the subgroup generated
by those two concrete pieces, and Lemma 9.1 then promotes `V` itself to a
norm group.
-/

namespace Towers.CField.NLimita

open IsDedekindDomain NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.NIndex
open Towers.CField.KNIndex

noncomputable section

universe u

private abbrev CK (K : Type u) [Field K] [NumberField K] :=
  IdeleClassGroup (RingOfIntegers K) K

/-- Lemma 9.3 from the open-neighborhood and Kummer norm-core inputs,
with all quotient and subgroup calculations proved here. -/
theorem exponent_prime_bridges
    (h91 : (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V))
    (hopen : OpenCoreBridge.{u})
    (hkummer : KummerCoreBridge.{u}) :
    ExistenceStatementInterface.{u} := by
  intro p K _ _ hp hroots V hVopen _hVfinite hexponent
  obtain ⟨S, hInfinite, hDividing, hClass, hOutside⟩ :=
    hopen p K hp V hVopen
  have hPowers : (powMonoidHom p : CK K →* CK K).range ≤ V := by
    rintro _ ⟨x, rfl⟩
    exact pow_quotient_exponent V p hexponent x
  have hCore : kummerCore K p S ≤ V :=
    sup_le hPowers hOutside
  obtain ⟨L, hL⟩ :=
    hkummer p K hp hroots S hInfinite hDividing hClass
  apply h91 K (ideleClassSubgroup L) V
  · exact ⟨L, rfl⟩
  · exact hL.trans hCore

end

end Towers.CField.NLimita
