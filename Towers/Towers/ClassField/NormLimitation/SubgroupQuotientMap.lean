import Towers.ClassField.NormLimitation.ExistenceStatement

/-!
# Chapter VII, Section 9, Lemma 9.1

A subgroup containing a norm group is again a norm group.  The group-theoretic
heart is that, for a surjection `f : C → G`, every subgroup `V` containing
`ker f` is the kernel of the induced map to `G / f(V)`.  Global reciprocity
and Galois correspondence identify these two kernels with the norm groups of
the original extension and the corresponding fixed field.
-/

namespace Towers.CField.NLimita

open NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip

noncomputable section

universe u

/-- The quotient map associated to a subgroup `V` and a homomorphism `f`. -/
def subgroupQuotientMap
    {C G : Type*} [CommGroup C] [CommGroup G]
    (f : C →* G) (V : Subgroup C) : C →* (G ⧸ V.map f) :=
  (QuotientGroup.mk' (V.map f)).comp f

/-- The elementary kernel calculation in Lemma 9.1. -/
theorem subgroup_quotient_ker
    {C G : Type*} [CommGroup C] [CommGroup G]
    (f : C →* G)
    (V : Subgroup C) (hker : f.ker ≤ V) :
    (subgroupQuotientMap f V).ker = V := by
  ext x
  constructor
  · intro hx
    have hfx : f x ∈ V.map f := by
      rw [← QuotientGroup.eq_one_iff]
      exact hx
    obtain ⟨v, hv, hfv⟩ := hfx
    have hxv : x * v⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfv]
      simp
    have hxvV := hker hxv
    have hvInv : v⁻¹ ∈ V := V.inv_mem hv
    have := V.mul_mem hxvV (V.inv_mem hvInv)
    simpa using this
  · intro hx
    change QuotientGroup.mk' (V.map f) (f x) = 1
    exact (QuotientGroup.eq_one_iff _).2 ⟨x, hx, rfl⟩

variable (K : Type u) [Field K] [NumberField K]

/-- A finite Artin map with exactly the kernel supplied by reciprocity. -/
structure FiniteArtinData (L : FASubext K) where
  artin : IdeleClassGroup (RingOfIntegers K) K →* Gal(L.1/K)
  surjective : Function.Surjective artin
  ker_norm_group : artin.ker = ideleClassSubgroup L

/-- The finite-layer consequence of Theorem 8.1 and the first inequality:
the Artin map is onto and has the expected norm kernel. -/
def FiniteReciprocityBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : FASubext K),
    Nonempty (FiniteArtinData K L)

/-- The fixed-field step in Milne's proof.  For a subgroup `H` of the finite
Galois group, the norm group of its fixed field is the kernel of the Artin
map followed by `G → G/H`.  This bridge contains no arbitrary supergroup of
the idèle class group. -/
def FixedNormBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : FASubext K)
    (data : FiniteArtinData K L)
    (H : Subgroup Gal(L.1/K)),
    ∃ M : FASubext K,
      ideleClassSubgroup M =
        ((QuotientGroup.mk' H).comp data.artin).ker

/-- Lemma 9.1 from finite reciprocity, the general quotient-kernel
calculation, and the fixed-field norm identification. -/
theorem subgroup_statement_bridges
    (hreciprocity : FiniteReciprocityBridge.{u})
    (hfixed : FixedNormBridge.{u})
    (K : Type u) [Field K] [NumberField K]
    (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K))
    (hU : IdeleNormGroup K U) (hUV : U ≤ V) :
    IdeleNormGroup K V := by
  obtain ⟨L, hL⟩ := hU
  letI : CommGroup Gal(L.1/K) :=
    { (inferInstance : Group Gal(L.1/K)) with mul_comm := mul_comm' }
  obtain ⟨data⟩ := hreciprocity K L
  have hker : data.artin.ker ≤ V :=
    (data.ker_norm_group.trans hL).le.trans hUV
  let H : Subgroup Gal(L.1/K) := V.map data.artin
  obtain ⟨M, hM⟩ := hfixed K L data H
  exact ⟨M, hM.trans (subgroup_quotient_ker data.artin V hker)⟩

end

end Towers.CField.NLimita
