import Mathlib.GroupTheory.Index
import Submission.ClassField.Ideles.IdeleClassNorm
import Submission.ClassField.KummerNormIndex.CoprimeExponent

/-!
# Chapter VII, Section 6, Lemma 6.1

Let `L/K` be cyclic of prime degree `p`.  Milne adjoins a primitive `p`th
root of unity, obtaining a square of fields with coprime auxiliary degree
`m ∣ p - 1`.  The two commuting norm squares induce maps

`C_K / Nm(C_L) → C_K' / Nm(C_L') → C_K / Nm(C_L)`.

Their composite is the `m`th-power map.  Since the first quotient is killed
by `p`, this composite is an automorphism.  The second map is consequently
surjective, so the original norm index divides the cyclotomic one.

The quotients and all four norm maps below are the actual idèle-class norm
quotients and canonical norm homomorphisms.  The cyclotomic field square
and the degree-power norm identity are kept as separately named bridges so
that the source's diagram chase remains visible; both are discharged by
the companion files in this section.
-/

namespace Submission.CField.KNIndex

open IsDedekindDomain NumberField
open Submission.CField.Ideles

noncomputable section

universe u

private abbrev CK (K : Type u) [Field K] [NumberField K] :=
  IdeleClassGroup (RingOfIntegers K) K

/-- The literal quotient `C_K / Nm(C_L)`. -/
abbrev IdeleNormQuotient
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :=
  CK K ⧸ (canonicalIdeleNorm (K := K) (L := L)).range

/-- The idèlic second inequality for one extension, stated using the actual
class-group norm quotient. -/
def SecondInequalityAt
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Prop :=
  Finite (IdeleNormQuotient K L) ∧
    Nat.card (IdeleNormQuotient K L) ∣ Module.finrank K L

/-- The cyclotomic field square and the two left-hand squares in Milne's
diagram.  The degree fields record

```
       L'
     m/  \p
     L    K'
     p\  /m
        K.
```

The maps `iK` and `iL` are the class maps induced by inclusion.  The final
two fields are exactly `Nm ∘ i = (·)^m` on the two class groups. -/
structure CCDataa
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (p : ℕ) where
  K' : Type u
  L' : Type u
  fieldK' : Field K'
  fieldL' : Field L'
  numberFieldK' : NumberField K'
  numberFieldL' : NumberField L'
  algebraKK' : Algebra K K'
  algebraLL' : Algebra L L'
  algebraK'L' : Algebra K' L'
  algebraKL' : Algebra K L'
  scalarTowerKK'L' : IsScalarTower K K' L'
  scalarTowerKLL' : IsScalarTower K L L'
  finiteDimensionalKK' : FiniteDimensional K K'
  finiteDimensionalLL' : FiniteDimensional L L'
  finiteDimensionalK'L' : FiniteDimensional K' L'
  isGaloisK'L' : IsGalois K' L'
  isCyclicK'L' : IsCyclic Gal(L'/K')
  m : ℕ
  primitiveRoot : (primitiveRoots p K').Nonempty
  degreeTop : Module.finrank K' L' = p
  degreeLeft : Module.finrank L L' = m
  degreeRight : Module.finrank K K' = m
  m_dvd_pred : m ∣ p - 1
  iK : CK K →* CK K'
  iL : CK L →* CK L'
  topSquare :
    iK.comp (canonicalIdeleNorm (K := K) (L := L)) =
      (canonicalIdeleNorm (K := K') (L := L')).comp iL
  bottomSquare :
    (canonicalIdeleNorm (K := K) (L := K')).comp
        (canonicalIdeleNorm (K := K') (L := L')) =
      (canonicalIdeleNorm (K := K) (L := L)).comp
        (canonicalIdeleNorm (K := L) (L := L'))
  downUpK :
    (canonicalIdeleNorm (K := K) (L := K')).comp iK =
      powMonoidHom m
  downUpL :
    (canonicalIdeleNorm (K := L) (L := L')).comp iL =
      powMonoidHom m

/-- The exact cyclotomic construction used in Lemma 6.1.  It asserts only
the displayed field square and its norm compatibilities, not either second
inequality. -/
def CyclotomicChangeBridge : Prop :=
  ∀ (p : ℕ), p.Prime →
    ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [IsCyclic Gal(L/K)],
      Module.finrank K L = p →
        Nonempty (CCDataa K L p)

/-- The standard norm identity used in the source: the norm of the class
obtained by extending an idèle class is its degree-th power.  Equivalently,
the actual norm quotient is killed by the extension degree. -/
def NormExponentBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    ∀ x : IdeleNormQuotient K L,
      x ^ Module.finrank K L = 1

private theorem map_le_eq
    {A B G H : Type*} [Group A] [Group B] [Group G] [Group H]
    (f : G →* H) (g : A →* G) (k : B →* H) (n : A →* B)
    (h : f.comp g = k.comp n) :
    g.range.map f ≤ k.range := by
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  exact ⟨n a, (DFunLike.congr_fun h a).symm⟩

namespace CCDataa

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
  {p : ℕ} (D : CCDataa K L p)

attribute [local instance]
  fieldK' fieldL' numberFieldK' numberFieldL'
  algebraKK' algebraLL' algebraK'L' algebraKL'
  scalarTowerKK'L' scalarTowerKLL'
  finiteDimensionalKK' finiteDimensionalLL' finiteDimensionalK'L'
  isGaloisK'L' isCyclicK'L'

/-- The upward map on the actual norm quotients induced by `iK`. -/
def up : IdeleNormQuotient K L →*
    IdeleNormQuotient D.K' D.L' :=
  QuotientGroup.map
    (canonicalIdeleNorm (K := K) (L := L)).range
    (canonicalIdeleNorm (K := D.K') (L := D.L')).range
    D.iK
    (Subgroup.map_le_iff_le_comap.mp
      (map_le_eq D.iK
        (canonicalIdeleNorm (K := K) (L := L))
        (canonicalIdeleNorm (K := D.K') (L := D.L'))
        D.iL D.topSquare))

/-- The downward map on the actual norm quotients induced by
`Nm_{K'/K}`. -/
def down : IdeleNormQuotient D.K' D.L' →*
    IdeleNormQuotient K L :=
  QuotientGroup.map
    (canonicalIdeleNorm (K := D.K') (L := D.L')).range
    (canonicalIdeleNorm (K := K) (L := L)).range
    (canonicalIdeleNorm (K := K) (L := D.K'))
    (Subgroup.map_le_iff_le_comap.mp
      (map_le_eq
        (canonicalIdeleNorm (K := K) (L := D.K'))
        (canonicalIdeleNorm (K := D.K') (L := D.L'))
        (canonicalIdeleNorm (K := K) (L := L))
        (canonicalIdeleNorm (K := L) (L := D.L'))
        D.bottomSquare))

/-- The down-after-up composite in Milne's diagram is multiplication by
`m` (multiplicatively, the `m`th-power map). -/
theorem down_up_apply (x : IdeleNormQuotient K L) :
    D.down (D.up x) = x ^ D.m := by
  refine Quotient.inductionOn' x fun c ↦ ?_
  change QuotientGroup.mk' _
      ((canonicalIdeleNorm (K := K) (L := D.K')) (D.iK c)) =
    QuotientGroup.mk' _ (c ^ D.m)
  have hc := DFunLike.congr_fun D.downUpK c
  change (canonicalIdeleNorm (K := K) (L := D.K')) (D.iK c) =
    c ^ D.m at hc
  exact congrArg (QuotientGroup.mk'
    (canonicalIdeleNorm (K := K) (L := L)).range) hc

end CCDataa

/-- A divisor of `p - 1` is coprime to the prime `p`. -/
private theorem coprime_dvd_pred
    {m p : ℕ} (hp : p.Prime) (hm : m ∣ p - 1) : m.Coprime p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hpm
  have hppred : p ∣ p - 1 := hpm.trans hm
  have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hle : p ≤ p - 1 := Nat.le_of_dvd hpos hppred
  omega

namespace CCDataa

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
  {p : ℕ} (D : CCDataa K L p)

attribute [local instance]
  fieldK' fieldL' numberFieldK' numberFieldL'
  algebraKK' algebraLL' algebraK'L' algebraKL'
  scalarTowerKK'L' scalarTowerKLL'
  finiteDimensionalKK' finiteDimensionalLL' finiteDimensionalK'L'
  isGaloisK'L' isCyclicK'L'

/-- The composite being an automorphism forces the downward quotient map to
be surjective. -/
theorem down_surjective
    (hp : p.Prime)
    (hexponent : ∀ x : IdeleNormQuotient K L, x ^ p = 1) :
    Function.Surjective D.down := by
  have hcop : D.m.Coprime p :=
    coprime_dvd_pred hp D.m_dvd_pred
  have hpow :=
    surjective_coprime_exponent
      (A := IdeleNormQuotient K L) hcop hexponent
  intro y
  obtain ⟨x, hx⟩ := hpow y
  exact ⟨D.up x, by
    rw [D.down_up_apply]
    exact hx⟩

end CCDataa

/-- The formal diagram chase in Lemma 6.1. -/
theorem idele_statement_bridges
    (hbase : CyclotomicChangeBridge.{u})
    (hexponent : NormExponentBridge.{u}) :
    (∀ (p : ℕ), p.Prime →
          (∀ (K L : Type u) [Field K] [Field L]
            [NumberField K] [NumberField L]
            [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
            [IsCyclic Gal(L/K)],
            (primitiveRoots p K).Nonempty → Module.finrank K L = p →
              SecondInequalityAt K L) →
          ∀ (K L : Type u) [Field K] [Field L]
            [NumberField K] [NumberField L]
            [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
            [IsCyclic Gal(L/K)],
            Module.finrank K L = p → SecondInequalityAt K L) := by
  intro p hp hroot K L _ _ _ _ _ _ _ _ hdegree
  obtain ⟨D⟩ := hbase p hp K L hdegree
  letI : Field D.K' := D.fieldK'
  letI : Field D.L' := D.fieldL'
  letI : NumberField D.K' := D.numberFieldK'
  letI : NumberField D.L' := D.numberFieldL'
  letI : Algebra K D.K' := D.algebraKK'
  letI : Algebra L D.L' := D.algebraLL'
  letI : Algebra D.K' D.L' := D.algebraK'L'
  letI : Algebra K D.L' := D.algebraKL'
  letI : IsScalarTower K D.K' D.L' := D.scalarTowerKK'L'
  letI : IsScalarTower K L D.L' := D.scalarTowerKLL'
  letI : FiniteDimensional K D.K' := D.finiteDimensionalKK'
  letI : FiniteDimensional L D.L' := D.finiteDimensionalLL'
  letI : FiniteDimensional D.K' D.L' := D.finiteDimensionalK'L'
  letI : IsGalois D.K' D.L' := D.isGaloisK'L'
  letI : IsCyclic Gal(D.L'/D.K') := D.isCyclicK'L'
  have htop : SecondInequalityAt D.K' D.L' :=
    hroot D.K' D.L' D.primitiveRoot D.degreeTop
  letI : Finite (IdeleNormQuotient D.K' D.L') := htop.1
  have hkill (x : IdeleNormQuotient K L) : x ^ p = 1 := by
    simpa only [hdegree] using hexponent K L x
  have hsurj : Function.Surjective D.down := D.down_surjective hp hkill
  have hfinite : Finite (IdeleNormQuotient K L) :=
    Finite.of_surjective D.down hsurj
  letI : Finite (IdeleNormQuotient K L) := hfinite
  refine ⟨hfinite, ?_⟩
  have hcard : Nat.card (IdeleNormQuotient K L) ∣
      Nat.card (IdeleNormQuotient D.K' D.L') :=
    Subgroup.card_dvd_of_surjective D.down hsurj
  exact hcard.trans (by simpa only [D.degreeTop, hdegree] using htop.2)

end

end Submission.CField.KNIndex
