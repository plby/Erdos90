import Mathlib.Data.Nat.Sqrt
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.SimpleRing.Field
import Towers.ClassField.BrauerGroups.FinrankSimpleSquare
import Towers.ClassField.CrossedProducts.IsMaximalCommutative


/-!
# Chapter IV, Corollary 3.5

Maximal subfields of a finite-dimensional central division algebra have
degree equal to the square root of the dimension of the algebra.
-/

namespace Towers.CField.CProduca

universe u

variable (k D : Type u) [Field k] [DivisionRing D] [Algebra k D]
  [Algebra.IsCentral k D] [Module.Finite k D]

omit [Algebra.IsCentral k D] in
/-- A commutative finite-dimensional subalgebra of a division algebra is a
field. This is the observation used in Milne's proof of Corollary IV.3.5. -/
theorem commutative_subalgebra_field (L : Subalgebra k D)
    (hcomm : ∀ x y : L, x * y = y * x) : IsField L := by
  letI : Module.Finite k L :=
    Module.Finite.of_injective L.val.toLinearMap Subtype.val_injective
  letI : CommRing L := { (inferInstance : Ring L) with mul_comm := hcomm }
  letI : IsDomain L :=
    Function.Injective.isDomain L.val.toRingHom Subtype.val_injective
  letI : Algebra.IsIntegral k L := Algebra.IsIntegral.of_finite k L
  exact isField_of_isIntegral_of_isField' (Field.toIsField k)

omit [Algebra.IsCentral k D] in
/-- In particular, a commutative subalgebra of a finite-dimensional division
algebra is a simple ring. -/
theorem commutative_subalgebra_simple (L : Subalgebra k D)
    (hcomm : ∀ x y : L, x * y = y * x) : IsSimpleRing L := by
  let hfield := commutative_subalgebra_field k D L hcomm
  letI : CommRing L := { (inferInstance : Ring L) with mul_comm := hcomm }
  exact (isSimpleRing_iff_isField L).2 hfield

/-- A commutative subalgebra of a central division algebra is maximal exactly
when its dimension squared is the dimension of the algebra. -/
theorem maximal_subfield_sq (L : Subalgebra k D)
    (hcomm : ∀ x y : L, x * y = y * x) :
    IsMaximalCommutative L ↔
      Module.finrank k D = (Module.finrank k L) ^ 2 := by
  letI : IsSimpleRing L := commutative_subalgebra_simple k D L hcomm
  exact (self_centralizing_commutative
    k D L hcomm).2.symm

/-- Milne, Corollary IV.3.5, in its literal square-root form. -/
theorem maximal_subfield_sqrt (L : Subalgebra k D)
    (hcomm : ∀ x y : L, x * y = y * x) :
    IsMaximalCommutative L ↔
      Module.finrank k L = Nat.sqrt (Module.finrank k D) := by
  constructor
  · intro hmax
    have hsquare := (maximal_subfield_sq k D L hcomm).1 hmax
    calc
      Module.finrank k L = Nat.sqrt ((Module.finrank k L) ^ 2) :=
        (Nat.sqrt_eq' _).symm
      _ = Nat.sqrt (Module.finrank k D) := congrArg Nat.sqrt hsquare.symm
  · intro hsqrt
    apply (maximal_subfield_sq k D L hcomm).2
    obtain ⟨n, hn⟩ := BGroups.finrank_simple_square k D
    have hsqrtn : Nat.sqrt (Module.finrank k D) = n := by
      rw [hn, Nat.sqrt_eq']
    have hLn : Module.finrank k L = n := hsqrt.trans hsqrtn
    rw [hn, hLn]

end Towers.CField.CProduca
