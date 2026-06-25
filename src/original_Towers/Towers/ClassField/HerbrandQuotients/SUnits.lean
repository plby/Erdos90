import Towers.NumberTheory.Units.SUnits

/-!
# Chapter VII, Section 3: the arithmetic of the unit module

For a finite set of finite primes, Mathlib's valuation-theoretic `S`-unit
group is the group denoted `U(T)` in this section (the infinite primes impose
no additional valuation condition).  The Towers ANT development already
proves the exact finite-generation, torsion, and rank statements used in the
proof of Proposition 3.1.

The numbered statements comparing Herbrand quotients of integral lattices
are formalized in the neighboring source-statement files.  They use the
universe-polymorphic low-Tate cardinal ratio introduced for Chapter VII,
while this file records the concrete arithmetic facts about `S`-units used
in the logarithmic-lattice construction of Proposition 3.1.
-/

namespace Towers.CField.HQuotie

open Towers.NumberTheory.Milne
open scoped NumberField

noncomputable section

variable (L : Type*) [Field L] [NumberField L]

/-- The finite-prime part of Milne's group `U(T)` of `T`-units. -/
abbrev SUnits (T : Set (FinitePrime L)) :=
  Towers.NumberTheory.Milne.SUnits L T

/-- The torsion in the `T`-unit group consists exactly of roots of unity. -/
theorem torsion_roots_unity (T : Set (FinitePrime L)) :
    CommGroup.torsion (SUnits L T) =
      (CommGroup.torsion Lˣ).comap (Set.unit T L).subtype :=
  s_roots_unity L T

/-- For finite `T`, the additive group underlying the `T`-units is a finite
`Z`-module. -/
theorem units_moduleFinite (T : Set (FinitePrime L)) (hT : T.Finite) :
    Module.Finite ℤ (Additive (SUnits L T)) :=
  s_units_module L T hT

/-- The `T`-unit group is finitely generated. -/
theorem units_finitelyGenerated (T : Set (FinitePrime L)) (hT : T.Finite) :
    Monoid.FG (SUnits L T) :=
  s_finitely_generated L T hT

/-- The rank formula used to identify the logarithmic `T`-unit lattice in
the proof of Proposition VII.3.1. -/
theorem units_rank (T : Set (FinitePrime L)) (hT : T.Finite) :
    Module.finrank ℤ (Additive (SUnits L T)) =
      NumberField.InfinitePlace.nrRealPlaces L +
        NumberField.InfinitePlace.nrComplexPlaces L + T.ncard - 1 :=
  s_complex_ncard L T hT

end

end Towers.CField.HQuotie
