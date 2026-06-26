import Towers.ClassField.Examples.SplittingPrimes
import Towers.ClassField.Examples.SplittingPrimeDensity

-- Theorem 0.1 is the completely-split case of Chebotarev density.
-- `Theorem01` now discharges the complete-splitting/Frobenius compatibility
-- and derives the theorem from the exact analytic Chebotarev proposition; it
-- also proves the trivial-extension case unconditionally and the field
-- determination consequence from Chebotarev alone.
import Towers.ClassField.Examples.FinitePrimeRemoval
import Towers.ClassField.Examples.QuadraticReciprocity
import Towers.ClassField.Examples.QuadraticResidues
import Towers.ClassField.Examples.SqrtNegFive

-- Theorems 0.4 and 0.5 are formalized using the Chapter V ray class groups.
-- The quotient-subgroup existence clause is proved equivalent to the global
-- ideal existence theorem, the trivial modulus gives the everywhere-
-- unramified clause, and ideal reciprocity supplies the converse ray-class
-- description, Artin quotient isomorphism, and residue-degree order formula.
import Towers.ClassField.Examples.ClassFieldExistence

-- The concrete class-number part of Example 0.6 is formalized next; its
-- narrow-class-group assertion still requires a dedicated narrow-class API.
import Towers.ClassField.Examples.SqrtSix

-- Example 0.7 additionally requires narrow class groups for its genus-
-- theory conclusion.  Theorem 0.8 is identified with global ideal
-- reciprocity and its factorization through the ray class group is proved
-- explicitly.  Theorem 0.9 is recovered exactly from the Chapter I local
-- correspondence: for characteristic-zero local fields, finite-index
-- subgroups are automa open.
import Towers.ClassField.Examples.RayClassDescription
import Towers.ClassField.Examples.LocalIndexSubgroup

-- Theorem 0.10 includes a fixed-prime Kummer--Dedekind factorization using
-- conductor coprimality, matching the local integral-closure condition and
-- avoiding the former global-monogenicity restriction; the global form is
-- retained as a corollary.
import Towers.ClassField.Examples.Dedekind

-- Exercise 0.11 completes the quadratic-reciprocity discussion by proving
-- that splitting is constant on prime residue classes modulo `4 * |d|`.
import Towers.ClassField.Examples.OddSplitsOrder

-- Exercise 0.12 requires Hilbert class fields.  Exercise 0.13's elementary
-- positive-fraction model, kernel computation, and residue-group quotient are
-- formalized without assuming a general ray-class-group API.
import Towers.ClassField.Examples.RayResidueMap

-- Exercise 0.14 is represented by the concrete assertions in `SqrtSix`.
-- Exercise 0.15(b,c) literally requires the global Artin map and ray class
-- groups; the modulo-20 character table and its finite quotient are recorded
-- next, followed by the explicit cyclotomic construction from the hint.
import Towers.ClassField.Examples.QuadraticCharacterPair
import Towers.ClassField.Examples.Cyclotomic

/-!
# Milne, Class Field Theory: Introduction

Formalized material from the introduction, in source order.
-/
