import Towers.ClassField.RayClassGroups.Modulus
import Towers.ClassField.RayClassGroups.ForbiddenIdeal
import Towers.ClassField.RayClassGroups.ZeroCoprimeForbidden
import Towers.ClassField.RayClassGroups.FiniteCRTFactor
import Towers.ClassField.RayClassGroups.RationalQuotient
import Towers.ClassField.RayClassGroups.RationalInfinity
import Towers.ClassField.RayClassGroups.Frobenius

/-!
# Milne, Class Field Theory, Chapter V, Section 1

This section introduces ideals prime to a finite set, moduli, and ray class
groups, and then reviews the Frobenius element. `Lemma11` defines `K^S` and
`I^S`, proves exactness at `I^S`, and proves that `I^S -> Cl(K)` is onto using
the coprime ideal representative theorem from the ANT development. `Modulus`
packages finite prime exponents and the real infinite part. `Lemma15` proves
that every element of `K^S` is a quotient of integral elements whose
principal ideals are prime to `S`. `Example14` and `Example18` formalize the
elementary rational ray quotient and the small real-quadratic unit
computations. `Theorem17` gives the Chinese-remainder decomposition of the
finite quotient ring and its unit group over the prime powers occurring in a
modulus.
`Frobenius` records Statements 1.9--1.12 from the existing ANT Frobenius
development: conjugacy, the tower power formula, restriction, and the
compositum product formula.

The remaining general ray class group statements require a number-field
approximation theorem expressed simultaneously at finite congruence
conditions and real signs. That combined API is not currently packaged in
Mathlib; the ideals-prime-to-a-finite-set sequence and the denominator lemma
are developed separately.
-/
