import Towers.ClassField.ArtinReciprocity.ArtinMap
import Towers.ClassField.ArtinReciprocity.Statements
import Towers.ClassField.ArtinReciprocity.FrobeniusExamples
import Towers.ClassField.ArtinReciprocity.Verlagerung
import Towers.ClassField.ArtinReciprocity.GeneratorEquations
import Towers.ClassField.ArtinReciprocity.Chebotarev

/-!
# Milne, Class Field Theory, Chapter V, Section 3

This section constructs the Artin homomorphism on the free abelian group of
pointed unramified primes, proves that its values are independent of the
point above an abelian base prime, and records the prime-generator norm and
Frobenius calculation of Proposition 3.3. Examples 3.1 and 3.2 record the
quadratic Legendre-symbol formula and the exact cyclotomic identity sending
Frobenius at `p` to `[p]` modulo the conductor. It also supplies Mathlib's
Verlag map of Proposition 3.18, the concrete `Q(sqrt(-5))` facts in
Example 3.9, and source-numbered consequences of the exact Chebotarev
density proposition.

Several central theorems in this section remain outside the current library:

* identifying fractional ideals prime to `S` with the free abelian group on
  the corresponding height-one primes in a form compatible with ideal norm;
* the global reciprocity law and existence theorem, including ray class
  fields and conductors;
* Furtwaengler's principal ideal theorem for transfer to the commutator
  subgroup;
* the analytic proof of Chebotarev density; and
* ray-class characters and the conductor-discriminant formula.

The files here state no axioms for these missing results.
-/
