import Towers.ClassField.GlobalClass.CardinalityRigidity
import Towers.ClassField.GlobalClass.LocalDegreeLCM
import Towers.ClassField.GlobalClass.FiniteCompletion
import Towers.ClassField.GlobalClass.FundamentalClass
import Towers.ClassField.GlobalClass.RelativeH2
import Towers.ClassField.GlobalClass.AbsoluteInvariant
import Towers.ClassField.GlobalClass.BrauerSequenceStatements
import Towers.ClassField.GlobalClass.CyclicCompletionData
import Towers.ClassField.GlobalClass.RatNeThirteen
import Towers.ClassField.GlobalClass.MaximalAbelianSubextension
import Towers.ClassField.GlobalClass.TateIndex
import Towers.ClassField.GlobalClass.Transitivity
import Towers.ClassField.GlobalClass.FiniteNormTransitivity
import Towers.ClassField.GlobalClass.GaloisClosureGroup
import Towers.ClassField.GlobalClass.Corestriction
import Towers.ClassField.GlobalClass.CorestrictionSquare
import Towers.ClassField.GlobalClass.Existential
import Towers.ClassField.GlobalClass.GaloisClosure
import Towers.ClassField.GlobalClass.TateTransport
import Towers.ClassField.GlobalClass.FixedFieldNorm

/-!
# Chapter VIII, Section 4: the fundamental exact sequence and fundamental class

The source-numbered wrappers use actual number-field completions and Brauer
groups.  In particular, Lemma 4.1 includes finite and infinite local degrees,
Theorem 4.2 and Corollary 4.3 state the canonical exact sequences, and Example
4.4 records both the cyclic norm sequence and the classification of global
division algebras by their local invariants.  Example 4.5 constructs the
biquadratic field `Q(sqrt 13, sqrt 17)`, proves that it has degree four and
Galois group of exponent two, and deduces that every local degree is one or
two from the stated local arithmetic calculation.
-/
