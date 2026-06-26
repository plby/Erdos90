import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Milne, Algebraic Number Theory, the Galois assertions of Theorem 3.34

We record the equality of ramification indices and inertia degrees above a fixed prime, and
the resulting equation `efg = [L : K]`.
-/

namespace Submission.NumberTheory.Milne

/-- Lemma 3.33: a nonzero prime of the extension divides the extension of `p` exactly
when its contraction is `p`. -/
theorem prime_dvd_comap
    {A B : Type*} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥)
    {P : Ideal B} [P.IsPrime] :
    P ∣ Ideal.map (algebraMap A B) p ↔
      p = Ideal.comap (algebraMap A B) P := by
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  constructor
  · intro h
    exact ((Ideal.liesOver_iff_dvd_map
      (inferInstance : P.IsPrime).ne_top).mpr h).over
  · intro h
    apply (Ideal.liesOver_iff_dvd_map
      (inferInstance : P.IsPrime).ne_top).mp
    exact ⟨h⟩

/-- A fraction-ring form of the first assertion of Theorem 3.34. -/
theorem deg_fraction_rings
    (A B K L : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Module.Finite A B]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        Ideal.ramificationIdx p P * Ideal.inertiaDeg p P =
      Module.finrank K L := by
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  exact Ideal.sum_ramification_inertia B K L hp

/-- The Galois uniformity assertion in Theorem 3.34: ramification indices are equal at all
primes above a fixed prime. -/
theorem ramificationIdx_galois
    {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (p : Ideal A) {P Q : Ideal B}
    (hP : P ∈ Ideal.primesOver p B) (hQ : Q ∈ Ideal.primesOver p B) :
    Ideal.ramificationIdx p P = Ideal.ramificationIdx p Q := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver p := hP.2
  letI : Q.IsPrime := hQ.1
  letI : Q.LiesOver p := hQ.2
  exact Ideal.ramificationIdx_eq_of_isGaloisGroup p P Q G

/-- The Galois uniformity assertion in Theorem 3.34: inertia degrees are equal at all
primes above a fixed prime. -/
theorem inertiaDeg_galois
    {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    (p : Ideal A) {P Q : Ideal B}
    (hP : P ∈ Ideal.primesOver p B) (hQ : Q ∈ Ideal.primesOver p B) :
    Ideal.inertiaDeg p P = Ideal.inertiaDeg p Q := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver p := hP.2
  letI : Q.IsPrime := hQ.1
  letI : Q.LiesOver p := hQ.2
  exact Ideal.inertiaDeg_eq_of_isGaloisGroup p P Q G

/-- The equation `efg = [L : K]` from Theorem 3.34, expressed for a finite Galois ring
extension.  Here `g` is the number of primes above `p`, while `e` and `f` are their common
ramification index and inertia degree. -/
theorem ncard_primes_deg
    (A B G : Type*) [CommRing A] [IsDedekindDomain A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥) :
    (Ideal.primesOver p B).ncard *
        (Ideal.ramificationIdxIn p B * Ideal.inertiaDegIn p B) =
      Nat.card G := by
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp
  exact Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B G

end Submission.NumberTheory.Milne
