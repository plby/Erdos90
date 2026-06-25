import Towers.Group.NilpotentProducts.GeneralResidues


/-!
# Powers in Struik's arbitrary-rank equation-(18) group

The multiplication table is triangular, so every coordinate of `c ^ n`
is an integral combination of `n`, `choose n 2`, and `choose n 3`.
This is the explicit power calculation used in Corollary 1.
-/

namespace Struik
namespace P1960

private lemma choose_succ_two (n : ℕ) :
    Ring.choose ((n + 1 : ℕ) : ℤ) 2 =
      Ring.choose (n : ℤ) 2 + n := by
  rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega,
    show 2 = 1 + 1 by omega, Ring.choose_succ_succ]
  rw [Ring.choose_one_right]
  ring

private lemma choose_succ_three (n : ℕ) :
    Ring.choose ((n + 1 : ℕ) : ℤ) 3 =
      Ring.choose (n : ℤ) 3 + Ring.choose (n : ℤ) 2 := by
  rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega,
    show 3 = 2 + 1 by omega, Ring.choose_succ_succ]
  ring

private lemma choose_one_add (n : ℕ) :
    Ring.choose (1 + (n : ℤ)) 2 =
      Ring.choose (n : ℤ) 2 + n := by
  rw [add_comm]
  exact choose_succ_two n

private lemma choose_one_three (n : ℕ) :
    Ring.choose (1 + (n : ℤ)) 3 =
      Ring.choose (n : ℤ) 3 + Ring.choose (n : ℤ) 2 := by
  rw [add_comm]
  exact choose_succ_three n

private lemma choose_two_int (x : ℤ) :
    Ring.choose (x + 1) 2 = Ring.choose x 2 + x := by
  rw [show 2 = 1 + 1 by omega, Ring.choose_succ_succ,
    Ring.choose_one_right]
  ring

private lemma choose_add_int (x : ℤ) :
    Ring.choose (x + 1) 3 =
      Ring.choose x 3 + Ring.choose x 2 := by
  rw [show 3 = 2 + 1 by omega, Ring.choose_succ_succ]
  ring

private lemma choose_mul_two (x y : ℤ) :
    Ring.choose (x * y) 2 =
      Ring.choose x 2 * y ^ 2 + x * Ring.choose y 2 := by
  have h :
      2 * Ring.choose (x * y) 2 =
        2 * (Ring.choose x 2 * y ^ 2 + x * Ring.choose y 2) := by
    calc
      2 * Ring.choose (x * y) 2 =
          x * y * (x * y - 1) := two_mul_choose (x * y)
      _ = (x * (x - 1)) * y ^ 2 + x * (y * (y - 1)) := by
        ring
      _ = (2 * Ring.choose x 2) * y ^ 2 +
          x * (2 * Ring.choose y 2) := by
        rw [two_mul_choose, two_mul_choose]
      _ = 2 * (Ring.choose x 2 * y ^ 2 +
          x * Ring.choose y 2) := by
        ring
  omega

private lemma sq_natCast (n : ℕ) :
    (n : ℤ) ^ 2 = (n : ℤ) + 2 * Ring.choose (n : ℤ) 2 := by
  have h := two_mul_choose (n : ℤ)
  nlinarith

/-- The closed coordinate formula for the `n`th power in equation (18). -/
noncomputable def generalPowCoordinates
    {t : ℕ} (c : GCoordi t) (n : ℕ) :
    GCoordi t where
  single i := (n : ℤ) * c.single i
  pair q :=
    (n : ℤ) * c.pair q -
      Ring.choose (n : ℤ) 2 * c.single q.j * c.single q.i
  pairLeft q :=
    (n : ℤ) * c.pairLeft q -
      Ring.choose (n : ℤ) 2 * c.single q.j *
        Ring.choose (c.single q.i) 2 +
      Ring.choose (n : ℤ) 2 * c.pair q * c.single q.i -
      Ring.choose (n : ℤ) 3 * c.single q.j *
        c.single q.i ^ 2
  pairRight q :=
    (n : ℤ) * c.pairRight q -
      Ring.choose (n : ℤ) 2 * c.single q.i *
        Ring.choose (c.single q.j) 2 +
      Ring.choose (n : ℤ) 2 * c.pair q * c.single q.j -
      Ring.choose (n : ℤ) 2 * c.single q.i *
        c.single q.j ^ 2 -
      2 * Ring.choose (n : ℤ) 3 * c.single q.i *
        c.single q.j ^ 2
  tripleFirst q :=
    (n : ℤ) * c.tripleFirst q +
      Ring.choose (n : ℤ) 2 *
        (c.pair q.ik * c.single q.j +
          c.pair q.ij * c.single q.k) -
      (4 * Ring.choose (n : ℤ) 3 +
          3 * Ring.choose (n : ℤ) 2) *
        c.single q.i * c.single q.j * c.single q.k
  tripleSecond q :=
    (n : ℤ) * c.tripleSecond q +
      Ring.choose (n : ℤ) 2 *
        (c.pair q.jk * c.single q.i +
          c.pair q.ik * c.single q.j) -
      (2 * Ring.choose (n : ℤ) 3 +
          Ring.choose (n : ℤ) 2) *
        c.single q.i * c.single q.j * c.single q.k

/-- Every coordinate of `c ^ n` is given by the closed equation-(18)
power formula. -/
theorem general_pow
    {t : ℕ} (c : GCoordi t) (n : ℕ) :
    c ^ n = generalPowCoordinates c n := by
  induction n with
  | zero =>
      change GCoordi.zero t =
        generalPowCoordinates c 0
      ext <;>
        simp [GCoordi.zero,
          generalPowCoordinates]
  | succ n ih =>
      rw [pow_succ, ih]
      change
        GCoordi.mul
            (generalPowCoordinates c n) c =
          generalPowCoordinates c (n + 1)
      ext q
      · simp [GCoordi.mul,
          generalPowCoordinates]
        ring
      · simp only [GCoordi.mul, generalPowCoordinates, Nat.cast_add,
          Nat.cast_one]
        rw [choose_two_int]
        ring
      · simp only [GCoordi.mul, generalPowCoordinates, Nat.cast_add,
          Nat.cast_one]
        rw [choose_two_int, choose_add_int]
        ring
      · simp only [GCoordi.mul, generalPowCoordinates, choose_mul_two,
          Nat.cast_add, Nat.cast_one]
        rw [choose_two_int, choose_add_int]
        ring
      · simp only [GCoordi.mul, generalPowCoordinates, Triple.ik,
          Triple.ij, Triple.jk, Nat.cast_add, Nat.cast_one]
        rw [choose_two_int, choose_add_int]
        ring_nf
        rw [sq_natCast n]
        ring
      · simp only [GCoordi.mul, generalPowCoordinates, Triple.ik,
          Triple.ij, Triple.jk, Nat.cast_add, Nat.cast_one]
        rw [choose_two_int, choose_add_int]
        ring

/-- Every displayed Hall factor in the coordinate tuple `c` is killed by
the exponent `N`.  For a coordinate of modulus `m` and exponent `a`, this
is exactly the condition `m ∣ N * a`. -/
structure GeneralOrdersDivide
    {t : ℕ} (order : Fin t → ℕ)
    (c : GCoordi t) (N : ℕ) : Prop where
  single :
    ∀ i, (order i : ℤ) ∣ (N : ℤ) * c.single i
  pair :
    ∀ q, (generalPairModulus order q : ℤ) ∣
      (N : ℤ) * c.pair q
  pairLeft :
    ∀ q, (generalPairModulus order q : ℤ) ∣
      (N : ℤ) * c.pairLeft q
  pairRight :
    ∀ q, (generalPairModulus order q : ℤ) ∣
      (N : ℤ) * c.pairRight q
  tripleFirst :
    ∀ q, (generalResiduesModulus order q : ℤ) ∣
      (N : ℤ) * c.tripleFirst q
  tripleSecond :
    ∀ q, (generalResiduesModulus order q : ℤ) ∣
      (N : ℤ) * c.tripleSecond q

private lemma dvd_coefficient_base
    {m N a x : ℤ}
    (hx : m ∣ N * x)
    (ha : N ∣ a) :
    m ∣ a * x := by
  rcases ha with ⟨k, rfl⟩
  convert dvd_mul_of_dvd_right hx k using 1 ; ring

private lemma pair_modulus_i
    {t : ℕ} (order : Fin t → ℕ) (q : Pair t) :
    (generalPairModulus order q : ℤ) ∣ (order q.i : ℤ) := by
  exact_mod_cast Nat.gcd_dvd_left (order q.i) (order q.j)

private lemma pair_modulus_j
    {t : ℕ} (order : Fin t → ℕ) (q : Pair t) :
    (generalPairModulus order q : ℤ) ∣ (order q.j : ℤ) := by
  exact_mod_cast Nat.gcd_dvd_right (order q.i) (order q.j)

private lemma triple_modulus_i
    {t : ℕ} (order : Fin t → ℕ) (q : Triple t) :
    (generalResiduesModulus order q : ℤ) ∣ (order q.i : ℤ) := by
  exact_mod_cast
    (Nat.gcd_dvd_left
      (Nat.gcd (order q.i) (order q.j)) (order q.k)).trans
        (Nat.gcd_dvd_left (order q.i) (order q.j))

private lemma triple_modulus_j
    {t : ℕ} (order : Fin t → ℕ) (q : Triple t) :
    (generalResiduesModulus order q : ℤ) ∣ (order q.j : ℤ) := by
  exact_mod_cast
    (Nat.gcd_dvd_left
      (Nat.gcd (order q.i) (order q.j)) (order q.k)).trans
        (Nat.gcd_dvd_right (order q.i) (order q.j))

private lemma triple_modulus_k
    {t : ℕ} (order : Fin t → ℕ) (q : Triple t) :
    (generalResiduesModulus order q : ℤ) ∣ (order q.k : ℤ) := by
  exact_mod_cast
    Nat.gcd_dvd_right
      (Nat.gcd (order q.i) (order q.j)) (order q.k)

private lemma triple_modulus_ij
    {t : ℕ} (order : Fin t → ℕ) (q : Triple t) :
    (generalResiduesModulus order q : ℤ) ∣
      (generalPairModulus order q.ij : ℤ) := by
  exact_mod_cast
    Nat.gcd_dvd_left
      (Nat.gcd (order q.i) (order q.j)) (order q.k)

private lemma triple_modulus_ik
    {t : ℕ} (order : Fin t → ℕ) (q : Triple t) :
    (generalResiduesModulus order q : ℤ) ∣
      (generalPairModulus order q.ik : ℤ) := by
  exact_mod_cast Nat.dvd_gcd
    ((Nat.gcd_dvd_left
      (Nat.gcd (order q.i) (order q.j)) (order q.k)).trans
        (Nat.gcd_dvd_left (order q.i) (order q.j)))
    (Nat.gcd_dvd_right
      (Nat.gcd (order q.i) (order q.j)) (order q.k))

private lemma triple_modulus_jk
    {t : ℕ} (order : Fin t → ℕ) (q : Triple t) :
    (generalResiduesModulus order q : ℤ) ∣
      (generalPairModulus order q.jk : ℤ) := by
  exact_mod_cast Nat.dvd_gcd
    ((Nat.gcd_dvd_left
      (Nat.gcd (order q.i) (order q.j)) (order q.k)).trans
        (Nat.gcd_dvd_right (order q.i) (order q.j)))
    (Nat.gcd_dvd_right
      (Nat.gcd (order q.i) (order q.j)) (order q.k))

/-- A power vanishes modulo every equation-(18) coordinate modulus as soon
as its exponent and its degree-two and degree-three binomial coefficients
are all divisible by an exponent killing the displayed Hall factors. -/
theorem general_mod_zero
    {t N M : ℕ} (order : Fin t → ℕ)
    (c : GCoordi t)
    (hc : GeneralOrdersDivide order c N)
    (hM : N ∣ M)
    (hchooseTwo : N ∣ Nat.choose M 2)
    (hchooseThree : N ∣ Nat.choose M 3) :
    GMEq order
      (c ^ M) (GCoordi.zero t) := by
  rw [general_pow]
  have hM' : (N : ℤ) ∣ (M : ℤ) :=
    Int.natCast_dvd_natCast.mpr hM
  have hchooseTwo' :
      (N : ℤ) ∣ Ring.choose (M : ℤ) 2 := by
    rw [Ring.choose_natCast]
    exact Int.natCast_dvd_natCast.mpr hchooseTwo
  have hchooseThree' :
      (N : ℤ) ∣ Ring.choose (M : ℤ) 3 := by
    rw [Ring.choose_natCast]
    exact Int.natCast_dvd_natCast.mpr hchooseThree
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [generalPowCoordinates,
      GCoordi.zero]
    rw [Int.modEq_zero_iff_dvd]
    exact
      dvd_coefficient_base
        (hc.single i) hM'
  · intro q
    simp only [generalPowCoordinates,
      GCoordi.zero]
    rw [Int.modEq_zero_iff_dvd]
    apply dvd_sub
    · exact
        dvd_coefficient_base
          (hc.pair q) hM'
    · apply dvd_mul_of_dvd_left
      exact
        dvd_coefficient_base
          ((pair_modulus_j order q).trans
            (hc.single q.j))
          hchooseTwo'
  · intro q
    simp only [generalPowCoordinates,
      GCoordi.zero]
    rw [Int.modEq_zero_iff_dvd]
    apply dvd_sub
    · apply dvd_add
      · apply dvd_sub
        · exact
            dvd_coefficient_base
              (hc.pairLeft q) hM'
        · apply dvd_mul_of_dvd_left
          exact
            dvd_coefficient_base
              ((pair_modulus_j order q).trans
                (hc.single q.j))
              hchooseTwo'
      · apply dvd_mul_of_dvd_left
        exact
          dvd_coefficient_base
            (hc.pair q) hchooseTwo'
    · apply dvd_mul_of_dvd_left
      exact
        dvd_coefficient_base
          ((pair_modulus_j order q).trans
            (hc.single q.j))
          hchooseThree'
  · intro q
    simp only [generalPowCoordinates,
      GCoordi.zero]
    rw [Int.modEq_zero_iff_dvd]
    apply dvd_sub
    · apply dvd_sub
      · apply dvd_add
        · apply dvd_sub
          · exact
              dvd_coefficient_base
                (hc.pairRight q) hM'
          · apply dvd_mul_of_dvd_left
            exact
              dvd_coefficient_base
                ((pair_modulus_i order q).trans
                  (hc.single q.i))
                hchooseTwo'
        · apply dvd_mul_of_dvd_left
          exact
            dvd_coefficient_base
              (hc.pair q) hchooseTwo'
      · apply dvd_mul_of_dvd_left
        exact
          dvd_coefficient_base
            ((pair_modulus_i order q).trans
            (hc.single q.i))
          hchooseTwo'
    · apply dvd_mul_of_dvd_left
      have hbase :=
        dvd_coefficient_base
          ((pair_modulus_i order q).trans
            (hc.single q.i))
          hchooseThree'
      convert dvd_mul_of_dvd_right hbase 2 using 1 ; ring
  · intro q
    simp only [generalPowCoordinates,
      GCoordi.zero]
    rw [Int.modEq_zero_iff_dvd]
    apply dvd_sub
    · apply dvd_add
      · exact
          dvd_coefficient_base
            (hc.tripleFirst q) hM'
      · have hik :=
          dvd_coefficient_base
            ((triple_modulus_ik order q).trans
                (hc.pair q.ik))
            hchooseTwo'
        have hij :=
          dvd_coefficient_base
            ((triple_modulus_ij order q).trans
                (hc.pair q.ij))
            hchooseTwo'
        convert
          (dvd_mul_of_dvd_left hik (c.single q.j)).add
            (dvd_mul_of_dvd_left hij (c.single q.k)) using 1 ;
          ring
    · have hcoefficient :
          (N : ℤ) ∣
            4 * Ring.choose (M : ℤ) 3 +
              3 * Ring.choose (M : ℤ) 2 :=
        (dvd_mul_of_dvd_right hchooseThree' 4).add
          (dvd_mul_of_dvd_right hchooseTwo' 3)
      have hi :=
        dvd_coefficient_base
          ((triple_modulus_i order q).trans
            (hc.single q.i))
          hcoefficient
      convert
        dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left hi (c.single q.j))
          (c.single q.k) using 1
  · intro q
    simp only [generalPowCoordinates,
      GCoordi.zero]
    rw [Int.modEq_zero_iff_dvd]
    apply dvd_sub
    · apply dvd_add
      · exact
          dvd_coefficient_base
            (hc.tripleSecond q) hM'
      · have hjk :=
          dvd_coefficient_base
            ((triple_modulus_jk order q).trans
                (hc.pair q.jk))
            hchooseTwo'
        have hik :=
          dvd_coefficient_base
            ((triple_modulus_ik order q).trans
                (hc.pair q.ik))
            hchooseTwo'
        convert
          (dvd_mul_of_dvd_left hjk (c.single q.i)).add
            (dvd_mul_of_dvd_left hik (c.single q.j)) using 1 ;
          ring
    · have hcoefficient :
          (N : ℤ) ∣
            2 * Ring.choose (M : ℤ) 3 +
              Ring.choose (M : ℤ) 2 :=
        (dvd_mul_of_dvd_right hchooseThree' 2).add
          hchooseTwo'
      have hi :=
        dvd_coefficient_base
          ((triple_modulus_i order q).trans
            (hc.single q.i))
          hcoefficient
      convert
        dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left hi (c.single q.j))
          (c.single q.k) using 1

/-- If the weight-one coordinates vanish, the `N`th power has no collection
corrections: every remaining coordinate is simply multiplied by `N`.
Consequently, any exponent killing the displayed Hall factors kills their
collected product.  This is the class-three instance of the commutator
branch in the corollary to Theorem 3. -/
theorem general_residue_single
    {t N : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (c : GCoordi t)
    (hc : GeneralOrdersDivide order c N)
    (hsingle : ∀ i, c.single i = 0) :
    (c : GeneralResidueGroup order horder) ^ N = 1 := by
  apply (generalCon order horder).eq.mpr
  change GMEq order
    (c ^ N) (GCoordi.zero t)
  rw [general_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [GCoordi.zero]
    rw [Int.modEq_zero_iff_dvd]
    simp [generalPowCoordinates, hsingle i]
  · intro q
    simp only [GCoordi.zero]
    rw [Int.modEq_zero_iff_dvd]
    simpa [generalPowCoordinates,
      GCoordi.zero, hsingle q.i, hsingle q.j] using
      hc.pair q
  · intro q
    simp only [GCoordi.zero]
    rw [Int.modEq_zero_iff_dvd]
    simpa [generalPowCoordinates,
      GCoordi.zero, hsingle q.i, hsingle q.j] using
      hc.pairLeft q
  · intro q
    simp only [GCoordi.zero]
    rw [Int.modEq_zero_iff_dvd]
    simpa [generalPowCoordinates,
      GCoordi.zero, hsingle q.i, hsingle q.j] using
      hc.pairRight q
  · intro q
    simp only [GCoordi.zero]
    rw [Int.modEq_zero_iff_dvd]
    simpa [generalPowCoordinates,
      GCoordi.zero,
      hsingle q.i, hsingle q.j, hsingle q.k] using
      hc.tripleFirst q
  · intro q
    simp only [GCoordi.zero]
    rw [Int.modEq_zero_iff_dvd]
    simpa [generalPowCoordinates,
      GCoordi.zero,
      hsingle q.i, hsingle q.j, hsingle q.k] using
      hc.tripleSecond q

private lemma odd_choose_two
    {N : ℕ} (hodd : Odd N) :
    N ∣ Nat.choose N 2 := by
  cases N with
  | zero => simp
  | succ n =>
      have hidentity := Nat.add_one_mul_choose_eq n 1
      have hdiv : n + 1 ∣ 2 * Nat.choose (n + 1) 2 := by
        refine ⟨n, ?_⟩
        simpa [mul_comm] using hidentity.symm
      exact hodd.coprime_two_right.dvd_of_dvd_mul_left hdiv

private lemma coprime_dvd_choose
    {N : ℕ} (hthree : ¬3 ∣ N) :
    N ∣ Nat.choose N 3 := by
  cases N with
  | zero => simp at hthree
  | succ n =>
      have hidentity := Nat.add_one_mul_choose_eq n 2
      have hdiv : n + 1 ∣ 3 * Nat.choose (n + 1) 3 := by
        refine ⟨Nat.choose n 2, ?_⟩
        simpa [mul_comm] using hidentity.symm
      have hcoprime : Nat.Coprime (n + 1) 3 :=
        Nat.coprime_comm.mpr
          ((Nat.prime_three.coprime_iff_not_dvd).mpr hthree)
      exact hcoprime.dvd_of_dvd_mul_left hdiv

private lemma choose_three_mul (x : ℤ) :
    Ring.choose (3 * x) 3 =
      3 * Ring.choose x 3 +
        6 * x * Ring.choose x 2 + x ^ 3 := by
  rw [show 3 * x = (x + x) + x by ring,
    Ring.add_choose_eq 3 (Commute.all (x + x) x)]
  simp [Finset.Nat.antidiagonal_eq_map, Finset.sum_range_succ,
    Ring.add_choose_eq]
  ring

private lemma dvd_choose_mul (N : ℕ) :
    N ∣ Nat.choose (3 * N) 3 := by
  have hthree :
      (N : ℤ) ∣ 3 * Ring.choose (N : ℤ) 3 := by
    have hidentity :=
      Ring.choose_smul_choose (N : ℤ) (n := 3) (k := 1) (by omega)
    refine ⟨Ring.choose ((N : ℤ) - 1) 2, ?_⟩
    simpa [nsmul_eq_mul, Ring.choose_one_right, mul_comm] using
      hidentity
  have htwo :
      (N : ℤ) ∣ 6 * (N : ℤ) * Ring.choose (N : ℤ) 2 := by
    exact dvd_mul_of_dvd_left (dvd_mul_left (N : ℤ) 6) _
  have hcubed : (N : ℤ) ∣ (N : ℤ) ^ 3 := by
    exact ⟨(N : ℤ) ^ 2, by ring⟩
  have h :
      (N : ℤ) ∣ Ring.choose (3 * (N : ℤ)) 3 := by
    rw [choose_three_mul]
    exact (hthree.add htwo).add hcubed
  have hcast :
      (N : ℤ) ∣ Ring.choose (((3 * N : ℕ) : ℤ)) 3 := by
    convert h using 1
  rw [Ring.choose_natCast] at hcast
  exact Int.natCast_dvd_natCast.mp hcast

private lemma odd_dvd_choose
    {N : ℕ} (hodd : Odd N) :
    N ∣ Nat.choose (3 * N) 2 := by
  have hchoose : N ∣ Nat.choose N 2 :=
    odd_choose_two hodd
  have h :
      (N : ℤ) ∣ Ring.choose (3 * (N : ℤ)) 2 := by
    rw [choose_mul_two]
    have h32 : Ring.choose (3 : ℤ) 2 = 3 := by decide
    rw [h32, Ring.choose_natCast]
    convert
      (dvd_mul_of_dvd_left (dvd_mul_left (N : ℤ) 3) (N : ℤ)).add
        (dvd_mul_of_dvd_right
          (Int.natCast_dvd_natCast.mpr hchoose) 3) using 1 ;
      ring
  have hcast :
      (N : ℤ) ∣ Ring.choose (((3 * N : ℕ) : ℤ)) 2 := by
    convert h using 1
  rw [Ring.choose_natCast] at hcast
  exact Int.natCast_dvd_natCast.mp hcast

/-- Corollary 1 in equation-(18) coordinates, in the case `3 ∤ N`:
if every displayed Hall factor is killed by the odd integer `N`, then so
is their collected product. -/
theorem general_residue_dvd
    {t N : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (c : GCoordi t)
    (hc : GeneralOrdersDivide order c N)
    (hodd : Odd N)
    (hthree : ¬3 ∣ N) :
    (c : GeneralResidueGroup order horder) ^ N = 1 := by
  apply (generalCon order horder).eq.mpr
  exact general_mod_zero order c hc
    dvd_rfl (odd_choose_two hodd)
      (coprime_dvd_choose hthree)

/-- Corollary 1 in equation-(18) coordinates, in the exceptional case:
for odd `N`, the cube multiple `3N` kills every collected product whose
displayed Hall factors are killed by `N`. -/
theorem general_residue_pow
    {t N : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (c : GCoordi t)
    (hc : GeneralOrdersDivide order c N)
    (hodd : Odd N) :
    (c : GeneralResidueGroup order horder) ^ (3 * N) = 1 := by
  apply (generalCon order horder).eq.mpr
  exact general_mod_zero order c hc
    (dvd_mul_left N 3)
      (odd_dvd_choose hodd)
      (dvd_choose_mul N)

end P1960
end Struik
