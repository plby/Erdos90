import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Submission.Group.Zassenhaus.FinitePGroup

/-!
# The binomial divisibility in Struik's tame-prime argument

If every prime divisor of `a` is larger than a cutoff `c`, then `a` is
coprime to every positive `k ≤ c`.  The identity

`a * choose (a - 1) (k - 1) = choose a k * k`

therefore shows that `a ∣ choose a k`.  This is the arithmetic step used in
the downward induction in Lemma 1.
-/

namespace Struik
namespace P1960

open Submission.TCTex

/-- Struik's convention permits order zero for an infinite cyclic factor.
Every finite prime divisor must be strictly above the cutoff. -/
def TameOrderCutoff (a cutoff : ℕ) : Prop :=
  a = 0 ∨ ∀ p : ℕ, p.Prime → p ∣ a → cutoff < p

/-- Struik's tame-prime hypothesis for a family of cyclic orders. -/
def TameOrdersCutoff
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ) : Prop :=
  ∀ i, TameOrderCutoff (order i) (n - 1)

theorem tame_order_coprime
    {a cutoff k : ℕ}
    (htame : TameOrderCutoff a cutoff)
    (ha : a ≠ 0)
    (hkpos : 0 < k) (hk : k ≤ cutoff) :
    Nat.Coprime a k := by
  rcases htame with hzero | htame
  · exact (ha hzero).elim
  · by_contra hcoprime
    obtain ⟨p, hp, hpa, hpk⟩ :=
      Nat.Prime.not_coprime_iff_dvd.mp hcoprime
    have hpkle : p ≤ k := Nat.le_of_dvd hkpos hpk
    have hpgt : cutoff < p := htame p hp hpa
    omega

/-- Every positive binomial coefficient whose lower index is at most the
cutoff is divisible by a tame cyclic order. -/
theorem tame_dvd_choose
    {a cutoff k : ℕ}
    (htame : TameOrderCutoff a cutoff)
    (hkpos : 0 < k) (hk : k ≤ cutoff) :
    a ∣ Nat.choose a k := by
  by_cases ha0 : a = 0
  · subst a
    cases k with
    | zero => omega
    | succ k => simp [Nat.choose_zero_succ]
  · have ha : 0 < a := Nat.pos_of_ne_zero ha0
    have hcoprime :
        Nat.Coprime a k :=
      tame_order_coprime htame ha0 hkpos hk
    have hidentity :
        a * Nat.choose (a - 1) (k - 1) =
          Nat.choose a k * k := by
      have h := Nat.add_one_mul_choose_eq (a - 1) (k - 1)
      rw [Nat.sub_add_cancel ha, Nat.sub_add_cancel hkpos] at h
      exact h
    have hdvd : a ∣ Nat.choose a k * k := by
      exact ⟨Nat.choose (a - 1) (k - 1), hidentity.symm⟩
    exact (Nat.Coprime.dvd_mul_right hcoprime).mp hdvd

theorem tame_orders_choose
    {t n k : ℕ} {order : Fin t → ℕ}
    (htame : TameOrdersCutoff order n)
    (i : Fin t)
    (hkpos : 0 < k) (hk : k ≤ n - 1) :
    order i ∣ Nat.choose (order i) k :=
  tame_dvd_choose (htame i) hkpos hk

/-- The polynomial form of Struik's binomial-divisibility argument.

An integer-valued polynomial of degree at most the cutoff and with zero
constant term takes a value divisible by every tame order. -/
theorem tame_integer_valued
    {a cutoff : ℕ} {f : ℕ → ℤ}
    (htame : TameOrderCutoff a cutoff)
    (hf : IVMost f cutoff)
    (hf0 : f 0 = 0) :
    (a : ℤ) ∣ f a := by
  rw [hf.nat_binomial_basisexpansion a]
  apply Finset.dvd_sum
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [natBinomialCoefficient, hf0]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hkcutoff : k ≤ cutoff :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hchoose :
        (a : ℤ) ∣ (Nat.choose a k : ℤ) := by
      exact_mod_cast
        tame_dvd_choose htame hkpos hkcutoff
    exact dvd_mul_of_dvd_right
      hchoose
      (natBinomialCoefficient f k)

/-- The same argument when the recorded polynomial degree is only bounded
above by the tame cutoff. -/
theorem tame_valued_degree
    {a degreeBound cutoff : ℕ} {f : ℕ → ℤ}
    (htame : TameOrderCutoff a cutoff)
    (hdegree : degreeBound ≤ cutoff)
    (hf : IVMost f degreeBound)
    (hf0 : f 0 = 0) :
    (a : ℤ) ∣ f a := by
  rcases hf with ⟨P, hPdegree, hPeval⟩
  exact tame_integer_valued
    htame ⟨P, hPdegree.trans hdegree, hPeval⟩ hf0

/-- Hall-coordinate form of the arithmetic step in Lemma 1.

Once Claim 5 supplies its weight-ratio degree bound, every coordinate of
`u ^ a` in a represented weight below the cutoff is divisible by a tame
order `a`. -/
theorem tame_dvd_pow
    {d n r s a cutoff : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ t : ℕ, BCWta d t)
    (hH :
      ∀ t : ℕ,
        1 ≤ t →
          t < n →
            (H t).FormsAssocGradedbasis (n := n))
    (hpower :
      ∀ (e : HEFam H) (t : ℕ),
        1 ≤ t →
          CollectedPolynomialData (n := n) H e t)
    (u : LowerCentralTruncation (FreeGroup (FreeGenerator d)) n)
    (hu :
      u ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator d)) n) (r - 1))
    (hr : 1 ≤ r)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (hdegree : s / r ≤ cutoff)
    (htame : TameOrderCutoff a cutoff)
    (i : (H s).index) :
    (a : ℤ) ∣ hallCoordinate hn H hH (u ^ a) i := by
  have hf :
      IVMost
        (fun q : ℕ => hallCoordinate hn H hH (u ^ q) i)
        (s / r) :=
    integer_valued_most
      hn H hH hpower u hu hr hs hsn i
  have hf0 :
      hallCoordinate hn H hH (u ^ 0) i = 0 := by
    simpa using coordinate_one_zero hn H hH hs hsn i
  exact tame_valued_degree
    htame hdegree hf hf0

end P1960
end Struik
