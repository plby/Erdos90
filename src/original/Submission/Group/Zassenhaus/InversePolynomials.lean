import Submission.Group.Zassenhaus.TriangularGHLaw

open Submission.TCTex

/-!
# Weighted binomial arithmetic for Hall product and inverse collection

This file develops the multivariable coefficient language needed by the
symbolic Hall collector in TeX Claim 8.  The collector itself will emit
products of generalized binomial coefficients.  The results below let later
collection steps introduce one source exponent, append independent recipes,
raise the allowed output weight, and combine recipes inside their integer
span.

The file is intentionally not imported by the existing collection proof.  It
is a standalone extension point for the missing product and inverse collector.
-/

namespace Submission
namespace TCTex

namespace WHMono

/--
The weighted cost of one symbolic recipe before checking that it can
contribute to a chosen output weight.
-/
def inputWeight
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    (m : WHMono H ι s) :
    ℕ :=
  ∑ ν, m.binomialIndex ν * (m.address ν).1

/-- A source exponent is represented by the singleton recipe `choose A 1`. -/
def single
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    (j : ι)
    (a : HEAddres H)
    (ha : a.1 ≤ s) :
    WHMono H ι s where
  length := 1
  length_pos := by simp
  input := fun _ => j
  address := fun _ => a
  binomialIndex := fun _ => 1
  binomialIndex_pos := by simp
  weightedWeight_le := by simpa using ha

@[simp]
lemma eval_single
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    (e : ι → HEFam H)
    (j : ι)
    (a : HEAddres H)
    (ha : a.1 ≤ s) :
    (single j a ha).eval e = e j a.1 a.2 := by
  simp [single, WHMono.eval]

/-- Raise the permitted target weight without changing a recipe. -/
def weaken
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s t : ℕ}
    (m : WHMono H ι s)
    (hst : s ≤ t) :
    WHMono H ι t where
  length := m.length
  length_pos := m.length_pos
  input := m.input
  address := m.address
  binomialIndex := m.binomialIndex
  binomialIndex_pos := m.binomialIndex_pos
  weightedWeight_le := m.weightedWeight_le.trans hst

@[simp]
lemma eval_weaken
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s t : ℕ}
    (e : ι → HEFam H)
    (m : WHMono H ι s)
    (hst : s ≤ t) :
    (m.weaken hst).eval e = m.eval e :=
  rfl

/-- Relabel the source inputs without changing the Hall addresses. -/
def mapInput
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    {s : ℕ}
    (f : ι → κ)
    (m : WHMono H ι s) :
    WHMono H κ s where
  length := m.length
  length_pos := m.length_pos
  input := f ∘ m.input
  address := m.address
  binomialIndex := m.binomialIndex
  binomialIndex_pos := m.binomialIndex_pos
  weightedWeight_le := m.weightedWeight_le

@[simp]
lemma eval_mapInput
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    {s : ℕ}
    (e : κ → HEFam H)
    (f : ι → κ)
    (m : WHMono H ι s) :
    (m.mapInput f).eval e = m.eval (e ∘ f) :=
  rfl

/--
Append two independent symbolic recipes.  Their weighted costs add, so a
collector can multiply coefficients while recording the corresponding sum of
input weights.
-/
def append
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s t v : ℕ}
    (m : WHMono H ι s)
    (m' : WHMono H ι t)
    (hst : s + t ≤ v) :
    WHMono H ι v where
  length := m.length + m'.length
  length_pos := Nat.add_pos_left m.length_pos _
  input := Fin.append m.input m'.input
  address := Fin.append m.address m'.address
  binomialIndex := Fin.append m.binomialIndex m'.binomialIndex
  binomialIndex_pos := by
    intro ν
    refine Fin.addCases ?_ ?_ ν
    · intro i
      simpa using m.binomialIndex_pos i
    · intro i
      simpa using m'.binomialIndex_pos i
  weightedWeight_le := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    exact (Nat.add_le_add m.weightedWeight_le m'.weightedWeight_le).trans hst

@[simp]
lemma eval_append
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s t v : ℕ}
    (e : ι → HEFam H)
    (m : WHMono H ι s)
    (m' : WHMono H ι t)
    (hst : s + t ≤ v) :
    (m.append m' hst).eval e = m.eval e * m'.eval e := by
  change
    (∏ ν : Fin (m.length + m'.length),
      Ring.choose
        (e (Fin.append m.input m'.input ν)
          (Fin.append m.address m'.address ν).1
          (Fin.append m.address m'.address ν).2)
        (Fin.append m.binomialIndex m'.binomialIndex ν)) =
      m.eval e * m'.eval e
  rw [Fin.prod_univ_add]
  change
    (∏ ν : Fin m.length,
      Ring.choose
        (e (Fin.append m.input m'.input (Fin.castAdd m'.length ν))
          (Fin.append m.address m'.address (Fin.castAdd m'.length ν)).1
          (Fin.append m.address m'.address (Fin.castAdd m'.length ν)).2)
        (Fin.append m.binomialIndex m'.binomialIndex (Fin.castAdd m'.length ν))) *
      (∏ ν : Fin m'.length,
        Ring.choose
          (e (Fin.append m.input m'.input (Fin.natAdd m.length ν))
            (Fin.append m.address m'.address (Fin.natAdd m.length ν)).1
            (Fin.append m.address m'.address (Fin.natAdd m.length ν)).2)
          (Fin.append m.binomialIndex m'.binomialIndex (Fin.natAdd m.length ν))) =
      m.eval e * m'.eval e
  congr 1
  · apply Finset.prod_congr rfl
    intro ν _hν
    rw [Fin.append_left, Fin.append_left, Fin.append_left]
  · apply Finset.prod_congr rfl
    intro ν _hν
    rw [Fin.append_right, Fin.append_right, Fin.append_right]

end WHMono

namespace ICMonomi

/-- The symbolic coefficient language contains zero. -/
lemma zero
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    (e : ι → HEFam H) :
    ICMonomi H s e 0 :=
  (Submodule.span ℤ _).zero_mem

/-- The symbolic coefficient language is closed under addition. -/
lemma add
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    {e : ι → HEFam H}
    {x y : ℤ}
    (hx : ICMonomi H s e x)
    (hy : ICMonomi H s e y) :
    ICMonomi H s e (x + y) :=
  (Submodule.span ℤ _).add_mem hx hy

/-- The symbolic coefficient language is closed under integer scaling. -/
lemma smul
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    {e : ι → HEFam H}
    (c : ℤ)
    {x : ℤ}
    (hx : ICMonomi H s e x) :
    ICMonomi H s e (c * x) := by
  simpa [smul_eq_mul] using (Submodule.span ℤ _).smul_mem c hx

/-- The symbolic coefficient language is closed under negation. -/
lemma neg
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    {e : ι → HEFam H}
    {x : ℤ}
    (hx : ICMonomi H s e x) :
    ICMonomi H s e (-x) := by
  simpa using smul (-1) hx

/-- The symbolic coefficient language is closed under subtraction. -/
lemma sub
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    {e : ι → HEFam H}
    {x y : ℤ}
    (hx : ICMonomi H s e x)
    (hy : ICMonomi H s e y) :
    ICMonomi H s e (x - y) := by
  simpa [sub_eq_add_neg] using add hx (neg hy)

/-- Each raw Hall exponent is available as a singleton symbolic recipe. -/
lemma inputExponent
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s : ℕ}
    (e : ι → HEFam H)
    (j : ι)
    (a : HEAddres H)
    (ha : a.1 ≤ s) :
    ICMonomi H s e (e j a.1 a.2) := by
  apply Submodule.subset_span
  exact ⟨WHMono.single j a ha, by simp⟩

/--
Relabelling a family of source inputs preserves every symbolic coefficient.
This is the bridge from a collector's local block labels to the ambient input
list used in Claim 8.
-/
lemma mapInput
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    {s : ℕ}
    (e : κ → HEFam H)
    (f : ι → κ)
    {x : ℤ}
    (hx :
      ICMonomi
        H s (e ∘ f) x) :
    ICMonomi H s e x := by
  apply (Submodule.span_mono ?_) hx
  rintro _ ⟨m, rfl⟩
  exact ⟨m.mapInput f, by simp⟩

/-- Increasing the permitted output weight preserves every symbolic recipe. -/
lemma mono
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s t : ℕ}
    {e : ι → HEFam H}
    {x : ℤ}
    (hst : s ≤ t)
    (hx : ICMonomi H s e x) :
    ICMonomi H t e x := by
  apply (Submodule.span_mono ?_) hx
  rintro _ ⟨m, rfl⟩
  exact ⟨m.weaken hst, by simp⟩

/--
Multiplying symbolic coefficients concatenates their recipes and adds their
weight budgets.
-/
lemma mul
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {s t v : ℕ}
    {e : ι → HEFam H}
    {x y : ℤ}
    (hst : s + t ≤ v)
    (hx : ICMonomi H s e x)
    (hy : ICMonomi H t e y) :
    ICMonomi H v e (x * y) := by
  refine Submodule.span_induction
    (p := fun a _ =>
      ICMonomi H v e (a * y))
    ?_ (by simp [zero e]) ?_ ?_ hx
  · rintro _ ⟨m, rfl⟩
    refine Submodule.span_induction
      (p := fun b _ =>
        ICMonomi H v e (m.eval e * b))
      ?_ (by simp [zero e]) ?_ ?_ hy
    · rintro _ ⟨m', rfl⟩
      apply Submodule.subset_span
      exact ⟨m.append m' hst, by simp⟩
    · intro a b _ha _hb ha hb
      simpa [mul_add] using add ha hb
    · intro c a _ha ha
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using smul c ha
  · intro a b _ha _hb ha hb
    simpa [add_mul] using add ha hb
  · intro c a _ha ha
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using smul c ha

end ICMonomi

end TCTex
end Submission
