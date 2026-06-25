import Submission.ClassField.QuadraticForms.HilbertInvariants
import Submission.ClassField.QuadraticForms.QuadraticHilbert
import Submission.ClassField.QuadraticForms.BasesDifferAdjacent
import Mathlib.NumberTheory.LocalField.Basic

/-! # Chapter VIII, Section 6, Proposition 6.7 -/

namespace Submission.CField.QForms

variable {G μ : Type*} [CommGroup G] [CommGroup μ]

namespace AHSym

variable (h : AHSym G μ)

/-- One adjacent two-dimensional basis change in the proof of Proposition
6.7.  Equivalent binary pieces have the same discriminant and the same
binary Hilbert symbol; all other diagonal coefficients are unchanged. -/
inductive DiagonalNeighbor : List G → List G → Prop
  | replace (pre post : List G) (a b a' b' : G)
      (discriminant_eq : a * b = a' * b')
      (symbol_eq : h.symbol a b = h.symbol a' b') :
      DiagonalNeighbor
        (pre ++ [a, b] ++ post)
        (pre ++ [a', b'] ++ post)

/-- A chain of the adjacent changes supplied geometrically by Lemma 6.8. -/
def DiagonalBasisChain : List G → List G → Prop :=
  Relation.ReflTransGen h.DiagonalNeighbor

/-- A single adjacent binary change preserves the Hasse invariant. -/
theorem hasse_diagonal_neighbor {xs ys : List G}
    (H : h.DiagonalNeighbor xs ys) :
    h.hasse xs = h.hasse ys := by
  cases H with
  | replace pre post a b a' b' hdisc hsymbol =>
      have hpairEpsilon : h.epsilon [a, b] = h.epsilon [a', b'] := by
        simpa [epsilon] using hsymbol
      have hpairDiscriminant : discriminant [a, b] = discriminant [a', b'] := by
        simpa [discriminant] using hdisc
      have htailEpsilon :
          h.epsilon ([a, b] ++ post) = h.epsilon ([a', b'] ++ post) := by
        rw [h.epsilon_append, h.epsilon_append, hpairEpsilon, hpairDiscriminant]
      have htailDiscriminant :
          discriminant ([a, b] ++ post) =
            discriminant ([a', b'] ++ post) := by
        simp only [discriminant, List.prod_append, List.prod_cons,
          List.prod_nil, mul_one]
        rw [hdisc]
      have hallEpsilon :
          h.epsilon (pre ++ ([a, b] ++ post)) =
            h.epsilon (pre ++ ([a', b'] ++ post)) := by
        calc
          h.epsilon (pre ++ ([a, b] ++ post)) =
              h.epsilon pre * h.epsilon ([a, b] ++ post) *
                h.symbol (discriminant pre) (discriminant ([a, b] ++ post)) :=
            h.epsilon_append pre ([a, b] ++ post)
          _ = h.epsilon pre * h.epsilon ([a', b'] ++ post) *
                h.symbol (discriminant pre) (discriminant ([a', b'] ++ post)) := by
            rw [htailEpsilon, htailDiscriminant]
          _ = h.epsilon (pre ++ ([a', b'] ++ post)) :=
            (h.epsilon_append pre ([a', b'] ++ post)).symm
      have hallDiscriminant :
          discriminant (pre ++ ([a, b] ++ post)) =
            discriminant (pre ++ ([a', b'] ++ post)) := by
        simp only [discriminant, List.prod_append, List.prod_cons,
          List.prod_nil, mul_one]
        calc
          pre.prod * (a * b * post.prod) =
              pre.prod * (a * b) * post.prod := by ac_rfl
          _ = pre.prod * (a' * b') * post.prod := by rw [hdisc]
          _ = pre.prod * (a' * b' * post.prod) := by ac_rfl
      rw [List.append_assoc, List.append_assoc]
      rw [h.hasse_epsilon_discriminant,
        h.hasse_epsilon_discriminant,
        hallEpsilon, hallDiscriminant]

/-- **Proposition VIII.6.7, diagonal-chain form.** The Hasse invariant is
unchanged along the chain of orthogonal bases from Lemma 6.8. -/
theorem hasse_invariant {xs ys : List G}
    (H : h.DiagonalBasisChain xs ys) :
    h.hasse xs = h.hasse ys := by
  induction H with
  | refl => rfl
  | tail _ hyz ih => exact ih.trans (h.hasse_diagonal_neighbor hyz)

end AHSym

noncomputable section

universe u

/-- The Hasse product of a list of actual field coefficients, formed with
the concrete quadratic Hilbert sign. -/
noncomputable def concreteQuadraticHasse {K : Type u} [Field K] : List K → ℤˣ
  | [] => 1
  | a :: as =>
      quadraticHilbertSign a a *
        (as.map fun b ↦ quadraticHilbertSign a b).prod *
          concreteQuadraticHasse as

/-- The Hasse invariant computed in one ordered orthogonal basis. -/
noncomputable def quadraticHasseBasis
    {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V)
    (B : Module.Basis (Fin (Module.finrank K V)) K V) : ℤˣ :=
  concreteQuadraticHasse (List.ofFn fun i ↦ Q (B i))

/-- The basis-chain input of Lemma 6.8, packaged at the universe used by the
source statement below. -/
def DiagonalInvariance : Prop :=
  ∀ (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    BasesDifferMost (k := K) (V := V)

/-- The remaining adjacent two-dimensional calculation.  Proposition 6.2
identifies the changed binary summands, and the already-proved abstract
`hasse_diagonal_neighbor` calculation then gives this equality.  It is
kept separate from Lemma 6.8's purely geometric basis chain. -/
def AdjacentBasisBridge : Prop :=
  ∀ (K V : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V)
    (B B' : Module.Basis (Fin (Module.finrank K V)) K V),
    Q.Nondegenerate → Q.polarBilin.IsOrthoᵢ B → Q.polarBilin.IsOrthoᵢ B' →
    BasesMostAdjacent B B' →
      quadraticHasseBasis Q B =
        quadraticHasseBasis Q B'

/-- Lemma 6.8 and the adjacent binary calculation imply independence from
the chosen orthogonal basis. -/
theorem basis_invariance_bridges
    (h68 : DiagonalInvariance.{u})
    (hadjacent : AdjacentBasisBridge.{u}) :
    ∀ (K V : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V)
    (B B' : Module.Basis (Fin (Module.finrank K V)) K V),
    Q.Nondegenerate → Q.polarBilin.IsOrthoᵢ B → Q.polarBilin.IsOrthoᵢ B' →
      quadraticHasseBasis Q B =
        quadraticHasseBasis Q B'
  := by
  intro K V _ _ _ _ _ _ _ _ Q B B' hQ hB hB'
  obtain ⟨m, Bs, hfirst, hlast, horthogonal, hstep⟩ :=
    h68 K V Q B B' hQ hB hB'
  have hchain : ∀ j : ℕ, (hj : j ≤ m) →
      quadraticHasseBasis Q (Bs 0) =
        quadraticHasseBasis Q (Bs ⟨j, Nat.lt_succ_of_le hj⟩) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
        intro hj
        have hjm : j < m := by omega
        let i : Fin m := ⟨j, hjm⟩
        have hnext := hadjacent K V Q (Bs i.castSucc) (Bs i.succ) hQ
          (horthogonal i.castSucc) (horthogonal i.succ) (hstep i)
        exact (ih (by omega)).trans hnext
  have hend := hchain m (Nat.le_refl m)
  rw [hfirst, hlast] at hend
  exact hend

/-- The source statement follows from basis independence by pulling the
second orthogonal basis back along the supplied isometry. -/
theorem diagonal_invariance_bridges
    (h68 : DiagonalInvariance.{u})
    (hadjacent : AdjacentBasisBridge.{u}) :
    (∀ (K V : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
          [ValuativeRel K] [IsNonarchimedeanLocalField K] [NeZero (2 : K)]
          [AddCommGroup V] [Module K V] [FiniteDimensional K V]
          (Q Q' : QuadraticForm K V)
          (B B' : Module.Basis (Fin (Module.finrank K V)) K V),
          Nonempty (Q.IsometryEquiv Q') → Q.Nondegenerate →
          Q.polarBilin.IsOrthoᵢ B → Q'.polarBilin.IsOrthoᵢ B' →
            quadraticHasseBasis Q B =
              quadraticHasseBasis Q' B') := by
  intro K V _ _ _ _ _ _ _ _ Q Q' B B' he hQ hB hB'
  obtain ⟨e⟩ := he
  let Bpull : Module.Basis (Fin (Module.finrank K V)) K V :=
    B'.map e.symm.toLinearEquiv
  have hBpull : Q.polarBilin.IsOrthoᵢ Bpull := by
    intro i j hij
    have hij' := hB' hij
    change QuadraticMap.polar Q' (B' i) (B' j) = 0 at hij'
    change QuadraticMap.polar Q (Bpull i) (Bpull j) = 0
    rw [show Bpull i = e.symm (B' i) by simp [Bpull],
      show Bpull j = e.symm (B' j) by simp [Bpull]]
    change Q (e.symm (B' i) + e.symm (B' j)) -
        Q (e.symm (B' i)) - Q (e.symm (B' j)) = 0
    have hadd : e.symm (B' i) + e.symm (B' j) =
        e.symm (B' i + B' j) := by
      exact (e.symm.toLinearEquiv.map_add (B' i) (B' j)).symm
    rw [hadd, e.symm.map_app, e.symm.map_app, e.symm.map_app]
    exact hij'
  have hinvariant := basis_invariance_bridges h68 hadjacent
    K V Q B Bpull hQ hB hBpull
  have hpull : quadraticHasseBasis Q Bpull =
      quadraticHasseBasis Q' B' := by
    unfold quadraticHasseBasis
    congr 1
    rw [List.ofFn_inj]
    funext i
    simp [Bpull, Module.Basis.map_apply]
  exact hinvariant.trans hpull

end

end Submission.CField.QForms
