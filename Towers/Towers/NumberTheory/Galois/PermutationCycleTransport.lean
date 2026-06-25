import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.EquivFin


/-!
# Transporting cyclic permutation subsets

The helpers in this file transport `Equiv.Perm.IsCycleOn` through an
equivalence that intertwines two permutations.  They are used to pass from
finite-field Frobenius to arithmetic Frobenius on integral roots, and then to
the polynomial Galois action on field-valued roots.
-/

namespace Towers.NumberTheory.Milne

open Equiv Function Set

variable {alpha beta : Type*}

/-- Conjugating a permutation through an equivalence transports every cyclic
subset to its image. -/
theorem Equiv.Perm.IsCycleOn.permCongr
    (e : alpha ≃ beta) {sigma : Equiv.Perm alpha} {s : Set alpha}
    (hcycle : sigma.IsCycleOn s) :
    (e.permCongr sigma).IsCycleOn (e '' s) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨sigma x, hcycle.1.mapsTo hx, by simp⟩
    · intro x hx y hy hxy
      exact (e.permCongr sigma).injective hxy
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := hcycle.1.surjOn hy
      refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
      simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, hxy]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := hcycle.2 hx hy
    refine ⟨n, ?_⟩
    have hpow : e.permCongr (sigma ^ n) = (e.permCongr sigma) ^ n :=
      map_zpow e.permCongrHom sigma n
    rw [← hpow]
    simp only [Equiv.permCongr_apply,
      Equiv.symm_apply_apply, hn]

/-- A pointwise intertwining equation identifies the target permutation with
the conjugate permutation and hence transports cyclic subsets. -/
theorem Equiv.Perm.IsCycleOn.transport
    (e : alpha ≃ beta) {sigma : Equiv.Perm alpha} {tau : Equiv.Perm beta}
    {s : Set alpha} (hcycle : sigma.IsCycleOn s)
    (hintertwine : ∀ x, e (sigma x) = tau (e x)) :
    tau.IsCycleOn (e '' s) := by
  have htau : tau = e.permCongr sigma := by
    ext y
    simpa using (hintertwine (e.symm y)).symm
  rw [htau]
  exact Equiv.Perm.IsCycleOn.permCongr e hcycle

/-- Finset form of `Equiv.Perm.IsCycleOn.transport`. -/
theorem Equiv.Perm.IsCycleOn.transp_finse
    (e : alpha ≃ beta) {sigma : Equiv.Perm alpha} {tau : Equiv.Perm beta}
    (s : Finset alpha) (hcycle : sigma.IsCycleOn (s : Set alpha))
    (hintertwine : ∀ x, e (sigma x) = tau (e x)) :
    tau.IsCycleOn (s.map e.toEmbedding : Set beta) := by
  classical
  convert Equiv.Perm.IsCycleOn.transport e hcycle hintertwine using 1
  ext y
  simp

/-- An equivalence preserves the cardinality of a mapped finset. -/
@[simp]
theorem Finset.card_map_equiv
    (e : alpha ≃ beta) (s : Finset alpha) :
    (s.map e.toEmbedding).card = s.card := by
  classical
  simp

/-- Mapping a two-piece cover through an equivalence again covers the target
type. -/
theorem Finset.map_equivunion_equniv
    [Fintype alpha] [Fintype beta] [DecidableEq alpha] [DecidableEq beta]
    (e : alpha ≃ beta) {s t : Finset alpha}
    (hcover : s ∪ t = Finset.univ) :
    s.map e.toEmbedding ∪ t.map e.toEmbedding = Finset.univ := by
  ext y
  have hx := Finset.ext_iff.mp hcover (e.symm y)
  simpa using hx

end Towers.NumberTheory.Milne
