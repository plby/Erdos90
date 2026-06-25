import Towers.ClassField.SimpleAlgebras.DoubleCentralizer

/-!
# Milne, Class Field Theory, Lemma IV.1.15

Milne writes `D` for the centralizer of the action of `A` in `End_k(V)` and
`B` for the centralizer of `D`.  Thus an element of `B` is a `k`-linear
endomorphism commuting with every `A`-linear endomorphism of `V`.  The lemma
says that its values on any finite tuple of vectors can be simultaneously
interpolated by one element of `A`.

The tracked double-centralizer theorem proves the stronger global statement.
Here we package a commuting `k`-linear endomorphism as an endomorphism linear
over `Module.End A V`, apply that theorem, and then evaluate the resulting
equality on the requested finite tuple.
-/

namespace Towers.CField.SAlgebr

noncomputable section

variable (k A V : Type*) [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
variable [IsSemisimpleModule A V] [Module.Finite k V]

/-- **Lemma IV.1.15.**  Let `b` lie in the bicommutant of the action of `A`
on `V`.  Given any finite family of vectors, one element of `A` agrees with
`b` simultaneously on every vector in that family. -/
theorem smul_bicommutant_fin
    {n : ℕ} (v : Fin n → V) (b : Module.End k V)
    (hb : ∀ d : Module.End A V,
      b.comp (d.restrictScalars k) = (d.restrictScalars k).comp b) :
    ∃ a : A, ∀ i : Fin n, a • v i = b (v i) := by
  let b' : Module.End (Module.End A V) V :=
    { toFun := b
      map_add' := b.map_add
      map_smul' := fun d x ↦ by
        change b (d x) = d (b x)
        exact DFunLike.congr_fun (hb d) x }
  obtain ⟨a, ha⟩ := doubleCentralizer_surjective k A V b'
  refine ⟨a, fun i ↦ ?_⟩
  change (Module.toModuleEnd (Module.End A V) (S := A) V a) (v i) =
    b' (v i)
  exact DFunLike.congr_fun ha (v i)

end

end Towers.CField.SAlgebr
