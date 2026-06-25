import Submission.ClassField.CohomologyOps.Uniqueness
import Mathlib.LinearAlgebra.TensorProduct.Associator

namespace Submission.CField.COps.CPFuncto

open CategoryTheory
open Submission.CField.COps.CPBuild
open scoped MonoidalCategory TensorProduct

variable {G : Type} [Group G]

theorem associator_tensorElement (M N P : Rep ℤ G) (m : M) (n : N) (p : P) :
    (α_ M N P).hom
        (tensorElement (M ⊗ N : Rep ℤ G) P (tensorElement M N m n) p) =
      tensorElement M (N ⊗ P : Rep ℤ G) m (tensorElement N P n p) := by
  letI := M.hV2
  letI := N.hV2
  letI := P.hV2
  letI := (M ⊗ N : Rep ℤ G).hV2
  letI := (N ⊗ P : Rep ℤ G).hV2
  change (TensorProduct.assoc ℤ M N P) ((m ⊗ₜ[ℤ] n) ⊗ₜ[ℤ] p) =
    m ⊗ₜ[ℤ] (n ⊗ₜ[ℤ] p)
  exact TensorProduct.assoc_tmul m n p

theorem initialProduct_assoc (r s t : ℕ) (q : Fin ((r + s) + t) → G) :
    initialProduct (r + s) t q =
      initialProduct r (s + t)
          (tupleCast (by omega : (r + s) + t = r + (s + t)) q) *
        initialProduct s t (fun j =>
          tupleCast (by omega : (r + s) + t = r + (s + t)) q
            (Fin.natAdd r j)) := by
  unfold initialProduct Fin.partialProd
  rw [List.take_add, List.prod_append]
  congr 1
  · apply congrArg List.prod
    apply List.ext_getElem
    · simp only [List.length_take, List.length_ofFn]
      rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    · intro i hi₁ hi₂
      simp only [List.getElem_take, List.getElem_ofFn]
      simp only [tupleCast_apply]
  · apply congrArg List.prod
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_ofFn]
      rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    · intro i hi₁ hi₂
      simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
      simp only [tupleCast_apply, Fin.natAdd]

theorem initial_left_assoc (r s t : ℕ) (q : Fin ((r + s) + t) → G) :
    initialProduct r s (fun i => q (Fin.castAdd t i)) =
      initialProduct r (s + t)
        (tupleCast (by omega : (r + s) + t = r + (s + t)) q) := by
  unfold initialProduct Fin.partialProd
  apply congrArg List.prod
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
  · intro i hi₁ hi₂
    simp only [List.getElem_take, List.getElem_ofFn, tupleCast_apply]
    congr 1

theorem cochainCup_assoc
    (M N P : Rep ℤ G) (r s t : ℕ)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N)
    (χ : (Fin t → G) → P) :
    (fun q => (α_ M N P).hom
      (cochainCup (M ⊗ N : Rep ℤ G) P (r + s) t
        (cochainCup M N r s φ ψ) χ q)) =
      cochainCast (by omega : (r + s) + t = r + (s + t))
        (cochainCup M (N ⊗ P : Rep ℤ G) r (s + t) φ
          (cochainCup N P s t ψ χ)) := by
  funext q
  simp only [cochainCup, associator_tensorElement, tensorElement_action,
    cochainCast]
  let h : (r + s) + t = r + (s + t) := by omega
  have hφ :
      (fun i : Fin r => q (Fin.castAdd t (Fin.castAdd s i))) =
        (fun i : Fin r => tupleCast h q (Fin.castAdd (s + t) i)) := by
    funext i
    simp only [tupleCast_apply]
    congr 1
  have hψ :
      (fun j : Fin s => q (Fin.castAdd t (Fin.natAdd r j))) =
        (fun j : Fin s => tupleCast h q (Fin.natAdd r (Fin.castAdd t j))) := by
    funext j
    simp only [tupleCast_apply]
    congr 1
  have hχ :
      (fun j : Fin t => q (Fin.natAdd (r + s) j)) =
        (fun j : Fin t => tupleCast h q (Fin.natAdd r (Fin.natAdd s j))) := by
    funext j
    simp only [tupleCast_apply]
    congr 1
    apply Fin.ext
    simp only [Fin.natAdd]
    omega
  have hA := initial_left_assoc r s t q
  have hAB := initialProduct_assoc r s t q
  rw [hφ, hψ, hχ, hA]
  rw [rep_action_mul, ← hAB]

noncomputable section

theorem cupCocycle_assoc
    (M N P : Rep ℤ G) (r s t : ℕ)
    (x : groupCohomology.cocycles M r)
    (y : groupCohomology.cocycles N s)
    (z : groupCohomology.cocycles P t) :
    groupCohomology.cocyclesMap (MonoidHom.id G) (α_ M N P).hom
        ((r + s) + t)
        (cupCocycle (M ⊗ N : Rep ℤ G) P (r + s) t
          (cupCocycle M N r s x y) z) =
      cocyclesCast (M ⊗ (N ⊗ P) : Rep ℤ G)
        (by omega : r + (s + t) = (r + s) + t)
        (cupCocycle M (N ⊗ P : Rep ℤ G) r (s + t) x
          (cupCocycle N P s t y z)) := by
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.iCocycles (M ⊗ (N ⊗ P) : Rep ℤ G)
      ((r + s) + t))).1 inferInstance
  have hmap := i_cocycles_id (A := ((M ⊗ N) ⊗ P : Rep ℤ G))
    (α_ M N P).hom ((r + s) + t)
    (cupCocycle (M ⊗ N : Rep ℤ G) P (r + s) t
      (cupCocycle M N r s x y) z)
  have hmap' :
      groupCohomology.iCocycles (M ⊗ (N ⊗ P) : Rep ℤ G) ((r + s) + t)
          (groupCohomology.cocyclesMap (MonoidHom.id G) (α_ M N P).hom
            ((r + s) + t)
            (cupCocycle (M ⊗ N : Rep ℤ G) P (r + s) t
              (cupCocycle M N r s x y) z)) =
        fun q => (α_ M N P).hom
          (groupCohomology.iCocycles ((M ⊗ N) ⊗ P : Rep ℤ G)
            ((r + s) + t)
            (cupCocycle (M ⊗ N : Rep ℤ G) P (r + s) t
              (cupCocycle M N r s x y) z) q) := by
    convert hmap using 1
  have hleftOuter := i_cup_cocycle
    (M ⊗ N : Rep ℤ G) P (r + s) t (cupCocycle M N r s x y) z
  have hleftInner := i_cup_cocycle M N r s x y
  have hrightOuter := i_cup_cocycle
    M (N ⊗ P : Rep ℤ G) r (s + t) x (cupCocycle N P s t y z)
  have hrightInner := i_cup_cocycle N P s t y z
  let h : (r + s) + t = r + (s + t) := by omega
  let rightCocycle :=
    cupCocycle M (N ⊗ P : Rep ℤ G) r (s + t) x
      (cupCocycle N P s t y z)
  have hcast := congrArg (fun q => q rightCocycle)
    (cocycles_cast_i (M ⊗ (N ⊗ P) : Rep ℤ G) h.symm)
  simp only [ConcreteCategory.comp_apply] at hcast
  rw [hmap', hleftOuter, hleftInner, hcast, cochain_hom,
    hrightOuter, hrightInner]
  · exact cochainCup_assoc M N P r s t
      (groupCohomology.iCocycles M r x)
      (groupCohomology.iCocycles N s y)
      (groupCohomology.iCocycles P t z)
  · exact h.symm

/-- Proposition II.1.39(a): cup product is associative.  The canonical
tensor associator identifies `(M ⊗ N) ⊗ P` with `M ⊗ (N ⊗ P)`, and the
degree cast records the corresponding reassociation of natural-number
degrees. -/
theorem cupCohomology_assoc
    (M N P : Rep ℤ G) (r s t : ℕ)
    (x : groupCohomology M r) (y : groupCohomology N s)
    (z : groupCohomology P t) :
    groupCohomology.map (MonoidHom.id G) (α_ M N P).hom ((r + s) + t)
        (cupCohomology (M ⊗ N : Rep ℤ G) P (r + s) t
          (cupCohomology M N r s x y) z) =
      cohomologyCast (M ⊗ (N ⊗ P) : Rep ℤ G)
        (by omega : r + (s + t) = (r + s) + t)
        (cupCohomology M (N ⊗ P : Rep ℤ G) r (s + t) x
          (cupCohomology N P s t y z)) := by
  induction x using groupCohomology_induction_on with
  | h xc =>
      induction y using groupCohomology_induction_on with
      | h yc =>
          induction z using groupCohomology_induction_on with
          | h zc =>
              rw [cupCohomology_π, cupCohomology_π,
                cupCohomology_π, cupCohomology_π]
              let leftCocycle :=
                cupCocycle (M ⊗ N : Rep ℤ G) P (r + s) t
                  (cupCocycle M N r s xc yc) zc
              have hmap := congrArg (fun q => q leftCocycle)
                (groupCohomology.π_map
                  (f := MonoidHom.id G) (φ := (α_ M N P).hom) ((r + s) + t))
              simp only [ConcreteCategory.comp_apply] at hmap
              dsimp only [leftCocycle] at hmap
              have hmap' :
                  groupCohomology.map (MonoidHom.id G) (α_ M N P).hom
                      ((r + s) + t)
                      (groupCohomology.π ((M ⊗ N) ⊗ P : Rep ℤ G)
                        ((r + s) + t)
                        (cupCocycle (M ⊗ N : Rep ℤ G) P (r + s) t
                          (cupCocycle M N r s xc yc) zc)) =
                    groupCohomology.π (M ⊗ (N ⊗ P) : Rep ℤ G)
                      ((r + s) + t)
                      (groupCohomology.cocyclesMap (MonoidHom.id G)
                        (α_ M N P).hom ((r + s) + t)
                        (cupCocycle (M ⊗ N : Rep ℤ G) P (r + s) t
                          (cupCocycle M N r s xc yc) zc)) := by
                convert hmap using 1
              let rightCocycle :=
                cupCocycle M (N ⊗ P : Rep ℤ G) r (s + t) xc
                  (cupCocycle N P s t yc zc)
              let h : (r + s) + t = r + (s + t) := by omega
              have hcast := congrArg (fun q => q rightCocycle)
                (π_comp_cohomologyCast (M ⊗ (N ⊗ P) : Rep ℤ G) h.symm)
              simp only [ConcreteCategory.comp_apply] at hcast
              dsimp only [rightCocycle] at hcast
              rw [hmap', hcast]
              exact congrArg
                (groupCohomology.π (M ⊗ (N ⊗ P) : Rep ℤ G) ((r + s) + t))
                (cupCocycle_assoc M N P r s t xc yc zc)

end

end Submission.CField.COps.CPFuncto
