import Submission.ClassField.Shifting.BarProjection

/-!
# Degree-one bar-projection formulas for Proposition II.3.2(b)

These formulas compute the explicit Shapiro projection on degree-one bar
generators.  For a chosen right-coset representative `q.out`, the result is
the correction factor `q.out * g * rep(q.out * g)⁻¹` in the subgroup.
-/

open CategoryTheory Finsupp

namespace Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

theorem diagonal_inv_single (n : ℕ)
    (x : Fin n → G) (s : G) (r : k) :
    ((diagonalSuccIsoFree k G n).inv).hom
        (single x (single s r)) =
      single (s • Fin.partialProd x : Fin (n + 1) → G) r := by
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial,
    Iso.trans_inv, Category.assoc, hom_comp,
    Representation.IntertwiningMap.comp_apply]
  change (Representation.linearizeOfMulActionIso k G
      (Fin (n + 1) → G)).symm _ = _
  rw [Representation.linearizeOfMulActionIso_symm_apply]
  change Representation.linearizeMap
      (Action.diagonalSuccIsoTensorTrivial G n).inv _ = _
  have hfree :
      ((leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv).hom
          (single x (single s r)) =
        single s 1 ⊗ₜ[k] single x r := by
    exact Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x s r
  rw [hfree]
  simp only [Action.tensorObj_V, Action.trivial_V, tensor_V, tensor_ρ,
    Iso.symm_inv, Functor.Monoidal.μIso_hom,
    MonoidalCategory.tensorIso_inv, hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply]
  change Representation.linearizeMap
      (Action.diagonalSuccIsoTensorTrivial G n).inv
      (Representation.LinearizeMonoidal.μ (k := k)
        (Action.leftRegular G) (Action.trivial G (Fin n → G))
        ((Representation.linearizeOfMulActionIso k G G).symm
            (single s 1) ⊗ₜ[k]
          (Representation.linearizeTrivialIso k G (Fin n → G)).symm
            (single x r))) = _
  rw [Representation.linearizeOfMulActionIso_symm_apply,
    Representation.linearizeTrivialIso_symm_apply]
  have hmu :
      Representation.LinearizeMonoidal.μ (k := k)
          (Action.leftRegular G) (Action.trivial G (Fin n → G))
          (single s 1 ⊗ₜ[k] single x r) =
        single (s, x) (1 * r) :=
    Representation.LinearizeMonoidal.μ_apply_single_single
      (k := k) (X := Action.leftRegular G)
      (Y := Action.trivial G (Fin n → G)) s x 1 r
  calc
    _ = Representation.linearizeMap
          (Action.diagonalSuccIsoTensorTrivial G n).inv
          (single (s, x) (1 * r)) :=
      congrArg
        (fun z => Representation.linearizeMap
          (Action.diagonalSuccIsoTensorTrivial G n).inv z) hmu
    _ = _ := by
      rw [Representation.linearizeMap_single,
        Action.diagonalSuccIsoTensorTrivial_inv_hom_apply]
      simp only [one_mul]

theorem diagonal_iso_single (n : ℕ)
    (x : Fin (n + 1) → G) (r : k) :
    ((diagonalSuccIsoFree k G n).hom).hom (single x r) =
      single (fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)
        (single (x 0) r) := by
  rw [← Iso.inv_hom_id_apply (diagonalSuccIsoFree k G n)
    (single (fun i => (x (Fin.castSucc i))⁻¹ * x i.succ)
      (single (x 0) r))]
  apply congrArg ((diagonalSuccIsoFree k G n).hom).hom
  rw [diagonal_inv_single]
  rw [Fin.partialProd_left_inv]

theorem bar_f_single (H : Subgroup G)
    (g s : G) (r : k) :
    ((barProjection (k := k) H).f 1).hom
        (single (fun _ : Fin 1 => g) (single s r)) =
      single
        (fun _ : Fin 1 =>
          (rightCosetCorrection H s)⁻¹ *
            rightCosetCorrection H (s * g))
        (single (rightCosetCorrection H s) r) := by
  simp only [barProjection, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f]
  change ((diagonalSuccIsoFree k H 1).hom).hom
      ((standardProjectionMap (k := k) H 1).hom
        (((diagonalSuccIsoFree k G 1).inv).hom
          (single (fun _ : Fin 1 => g) (single s r)))) = _
  rw [diagonal_inv_single]
  let z : Fin 2 → G := s • Fin.partialProd (fun _ : Fin 1 => g)
  have hproj :
      (standardProjectionMap (k := k) H 1).hom (single z r) =
        single (fun i => rightCosetCorrection H (z i)) r :=
    standard_projection_single H 1 z r
  change ((diagonalSuccIsoFree k H 1).hom).hom
      ((standardProjectionMap (k := k) H 1).hom (single z r)) = _
  calc
    _ = ((diagonalSuccIsoFree k H 1).hom).hom
          (single (fun i => rightCosetCorrection H (z i)) r) :=
      congrArg ((diagonalSuccIsoFree k H 1).hom).hom hproj
    _ = single
          (fun i : Fin 1 =>
            (rightCosetCorrection H (z (Fin.castSucc i)))⁻¹ *
              rightCosetCorrection H (z i.succ))
          (single (rightCosetCorrection H (z 0)) r) := by
      rw [diagonal_iso_single]
    _ = _ := by
      have hz0 : z 0 = s := by
        simp [z, Fin.partialProd]
      have hindex :
          (fun i : Fin 1 =>
            (rightCosetCorrection H (z (Fin.castSucc i)))⁻¹ *
              rightCosetCorrection H (z i.succ)) =
          (fun _ : Fin 1 =>
            (rightCosetCorrection H s)⁻¹ *
              rightCosetCorrection H (s * g)) := by
        funext i
        fin_cases i
        simp [z, Fin.partialProd]
      rw [hindex, hz0]

theorem right_coset_out (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) :
    rightCosetCorrection H (Quotient.out q) = 1 := by
  apply Subtype.ext
  change Quotient.out q *
      (Quotient.out (Quotient.mk (QuotientGroup.rightRel H)
        (Quotient.out q)))⁻¹ = 1
  rw [show Quotient.mk (QuotientGroup.rightRel H) (Quotient.out q) = q from
    Quotient.out_eq q]
  simp

/-- On a degree-one generator based at a chosen right-coset representative,
the bar projection returns exactly the transfer correction factor. -/
theorem bar_f_coset (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) (g : G) (r : k) :
    ((barProjection (k := k) H).f 1).hom
        (single (fun _ : Fin 1 => g) (single (Quotient.out q) r)) =
      single
        (fun _ : Fin 1 =>
          rightCosetCorrection H (Quotient.out q * g))
        (single (1 : H) r) := by
  rw [bar_f_single]
  rw [right_coset_out]
  simp

end Rep
