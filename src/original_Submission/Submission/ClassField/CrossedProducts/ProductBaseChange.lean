import Submission.ClassField.BrauerGroups.BaseChangeTower
import Submission.ClassField.BrauerGroups.MixedUniverseChange
import Submission.ClassField.CrossedProducts.CrossedProductBrauer


/-!
# Base change of Galois crossed products

This file identifies a scalar-extended crossed product with the crossed
product obtained by transporting its Galois group, coefficient field, and
factor set.  The intended application is completion at a place whose
decomposition group is the full global Galois group.
-/

namespace Submission.CField.CProduca

noncomputable section

open scoped TensorProduct

attribute [local instance] Units.mulDistribMulActionRight
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

section TransportedCocycle

variable {k L : Type u} {F E : Type v}
  [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- Transport a global factor set through an equivalence of Galois groups
and an equivariant embedding of coefficient fields. -/
noncomputable def transportedGaloisCocycle
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ)) :
    NMCocycl₂ (G := Gal(E/F)) (M := Eˣ) := by
  let mapUnits : Lˣ →* Eˣ := Units.map i
  have hmap (sigma : Gal(E/F)) (a : Lˣ) :
      mapUnits (g.symm sigma • a) = sigma • mapUnits a := by
    apply Units.ext
    change i (g.symm sigma (a : L)) = sigma (i (a : L))
    rw [hi]
    exact congrArg (fun tau : Gal(E/F) => tau (i (a : L)))
      (g.apply_symm_apply sigma)
  exact
    { toFun := fun p => mapUnits (c (g.symm p.1, g.symm p.2))
      isMulCocycle₂ := by
        intro sigma tau rho
        calc
          mapUnits (c (g.symm (sigma * tau), g.symm rho)) *
                mapUnits (c (g.symm sigma, g.symm tau)) =
              mapUnits
                (c (g.symm (sigma * tau), g.symm rho) *
                  c (g.symm sigma, g.symm tau)) := (map_mul mapUnits _ _).symm
          _ = mapUnits
                ((g.symm sigma • c (g.symm tau, g.symm rho)) *
                  c (g.symm sigma, g.symm (tau * rho))) := by
                congr 1
                simpa only [map_mul] using
                  c.isMulCocycle₂ (g.symm sigma) (g.symm tau) (g.symm rho)
          _ = mapUnits (g.symm sigma • c (g.symm tau, g.symm rho)) *
                mapUnits (c (g.symm sigma, g.symm (tau * rho))) :=
              map_mul mapUnits _ _
          _ = sigma • mapUnits (c (g.symm tau, g.symm rho)) *
                mapUnits (c (g.symm sigma, g.symm (tau * rho))) := by
              rw [hmap]
      map_one_fst := by simp
      map_one_snd := by simp }

omit [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional F E] [IsGalois F E] in
@[simp]
theorem transported_galois_cocycle
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (sigma tau : Gal(L/k)) :
    transportedGaloisCocycle i g hi c (g sigma, g tau) =
      Units.map i (c (sigma, tau)) := by
  simp [transportedGaloisCocycle]

variable [Algebra k F] [Algebra k E] [IsScalarTower k F E]

private noncomputable def crossedTransportFn
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ)) :
    CProduc c → CProduc (transportedGaloisCocycle i g hi c) :=
  fun x => CProduc.sum c x fun sigma a =>
    CProduc.single (transportedGaloisCocycle i g hi c) (g sigma) (i a)

omit [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional F E] [IsGalois F E] [Algebra k F]
  [Algebra k E] [IsScalarTower k F E] in
@[simp]
private theorem crossed_transport_fn
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (sigma : Gal(L/k)) (a : L) :
    crossedTransportFn i g hi c (CProduc.single c sigma a) =
      CProduc.single (transportedGaloisCocycle i g hi c)
        (g sigma) (i a) := by
  apply CProduc.sum_single_index
  simp

omit [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional F E] [IsGalois F E] [Algebra k F]
  [Algebra k E] [IsScalarTower k F E] in
@[simp]
private theorem crossed_fn_zero
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ)) :
    crossedTransportFn i g hi c 0 = 0 := by
  exact CProduc.sum_zero_index c

omit [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional F E] [IsGalois F E] [Algebra k F]
  [Algebra k E] [IsScalarTower k F E] in
private theorem crossed_fn_add
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (x y : CProduc c) :
    crossedTransportFn i g hi c (x + y) =
      crossedTransportFn i g hi c x +
        crossedTransportFn i g hi c y := by
  apply CProduc.sum_add_index'
  · intro sigma
    simp
  · intro sigma a b
    simp

omit [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional F E] [IsGalois F E] [Algebra k F]
  [Algebra k E] [IsScalarTower k F E] in
@[simp]
private theorem crossed_fn_one
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ)) :
    crossedTransportFn i g hi c 1 = 1 := by
  rw [CProduc.one_def, crossed_transport_fn,
    CProduc.one_def]
  simp

omit [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional F E] [IsGalois F E] [Algebra k F]
  [Algebra k E] [IsScalarTower k F E] in
private theorem crossed_fn_single
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (sigma tau : Gal(L/k)) (a b : L) :
    crossedTransportFn i g hi c
        (CProduc.single c sigma a * CProduc.single c tau b) =
      crossedTransportFn i g hi c (CProduc.single c sigma a) *
        crossedTransportFn i g hi c
          (CProduc.single c tau b) := by
  rw [CProduc.single_mul_single,
    crossed_transport_fn,
    crossed_transport_fn,
    crossed_transport_fn,
    CProduc.single_mul_single]
  rw [map_mul g sigma tau]
  apply congrArg (CProduc.single
    (transportedGaloisCocycle i g hi c) (g sigma * g tau))
  rw [map_mul, map_mul]
  change i a * i (sigma b) * i ((c (sigma, tau) : Lˣ) : L) =
    i a * g sigma (i b) *
      (((transportedGaloisCocycle i g hi c) (g sigma, g tau) : Eˣ) : E)
  rw [hi]
  have hc := congrArg Units.val
    (transported_galois_cocycle i g hi c sigma tau)
  change (((transportedGaloisCocycle i g hi c)
      (g sigma, g tau) : Eˣ) : E) = i ((c (sigma, tau) : Lˣ) : L) at hc
  rw [hc]

omit [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional F E]
  [IsGalois F E] [Algebra k F] [Algebra k E] [IsScalarTower k F E] in
private theorem crossed_fn_mul
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (x y : CProduc c) :
    crossedTransportFn i g hi c (x * y) =
      crossedTransportFn i g hi c x *
        crossedTransportFn i g hi c y := by
  induction x using CProduc.induction_on c with
  | zero => simp
  | hadd x₁ x₂ hx₁ hx₂ =>
      rw [add_mul, crossed_fn_add,
        crossed_fn_add, add_mul, hx₁, hx₂]
  | hsingle sigma a =>
      induction y using CProduc.induction_on c with
      | zero => simp
      | hadd y₁ y₂ hy₁ hy₂ =>
          rw [mul_add, crossed_fn_add,
            crossed_fn_add, mul_add, hy₁, hy₂]
      | hsingle tau b =>
          exact crossed_fn_single i g hi c sigma tau a b

/-- The ring homomorphism on crossed products induced by coefficient and
Galois-group transport. -/
noncomputable def crossedProductTransport
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ)) :
    CProduc c →+*
      CProduc (transportedGaloisCocycle i g hi c) where
  toFun := crossedTransportFn i g hi c
  map_zero' := crossed_fn_zero i g hi c
  map_one' := crossed_fn_one i g hi c
  map_add' := crossed_fn_add i g hi c
  map_mul' := crossed_fn_mul i g hi c

omit [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional F E]
  [IsGalois F E] [Algebra k F] [Algebra k E] [IsScalarTower k F E] in
@[simp]
theorem crossed_transport_single
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (sigma : Gal(L/k)) (a : L) :
    crossedProductTransport i g hi c (CProduc.single c sigma a) =
      CProduc.single (transportedGaloisCocycle i g hi c)
        (g sigma) (i a) :=
  crossed_transport_fn i g hi c sigma a

/-- Scalar extension of a crossed product, mapped to the crossed product of
the transported cocycle.  The compatibility hypothesis says that the
coefficient embedding `i` lies over the prescribed map `k → F`. -/
noncomputable def crossedBaseChange
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (hbase : ∀ a : k,
      i (algebraMap k L a) = algebraMap F E (algebraMap k F a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ)) :
    CProduc c ⊗[k] F →ₐ[F]
      CProduc (transportedGaloisCocycle i g hi c) := by
  let d := transportedGaloisCocycle i g hi c
  let B := CProduc d
  letI : Algebra k B := Algebra.restrictScalars k F B
  letI : IsScalarTower k F B := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rfl
  let transportK : CProduc c →ₐ[k] B :=
    { crossedProductTransport i g hi c with
      commutes' := by
        intro a
        rw [CProduc.algebraMap_apply]
        change crossedProductTransport i g hi c
            (CProduc.single c 1 (algebraMap k L a)) =
          CProduc.single d 1
            (algebraMap F E (algebraMap k F a))
        rw [crossed_transport_single]
        change CProduc.single d (g 1) (i (algebraMap k L a)) =
          CProduc.single d 1
            (algebraMap F E (algebraMap k F a))
        rw [map_one, hbase] }
  let baseF : F →ₐ[F] B := IsScalarTower.toAlgHom F F B
  let lifted : F ⊗[k] CProduc c →ₐ[F] B :=
    Algebra.TensorProduct.lift baseF transportK
      (fun a x => Algebra.commutes a (transportK x))
  exact lifted.comp
    (Algebra.TensorProduct.commRight k F (CProduc c)).symm.toAlgHom

omit [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional F E]
  [IsGalois F E] [Algebra k E] [IsScalarTower k F E] in
@[simp]
theorem crossed_change_tmul
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (hbase : ∀ a : k,
      i (algebraMap k L a) = algebraMap F E (algebraMap k F a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (x : CProduc c) (a : F) :
    crossedBaseChange i g hi hbase c (x ⊗ₜ[k] a) =
      crossedProductTransport i g hi c x *
        algebraMap F
          (CProduc (transportedGaloisCocycle i g hi c)) a := by
  let d := transportedGaloisCocycle i g hi c
  let B := CProduc d
  letI : Algebra k B := Algebra.restrictScalars k F B
  letI : IsScalarTower k F B := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    rfl
  simp only [CProduc.algebraMap_apply]
  exact Algebra.commutes a (crossedProductTransport i g hi c x)

/-- The `k`-linear map placing a coefficient in one crossed-product basis
coordinate. -/
private def crossedSingleLinear
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (sigma : Gal(L/k)) : L →ₗ[k] CProduc c where
  toFun a := CProduc.single c sigma a
  map_add' a b := CProduc.single_add c sigma a b
  map_smul' r a := by
    simp only [RingHom.id_apply]
    rw [Algebra.smul_def]
    change CProduc.single c sigma (algebraMap k L r * a) =
      (algebraMap k L r) • CProduc.single c sigma a
    rw [CProduc.smul_single]

omit [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional F E]
  [IsGalois F E] [Algebra k E] [IsScalarTower k F E] in
/-- If the transported coefficient field is generated by scalar extension
of `L`, then the crossed-product scalar-extension map is surjective. -/
theorem crossed_change_surjective
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (hbase : ∀ a : k,
      i (algebraMap k L a) = algebraMap F E (algebraMap k F a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (coeffEquiv : L ⊗[k] F ≃ₐ[F] E)
    (hcoeff : ∀ (a : L) (b : F),
      coeffEquiv (a ⊗ₜ[k] b) = i a * algebraMap F E b) :
    Function.Surjective
      (crossedBaseChange i g hi hbase c) := by
  let d := transportedGaloisCocycle i g hi c
  let f := crossedBaseChange i g hi hbase c
  intro y
  induction y using CProduc.induction_on d with
  | zero =>
      exact ⟨0, map_zero f⟩
  | hadd x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add f x' y'⟩
  | hsingle sigma e =>
      let tau : Gal(L/k) := g.symm sigma
      let t : L ⊗[k] F := coeffEquiv.symm e
      let singleMap : L →ₗ[k] CProduc c :=
        crossedSingleLinear c tau
      let tensorMap : L ⊗[k] F →ₗ[k] CProduc c ⊗[k] F :=
        TensorProduct.map singleMap (LinearMap.id (R := k) (M := F))
      have hmap : ∀ z : L ⊗[k] F,
          f (tensorMap z) =
            CProduc.single d (g tau) (coeffEquiv z) := by
        intro z
        induction z with
        | zero => simp [tensorMap]
        | add z w hz hw => simp [tensorMap, hz, hw]
        | tmul a b =>
            rw [show tensorMap (a ⊗ₜ[k] b) =
                CProduc.single c tau a ⊗ₜ[k] b by
              simp [tensorMap, singleMap,
                crossedSingleLinear]]
            rw [crossed_change_tmul,
              crossed_transport_single,
              CProduc.algebraMap_apply,
              CProduc.single_mul_single]
            simp only [NMCocycl₂.apply_one_snd]
            change CProduc.single d (g tau)
                (i a * (g tau) (algebraMap F E b) * 1) =
              CProduc.single d (g tau) (coeffEquiv (a ⊗ₜ[k] b))
            rw [(g tau).commutes b, hcoeff]
            simp
      refine ⟨tensorMap t, ?_⟩
      rw [hmap, g.apply_symm_apply]
      change CProduc.single d sigma (coeffEquiv (coeffEquiv.symm e)) = _
      rw [coeffEquiv.apply_symm_apply]

/-- Base change of a Galois crossed product is the crossed product obtained
by transporting the coefficient field, Galois group, and factor set. -/
noncomputable def crossedChangeAlg
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (hbase : ∀ a : k,
      i (algebraMap k L a) = algebraMap F E (algebraMap k F a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (coeffEquiv : L ⊗[k] F ≃ₐ[F] E)
    (hcoeff : ∀ (a : L) (b : F),
      coeffEquiv (a ⊗ₜ[k] b) = i a * algebraMap F E b) :
    CProduc c ⊗[k] F ≃ₐ[F]
      CProduc (transportedGaloisCocycle i g hi c) := by
  let d := transportedGaloisCocycle i g hi c
  let f := crossedBaseChange i g hi hbase c
  letI : Module.Finite F (F ⊗[k] CProduc c) :=
    Module.Finite.base_change k F (CProduc c)
  letI : Module.Finite F (CProduc c ⊗[k] F) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight k F (CProduc c)).toLinearEquiv
  have hcoeffdim : Module.finrank k L = Module.finrank F E := by
    calc
      Module.finrank k L = Module.finrank F (F ⊗[k] L) :=
        (Module.finrank_baseChange (R := F) (S := k) (M' := L)).symm
      _ = Module.finrank F (L ⊗[k] F) :=
        (Algebra.TensorProduct.commRight k F L).toLinearEquiv.finrank_eq
      _ = Module.finrank F E := coeffEquiv.toLinearEquiv.finrank_eq
  have hdim :
      Module.finrank F (CProduc c ⊗[k] F) =
        Module.finrank F (CProduc d) := by
    calc
      Module.finrank F (CProduc c ⊗[k] F) =
          Module.finrank F (F ⊗[k] CProduc c) :=
        (Algebra.TensorProduct.commRight k F
          (CProduc c)).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank k (CProduc c) :=
        Module.finrank_baseChange (R := F) (S := k)
          (M' := CProduc c)
      _ = (Module.finrank k L) ^ 2 :=
        CProduc.finrank_over_base k L c
      _ = (Module.finrank F E) ^ 2 := by rw [hcoeffdim]
      _ = Module.finrank F (CProduc d) :=
        (CProduc.finrank_over_base F E d).symm
  have hsurj : Function.Surjective f :=
    crossed_change_surjective
      i g hi hbase c coeffEquiv hcoeff
  have hinj : Function.Injective f.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hdim (f := f.toLinearMap)).2 hsurj
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

end TransportedCocycle

section SameUniverse

variable {k L F E : Type u}
  [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  [Field F] [Algebra k F]
  [Field E] [Algebra F E] [Algebra k E] [IsScalarTower k F E]
  [FiniteDimensional F E] [IsGalois F E]

omit [Algebra k E] [IsScalarTower k F E] in
/-- Brauer localization of a crossed-product class is represented by the
crossed product of the transported local cocycle. -/
theorem brauer_base_crossed
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (hbase : ∀ a : k,
      i (algebraMap k L a) = algebraMap F E (algebraMap k F a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (coeffEquiv : L ⊗[k] F ≃ₐ[F] E)
    (hcoeff : ∀ (a : L) (b : F),
      coeffEquiv (a ⊗ₜ[k] b) = i a * algebraMap F E b) :
    BGroups.brauerBaseChange k F
        (CProduc.brauerClass k L c) =
      CProduc.brauerClass F E
        (transportedGaloisCocycle i g hi c) := by
  rw [CProduc.brauerClass,
    BGroups.brauer_change_class]
  apply (BGroups.brauer_class _ _ _).2
  exact BGroups.brauer_equivalent_alg F _ _
    (crossedChangeAlg
      i g hi hbase c coeffEquiv hcoeff)

end SameUniverse

section ZeroToUniverse

variable {k L : Type} {F E : Type u}
  [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  [Field F] [Algebra k F]
  [Field E] [Algebra F E] [Algebra k E] [IsScalarTower k F E]
  [FiniteDimensional F E] [IsGalois F E]

omit [Algebra k E] [IsScalarTower k F E] in
/-- Type-0-to-ambient scalar extension of a crossed-product class is
represented by the crossed product of the transported cocycle. -/
theorem brauer_universe_crossed
    (i : L →+* E) (g : Gal(L/k) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(L/k), ∀ a : L,
      i (sigma a) = g sigma (i a))
    (hbase : ∀ a : k,
      i (algebraMap k L a) = algebraMap F E (algebraMap k F a))
    (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (coeffEquiv : L ⊗[k] F ≃ₐ[F] E)
    (hcoeff : ∀ (a : L) (b : F),
      coeffEquiv (a ⊗ₜ[k] b) = i a * algebraMap F E b) :
    BGroups.brauerChangeUniverse k F
        (CProduc.brauerClass k L c) =
      CProduc.brauerClass F E
        (transportedGaloisCocycle i g hi c) := by
  rw [CProduc.brauerClass,
    BGroups.brauer_base_universe]
  apply (BGroups.brauer_class _ _ _).2
  exact BGroups.brauer_equivalent_alg F _ _
    (crossedChangeAlg
      i g hi hbase c coeffEquiv hcoeff)

end ZeroToUniverse

end

end Submission.CField.CProduca
