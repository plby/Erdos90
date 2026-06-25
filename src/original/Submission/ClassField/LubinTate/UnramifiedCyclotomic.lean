import Submission.ClassField.NormCorrespondence.UnramifiedFrobenius
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Class Field Theory, Chapter I, Section 3: the unramified cyclotomic residue extension

Milne begins the construction of the maximal unramified extension by adjoining
roots of unity whose orders are prime to the residue characteristic.  Building
the corresponding extension of local fields, and then taking its infinite
union, requires local and infinite Galois infrastructure that is not yet
available in this project.  This file proves the finite residue-field argument
used in that construction.

In particular, a primitive `m`th root generates a residue extension whose
degree is the least positive `f` for which `q ^ f = 1 (mod m)`, where `q` is
the cardinality of the base residue field.
-/

namespace Submission.CField.LTate

open Module Polynomial

noncomputable section

/-- If `m` is prime to the characteristic, then `X ^ m - 1` has no repeated
roots.  This is the residue-field separability input in the opening paragraph
of Section 3. -/
theorem x_separable_dvd
    (k : Type*) [Field k] (p m : ℕ) [CharP k p] (hm : ¬p ∣ m) :
    (X ^ m - 1 : k[X]).Separable := by
  simpa using
    (Polynomial.separable_X_pow_sub_C' p m (1 : k) hm one_ne_zero)

/-- A finite field contains a primitive `m`th root of unity exactly when `m`
divides the order of its multiplicative group. -/
theorem primitive_dvd_sub
    (k : Type*) [Field k] [Fintype k] (m : ℕ) [NeZero m] :
    (∃ zeta : k, IsPrimitiveRoot zeta m) ↔ m ∣ Fintype.card k - 1 := by
  classical
  constructor
  · rintro ⟨zeta, hzeta⟩
    let u : kˣ := (hzeta.isUnit (NeZero.ne m)).unit
    have hu : IsPrimitiveRoot u m := hzeta.isUnit_unit (NeZero.ne m)
    rw [← Fintype.card_units]
    simpa only [Nat.card_eq_fintype_card, hu.eq_orderOf] using
      (orderOf_dvd_natCard u)
  · intro hm
    obtain ⟨u : kˣ, hu⟩ :=
      IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
    have hcard : orderOf u = Fintype.card k - 1 := by
      calc
        orderOf u = Nat.card kˣ := hu
        _ = Fintype.card kˣ := Nat.card_eq_fintype_card
        _ = Fintype.card k - 1 := Fintype.card_units k
    have hm' : m ∣ orderOf u := hcard.symm ▸ hm
    have hu0 : orderOf u ≠ 0 := (orderOf_pos u).ne'
    let zeta : kˣ := u ^ (orderOf u / m)
    have hzeta : IsPrimitiveRoot zeta m :=
      IsPrimitiveRoot.iff_orderOf.mpr
        (orderOf_pow_orderOf_div hu0 hm')
    exact ⟨(zeta : k), IsPrimitiveRoot.coe_units_iff.mpr hzeta⟩

/-- Over a finite field, a separable roots-of-unity polynomial splits exactly
when its order divides the size of the multiplicative group. -/
theorem x_splits_card
    (k : Type*) [Field k] [Fintype k] (m : ℕ) [NeZero m]
    (hm : (m : k) ≠ 0) :
    (X ^ m - 1 : k[X]).Splits ↔ m ∣ Fintype.card k - 1 := by
  classical
  constructor
  · intro hsplit
    apply (primitive_dvd_sub k m).mp
    rw [← card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot]
    have hnodup : (nthRoots m (1 : k)).Nodup := by
      simpa only [nthRoots] using
        Polynomial.nodup_roots
          ((Polynomial.X_pow_sub_one_separable_iff (F := k)).mpr hm)
    let rootsEquiv : {x // x ∈ nthRoots m (1 : k)} ≃
        {x // x ∈ (nthRoots m (1 : k)).toFinset} :=
      { toFun := fun x => ⟨x, Multiset.mem_toFinset.mpr x.2⟩
        invFun := fun x => ⟨x, Multiset.mem_toFinset.mp x.2⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => Subtype.ext rfl }
    calc
      Fintype.card (rootsOfUnity m k) =
          Fintype.card {x // x ∈ nthRoots m (1 : k)} :=
        Fintype.card_congr (rootsOfUnityEquivNthRoots k m)
      _ = Fintype.card {x // x ∈ (nthRoots m (1 : k)).toFinset} :=
        Fintype.card_congr rootsEquiv
      _ = (nthRoots m (1 : k)).toFinset.card :=
        Fintype.card_coe _
      _ = Multiset.card (nthRoots m (1 : k)) :=
        Multiset.toFinset_card_of_nodup hnodup
      _ = m := by
        have hsplit' : (X ^ m - C (1 : k)).Splits := by
          simpa using hsplit
        rw [nthRoots, ← hsplit'.natDegree_eq_card_roots]
        exact natDegree_X_pow_sub_C
  · intro hdiv
    obtain ⟨zeta, hzeta⟩ :=
      (primitive_dvd_sub k m).mpr hdiv
    simpa using Polynomial.X_pow_sub_one_splits hzeta

variable (k l : Type*) [Field k] [Field l] [Fintype k] [Finite l]
  [Algebra k l] [Algebra.IsAlgebraic k l]

omit [Finite l] in
/-- The `f`th residue Frobenius sends an element to its `q ^ f`th power. -/
theorem residue_frobenius (f : ℕ) (x : l) :
    (NCorr.residueFrobenius k l ^ f) x =
      x ^ (Fintype.card k ^ f) := by
  rw [AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

omit [Finite l] in
/-- On a primitive `m`th root, the `f`th residue Frobenius is trivial exactly
when `q ^ f` is congruent to one modulo `m`. -/
theorem residue_primitive_fixed
    {m : ℕ} [NeZero m] (zeta : l) (hzeta : IsPrimitiveRoot zeta m) (f : ℕ) :
    (NCorr.residueFrobenius k l ^ f) zeta = zeta ↔
      Fintype.card k ^ f ≡ 1 [MOD m] := by
  rw [residue_frobenius]
  simpa only [pow_one, ← hzeta.eq_orderOf] using
    ((hzeta.isOfFinOrder (NeZero.ne m)).pow_eq_pow_iff_modEq
      (n := Fintype.card k ^ f) (m := 1))

/-- If a primitive `m`th root generates the residue extension, then its degree
divides `f` exactly when `q ^ f` is one modulo `m`.  This is a slightly stronger
form of the minimal-degree assertion in the opening paragraph of Section 3. -/
theorem dvd_adjoin_top
    {m : ℕ} [NeZero m] (zeta : l) (hzeta : IsPrimitiveRoot zeta m)
    (hgen : Algebra.adjoin k ({zeta} : Set l) = ⊤) (f : ℕ) :
    finrank k l ∣ f ↔ Fintype.card k ^ f ≡ 1 [MOD m] := by
  rw [← NCorr.order_residue_frobenius k l,
    orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro hpow
    have hfix := DFunLike.congr_fun hpow zeta
    simpa using
      (residue_primitive_fixed k l zeta hzeta f).mp hfix
  · intro hcong
    have hfix : (NCorr.residueFrobenius k l ^ f) zeta = zeta :=
      (residue_primitive_fixed k l zeta hzeta f).mpr hcong
    apply AlgEquiv.coe_algHom_injective
    apply AlgHom.ext_of_adjoin_eq_top hgen
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    simpa using hfix

/-- The congruence in the preceding theorem is equivalently Milne's
divisibility condition `m ∣ q ^ f - 1`. -/
theorem finrank_adjoin_top
    {m : ℕ} [NeZero m] (zeta : l) (hzeta : IsPrimitiveRoot zeta m)
    (hgen : Algebra.adjoin k ({zeta} : Set l) = ⊤) (f : ℕ) :
    finrank k l ∣ f ↔ m ∣ Fintype.card k ^ f - 1 := by
  have hone : 1 ≤ Fintype.card k ^ f :=
    Nat.one_le_pow f (Fintype.card k) Fintype.card_pos
  rw [dvd_adjoin_top k l zeta hzeta hgen]
  constructor
  · intro h
    exact (Nat.modEq_iff_dvd' hone).mp h.symm
  · intro h
    exact ((Nat.modEq_iff_dvd' hone).mpr h).symm

/-- Consequently, the degree of the residue extension generated by a
primitive `m`th root is the least positive `f` such that `q ^ f = 1 (mod m)`.
-/
theorem finrank_minimal_degree
    {m : ℕ} [NeZero m] (zeta : l) (hzeta : IsPrimitiveRoot zeta m)
    (hgen : Algebra.adjoin k ({zeta} : Set l) = ⊤) :
    Fintype.card k ^ finrank k l ≡ 1 [MOD m] ∧
      ∀ f : ℕ, 0 < f → Fintype.card k ^ f ≡ 1 [MOD m] → finrank k l ≤ f := by
  have hcriterion :=
    dvd_adjoin_top k l zeta hzeta hgen
  constructor
  · exact (hcriterion (finrank k l)).mp dvd_rfl
  · intro f hf hcong
    exact Nat.le_of_dvd hf ((hcriterion f).mpr hcong)

/-- For a cyclotomic residue extension, the residue degree itself is the least
positive integer satisfying Milne's divisibility condition. -/
theorem cyclotomic_residue_minimal
    {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} k l] :
    m ∣ Fintype.card k ^ finrank k l - 1 ∧
      ∀ f : ℕ, 0 < f → m ∣ Fintype.card k ^ f - 1 → finrank k l ≤ f := by
  obtain ⟨zeta, hzeta⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot k l
      (Set.mem_singleton m) (NeZero.ne m)
  have hgen : Algebra.adjoin k ({zeta} : Set l) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hzeta
  have hcriterion :=
    finrank_adjoin_top
      k l zeta hzeta hgen
  constructor
  · exact (hcriterion (finrank k l)).mp dvd_rfl
  · intro f hf hdiv
    exact Nat.le_of_dvd hf ((hcriterion f).mpr hdiv)

omit [Algebra.IsAlgebraic k l] in
/-- The corresponding residue field has `q ^ f` elements, with `f` its
degree over the base residue field. -/
theorem card_pow_finrank :
    Nat.card l = Fintype.card k ^ finrank k l := by
  simpa only [Nat.card_eq_fintype_card] using
    (Module.natCard_eq_pow_finrank (K := k) (V := l))

end

end Submission.CField.LTate
