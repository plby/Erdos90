import Submission.NumberTheory.Galois.SymmetricPolynomialConstruction
import Submission.NumberTheory.Galois.DedekindCyclePartition
import Submission.NumberTheory.Galois.OddPowerSwap
import Submission.NumberTheory.Galois.PermutationGroupCriterion
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-!
# The Galois group in Milne's Example 8.27

The modular factorizations are converted, via arithmetic Frobenius, into
actual permutations in `Polynomial.Gal.galActionHom`.
-/

namespace Submission.NumberTheory.Milne

open Equiv Finset Polynomial
open NumberField
open scoped NumberField

noncomputable section

private abbrev primeIdeal (q : ℕ) : Ideal ℤ :=
  Ideal.span ({(q : ℤ)} : Set ℤ)

private abbrev symmetricGaloisQ (f₁ f₂ f₃ : ℤ[X]) : ℚ[X] :=
  (symmetricGroupConstruction f₁ f₂ f₃).map (algebraMap ℤ ℚ)

private abbrev SymmetricSplittingField (f₁ f₂ f₃ : ℤ[X]) :=
  (symmetricGaloisQ f₁ f₂ f₃).SplittingField

private theorem swap_perm_congr {alpha beta : Type*}
    [DecidableEq alpha] [DecidableEq beta]
    (e : alpha ≃ beta) {sigma : Equiv.Perm alpha}
    (h : sigma.IsSwap) : (e.permCongr sigma).IsSwap := by
  obtain ⟨a, b, hab, rfl⟩ := h
  refine ⟨e a, e b, e.injective.ne hab, ?_⟩
  ext x
  by_cases hxa : e.symm x = a
  · subst a
    simp
  by_cases hxb : e.symm x = b
  · subst b
    simp
  have hxea : x ≠ e a := fun h => hxa (e.injective (by simpa using h))
  have hxeb : x ≠ e b := fun h => hxb (e.injective (by simpa using h))
  simp [Equiv.permCongr_apply, Equiv.swap_apply_def, hxa, hxb, hxea, hxeb]

private theorem exists_cyclePartition
    {F : Type*} [Field F] [Algebra ℚ F] [NumberField F]
    [DecidableEq (𝓞 F)]
    {fZ : ℤ[X]} {f : ℚ[X]}
    [MulSemiringAction f.Gal F]
    [IsGaloisGroup f.Gal ℤ (𝓞 F)]
    (hfmonic : fZ.Monic)
    (hfZsplits : (fZ.map (algebraMap ℤ (𝓞 F))).Splits)
    (q : ℕ) (hq : Nat.Prime q)
    {j : Type*} [Fintype j]
    (g : j → (ℤ ⧸ primeIdeal q)[X])
    (hfac : fZ.map (Ideal.Quotient.mk (primeIdeal q)) = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i)) (hmonic : ∀ i, (g i).Monic)
    (hinj : Function.Injective g)
    (hsep : (fZ.map (Ideal.Quotient.mk (primeIdeal q))).Separable) :
    ∃ sigma : f.Gal, ∃ s : j → Finset (fZ.rootSet (𝓞 F)),
      (∀ i, (arithmeticRootPerm fZ sigma).IsCycleOn
        (s i : Set (fZ.rootSet (𝓞 F)))) ∧
      (∀ i, (s i).card = (g i).natDegree) ∧
      (Finset.univ.biUnion s = Finset.univ) := by
  classical
  let p := primeIdeal q
  letI : Fact q.Prime := ⟨hq⟩
  letI : p.IsMaximal := Int.ideal_span_isMaximal_of_prime q
  letI : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : Field (ℤ ⧸ p) := Ideal.Quotient.field p
  letI : Fintype (ℤ ⧸ p) := Fintype.ofFinite _
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) p
  letI : Q.IsMaximal := hQmax
  letI : Q.IsPrime := Ideal.IsMaximal.isPrime hQmax
  letI : Q.LiesOver p := hQover
  letI : Field (𝓞 F ⧸ Q) := Ideal.Quotient.field Q
  letI : Fintype (𝓞 F ⧸ Q) := Fintype.ofFinite _
  obtain ⟨sigma, s, -, hcycle, hcard, hcover⟩ :=
    arithmetic_cycle_partition
      (G := f.Gal) (p := p) (Q := Q) fZ hfmonic hfZsplits hsep
      g hfac hirr hmonic hinj
  exact ⟨sigma, s, hcycle, hcard, hcover⟩

section CanonicalSplittingField

variable (f₁ f₂ f₃ : ℤ[X])

local notation "F₈₂₇" => SymmetricSplittingField f₁ f₂ f₃

local instance : Fact (((symmetricGaloisQ f₁ f₂ f₃).map
    (algebraMap ℚ F₈₂₇)).Splits) :=
  ⟨Polynomial.SplittingField.splits
    (symmetricGaloisQ f₁ f₂ f₃)⟩

private theorem root_set_card
    (n : ℕ)
    (hfmonic : (symmetricGroupConstruction f₁ f₂ f₃).Monic)
    (hfdegree : (symmetricGroupConstruction f₁ f₂ f₃).natDegree = n)
    (hirr₂ : Irreducible ((symmetricGroupConstruction f₁ f₂ f₃).map
      (Ideal.Quotient.mk (primeIdeal 2)))) :
    Fintype.card
      ((symmetricGaloisQ f₁ f₂ f₃).rootSet F₈₂₇) = n := by
  let fZ := symmetricGroupConstruction f₁ f₂ f₃
  let f := symmetricGaloisQ f₁ f₂ f₃
  have hirrZ : Irreducible fZ :=
    Polynomial.Monic.irreducible_of_irreducible_map
      (Ideal.Quotient.mk (primeIdeal 2)) fZ hfmonic hirr₂
  have hirrQ : Irreducible f :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      hfmonic.isPrimitive).mp hirrZ
  calc
    Fintype.card (f.rootSet F₈₂₇) = f.natDegree :=
      card_rootSet_eq_natDegree hirrQ.separable
        (Polynomial.SplittingField.splits f)
    _ = fZ.natDegree := by
      change (fZ.map (algebraMap ℤ ℚ)).natDegree = fZ.natDegree
      exact Polynomial.natDegree_map_eq_of_injective
        (IsFractionRing.injective ℤ ℚ) fZ
    _ = n := hfdegree

set_option maxHeartbeats 4000000 in
-- The three simultaneous residue-field cycle partitions create a large term.
set_option maxRecDepth 100000 in
-- The three simultaneous residue-field cycle partitions create a deep
-- typeclass and coercion elaboration tree.
/-- Milne's Example 8.27: the specified factorizations modulo `2`, `3`, and
`5` force the image of the polynomial Galois action to be the full symmetric
group on the roots. -/
theorem root_action_top
    (n : ℕ) (hn : 3 ≤ n)
    (hfmonic : (symmetricGroupConstruction f₁ f₂ f₃).Monic)
    (hfdegree : (symmetricGroupConstruction f₁ f₂ f₃).natDegree = n)
    (hirr₂ : Irreducible ((symmetricGroupConstruction f₁ f₂ f₃).map
      (Ideal.Quotient.mk (primeIdeal 2))))
    (g₃ : Fin 2 → (ℤ ⧸ primeIdeal 3)[X])
    (hfac₃ : (symmetricGroupConstruction f₁ f₂ f₃).map
      (Ideal.Quotient.mk (primeIdeal 3)) = ∏ i, g₃ i)
    (hirr₃ : ∀ i, Irreducible (g₃ i))
    (hmonic₃ : ∀ i, (g₃ i).Monic)
    (hinj₃ : Function.Injective g₃)
    (hdeg₃zero : (g₃ 0).natDegree = 1)
    (hdeg₃one : (g₃ 1).natDegree = n - 1)
    (hsep₃ : ((symmetricGroupConstruction f₁ f₂ f₃).map
      (Ideal.Quotient.mk (primeIdeal 3))).Separable)
    {iota : Type*} [Fintype iota]
    (g₅ : Option iota → (ℤ ⧸ primeIdeal 5)[X])
    (hfac₅ : (symmetricGroupConstruction f₁ f₂ f₃).map
      (Ideal.Quotient.mk (primeIdeal 5)) = ∏ i, g₅ i)
    (hirr₅ : ∀ i, Irreducible (g₅ i))
    (hmonic₅ : ∀ i, (g₅ i).Monic)
    (hinj₅ : Function.Injective g₅)
    (hdeg₅two : (g₅ none).natDegree = 2)
    (hdeg₅odd : ∀ i, Odd (g₅ (some i)).natDegree)
    (hsep₅ : ((symmetricGroupConstruction f₁ f₂ f₃).map
      (Ideal.Quotient.mk (primeIdeal 5))).Separable) :
    (Polynomial.Gal.galActionHom
      (symmetricGaloisQ f₁ f₂ f₃) F₈₂₇).range = ⊤ := by
  classical
  let fZ := symmetricGroupConstruction f₁ f₂ f₃
  let f := symmetricGaloisQ f₁ f₂ f₃
  letI : NumberField F₈₂₇ := NumberField.of_module_finite ℚ F₈₂₇
  letI : IsSplittingField ℚ F₈₂₇ f :=
    Polynomial.IsSplittingField.splittingField f
  letI : Fact ((f.map (algebraMap ℚ F₈₂₇)).Splits) :=
    ⟨Polynomial.SplittingField.splits f⟩
  letI : DecidableEq F₈₂₇ := Classical.decEq _
  have hirrZ : Irreducible fZ :=
    Polynomial.Monic.irreducible_of_irreducible_map
      (Ideal.Quotient.mk (primeIdeal 2)) fZ hfmonic hirr₂
  have hirrQ : Irreducible f := by
    exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      hfmonic.isPrimitive).mp hirrZ
  letI : IsGalois ℚ F₈₂₇ :=
    IsGalois.of_separable_splitting_field hirrQ.separable
  letI : IsGaloisGroup f.Gal ℚ F₈₂₇ :=
    IsGaloisGroup.of_isGalois ℚ F₈₂₇
  have hfZsplits : (fZ.map (algebraMap ℤ (𝓞 F₈₂₇))).Splits := by
    apply Polynomial.Splits.of_splits_map_of_injective
        (i := algebraMap (𝓞 F₈₂₇) F₈₂₇)
        (FaithfulSMul.algebraMap_injective _ _)
    · convert Polynomial.IsSplittingField.splits F₈₂₇ f using 1
      ext k
      simp [fZ, f, symmetricGaloisQ]
    · intro a ha
      have hpoly : (fZ.map (algebraMap ℤ (𝓞 F₈₂₇))).map
          (algebraMap (𝓞 F₈₂₇) F₈₂₇) =
            fZ.map (algebraMap ℤ F₈₂₇) := by
        ext k
        simp
      have ha' : a ∈ fZ.aroots F₈₂₇ := by
        rw [Polynomial.aroots_def]
        rwa [hpoly] at ha
      exact ⟨⟨a, roots_mem_integralClosure hfmonic ha'⟩, rfl⟩
  have hpolyInt : (fZ.map (algebraMap ℤ (𝓞 F₈₂₇))).map
      (algebraMap (𝓞 F₈₂₇) F₈₂₇) = f.map (algebraMap ℚ F₈₂₇) := by
    ext k
    simp [fZ, f, symmetricGaloisQ]
  have hpolyRat : f.map (algebraMap ℚ F₈₂₇) =
      fZ.map (algebraMap ℤ F₈₂₇) := by
    ext k
    simp [fZ, f, symmetricGaloisQ]
  let eInt : fZ.rootSet (𝓞 F₈₂₇) ≃ f.rootSet F₈₂₇ :=
    { toFun := fun x => ⟨(x : 𝓞 F₈₂₇), by
        rw [(hfmonic.map (algebraMap ℤ ℚ)).mem_rootSet]
        have hx := hfmonic.mem_rootSet.mp x.2
        have hx' := congrArg (algebraMap (𝓞 F₈₂₇) F₈₂₇) hx
        rw [aeval_def, eval₂_eq_eval_map, ← hpolyInt, eval_map,
          eval₂_hom]
        simpa [aeval_def, eval₂_eq_eval_map] using hx'⟩
      invFun := fun y => by
        have hyroot : (y : F₈₂₇) ∈ fZ.aroots F₈₂₇ := by
          rw [Polynomial.aroots_def, mem_roots (hfmonic.map _).ne_zero]
          have hy := (hfmonic.map (algebraMap ℤ ℚ)).mem_rootSet.mp y.2
          rw [aeval_def, eval₂_eq_eval_map, hpolyRat] at hy
          simpa [IsRoot] using hy
        let z : 𝓞 F₈₂₇ := ⟨y, roots_mem_integralClosure hfmonic hyroot⟩
        exact ⟨z, by
          rw [hfmonic.mem_rootSet]
          apply NumberField.RingOfIntegers.coe_injective
          have hy := (hfmonic.map (algebraMap ℤ ℚ)).mem_rootSet.mp y.2
          rw [aeval_def, eval₂_eq_eval_map] at hy ⊢
          rw [map_zero, ← eval₂_hom, ← eval_map, hpolyInt]
          simpa [z] using hy⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e := Polynomial.Gal.rootsEquivRoots f F₈₂₇
  let eGal := eInt.trans e
  let action : f.Gal →* Equiv.Perm (f.rootSet F₈₂₇) :=
    Polynomial.Gal.galActionHom f F₈₂₇
  have hintertwine (sigma : f.Gal) (x : fZ.rootSet (𝓞 F₈₂₇)) :
      eGal (arithmeticRootPerm fZ sigma x) = action sigma (eGal x) := by
    have hraw : eInt (sigma • x) =
        (@MulAction.toPermHom _ _ _
          (Polynomial.Gal.galActionAux (p := f)) sigma) (eInt x) := by
      apply Subtype.ext
      exact integralClosure.coe_smul sigma x.1
    change e (eInt (sigma • x)) =
      e ((@MulAction.toPermHom _ _ _
        (Polynomial.Gal.galActionAux (p := f)) sigma)
          (e.symm (e (eInt x))))
    rw [e.symm_apply_apply, hraw]
  have hrootcard : Fintype.card (f.rootSet F₈₂₇) = n := by
    calc
      Fintype.card (f.rootSet F₈₂₇) = f.natDegree :=
        card_rootSet_eq_natDegree hirrQ.separable
          (Polynomial.IsSplittingField.splits F₈₂₇ f)
      _ = n := by
        change (fZ.map (algebraMap ℤ ℚ)).natDegree = n
        rw [Polynomial.natDegree_map_eq_of_injective
          (IsFractionRing.injective ℤ ℚ)]
        exact hfdegree
  let H := MonoidHom.range action
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : (primeIdeal 2).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  letI : (primeIdeal 2).IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : Field (ℤ ⧸ primeIdeal 2) :=
    Ideal.Quotient.field (primeIdeal 2)
  have hsep₂ : (fZ.map
      (Ideal.Quotient.mk (primeIdeal 2))).Separable :=
    by
      dsimp only [fZ]
      exact PerfectField.separable_of_irreducible
        (f := (symmetricGroupConstruction f₁ f₂ f₃).map
          (Ideal.Quotient.mk (primeIdeal 2))) hirr₂
  obtain ⟨sigma₂, s₂, hcycle₂, hcard₂, hcover₂⟩ :=
    exists_cyclePartition hfmonic hfZsplits 2 Nat.prime_two
      (f := f)
      (j := Unit) (fun _ : Unit =>
      fZ.map (Ideal.Quotient.mk (primeIdeal 2)))
      (by rw [Fintype.prod_unique])
      (fun _ => hirr₂) (fun _ => hfmonic.map _) (fun _ _ _ => rfl)
      hsep₂
  have hs₂univ : s₂ () = Finset.univ := by simpa using hcover₂
  have hfullOn : (action sigma₂).IsCycleOn
      (Set.univ : Set (f.rootSet F₈₂₇)) := by
    have ht := Equiv.Perm.IsCycleOn.transp_finse eGal (s₂ ())
      (hcycle₂ ()) (hintertwine sigma₂)
    rw [hs₂univ] at ht
    simpa using ht
  obtain ⟨hfullCycle, hfullSupport⟩ :=
    cycle_support_univ (action sigma₂)
      (by rw [hrootcard]; omega) hfullOn
  obtain ⟨sigma₃, s₃, hcycle₃, hcard₃, hcover₃⟩ :=
    exists_cyclePartition hfmonic hfZsplits 3 Nat.prime_three
      (f := f) g₃ hfac₃ hirr₃ hmonic₃ hinj₃ hsep₃
  let t₃ : Fin 2 → Finset (f.rootSet F₈₂₇) := fun i =>
    (s₃ i).map eGal.toEmbedding
  have htcycle₃ (i : Fin 2) :
      (action sigma₃).IsCycleOn (t₃ i : Set _) :=
    Equiv.Perm.IsCycleOn.transp_finse eGal (s₃ i)
      (hcycle₃ i) (hintertwine sigma₃)
  have htcard₃ (i : Fin 2) : (t₃ i).card = (g₃ i).natDegree := by
    simp [t₃, hcard₃]
  have htcover₃ : Finset.univ.biUnion t₃ = Finset.univ := by
    ext y
    simpa [t₃] using Finset.ext_iff.mp hcover₃ (eGal.symm y)
  have htNontrivial : (t₃ 1 : Set (f.rootSet F₈₂₇)).Nontrivial := by
    apply Finset.Nontrivial.coe
    rw [← Finset.one_lt_card_iff_nontrivial, htcard₃, hdeg₃one]
    omega
  have hlongSupport : (action sigma₃).support = t₃ 1 := by
    ext y
    rw [Equiv.Perm.mem_support]
    constructor
    · intro hy
      have hycover : y ∈ t₃ 0 ∨ y ∈ t₃ 1 := by
        have := Finset.ext_iff.mp htcover₃ y
        simpa using this
      rcases hycover with hyzero | hyone
      · exact False.elim (hy ((htcycle₃ 0).pow_apply_eq hyzero |>.2 (by
          rw [htcard₃, hdeg₃zero])))
      · exact hyone
    · intro hy
      exact (htcycle₃ 1).apply_ne htNontrivial hy
  have hlongCycle : (action sigma₃).IsCycle := by
    rw [Equiv.Perm.isCycle_iff_exists_isCycleOn]
    refine ⟨(t₃ 1 : Set _), htNontrivial, htcycle₃ 1, ?_⟩
    intro x hx
    have hx' : x ∈ (action sigma₃).support := by
      simpa [Equiv.Perm.mem_support, Function.IsFixedPt] using hx
    simpa [hlongSupport] using hx'
  have hlongCard : (action sigma₃).support.card + 1 =
      Fintype.card (f.rootSet F₈₂₇) := by
    rw [hlongSupport, htcard₃, hdeg₃one, hrootcard]
    omega
  obtain ⟨sigma₅, s₅, hcycle₅, hcard₅, hcover₅⟩ :=
    exists_cyclePartition hfmonic hfZsplits 5 Nat.prime_five
      (f := f) g₅ hfac₅ hirr₅ hmonic₅ hinj₅ hsep₅
  have hswapInt :
      (arithmeticRootPerm (S := 𝓞 F₈₂₇) fZ sigma₅ ^
        (Finset.univ.prod fun i : iota => (s₅ (some i)).card)).IsSwap := by
    apply Equiv.Perm.swappo_prodc_cycle
      (sTwo := s₅ none) (sOdd := fun i => s₅ (some i))
    · simpa [hcard₅] using hdeg₅two
    · exact hcycle₅ none
    · intro i _
      rw [hcard₅]
      exact hdeg₅odd i
    · intro i _
      exact hcycle₅ (some i)
    · intro y
      have hy := Finset.ext_iff.mp hcover₅ y
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true] at hy
      obtain ⟨j, hj⟩ := hy
      cases j with
      | none => exact Or.inl hj
      | some i => exact Or.inr ⟨i, Finset.mem_univ i, hj⟩
  let m := Finset.univ.prod fun i : iota => (s₅ (some i)).card
  have hconj₅ : action sigma₅ = eGal.permCongr (arithmeticRootPerm fZ sigma₅) := by
    ext y
    simpa using (hintertwine sigma₅ (eGal.symm y)).symm
  have hswap : (action (sigma₅ ^ m)).IsSwap := by
    rw [map_pow, hconj₅]
    change (eGal.permCongrHom (arithmeticRootPerm fZ sigma₅) ^ m).IsSwap
    rw [← map_pow]
    exact swap_perm_congr eGal (by simpa [m] using hswapInt)
  letI : MulAction.IsPretransitive H (f.rootSet F₈₂₇) := by
    constructor
    intro a b
    have ha : a ∈ (action sigma₂).support := by
      rw [hfullSupport]
      exact Finset.mem_univ a
    have hb : b ∈ (action sigma₂).support := by
      rw [hfullSupport]
      exact Finset.mem_univ b
    have ha' : action sigma₂ a ≠ a := by
      simpa [Equiv.Perm.mem_support] using ha
    have hb' : action sigma₂ b ≠ b := by
      simpa [Equiv.Perm.mem_support] using hb
    obtain ⟨k, hk⟩ := hfullCycle.exists_pow_eq ha' hb'
    refine ⟨⟨action (sigma₂ ^ k), ⟨sigma₂ ^ k, by simp⟩⟩, ?_⟩
    simpa using hk
  have hHtop : H = ⊤ := by
    apply perm_pretransitive_cycle
      H hlongCycle hlongCard hswap
    · exact ⟨sigma₃, rfl⟩
    · exact ⟨sigma₅ ^ m, rfl⟩
  simpa [H, action, f] using hHtop

/-- The abstract-group form of Example 8.27: once the modular argument has
identified the root action with the full permutation group and the roots have
been numbered, the polynomial Galois group is the standard symmetric group
`S_n = Equiv.Perm (Fin n)`. -/
theorem polynomial_gal_sn
    (n : ℕ)
    (hcard : Fintype.card
      ((symmetricGaloisQ f₁ f₂ f₃).rootSet F₈₂₇) = n)
    (hrange : (Polynomial.Gal.galActionHom
      (symmetricGaloisQ f₁ f₂ f₃) F₈₂₇).range = ⊤) :
    Nonempty ((symmetricGaloisQ f₁ f₂ f₃).Gal ≃*
      Equiv.Perm (Fin n)) := by
  let action := Polynomial.Gal.galActionHom
    (symmetricGaloisQ f₁ f₂ f₃) F₈₂₇
  let eRange : (symmetricGaloisQ f₁ f₂ f₃).Gal ≃* action.range :=
    MonoidHom.ofInjective
      (Polynomial.Gal.galActionHom_injective
        (symmetricGaloisQ f₁ f₂ f₃) F₈₂₇)
  let eRoots :
      (symmetricGaloisQ f₁ f₂ f₃).rootSet F₈₂₇ ≃ Fin n :=
    Fintype.equivFinOfCardEq hcard
  exact ⟨eRange.trans
    ((MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv) |>.trans
      eRoots.permCongrHom⟩

set_option maxHeartbeats 4000000 in
-- Reusing the full three-prime modular argument needs its elaboration budget.
set_option maxRecDepth 100000 in
/-- Milne's Example 8.27 in its final form: the three stated modular
factorization patterns force the polynomial Galois group itself to be
isomorphic to `S_n`.  In particular, the cycle elements and the full root
action are conclusions rather than hypotheses. -/
theorem gal_sn_factorizations
    (n : ℕ) (hn : 3 ≤ n)
    (hfmonic : (symmetricGroupConstruction f₁ f₂ f₃).Monic)
    (hfdegree : (symmetricGroupConstruction f₁ f₂ f₃).natDegree = n)
    (hirr₂ : Irreducible ((symmetricGroupConstruction f₁ f₂ f₃).map
      (Ideal.Quotient.mk (primeIdeal 2))))
    (g₃ : Fin 2 → (ℤ ⧸ primeIdeal 3)[X])
    (hfac₃ : (symmetricGroupConstruction f₁ f₂ f₃).map
      (Ideal.Quotient.mk (primeIdeal 3)) = ∏ i, g₃ i)
    (hirr₃ : ∀ i, Irreducible (g₃ i))
    (hmonic₃ : ∀ i, (g₃ i).Monic)
    (hinj₃ : Function.Injective g₃)
    (hdeg₃zero : (g₃ 0).natDegree = 1)
    (hdeg₃one : (g₃ 1).natDegree = n - 1)
    (hsep₃ : ((symmetricGroupConstruction f₁ f₂ f₃).map
      (Ideal.Quotient.mk (primeIdeal 3))).Separable)
    {iota : Type*} [Fintype iota]
    (g₅ : Option iota → (ℤ ⧸ primeIdeal 5)[X])
    (hfac₅ : (symmetricGroupConstruction f₁ f₂ f₃).map
      (Ideal.Quotient.mk (primeIdeal 5)) = ∏ i, g₅ i)
    (hirr₅ : ∀ i, Irreducible (g₅ i))
    (hmonic₅ : ∀ i, (g₅ i).Monic)
    (hinj₅ : Function.Injective g₅)
    (hdeg₅two : (g₅ none).natDegree = 2)
    (hdeg₅odd : ∀ i, Odd (g₅ (some i)).natDegree)
    (hsep₅ : ((symmetricGroupConstruction f₁ f₂ f₃).map
      (Ideal.Quotient.mk (primeIdeal 5))).Separable) :
    Nonempty ((symmetricGaloisQ f₁ f₂ f₃).Gal ≃*
      Equiv.Perm (Fin n)) := by
  have hrange := root_action_top f₁ f₂ f₃ n hn
    hfmonic hfdegree hirr₂ g₃ hfac₃ hirr₃ hmonic₃ hinj₃
    hdeg₃zero hdeg₃one hsep₃ g₅ hfac₅ hirr₅ hmonic₅ hinj₅
    hdeg₅two hdeg₅odd hsep₅
  exact polynomial_gal_sn f₁ f₂ f₃ n
    (root_set_card f₁ f₂ f₃ n hfmonic hfdegree hirr₂)
    hrange

end CanonicalSplittingField

end

end Submission.NumberTheory.Milne
