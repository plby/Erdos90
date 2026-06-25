import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Towers.ClassField.CohomologyOps.FunctorialMapsGroup
import Towers.ClassField.CohomologyOps.AcyclicInflation
import Towers.ClassField.CohomologyOps.RestrictedCoinducedAcyclic

/-!
# Milne, Class Field Theory, Proposition II.1.34

This file proves the full higher inflation--restriction statement by Milne's
dimension-shifting argument.  In particular, the maps below are the actual
cohomological inflation and restriction maps, rather than maps transported
across chosen isomorphisms.
-/

namespace Towers.CField.COps

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Naturality

/-- Restriction applied simultaneously to the three terms of a short complex. -/
noncomputable def restrictionShortComplex
    (X : ShortComplex (Rep k G)) (H : Subgroup G) :
    X.map (groupCohomology.cochainsFunctor k G) ⟶
      (X.map (Rep.resFunctor H.subtype)).map
        (groupCohomology.cochainsFunctor k H) where
  τ₁ := groupCohomology.cochainsMap H.subtype (𝟙 _)
  τ₂ := groupCohomology.cochainsMap H.subtype (𝟙 _)
  τ₃ := groupCohomology.cochainsMap H.subtype (𝟙 _)
  comm₁₂ := by
    change groupCohomology.cochainsMap H.subtype (𝟙 _) ≫
        groupCohomology.cochainsMap (MonoidHom.id H)
          ((Rep.resFunctor H.subtype).map X.f) =
      groupCohomology.cochainsMap (MonoidHom.id G) X.f ≫
        groupCohomology.cochainsMap H.subtype (𝟙 _)
    rw [← groupCohomology.cochainsMap_comp,
      ← groupCohomology.cochainsMap_comp]
    rfl
  comm₂₃ := by
    change groupCohomology.cochainsMap H.subtype (𝟙 _) ≫
        groupCohomology.cochainsMap (MonoidHom.id H)
          ((Rep.resFunctor H.subtype).map X.g) =
      groupCohomology.cochainsMap (MonoidHom.id G) X.g ≫
        groupCohomology.cochainsMap H.subtype (𝟙 _)
    rw [← groupCohomology.cochainsMap_comp,
      ← groupCohomology.cochainsMap_comp]
    rfl

/-- Connecting homomorphisms commute with restriction. -/
theorem restriction_delta_naturality
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (H : Subgroup G) (n : ℕ) :
    groupCohomology.δ hX n (n + 1) rfl ≫
        (groupCohomology.resNatTrans (k := k) H.subtype (n + 1)).app X.X₁ =
      (groupCohomology.resNatTrans (k := k) H.subtype n).app X.X₃ ≫
        groupCohomology.δ
          (hX.map_of_exact (Rep.resFunctor H.subtype)) n (n + 1) rfl := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (restrictionShortComplex X H)
    (groupCohomology.map_cochainsFunctor_shortExact hX)
    (groupCohomology.map_cochainsFunctor_shortExact
      (hX.map_of_exact (Rep.resFunctor H.subtype))) n (n + 1) rfl

variable (H : Subgroup G) [H.Normal]

private noncomputable def invariantsInclusion
    (A : Rep k G) :
    Rep.res (QuotientGroup.mk' H) (A.quotientToInvariants H) ⟶ A :=
  Rep.ofHom (A.ρ.quotientToInvariants_lift H)

/-- Inflation applied simultaneously to the three terms of a short complex. -/
noncomputable def inflationCochainsComplex
    (X : ShortComplex (Rep k G)) :
    (X.map (Rep.quotientToInvariantsFunctor k H)).map
        (groupCohomology.cochainsFunctor k (G ⧸ H)) ⟶
      X.map (groupCohomology.cochainsFunctor k G) where
  τ₁ := groupCohomology.cochainsMap (QuotientGroup.mk' H)
    (invariantsInclusion H X.X₁)
  τ₂ := groupCohomology.cochainsMap (QuotientGroup.mk' H)
    (invariantsInclusion H X.X₂)
  τ₃ := groupCohomology.cochainsMap (QuotientGroup.mk' H)
    (invariantsInclusion H X.X₃)
  comm₁₂ := by
    change groupCohomology.cochainsMap (QuotientGroup.mk' H)
          (invariantsInclusion H X.X₁) ≫
        groupCohomology.cochainsMap (MonoidHom.id G) X.f =
      groupCohomology.cochainsMap (MonoidHom.id (G ⧸ H))
          ((Rep.quotientToInvariantsFunctor k H).map X.f) ≫
        groupCohomology.cochainsMap (QuotientGroup.mk' H)
          (invariantsInclusion H X.X₂)
    rw [← groupCohomology.cochainsMap_comp,
      ← groupCohomology.cochainsMap_comp]
    congr 1
  comm₂₃ := by
    change groupCohomology.cochainsMap (QuotientGroup.mk' H)
          (invariantsInclusion H X.X₂) ≫
        groupCohomology.cochainsMap (MonoidHom.id G) X.g =
      groupCohomology.cochainsMap (MonoidHom.id (G ⧸ H))
          ((Rep.quotientToInvariantsFunctor k H).map X.g) ≫
        groupCohomology.cochainsMap (QuotientGroup.mk' H)
          (invariantsInclusion H X.X₃)
    rw [← groupCohomology.cochainsMap_comp,
      ← groupCohomology.cochainsMap_comp]
    congr 1

/-- Connecting homomorphisms commute with inflation. -/
theorem inflation_delta_naturality
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (hXQ : (X.map
      (Rep.quotientToInvariantsFunctor k H)).ShortExact) (n : ℕ) :
    groupCohomology.δ hXQ n (n + 1) rfl ≫
        (groupCohomology.infNatTrans (k := k) H (n + 1)).app X.X₁ =
      (groupCohomology.infNatTrans (k := k) H n).app X.X₃ ≫
        groupCohomology.δ hX n (n + 1) rfl := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (inflationCochainsComplex H X)
    (groupCohomology.map_cochainsFunctor_shortExact hXQ)
    (groupCohomology.map_cochainsFunctor_shortExact hX) n (n + 1) rfl

end Naturality

section InflationRestriction

variable (A : Rep k G) (H : Subgroup G) [H.Normal]

/-- Inflation in the sequence of Proposition II.1.34. -/
noncomputable abbrev cochainsShortInflation (n : ℕ) :
    groupCohomology (A.quotientToInvariants H) n ⟶
      groupCohomology A n :=
  (groupCohomology.infNatTrans (k := k) H n).app A

/-- Restriction in the sequence of Proposition II.1.34. -/
noncomputable abbrev restrictionCochainsMap (n : ℕ) :
    groupCohomology A n ⟶
      groupCohomology (Rep.res H.subtype A) n :=
  (groupCohomology.resNatTrans (k := k) H.subtype n).app A

set_option maxHeartbeats 2000000 in
-- The recursive proof elaborates three naturality squares at each shift.
/-- Under Milne's vanishing hypothesis, restriction after inflation is zero.
This is proved along with the same dimension shift used for exactness, rather
than by replacing either map with a merely isomorphic one. -/
theorem inflation_comp_restriction
    (n : ℕ) (hn : 0 < n)
    (hH : ∀ j : ℕ, 0 < j → j < n →
      IsZero (groupCohomology (Rep.res H.subtype A) j)) :
    cochainsShortInflation A H n ≫
      restrictionCochainsMap A H n = 0 := by
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
      cases n with
      | zero => exact (Nat.not_lt_zero 0 hn).elim
      | succ m =>
          by_cases hm : m = 0
          · subst m
            exact (groupCohomology.H1InfRes A H).zero
          · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
            let X := dimensionShiftSequence A
            let hX := shift_sequence_short A
            let XH := X.map (Rep.resFunctor H.subtype)
            have hXH : XH.ShortExact :=
              hX.map_of_exact (Rep.resFunctor H.subtype)
            have hmiddleH : ∀ q : ℕ, 0 < q →
                IsZero (groupCohomology XH.X₂ q) := by
              intro q hq
              exact
                middle_unconditional_acyclic H A q hq
            have hshifted : ∀ j : ℕ, 0 < j → j < m →
                IsZero (groupCohomology
                  (Rep.res H.subtype X.X₃) j) := by
              intro j hj hjm
              exact (hH (j + 1) (Nat.succ_pos j) (by omega)).of_iso
                (dimensionShiftingIso hXH hmiddleH j hj)
            have hprevious := ih m (Nat.lt_succ_self m) X.X₃ hmpos hshifted
            have hH1 : IsZero
                (groupCohomology (Rep.res H.subtype A) 1) :=
              hH 1 Nat.zero_lt_one (by omega)
            let F := Rep.quotientToInvariantsFunctor k H
            let XQ := X.map F
            have hXQ : XQ.ShortExact :=
              invariants_short_exact H hX hH1
            have hmiddleQ : IsZero
                (groupCohomology XQ.X₂ (m + 1)) := by
              exact (zero_cohomology_coinduced
                (Rep.trivial k (⊥ : Subgroup (G ⧸ H)) A)
                (m + 1) (Nat.succ_pos m)).of_iso
                  ((groupCohomology.functor k (G ⧸ H) (m + 1)).mapIso
                    (shiftMiddleIso A H))
            haveI hdeltaQ : Epi
                (groupCohomology.δ hXQ m (m + 1) rfl) :=
              groupCohomology.epi_δ_of_isZero hXQ m hmiddleQ
            have hinf :
                groupCohomology.δ hXQ m (m + 1) rfl ≫
                    cochainsShortInflation A H (m + 1) =
                  cochainsShortInflation X.X₃ H m ≫
                    groupCohomology.δ hX m (m + 1) rfl := by
              simpa [X, XQ, F] using
                (inflation_delta_naturality H hX hXQ m)
            have hres :
                groupCohomology.δ hX m (m + 1) rfl ≫
                    restrictionCochainsMap A H (m + 1) =
                  restrictionCochainsMap X.X₃ H m ≫
                    groupCohomology.δ hXH m (m + 1) rfl := by
              simpa [X, XH] using restriction_delta_naturality hX H m
            have hres_assoc :
                cochainsShortInflation X.X₃ H m ≫
                    (groupCohomology.δ hX m (m + 1) rfl ≫
                      restrictionCochainsMap A H (m + 1)) =
                  cochainsShortInflation X.X₃ H m ≫
                    (restrictionCochainsMap X.X₃ H m ≫
                      groupCohomology.δ hXH m (m + 1) rfl) :=
              congrArg
                (fun z ↦ cochainsShortInflation X.X₃ H m ≫ z) hres
            apply (cancel_epi
              (groupCohomology.δ hXQ m (m + 1) rfl)).mp
            have hfirst :
              groupCohomology.δ hXQ m (m + 1) rfl ≫
                    (cochainsShortInflation A H (m + 1) ≫
                      restrictionCochainsMap A H (m + 1)) =
                  cochainsShortInflation X.X₃ H m ≫
                    (groupCohomology.δ hX m (m + 1) rfl ≫
                      restrictionCochainsMap A H (m + 1)) := by
              calc
                groupCohomology.δ hXQ m (m + 1) rfl ≫
                      (cochainsShortInflation A H (m + 1) ≫
                        restrictionCochainsMap A H (m + 1)) =
                  (groupCohomology.δ hXQ m (m + 1) rfl ≫
                    cochainsShortInflation A H (m + 1)) ≫
                      restrictionCochainsMap A H (m + 1) :=
                  (Category.assoc _ _ _).symm
                _ = (cochainsShortInflation X.X₃ H m ≫
                      groupCohomology.δ hX m (m + 1) rfl) ≫
                        restrictionCochainsMap A H (m + 1) :=
                  congrArg
                    (fun z ↦ z ≫ restrictionCochainsMap A H (m + 1)) hinf
                _ = cochainsShortInflation X.X₃ H m ≫
                      (groupCohomology.δ hX m (m + 1) rfl ≫
                        restrictionCochainsMap A H (m + 1)) :=
                  Category.assoc _ _ _
            have hzero :
                cochainsShortInflation X.X₃ H m ≫
                    (groupCohomology.δ hX m (m + 1) rfl ≫
                      restrictionCochainsMap A H (m + 1)) = 0 := by
              calc
                cochainsShortInflation X.X₃ H m ≫
                    (groupCohomology.δ hX m (m + 1) rfl ≫
                      restrictionCochainsMap A H (m + 1)) =
                  cochainsShortInflation X.X₃ H m ≫
                    (restrictionCochainsMap X.X₃ H m ≫
                      groupCohomology.δ hXH m (m + 1) rfl) := hres_assoc
                _ = (cochainsShortInflation X.X₃ H m ≫
                      restrictionCochainsMap X.X₃ H m) ≫
                        groupCohomology.δ hXH m (m + 1) rfl :=
                  (Category.assoc _ _ _).symm
                _ = 0 := by rw [hprevious, zero_comp]
            simpa only [comp_zero] using hfirst.trans hzero

/-- The inflation--restriction short complex in degree `n`, under exactly
the lower-degree vanishing hypothesis of Proposition II.1.34. -/
noncomputable def restrictionCochainsComplex
    (n : ℕ) (hn : 0 < n)
    (hH : ∀ j : ℕ, 0 < j → j < n →
      IsZero (groupCohomology (Rep.res H.subtype A) j)) :
    ShortComplex (ModuleCat k) :=
  ShortComplex.mk (cochainsShortInflation A H n)
    (restrictionCochainsMap A H n)
    (inflation_comp_restriction A H n hn hH)

set_option maxHeartbeats 2000000 in
-- The induction elaborates three long-exact-sequence connecting isomorphisms.
/-- **Proposition II.1.34 (inflation--restriction), full exactness.** Let `H` be normal in
`G`, let `n > 0`, and suppose `H^j(H,A) = 0` for `0 < j < n`.  Then

`0 → H^n(G/H,A^H) → H^n(G,A) → H^n(H,A)`

is exact: inflation is a monomorphism and its image is the kernel of
restriction.  No finiteness assumption is imposed on `G` or on the index of
`H`.  The conjunction is Mathlib's standard encoding of exactness at the
left and middle objects. -/
theorem cochains_short_mono
    (n : ℕ) (hn : 0 < n)
    (hH : ∀ j : ℕ, 0 < j → j < n →
      IsZero (groupCohomology (Rep.res H.subtype A) j)) :
    (restrictionCochainsComplex A H n hn hH).Exact ∧
      Mono (restrictionCochainsComplex A H n hn hH).f := by
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
      cases n with
      | zero => exact (Nat.not_lt_zero 0 hn).elim
      | succ m =>
          by_cases hm : m = 0
          · subst m
            constructor
            · simpa [restrictionCochainsComplex, cochainsShortInflation,
                restrictionCochainsMap] using
                  (groupCohomology.H1InfRes_exact A H)
            · change Mono (groupCohomology.H1InfRes A H).f
              infer_instance
          · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
            let X := dimensionShiftSequence A
            let hX := shift_sequence_short A
            let XH := X.map (Rep.resFunctor H.subtype)
            have hXH : XH.ShortExact :=
              hX.map_of_exact (Rep.resFunctor H.subtype)
            have hmiddleH : ∀ q : ℕ, 0 < q →
                IsZero (groupCohomology XH.X₂ q) := by
              intro q hq
              exact
                middle_unconditional_acyclic H A q hq
            have hshifted : ∀ j : ℕ, 0 < j → j < m →
                IsZero (groupCohomology
                  (Rep.res H.subtype X.X₃) j) := by
              intro j hj hjm
              exact (hH (j + 1) (Nat.succ_pos j) (by omega)).of_iso
                (dimensionShiftingIso hXH hmiddleH j hj)
            have hprevious :
                (restrictionCochainsComplex X.X₃ H m hmpos hshifted).Exact ∧
                  Mono (restrictionCochainsComplex X.X₃ H m hmpos hshifted).f :=
              ih m (Nat.lt_succ_self m) X.X₃ hmpos hshifted
            have hH1 : IsZero
                (groupCohomology (Rep.res H.subtype A) 1) :=
              hH 1 Nat.zero_lt_one (by omega)
            let F := Rep.quotientToInvariantsFunctor k H
            let XQ := X.map F
            have hXQ : XQ.ShortExact :=
              invariants_short_exact H hX hH1
            have hmiddleQ : ∀ q : ℕ, 0 < q →
                IsZero (groupCohomology XQ.X₂ q) := by
              intro q hq
              exact (zero_cohomology_coinduced
                (Rep.trivial k (⊥ : Subgroup (G ⧸ H)) A) q hq).of_iso
                  ((groupCohomology.functor k (G ⧸ H) q).mapIso
                    (shiftMiddleIso A H))
            let dQ := groupCohomology.δ hXQ m (m + 1) rfl
            let dG := groupCohomology.δ hX m (m + 1) rfl
            let dH := groupCohomology.δ hXH m (m + 1) rfl
            letI hdQ : IsIso dQ :=
              groupCohomology.isIso_δ_of_isZero hXQ m
                (hmiddleQ m hmpos) (hmiddleQ (m + 1) (Nat.succ_pos m))
            letI hdG : IsIso dG :=
              groupCohomology.isIso_δ_of_isZero hX m
                (shift_middle_acyclic A m hmpos)
                (shift_middle_acyclic A (m + 1)
                  (Nat.succ_pos m))
            letI hdH : IsIso dH :=
              groupCohomology.isIso_δ_of_isZero hXH m
                (hmiddleH m hmpos) (hmiddleH (m + 1) (Nat.succ_pos m))
            have hinf :
                dQ ≫ cochainsShortInflation A H (m + 1) =
                  cochainsShortInflation X.X₃ H m ≫ dG := by
              simpa [dQ, dG, X, XQ, F] using
                (inflation_delta_naturality H hX hXQ m)
            have hres :
                dG ≫ restrictionCochainsMap A H (m + 1) =
                  restrictionCochainsMap X.X₃ H m ≫ dH := by
              simpa [dG, dH, X, XH] using
                restriction_delta_naturality hX H m
            let e : restrictionCochainsComplex X.X₃ H m hmpos hshifted ≅
                restrictionCochainsComplex A H (m + 1) (Nat.succ_pos m) hH :=
              ShortComplex.isoMk
                (@asIso (ModuleCat k) _ _ _ dQ hdQ)
                (@asIso (ModuleCat k) _ _ _ dG hdG)
                (@asIso (ModuleCat k) _ _ _ dH hdH)
                (by
                  simpa [restrictionCochainsComplex] using hinf)
                (by
                  simpa [restrictionCochainsComplex] using hres)
            exact (ShortComplex.exact_and_mono_f_iff_of_iso e).mp hprevious

/-- The leading map in Proposition II.1.34 is injective: inflation is a
monomorphism under Milne's lower-degree vanishing hypothesis. -/
theorem inflation_mono
    (n : ℕ) (hn : 0 < n)
    (hH : ∀ j : ℕ, 0 < j → j < n →
      IsZero (groupCohomology (Rep.res H.subtype A) j)) :
    Mono (cochainsShortInflation A H n) := by
  simpa [restrictionCochainsComplex] using
    (cochains_short_mono A H n hn hH).2

/-- Exactness at the middle term in Proposition II.1.34. -/
theorem restrictionCochainsShort
    (n : ℕ) (hn : 0 < n)
    (hH : ∀ j : ℕ, 0 < j → j < n →
      IsZero (groupCohomology (Rep.res H.subtype A) j)) :
    (restrictionCochainsComplex A H n hn hH).Exact :=
  (cochains_short_mono A H n hn hH).1

end InflationRestriction

end

end Towers.CField.COps
