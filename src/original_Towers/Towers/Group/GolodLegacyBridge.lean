import Towers.Group.PresentedAugmentationBridge
import Towers.Group.FoxAssociatedGraded
import Towers.Group.HilbertJenningsFox
import Towers.Group.IdealJenningsFox


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Towers

/-!
Compatibility declarations from the original Golod-Shafarevich bridge in
`Erdos90/I.lean`.  The underlying implementation now lives in the decomposed
`Towers.Group` modules; this file preserves the original theorem surface.
-/
noncomputable def PPDatum.presrelator_foxinit_componentmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hn : 2 ≤ n)
    (i : H.pres_highdegree_relatorindex depth n) :
    H.pALayer (rels := rels) (n - depth i.1) →ₗ[
        ZMod H.realizesFiniteNontrivial.p]
      H.pres_highdegree_gensource (rels := rels) n where
  toFun y := fun j =>
    H.presentedLeftMul
      (rels := rels)
      (m := depth i.1 - 1)
      (n := n - depth i.1)
      (k := n - 1)
      (by
        have hi_le : depth i.1 ≤ n := i.2
        have hi_depth : 2 ≤ depth i.1 := hdepth i.1
        omega)
      (H.presentedFoxCoefficient (rels := rels) i.1 j)
      (H.presented_relator_fox
        (rels := rels) hmem hdepth i.1 j)
      y
  map_add' y z := by
    ext j
    simp
  map_smul' c y := by
    ext j
    simp

/--
The right-oriented one-relator component of the associated-graded Fox map.

This orientation is the one matched by `presented_relator_syzygy`: a source
class in degree `n - depth i` is right-multiplied by each Fox coefficient,
landing in the degree `n - 1` generator source.
-/
noncomputable def PPDatum.presrelator_foxinit_righcompmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hn : 2 ≤ n)
    (i : H.pres_highdegree_relatorindex depth n) :
    H.pALayer (rels := rels) (n - depth i.1) →ₗ[
        ZMod H.realizesFiniteNontrivial.p]
      H.pres_highdegree_gensource (rels := rels) n where
  toFun y := fun j =>
    H.presentedAugmentationMul
      (rels := rels)
      (m := depth i.1 - 1)
      (n := n - depth i.1)
      (k := n - 1)
      (by
        have hi_le : depth i.1 ≤ n := i.2
        have hi_depth : 2 ≤ depth i.1 := hdepth i.1
        omega)
      (H.presentedFoxCoefficient (rels := rels) i.1 j)
      (H.presented_relator_fox
        (rels := rels) hmem hdepth i.1 j)
      y
  map_add' y z := by
    ext j
    simp
  map_smul' c y := by
    ext j
    simp

set_option synthInstance.maxHeartbeats 80000 in
-- The dependent direct-sum source needs extra search for its linear-map structure.
/--
The associated-graded Fox map from all relator correction layers to the
generator source.

This is the concrete map that should be used for the relator side of the
Golod--Shafarevich complex. It uses the right-oriented multiplication order
matched by the Fox syzygy.
-/
noncomputable def PPDatum.pres_relatorfox_initmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hn : 2 ≤ n) :
    H.pHSrc (rels := rels) depth n →ₗ[
        ZMod H.realizesFiniteNontrivial.p]
      H.pres_highdegree_gensource (rels := rels) n :=
  LinearMap.lsum
    (ZMod H.realizesFiniteNontrivial.p)
    (fun i : H.pres_highdegree_relatorindex depth n =>
      H.pALayer (rels := rels) (n - depth i.1))
    (ZMod H.realizesFiniteNontrivial.p)
    (fun i =>
      H.presrelator_foxinit_righcompmap
        (rels := rels) hmem hdepth n hn i)

set_option synthInstance.maxHeartbeats 80000 in
-- The dependent direct-sum source needs extra search for its linear-map structure.
/--
The right-oriented associated-graded Fox map from all relator correction layers
to the generator source.

This is the version whose composition with the right-oriented generator
multiplication map is governed directly by the numerator Fox syzygy.
-/
noncomputable def PPDatum.presrelator_foxinit_rightmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hn : 2 ≤ n) :
    H.pHSrc (rels := rels) depth n →ₗ[
        ZMod H.realizesFiniteNontrivial.p]
      H.pres_highdegree_gensource (rels := rels) n :=
  LinearMap.lsum
    (ZMod H.realizesFiniteNontrivial.p)
    (fun i : H.pres_highdegree_relatorindex depth n =>
      H.pALayer (rels := rels) (n - depth i.1))
    (ZMod H.realizesFiniteNontrivial.p)
    (fun i =>
      H.presrelator_foxinit_righcompmap
        (rels := rels) hmem hdepth n hn i)

/-- Presentation-generator differences lie in the presented augmentation ideal. -/
theorem PPDatum.presrelatorfox_initmaprange_legenkernel
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hn : 2 ≤ n) :
    LinearMap.range
        (H.pres_relatorfox_initmap (rels := rels) hmem hdepth n hn) ≤
      LinearMap.ker
        (H.presentedHighMultiplication
          (rels := rels) n (by omega)) := by
  classical
  let genDiff : Fin H.generatorRank → H.presentedGroupAlgebra rels :=
    H.presentedGeneratorDifference (rels := rels)
  have hgen : ∀ j, genDiff j ∈ H.presentedAugmentationIdeal rels := by
    intro j
    exact H.presented_difference_ideal (rels := rels) j
  let β :=
    H.presentedHighMultiplication
      (rels := rels) n (by omega)
  have hcomponent_zero :
      ∀ i y,
        β (H.presrelator_foxinit_righcompmap
          (rels := rels) hmem hdepth n hn i y) = 0 := by
    intro i y
    refine Submodule.Quotient.induction_on
      (p := H.presentedAugmentationKernel
        (rels := rels) (n - depth i.1)) y ?_
    intro y0
    let Kprev := H.presentedAugmentationKernel (rels := rels) (n - 1)
    let Ktarget := H.presentedAugmentationKernel (rels := rels) n
    let foxPart : Fin H.generatorRank →
        H.presentedAugmentationSubmodule (rels := rels) (n - 1) :=
      fun j =>
        H.presentedRightMul
          (m := depth i.1 - 1)
          (n := n - depth i.1)
          (k := n - 1)
          (by
            have hi_le : depth i.1 ≤ n := i.2
            have hi_depth : 2 ≤ depth i.1 := hdepth i.1
            omega)
          (H.presentedFoxCoefficient (rels := rels) i.1 j)
          (H.presented_relator_fox
            (rels := rels) hmem hdepth i.1 j)
          y0
    have hcomponent :
        H.presrelator_foxinit_righcompmap
            (rels := rels) hmem hdepth n hn i
            (Submodule.Quotient.mk y0) =
          fun j => Kprev.mkQ (foxPart j) := by
      ext j
      dsimp [foxPart, Kprev,
        PPDatum.presrelator_foxinit_righcompmap]
      exact H.presented_augmentation_mk
        (m := depth i.1 - 1)
        (n := n - depth i.1)
        (k := n - 1)
        (by
          have hi_le : depth i.1 ≤ n := i.2
          have hi_depth : 2 ≤ depth i.1 := hdepth i.1
          omega)
        (H.presentedFoxCoefficient (rels := rels) i.1 j)
        (H.presented_relator_fox
          (rels := rels) hmem hdepth i.1 j)
        y0
    rw [hcomponent]
    have hβ :
        β (fun j => Kprev.mkQ (foxPart j)) =
          Ktarget.mkQ
            (∑ j,
              H.presentedRightMul
                (m := 1) (n := n - 1) (k := n)
                (by omega)
                (genDiff j)
                (by simpa [genDiff, Submodule.pow_one] using hgen j)
                (foxPart j)) := by
      simpa [β, Kprev, Ktarget, genDiff,
        PPDatum.presentedHighMultiplication]
        using
          H.presented_multiplication_mk
            (rels := rels)
            genDiff
            hgen
            n
            (by omega)
            foxPart
    rw [hβ]
    apply (Submodule.Quotient.mk_eq_zero Ktarget).mpr
    change
      (((∑ j,
          H.presentedRightMul
            (m := 1) (n := n - 1) (k := n)
            (by omega)
            (genDiff j)
            (by simpa [genDiff, Submodule.pow_one] using hgen j)
            (foxPart j)) :
        H.presentedAugmentationSubmodule (rels := rels) n) :
          H.presentedGroupAlgebra rels) ∈
        H.presentedAugmentationSubmodule (rels := rels) (n + 1)
    have hsum_zero :
        (((∑ j,
            H.presentedRightMul
              (m := 1) (n := n - 1) (k := n)
              (by omega)
              (genDiff j)
              (by simpa [genDiff, Submodule.pow_one] using hgen j)
              (foxPart j)) :
          H.presentedAugmentationSubmodule (rels := rels) n) :
            H.presentedGroupAlgebra rels) = 0 := by
      dsimp [foxPart, genDiff]
      simpa [PPDatum.presentedRightMul]
        using
          H.presented_fox_syzygy
            (rels := rels)
            i.1
            (y0 : H.presentedGroupAlgebra rels)
    rw [hsum_zero]
    exact Submodule.zero_mem _
  intro z hz
  rcases hz with ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  change β (H.pres_relatorfox_initmap (rels := rels) hmem hdepth n hn x) = 0
  rw [PPDatum.pres_relatorfox_initmap, LinearMap.lsum_apply]
  rw [LinearMap.sum_apply]
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _hi => hcomponent_zero i (x i)

set_option synthInstance.maxHeartbeats 80000 in
-- The exactness statement compares kernels and ranges of dependent graded maps.
/--
The strict associated-graded Fox exactness hypothesis in degree `n`.

This is the extra filtered-standard-basis input that is not implied merely by
knowing the individual Zassenhaus depths of the relators. It says that the
Fox-Lyndon relation map remains exact after passing to the associated graded
augmentation algebra in this degree.
-/
abbrev PPDatum.presrelator_foxinitstrict_exactindegree
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hn : 2 ≤ n) : Prop :=
  LinearMap.ker
      (H.presentedHighMultiplication
        (rels := rels) n (by omega)) ≤
    LinearMap.range
      (H.pres_relatorfox_initmap (rels := rels) hmem hdepth n hn)

set_option synthInstance.maxHeartbeats 80000 in
-- The theorem target repeats the dependent quotient/pi range expression.
/--
The exactness half of the Fox complex in degree `n`, under the strict filtered
Fox-Lyndon exactness hypothesis.

After the concrete Fox initial map has been constructed, the desired exactness
claim is that every homogeneous relation among the presentation-generator
multiplications is generated by the initial forms of the defining relators.
This does not follow from exact individual relator depths alone; the hypothesis
`hstrict` is the needed associated-graded relation-module exactness condition.
-/
theorem PPDatum.presrelator_foxinitmap_coversgenkernel
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (_hrels :
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (_hdepth_exact :
      ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hn : 2 ≤ n)
    (hstrict :
      H.presrelator_foxinitstrict_exactindegree
        (rels := rels) hmem hdepth n hn) :
    LinearMap.ker
        (H.presentedHighMultiplication
          (rels := rels) n (by omega)) ≤
      LinearMap.range
        (H.pres_relatorfox_initmap (rels := rels) hmem hdepth n hn) := by
  exact hstrict

/--
The remaining concrete relator-kernel statement.

For the specific multiplication map induced by the presentation generators,
the initial forms of the defining relators should generate every homogeneous
syzygy in degree `n`.  This is now the only place where the
Fox-derivative/initial-form argument is needed: `hmem` and `hdepth_exact`
say that the chosen depths are the actual initial degrees, `hstrict` supplies
the associated-graded exactness of the filtered relation module, and `hdepth`
ensures the source layers are the shifted layers
`I^(n - depth i) / I^(n - depth i + 1)` that occur in the
Golod--Shafarevich recurrence.
-/
theorem
    PPDatum.preshigh_degrpresrela_kerncoveexis
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels :
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth_exact :
      ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hn : 2 ≤ n)
    (hstrict :
      H.presrelator_foxinitstrict_exactindegree
        (rels := rels) hmem hdepth n hn) :
    ∃ α :
      H.pHSrc (rels := rels) depth n →ₗ[ZMod
          H.realizesFiniteNontrivial.p]
        H.pres_highdegree_gensource (rels := rels) n,
      LinearMap.ker
        (H.presentedHighMultiplication
          (rels := rels) n (by omega)) ≤
        LinearMap.range α := by
  refine ⟨H.pres_relatorfox_initmap (rels := rels) hmem hdepth n hn, ?_⟩
  exact
    H.presrelator_foxinitmap_coversgenkernel
      _p_prime _isPGroup hrels hmem hdepth_exact hdepth n hn hstrict

/--
The relator part of the GS complex covers the kernel of the multiplication map.

This is the genuinely relation-theoretic part under strict filtered Fox
exactness: relators with `depth i ≤ n` produce initial forms in degree
`depth i`, and multiplying these by degree `n - depth i` classes gives all
syzygies among the degree-one multiplication generators in degree `n`.
-/
theorem PPDatum.preshigh_degreerelator_kerncoveexis
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels :
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth_exact :
      ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hn : 2 ≤ n)
    (hstrict :
      H.presrelator_foxinitstrict_exactindegree
        (rels := rels) hmem hdepth n hn)
    (_hβ :
      ∃ β :
        H.pres_highdegree_gensource (rels := rels) n →ₗ[ZMod
            H.realizesFiniteNontrivial.p]
          H.pALayer (rels := rels) n,
        Function.Surjective β) :
    ∃ β :
      H.pres_highdegree_gensource (rels := rels) n →ₗ[ZMod
          H.realizesFiniteNontrivial.p]
        H.pALayer (rels := rels) n,
      Function.Surjective β ∧
        ∃ α :
          H.pHSrc (rels := rels) depth n →ₗ[ZMod
              H.realizesFiniteNontrivial.p]
          H.pres_highdegree_gensource (rels := rels) n,
          LinearMap.ker β ≤ LinearMap.range α := by
  classical
  have hn' : 1 ≤ n := by omega
  let β :=
    H.presentedHighMultiplication
      (rels := rels) n hn'
  have hβsurj : Function.Surjective β :=
    H.presented_high_multiplication
      _p_prime _isPGroup hrels n hn'
  rcases H.preshigh_degrpresrela_kerncoveexis
      _p_prime _isPGroup hrels hmem hdepth_exact hdepth n hn hstrict with
    ⟨α, hαker⟩
  refine ⟨β, hβsurj, α, ?_⟩
  simpa [β] using hαker

/--
Package the two high-degree algebraic ingredients as an exact GS complex.
-/
theorem PPDatum.preshigh_degreegs_complexexists
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels :
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth_exact :
      ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hn : 2 ≤ n)
    (hstrict :
      H.presrelator_foxinitstrict_exactindegree
        (rels := rels) hmem hdepth n hn) :
    Nonempty (H.PresHighdegreeGscomplex (rels := rels) depth n) := by
  have hβ :
      ∃ β :
        H.pres_highdegree_gensource (rels := rels) n →ₗ[ZMod
            H.realizesFiniteNontrivial.p]
          H.pALayer (rels := rels) n,
        Function.Surjective β :=
    H.preshigh_degreegen_targsurjexis
      _p_prime _isPGroup hrels n hn
  rcases H.preshigh_degreerelator_kerncoveexis
      _p_prime _isPGroup hrels hmem hdepth_exact hdepth n hn hstrict hβ with
    ⟨β, hβsurj, α, hαker⟩
  exact ⟨
    { generatorToTarget := β
      relatorToGenerator := α
      generator_target_surjective := hβsurj
      relator_covers_kernel := hαker }⟩

set_option synthInstance.maxHeartbeats 80000 in
-- The target quotient's projective instance is inferred through vector-space freeness.
/--
The genuinely algebraic high-degree Golod--Shafarevich map.

Mathematically, this packages the exact-sequence statement obtained from
multiplication by the degree-one generator classes, with the kernel controlled
by the initial forms of the relators. Once this map is constructed, the
remaining coefficient inequality is a finite-dimensional rank count.
-/
theorem PPDatum.preshigh_degreegslin_mapsurjexists
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels :
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth_exact :
      ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hn : 2 ≤ n)
    (hstrict :
      H.presrelator_foxinitstrict_exactindegree
        (rels := rels) hmem hdepth n hn) :
    ∃ Ψ :
      H.pres_highdegree_targetrelators (rels := rels) depth n →ₗ[ZMod
          H.realizesFiniteNontrivial.p]
        H.pres_highdegree_gensource (rels := rels) n,
      Function.Surjective Ψ := by
  classical
  letI : Fact (Nat.Prime H.realizesFiniteNontrivial.p) := ⟨_p_prime⟩
  rcases H.preshigh_degreegs_complexexists
      _p_prime _isPGroup hrels hmem hdepth_exact hdepth n hn hstrict with
    ⟨C⟩
  exact
    linear_coprod_range
      C.generatorToTarget
      C.relatorToGenerator
      C.generator_target_surjective
      C.relator_covers_kernel

set_option synthInstance.maxHeartbeats 80000 in
-- The dependent quotient/pi types below require extra typeclass search for finrank formulas.
set_option maxHeartbeats 800000 in
-- The rank-count proof unfolds several finite-dimensional product and Pi computations.
/--
The finite-dimensional rank count following from the high-degree
Golod--Shafarevich map.

This theorem is deliberately separated from the construction of the map above:
it should follow from surjectivity, the product/pi dimension formulas, and the
fact that summing over the contributing subtype is the same as summing the
original `if depth i ≤ n then ... else 0` expression.
-/
theorem PPDatum.presauglayer_finrhighdegr_genrelaesti
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels :
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i))
    (hdepth_exact :
      ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hn : 2 ≤ n)
    (hstrict :
      H.presrelator_foxinitstrict_exactindegree
        (rels := rels) hmem hdepth n hn) :
    H.generatorRank * H.presentedAugmentationFinrank hrels (n - 1) ≤
      H.presentedAugmentationFinrank hrels n +
        ∑ i, if depth i ≤ n then
          H.presentedAugmentationFinrank hrels (n - depth i)
        else
          0 := by
  have hΨ :
      ∃ Ψ :
        H.pres_highdegree_targetrelators (rels := rels) depth n →ₗ[ZMod
            H.realizesFiniteNontrivial.p]
          H.pres_highdegree_gensource (rels := rels) n,
        Function.Surjective Ψ :=
    H.preshigh_degreegslin_mapsurjexists
      _p_prime _isPGroup hrels hmem hdepth_exact hdepth n hn hstrict
  exact
    H.preshigh_degreegen_relaestisurj
      _p_prime (rels := rels) (depth := depth) hrels n hn hΨ

/--
The high-degree part of the full natural-number coefficient inequality.

This is the genuine Golod--Shafarevich linear-algebra estimate after the two
low-degree boundary cases have been removed. For `n ≥ 2`, multiplication by the
degree-one generator classes gives the usual map from `generatorRank` copies of
the previous augmentation layer to the `n`th layer, and the failure of
surjectivity is bounded by the relator initial forms in the shifted layers
indexed by `depth`.
-/
theorem
    PPDatum.presauglayer_finrankfullnat_coeffineqtwole
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier) :
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      (hrels :
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
      (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (hdepth_exact :
        ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1)) →
      (hdepth : ∀ i, 2 ≤ depth i) →
      (∀ n (hn : 2 ≤ n),
        H.presrelator_foxinitstrict_exactindegree
          (rels := rels) hmem hdepth n hn) →
      ∀ n,
        2 ≤ n →
        GShafar.fullCoefficientInequality
          H.generatorRank (H.presentedAugmentationFinrank hrels) depth n := by
  intro rels depth hrels hmem hdepth_exact hdepth hstrict n hn
  apply full_inequality_high
  · omega
  · exact
      H.presauglayer_finrhighdegr_genrelaesti
        _p_prime _isPGroup hrels hmem hdepth_exact hdepth n hn (hstrict n hn)

/--
The concrete augmentation-layer Hilbert sequence satisfies the
Golod--Shafarevich full coefficient inequalities.

This is the remaining generator/relator multiplication estimate in its natural
dimension form. The intended proof constructs, for each coefficient, the
classical multiplication map whose surjectivity bounds the generator
contribution by the target layer plus the relator correction layers.
-/
theorem
    PPDatum.presaug_layefinrfull_natcoeffineq
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier) :
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      (hrels :
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
      (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (hdepth_exact :
        ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1)) →
      (hdepth : ∀ i, 2 ≤ depth i) →
      (∀ n (hn : 2 ≤ n),
        H.presrelator_foxinitstrict_exactindegree
          (rels := rels) hmem hdepth n hn) →
      ∀ n,
        GShafar.fullCoefficientInequality
          H.generatorRank (H.presentedAugmentationFinrank hrels) depth n := by
  intro rels depth hrels hmem hdepth_exact hdepth hstrict n
  by_cases hn0 : n = 0
  · subst n
    exact full_coefficient_inequality
  by_cases hn1 : n = 1
  · subst n
    have hb0 :
        H.presentedAugmentationFinrank hrels 0 = 1 :=
      H.presaug_layerfinrank_zeroeqone _p_prime hrels
    have hb1 :
        H.generatorRank ≤ H.presentedAugmentationFinrank hrels 1 :=
      H.presaug_layerfinrankone_gegenrank
        _p_prime _isPGroup hrels
    have hrel :
        GShafar.fullRelatorTerm
          (H.presentedAugmentationFinrank hrels) depth 1 = 0 :=
      full_depth_two
        (H.presentedAugmentationFinrank hrels) depth hdepth
    change
      H.generatorRank *
          GShafar.fullNatTerm
            (H.presentedAugmentationFinrank hrels) 1 ≤
        H.presentedAugmentationFinrank hrels 1 +
          GShafar.fullRelatorTerm
            (H.presentedAugmentationFinrank hrels) depth 1
    rw [full_nat_generator, hrel, hb0, mul_one, add_zero]
    exact hb1
  have hn2 : 2 ≤ n := by omega
  exact H.presauglayer_finrankfullnat_coeffineqtwole
    _p_prime _isPGroup hrels hmem hdepth_exact hdepth hstrict n hn2

/--
The augmentation-layer Hilbert sequence eventually vanishes for the finite
presented group algebra.

Mathematically this is nilpotence of the augmentation ideal in the group algebra
of a finite `p`-group.
-/
theorem
    PPDatum.presauglayer_finrfinwind_natcoeffineq
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier) :
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      (hrels :
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
      (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (hdepth_exact :
        ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1)) →
      (hdepth : ∀ i, 2 ≤ depth i) →
      (∀ n (hn : 2 ≤ n),
        H.presrelator_foxinitstrict_exactindegree
          (rels := rels) hmem hdepth n hn) →
      ∃ N : ℕ,
        ∀ n, n ≤ GShafar.truncationWindow N depth →
          GShafar.recurrenceNatInequality
            H.generatorRank (H.presentedAugmentationFinrank hrels) N depth n := by
  intro rels depth hrels hmem hdepth_exact hdepth hstrict
  rcases H.presaug_layerfinrank_eventuallyzero
      _p_prime _isPGroup hrels with
    ⟨N, hzero⟩
  refine ⟨N, ?_⟩
  intro n _hn
  exact
    GShafar.recurrence_inequality_eventually
      (N := N)
      (hzero := hzero)
      (H.presaug_layefinrfull_natcoeffineq
        _p_prime _isPGroup hrels hmem hdepth_exact hdepth hstrict n)

/--
The natural-number finite-window dimension inequalities imply the corresponding
real-valued coefficient inequalities for the concrete Hilbert sequence.
-/
theorem
    PPDatum.presaug_hilbsequfin_windowcoeffineq
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier) :
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      (hrels :
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
      (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (hdepth_exact :
        ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1)) →
      (hdepth : ∀ i, 2 ≤ depth i) →
      (∀ n (hn : 2 ≤ n),
        H.presrelator_foxinitstrict_exactindegree
          (rels := rels) hmem hdepth n hn) →
      ∃ N : ℕ,
        ∀ n, n ≤ GShafar.truncationWindow N depth →
          GShafar.recurrenceCoefficientInequality
            H.generatorRank (H.presentedHilbertSequence hrels) N depth n := by
  intro rels depth hrels hmem hdepth_exact hdepth hstrict
  rcases H.presauglayer_finrfinwind_natcoeffineq
      _p_prime _isPGroup hrels hmem hdepth_exact hdepth hstrict with
    ⟨N, hnat⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hreal :=
    GShafar.recurrence_inequality_nat
      (d := H.generatorRank)
      (b := H.presentedAugmentationFinrank hrels)
      (N := N)
      (depth := depth)
      (n := n)
      (hnat n hn)
  simpa [PPDatum.presentedHilbertSequence] using hreal

/--
The concrete augmentation-layer Hilbert sequence satisfies the finite-window
Golod--Shafarevich recurrence once the corresponding dimension inequalities
are available.
-/
theorem
    PPDatum.presaug_hilbertsequence_finwindrecu
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier) :
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      (hrels :
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
      (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (hdepth_exact :
        ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1)) →
      (hdepth : ∀ i, 2 ≤ depth i) →
      (∀ n (hn : 2 ≤ n),
        H.presrelator_foxinitstrict_exactindegree
          (rels := rels) hmem hdepth n hn) →
      ∃ N : ℕ,
        ∀ n, n ≤ GShafar.truncationWindow N depth → 0 ≤
          GShafar.truncatedSequence
              (H.presentedHilbertSequence hrels) N n
            - (H.generatorRank : ℝ) *
                (if 1 ≤ n then
                  GShafar.truncatedSequence
                    (H.presentedHilbertSequence hrels) N (n - 1)
                else 0)
            + ∑ i, if depth i ≤ n then
                GShafar.truncatedSequence
                  (H.presentedHilbertSequence hrels) N (n - depth i)
              else 0 := by
  intro rels depth hrels hmem hdepth_exact hdepth hstrict
  rcases H.presaug_hilbsequfin_windowcoeffineq
      _p_prime _isPGroup hrels hmem hdepth_exact hdepth hstrict with
    ⟨N, hineq⟩
  refine ⟨N, ?_⟩
  exact
    GShafar.truncation_recurrence_inequalities
      (d := H.generatorRank)
      (a := H.presentedHilbertSequence hrels)
      (N := N)
      (depth := depth)
      hineq

/--
The finite-window version of the remaining Hilbert-series recurrence.

This is now the smallest explicit frontier in this file: produce the
augmentation-filtration coefficient sequence and verify only the finitely many
inequalities in the natural coefficient window.
-/
theorem PPDatum.fintrunc_hilbertrecurre_minpres
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier) :
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (hdepth_exact :
        ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1)) →
      (hdepth : ∀ i, 2 ≤ depth i) →
      (∀ n (hn : 2 ≤ n),
        H.presrelator_foxinitstrict_exactindegree
          (rels := rels) hmem hdepth n hn) →
      ∃ (N : ℕ) (a : ℕ → ℝ),
        (∀ n, 0 ≤ a n) ∧
        0 < a 0 ∧
        ∀ n, n ≤ GShafar.truncationWindow N depth → 0 ≤
          GShafar.truncatedSequence a N n
            - (H.generatorRank : ℝ) *
                (if 1 ≤ n then
                  GShafar.truncatedSequence a N (n - 1)
                else 0)
            + ∑ i, if depth i ≤ n then
                GShafar.truncatedSequence a N (n - depth i)
              else 0 := by
  intro rels depth hrels hmem hdepth_exact hdepth hstrict
  rcases H.presaug_hilbertsequence_finwindrecu
      _p_prime _isPGroup hrels hmem hdepth_exact hdepth hstrict with
    ⟨N, hrec⟩
  refine ⟨N, H.presentedHilbertSequence hrels, ?_, ?_, hrec⟩
  · exact H.pres_aughilbert_sequencenonneg hrels
  · exact H.presaug_hilbertsequence_zeropos _p_prime hrels

/--
The next Hilbert-series frontier: construct a finite nonnegative coefficient
sequence, with positive constant term, satisfying the truncated recurrence
associated to the chosen Zassenhaus depths.

Mathematically this is the augmentation-filtration dimension estimate in the
Golod--Shafarevich proof. It is smaller than the coefficientwise polynomial
witness because the passage from such a sequence to the polynomial witness is
now proved in `coefficientwise_hilbert_witness`.
-/
theorem PPDatum.trunc_hilbertrecurre_minpres
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier) :
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (hdepth_exact :
        ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1)) →
      (hdepth : ∀ i, 2 ≤ depth i) →
      (∀ n (hn : 2 ≤ n),
        H.presrelator_foxinitstrict_exactindegree
          (rels := rels) hmem hdepth n hn) →
      ∃ (N : ℕ) (a : ℕ → ℝ),
        (∀ n, 0 ≤ a n) ∧
        0 < a 0 ∧
        ∀ n, 0 ≤
          GShafar.truncatedSequence a N n
            - (H.generatorRank : ℝ) *
                (if 1 ≤ n then
                  GShafar.truncatedSequence a N (n - 1)
                else 0)
            + ∑ i, if depth i ≤ n then
                GShafar.truncatedSequence a N (n - depth i)
              else 0 := by
  intro rels depth hrels hmem hdepth_exact hdepth hstrict
  rcases H.fintrunc_hilbertrecurre_minpres
      _p_prime _isPGroup hrels hmem hdepth_exact hdepth hstrict with
    ⟨N, a, ha, ha0, hrec⟩
  refine ⟨N, a, ha, ha0, ?_⟩
  intro n
  by_cases hn : n ≤ GShafar.truncationWindow N depth
  · exact hrec n hn
  · have hzero :=
      GShafar.truncation_recurrence_window
        (a := a) (N := N) (d := H.generatorRank) (r := H.relationRank)
        (depth := depth) (n := n) (Nat.lt_of_not_ge hn)
    rw [hzero]

/--
The coefficientwise Hilbert-series witness expected from a minimal presentation
whose relators are assigned Zassenhaus depths. This is now the concentrated
frontier: it is a smaller statement than the bridge theorem because it no
longer mentions arbitrary `t`; it asks for the finite polynomial witness from
which positivity follows formally. The filtered Fox exactness needed for the
relator contribution is carried explicitly as a strictness hypothesis.
-/
theorem PPDatum.coeff_hilbertwitness_minpres
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier) :
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (hdepth_exact :
        ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1)) →
      (hdepth : ∀ i, 2 ≤ depth i) →
      (∀ n (hn : 2 ≤ n),
        H.presrelator_foxinitstrict_exactindegree
          (rels := rels) hmem hdepth n hn) →
      GShafar.CoefficientwiseHilbertWitness
        H.generatorRank H.relationRank depth := by
  intro rels depth hrels hmem hdepth_exact hdepth hstrict
  rcases H.trunc_hilbertrecurre_minpres
      _p_prime _isPGroup hrels hmem hdepth_exact hdepth hstrict with
    ⟨N, a, ha, ha0, hrec⟩
  exact
    GShafar.coefficientwise_hilbert_witness
      (d := H.generatorRank) (r := H.relationRank)
      (depth := depth) (a := a) (N := N) ha ha0 hrec

/--
The bridge theorem follows formally from the coefficientwise Hilbert-series
witness: this lemma removes the analytic part from the remaining group-algebra
work.
-/
theorem PPDatum.MinPreshilbertSeriesbridge
    (H : PPDatum)
    (_p_prime : Nat.Prime H.realizesFiniteNontrivial.p)
    [Finite H.realizesFiniteNontrivial.carrier]
    [Nontrivial H.realizesFiniteNontrivial.carrier]
    (_isPGroup : IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier) :
  ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
    ⦃depth : Fin H.relationRank → ℕ⦄,
      Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
      (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
      (hdepth_exact :
        ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1)) →
      (hdepth : ∀ i, 2 ≤ depth i) →
      (∀ n (hn : 2 ≤ n),
        H.presrelator_foxinitstrict_exactindegree
          (rels := rels) hmem hdepth n hn) →
      ∀ t : ℝ, 0 < t → t < 1 →
        0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  intro rels depth hrels hmem hdepth_exact hdepth hstrict t ht0 _ht1
  rcases H.coeff_hilbertwitness_minpres
      _p_prime _isPGroup hrels hmem hdepth_exact hdepth hstrict with
    ⟨P, hPcoeff, hPzero, hprodcoeff⟩
  exact
    GShafar.coefficientwise_hilbert_inequality
      (d := H.generatorRank)
      (r := H.relationRank)
      depth hdepth hPcoeff hPzero hprodcoeff t ht0


/--
To finish `MinPreshilbertSeriesbridge`, it is enough to produce the
classical coefficientwise Hilbert-series inequality for each minimal relator
family with chosen depths.

The remaining frontier is therefore very explicit: build a polynomial witness
`P` with nonnegative coefficients and positive constant term such that every
coefficient of
`(1 - dX + Σ_i X^(depth i)) * P`
is nonnegative.
-/
theorem
    PPDatum.hilbertbridge_presaug_finrecurrence
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          ∃ N : ℕ,
            ∀ n ≤ N + max 1 (Finset.univ.sup depth), 0 ≤
              GShafar.truncatedSequence
                  (H.pres_aug_quotsequence (rels := rels) hrels) N n
                - (H.generatorRank : ℝ) *
                    (if 1 ≤ n then
                      GShafar.truncatedSequence
                        (H.pres_aug_quotsequence (rels := rels) hrels) N (n - 1)
                    else 0)
                + ∑ i, if depth i ≤ n then
                    GShafar.truncatedSequence
                      (H.pres_aug_quotsequence (rels := rels) hrels) N (n - depth i)
                  else 0) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine H.minpres_hilbseribrid_presaugrecu ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, hrec⟩
  refine ⟨N, ?_⟩
  intro n
  by_cases hn : n ≤ N + max 1 (Finset.univ.sup depth)
  · exact hrec n hn
  · have hzero :=
      GShafar.truncation_recurrence_window
        (a := H.pres_aug_quotsequence (rels := rels) hrels)
        (N := N) (d := H.generatorRank) (r := H.relationRank) (depth := depth)
        (n := n) (Nat.lt_of_not_ge hn)
    simp only [mul_ite, mul_zero, ge_iff_le] at hzero ⊢
    rw [hzero]

/-
To finish the Hilbert-series bridge, it is enough to verify a finite family of
explicit dimension inequalities for the concrete presented augmentation
quotients `B / I^(n + 2)`.

This removes the remaining abstraction of `truncatedSequence`: the open step is
now a finite-window linear-algebra statement relating the dimensions of the
quotients `B / I^(k)` indexed by `n`, `n - 1`, and `n - depth i`.
-/
theorem
    PPDatum.hilbertbridge_presaugfin_windowdimineq
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          ∃ N : ℕ,
            ∀ n ≤ N + max 1 (Finset.univ.sup depth),
              H.generatorRank * (if 1 ≤ n then
                  if n - 1 ≤ N then
                    H.pres_aug_quotfinrank (rels := rels) hrels (n - 1)
                  else 0
                else 0) ≤
                (if n ≤ N then
                    H.pres_aug_quotfinrank (rels := rels) hrels n
                  else 0) +
                  ∑ i, if depth i ≤ n then
                    if n - depth i ≤ N then
                      H.pres_aug_quotfinrank
                        (rels := rels) hrels (n - depth i)
                    else 0
                  else 0) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine H.hilbertbridge_presaug_finrecurrence ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, hdim⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hdim' :
      (H.generatorRank : ℝ) * (if 1 ≤ n then
            if n - 1 ≤ N then
              (H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) : ℝ)
            else 0
          else 0) ≤
        (if n ≤ N then
              (H.pres_aug_quotfinrank (rels := rels) hrels n : ℝ)
            else 0) +
            ∑ i, if depth i ≤ n then
              if n - depth i ≤ N then
                (H.pres_aug_quotfinrank (rels := rels) hrels (n - depth i) : ℝ)
              else 0
            else 0 := by
    exact_mod_cast hdim n hn
  have hrec' :
      0 ≤
        (if n ≤ N then
            (H.pres_aug_quotfinrank (rels := rels) hrels n : ℝ)
          else 0) -
          (H.generatorRank : ℝ) * (if 1 ≤ n then
            if n - 1 ≤ N then
              (H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) : ℝ)
            else 0
          else 0) +
          ∑ i, if depth i ≤ n then
            if n - depth i ≤ N then
              (H.pres_aug_quotfinrank (rels := rels) hrels (n - depth i) : ℝ)
            else 0
          else 0 := by
    nlinarith
  simpa [PPDatum.pres_aug_quotsequence,
    GShafar.truncatedSequence] using hrec'

/-
It is enough to prove the previous finite-window dimension inequalities by
constructing a surjective linear map whose source and target have exactly the
required quotient dimensions.

This isolates the remaining Hilbert-series step as an explicit finite-dimensional
linear-algebra problem: for each `n` in the active window, choose finite
`𝔽_p`-vector spaces matching the truncated quotient dimensions and surject onto
`generatorRank` copies of the previous one.
-/
theorem
    PPDatum.finrankpresaug_activetargetle_sourassesurj
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ)
    (Γ : H.pres_aug_gencomponents hrels n)
    (Φ : H.pres_aug_relatorcompone (depth := depth) hrels n)
    (hf : Function.Surjective (H.pres_aug_assembledmap hrels n Γ Φ)) :
    Module.finrank (ZMod H.realizesFiniteNontrivial.p)
        (H.pres_aug_activetarget (rels := rels) hrels n) ≤
      Module.finrank (ZMod H.realizesFiniteNontrivial.p)
        (H.pres_aug_activesource (rels := rels) hrels depth n) := by
  exact
    H.finrankpres_augactivetarget_lesourcesurj
      hrels n (H.pres_aug_assembledmap hrels n Γ Φ) hf

/--
Once the relator-side correction maps are chosen, surjectivity of the assembled
map with the canonical generator factors already implies the exact concrete
coefficient inequality for the active augmentation quotients.
-/
theorem
    PPDatum.hilbertbridge_presaug_windowdimineq
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          ∃ N : ℕ,
            (∀ n, 1 ≤ n → n ≤ N →
              H.generatorRank *
                  H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) ≤
                H.pres_aug_quotfinrank (rels := rels) hrels n +
                  ∑ i, if depth i ≤ n then
                    H.pres_aug_quotfinrank
                      (rels := rels) hrels (n - depth i)
                  else 0) ∧
              H.generatorRank *
                  H.pres_aug_quotfinrank (rels := rels) hrels N ≤
                ∑ i, if depth i ≤ N + 1 then
                  H.pres_aug_quotfinrank
                    (rels := rels) hrels (N + 1 - depth i)
                else 0) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine
    H.hilbertbridge_presaugfin_windowdimineq
      ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, hmain, hboundary⟩
  refine ⟨N, ?_⟩
  intro n hn
  by_cases h0 : n = 0
  · subst h0
    simp
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0)
  by_cases hnN : n ≤ N
  · have hmain' := hmain n hn1 hnN
    have hnm1 : n - 1 ≤ N := le_trans (Nat.sub_le _ _) hnN
    have hsum :
        (∑ i, if depth i ≤ n then
            if n ≤ N + depth i then
              H.pres_aug_quotfinrank
                (rels := rels) hrels (n - depth i)
            else 0
          else 0) =
          ∑ i, if depth i ≤ n then
            H.pres_aug_quotfinrank
              (rels := rels) hrels (n - depth i)
          else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hdi : depth i ≤ n
      · have hsub : n ≤ N + depth i := le_trans hnN (Nat.le_add_right _ _)
        simp [hdi, hsub]
      · simp [hdi]
    have hleft :
        H.generatorRank * (if 1 ≤ n then
            if n - 1 ≤ N then
              H.pres_aug_quotfinrank (rels := rels) hrels (n - 1)
            else 0
          else 0) =
          H.generatorRank *
            H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) := by
      simp [hn1, hnm1]
    have hright :
        ((if n ≤ N then
            H.pres_aug_quotfinrank (rels := rels) hrels n
          else 0) +
            ∑ i, if depth i ≤ n then
              if n - depth i ≤ N then
                H.pres_aug_quotfinrank
                  (rels := rels) hrels (n - depth i)
              else 0
            else 0) =
          (H.pres_aug_quotfinrank (rels := rels) hrels n +
            ∑ i, if depth i ≤ n then
              H.pres_aug_quotfinrank
                (rels := rels) hrels (n - depth i)
            else 0) := by
      simp [hnN, hsum]
    rw [hleft, hright]
    exact hmain'
  · have hsplit : n = N + 1 ∨ N + 2 ≤ n := by
      omega
    cases hsplit with
    | inl hsucc =>
        subst hsucc
        have hsum :
            (∑ i, if depth i ≤ N + 1 then
                if 1 ≤ depth i then
                  H.pres_aug_quotfinrank
                    (rels := rels) hrels (N + 1 - depth i)
                else 0
              else 0) =
              ∑ i, if depth i ≤ N + 1 then
                H.pres_aug_quotfinrank
                  (rels := rels) hrels (N + 1 - depth i)
              else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hdi : depth i ≤ N + 1
          · have hpos : 1 ≤ depth i := le_trans (by decide : 1 ≤ 2) (hdepth i)
            simp [hdi, hpos]
          · simp [hdi]
        have hleft :
            H.generatorRank * (if 1 ≤ N + 1 then
                if N + 1 - 1 ≤ N then
                  H.pres_aug_quotfinrank (rels := rels) hrels (N + 1 - 1)
                else 0
              else 0) =
              H.generatorRank *
                H.pres_aug_quotfinrank (rels := rels) hrels N := by
          simp
        have hright :
            ((if N + 1 ≤ N then
                H.pres_aug_quotfinrank (rels := rels) hrels (N + 1)
              else 0) +
                ∑ i, if depth i ≤ N + 1 then
                  if N + 1 - depth i ≤ N then
                    H.pres_aug_quotfinrank
                      (rels := rels) hrels (N + 1 - depth i)
                  else 0
                else 0) =
              (∑ i, if depth i ≤ N + 1 then
                H.pres_aug_quotfinrank
                  (rels := rels) hrels (N + 1 - depth i)
              else 0) := by
          simp [hsum]
        rw [hleft, hright]
        exact hboundary
    | inr hbig =>
        have hnm1 : ¬ n - 1 ≤ N := by
          omega
        have hleft :
            H.generatorRank * (if 1 ≤ n then
                if n - 1 ≤ N then
                  H.pres_aug_quotfinrank (rels := rels) hrels (n - 1)
                else 0
              else 0) = 0 := by
          simp [hn1, hnm1]
        have hright :
            ((if n ≤ N then
                H.pres_aug_quotfinrank (rels := rels) hrels n
              else 0) +
                ∑ i, if depth i ≤ n then
                  if n - depth i ≤ N then
                    H.pres_aug_quotfinrank
                      (rels := rels) hrels (n - depth i)
                  else 0
                else 0) =
              (∑ i, if depth i ≤ n then
                if n - depth i ≤ N then
                  H.pres_aug_quotfinrank
                    (rels := rels) hrels (n - depth i)
                else 0
              else 0) := by
          simp [hnN]
        rw [hleft, hright]
        exact Nat.zero_le _

/-
The Hilbert-series bridge now reduces to two explicit finite tasks:
construct canonical-map surjections for the positive indices `n ≤ N`, and
separately discharge the single boundary inequality at `n = N + 1`.
-/
theorem
    PPDatum.hilbertbridge_canonmap_surjupbound
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          ∃ N : ℕ,
            (∀ n, 1 ≤ n → n ≤ N →
              ∃ Ψ :
                H.PresAugRelatorcoeffs
                  (rels := rels) (depth := depth) n,
                Function.Surjective
                  (H.pres_aug_canonmap hrels n
                    (H.one_ledepth_activerelator (depth := depth) (n := n) hdepth) Ψ)) ∧
              H.generatorRank *
                  H.pres_aug_quotfinrank (rels := rels) hrels N ≤
                ∑ i, if depth i ≤ N + 1 then
                  H.pres_aug_quotfinrank
                    (rels := rels) hrels (N + 1 - depth i)
                else 0) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine
    H.hilbertbridge_presaug_windowdimineq
      ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, hsurj, hboundary⟩
  refine ⟨N, ?_, hboundary⟩
  intro n hn1 hnN
  rcases hsurj n hn1 hnN with ⟨Ψ, hΨ⟩
  exact
    H.presaug_dimineq_canonmapsurj
      hrels n
      (H.one_ledepth_activerelator (depth := depth) (n := n) hdepth) Ψ hΨ

/-
The single boundary inequality at `n = N + 1` can itself be supplied by a
surjective relator-only map, leaving the remaining work as explicit
surjectivity constructions on named quotient spaces.
-/
theorem
    PPDatum.hilbertbridge_canonmapsurj_relabounsurj
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          ∃ N : ℕ,
            (∀ n, 1 ≤ n → n ≤ N →
              ∃ Ψ :
                H.PresAugRelatorcoeffs
                  (rels := rels) (depth := depth) n,
                Function.Surjective
                  (H.pres_aug_canonmap hrels n
                    (H.one_ledepth_activerelator (depth := depth) (n := n) hdepth) Ψ)) ∧
              ∃ Φ : H.pres_aug_relatorcompone (depth := depth) hrels (N + 1),
                Function.Surjective (H.pres_aug_relatormap hrels (N + 1) Φ)) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine
    H.hilbertbridge_canonmap_surjupbound
      ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, hsurj, Φ, hΦ⟩
  refine ⟨N, hsurj, ?_⟩
  exact
    H.presaug_bounddimineq_relatormapsurj
      hrels (N + 1) Φ hΦ

/--
A canonical finite cutoff for the remaining Golod--Shafarevich surjectivity
tasks: the maximal declared relator depth.
-/
theorem
    PPDatum.hilbert_bridgecanon_windowwitnesses
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          H.PresAugcanonWindowwitness
              (rels := rels) (depth := depth) hrels hdepth ×
            H.PresAugcanonBoundwitness
              (rels := rels) (depth := depth) hrels) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine
    H.hilbertbridge_canonmapsurj_relabounsurj
      ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨window, boundary⟩
  refine ⟨H.pres_aug_canonwindow (depth := depth), ?_, ?_⟩
  · intro n hn1 hnN
    exact ⟨window.coeff n hn1 hnN, window.surj n hn1 hnN⟩
  · refine ⟨boundary.components, ?_⟩
    simpa [PPDatum.pres_aug_canonbound] using
      boundary.surj

/--
The final Hilbert-series bridge can be reduced all the way to surjectivity of
specifically named canonical window and boundary maps attached to fixed
candidate data.
-/
def PPDatum.StrictMinpresZassdepths
    (H : PPDatum) : Prop :=
  ∃ rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank),
    Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) ∧
    ∃ depth : Fin H.relationRank → ℕ,
      ∃ hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i),
      (∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1)) ∧
      ∃ hdepth : ∀ i, 2 ≤ depth i,
        ∀ n (hn : 2 ≤ n),
          H.presrelator_foxinitstrict_exactindegree
            (rels := rels) hmem hdepth n hn

/--
Combining a concrete minimal presentation with declared Zassenhaus depths and
the Hilbert-series bridge above yields the exact witness currently packaged as
`H.PRSeries`.
-/
theorem PPDatum.posrel_seriesmin_presbridge
    (H : PPDatum)
    (hpres : H.StrictMinpresZassdepths) :
    H.PRSeries := by
  rcases hpres with ⟨rels, hrels, depth, hmem, hdepth_exact, hdepth, hstrict⟩
  have hp : Nat.Prime H.realizesFiniteNontrivial.p := by
    exact Fact.out
  have hPGroup :
      IsPGroup H.realizesFiniteNontrivial.p H.realizesFiniteNontrivial.carrier :=
    H.realizesFiniteNontrivial.isPGroup
  refine ⟨depth, hdepth, ?_⟩
  intro t ht0 ht1
  exact H.MinPreshilbertSeriesbridge
    hp hPGroup hrels hmem hdepth_exact hdepth hstrict t ht0 ht1

/--
Combining the mod-`p` abelianization control of minimal relators with the
Hilbert-series bridge yields the desired positive relation-series witness.
-/
theorem PPDatum.posrel_seriesrelator_abelianidvd
    (H : PPDatum)
    (_hdiv : H.MinrelatorsHavepDvdabeliani)
    (hpres : H.StrictMinpresZassdepths) :
    H.PRSeries := by
  exact H.posrel_seriesmin_presbridge hpres

/--
Once minimal relators are known to vanish in the mod-`p` abelianization of the
free group, the only remaining input is the Hilbert-series bridge from their
Zassenhaus depths.
-/
theorem PPDatum.posrel_serirelamod_pabelvani
    (H : PPDatum)
    (_hzero : H.MinrelatorsHavevanishingModpabeliani)
    (hpres : H.StrictMinpresZassdepths) :
    H.PRSeries := by
  exact H.posrel_seriesmin_presbridge hpres

/--
The mod-`p` abelianization step is now internal to the current finite `p`-group
presentation model, so the Hilbert-series bridge alone yields the desired
positive relation-series witness.
-/
theorem PPDatum.posrel_serieshilbert_seriesbridge
    (H : PPDatum)
    (hpres : H.StrictMinpresZassdepths) :
    H.PRSeries := by
  exact
    H.posrel_serirelamod_pabelvani
      H.minrelators_havevanishing_modpabeliani hpres

/--
The previous reduction packages the final open Golod--Shafarevich step in the
most concrete form currently supported by the local codebase: a minimal
presentation, Zassenhaus depth bounds for its relators, and the Hilbert-series
positivity theorem for that data.
-/
theorem golod_shafarevich_inequality
    (H : PPDatum)
    (hpres : H.StrictMinpresZassdepths) :
    (H.relationRank : ℝ) > (H.generatorRank : ℝ) ^ (2 : ℕ) / 4 := by
  apply golod_shafarevich_bounds
  exact
    GShafar.pos_positive_witness
      (H.posrel_seriesmin_presbridge hpres)

/--
The depth-counted Golod--Shafarevich relation-series input implies the desired strict
quadratic inequality.

What remains open is to construct `H.PRSeries` from a minimal
presentation and the classical Hilbert-series argument.
-/
theorem golod_shafarevich_divisible
    (H : PPDatum)
    (hdiv : H.MinrelatorsHavepDvdabeliani)
    (hpres : H.StrictMinpresZassdepths) :
    (H.relationRank : ℝ) > (H.generatorRank : ℝ) ^ (2 : ℕ) / 4 := by
  apply golod_shafarevich_pro
  exact H.posrel_seriesrelator_abelianidvd hdiv hpres

/--
This is the sharpest current reduction for the minimal-relator input:
show that each relator dies in the elementary abelian Frattini quotient, and
the rest of the local Golod--Shafarevich machinery takes over.
-/
theorem golod_shafarevich_vanishing
    (H : PPDatum)
    (hzero : H.MinrelatorsHavevanishingModpabeliani)
    (hpres : H.StrictMinpresZassdepths) :
    (H.relationRank : ℝ) > (H.generatorRank : ℝ) ^ (2 : ℕ) / 4 := by
  apply golod_shafarevich_pro
  exact H.posrel_serirelamod_pabelvani hzero hpres

/--
The final remaining external Golod--Shafarevich ingredient in this file is now
exactly the Hilbert-series bridge from minimal presentations with Zassenhaus
depths to positivity of the relation series.
-/
theorem golod_shafarevich_bridge
    (H : PPDatum)
    (hpres : H.StrictMinpresZassdepths) :
    (H.relationRank : ℝ) > (H.generatorRank : ℝ) ^ (2 : ℕ) / 4 := by
  apply golod_shafarevich_pro
  exact H.posrel_serieshilbert_seriesbridge hpres

end Towers
