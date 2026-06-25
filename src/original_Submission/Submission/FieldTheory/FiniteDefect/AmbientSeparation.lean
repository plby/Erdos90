import Submission.FieldTheory.FiniteDefect.StageObstructionPersistence
import Submission.Group.FiniteQuotientTower.AmbientSeparation
import Submission.Group.FinitePRelator.KernelCofinalFamilies


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PRFact

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The kernel invisible to all honest finite kernel-image quotient maps from the
initial free pro-`3` group.
-/
def InitialAmbientResidual :
    Subgroup initialKochFree.Carrier :=
  InitialKochSystem.pullbackAmbientKernel
    initialKochQuotient
    initialKochFactor

/--
The honest ambient residual kernel is the literal intersection of the honest
finite kernel-image ambient quotient kernels.
-/
lemma s_inf_kernels :
    InitialAmbientResidual =
      sInf (Set.range fun n : ℕ =>
        (initialKochImage n).ker) := by
  unfold InitialAmbientResidual
  unfold Group.cSQuotie.pullbackAmbientKernel
  unfold Group.cSQuotie.ambientKernel
  apply congrArg sInf
  ext K
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, congrArg (fun φ => φ.ker)
      (initial_image_comp n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, congrArg (fun φ => φ.ker)
      (initial_image_comp n)⟩

/--
Membership in the honest ambient residual kernel is pointwise triviality in
every honest finite kernel-image quotient.
-/
lemma image_ambient_residual
    (x : initialKochFree.Carrier) :
    x ∈ InitialAmbientResidual ↔
      ∀ n : ℕ, initialKochImage n x = 1 := by
  rw [InitialAmbientResidual,
    InitialKochSystem.pullback_ambient_kernel]
  exact forall_congr' fun n => by
    have hfactor := DFunLike.congr_fun
      (initial_image_comp n)
      x
    change initialKochFactor n (initialKochQuotient x) =
      initialKochImage n x at hfactor
    constructor
    · intro hleft
      exact hfactor.symm.trans hleft
    · intro hright
      exact hfactor.trans hright

/--
The honest finite kernel-image quotient factors themselves separate every
nonidentity element of the actual initial Galois group.
-/
lemma initial_koch_ne
    (D : KRData)
    (y : initialGaloisGroup)
    (hy : y ≠ 1) :
    ∃ n : ℕ, initialKochFactor n y ≠ 1 := by
  rcases D.initial_shadow_ne hy with
    ⟨n, hn⟩
  change initialKochFactor n y ≠ 1 at hn
  exact ⟨n, hn⟩

/--
The honest finite kernel-image ambient quotient maps recover exactly the actual
initial Koch kernel.
-/
lemma initial_ambient_residual
    (D : KRData) :
    initialKochQuotient.ker =
      InitialAmbientResidual := by
  exact InitialKochSystem.quotient_separates_nontrivial
    initialKochQuotient
    initialKochFactor
    D.initial_koch_ne

/--
Every word outside the actual initial Koch kernel survives in one honest finite
kernel-image ambient quotient.
-/
lemma initial_koch_fin
    (D : KRData)
    {x : initialKochFree.Carrier}
    (hx : x ∉ initialKochQuotient.ker) :
    ∃ n : ℕ, initialKochImage n x ≠ 1 := by
  rcases InitialKochSystem.pullback_coord_not
      initialKochQuotient
      initialKochFactor
      D.initial_koch_ne
      hx with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro hquotient
  apply hn
  have hfactor := DFunLike.congr_fun
    (initial_image_comp n)
    x
  change initialKochFactor n (initialKochQuotient x) =
    initialKochImage n x at hfactor
  exact hfactor.trans hquotient

/--
The kernel invisible to all corrected canonical finite defect ambient quotient
maps from the initial free pro-`3` group.
-/
def CanonicalDefectAmbient
    (D : KRData) :
    Subgroup initialKochFree.Carrier :=
  D.CanonicalDefectSystem.pullbackAmbientKernel
    initialKochQuotient
    D.canonicalDefectFactor

/--
The corrected canonical finite defect ambient residual kernel is the literal
intersection of the corrected ambient quotient kernels.
-/
lemma ambient_inf_kernels
    (D : KRData) :
    D.CanonicalDefectAmbient =
      sInf (Set.range fun n : ℕ =>
        (D.canonicalDefectAmbient n).ker) := by
  rfl

/--
Membership in the corrected canonical finite defect ambient residual kernel is
pointwise triviality in every corrected ambient quotient.
-/
lemma canonical_defect_ambient
    (D : KRData)
    (x : initialKochFree.Carrier) :
    x ∈ D.CanonicalDefectAmbient ↔
      ∀ n : ℕ, D.canonicalDefectAmbient n x = 1 := by
  exact D.CanonicalDefectSystem.pullback_ambient_kernel
    initialKochQuotient
    D.canonicalDefectFactor
    x

/--
The corrected canonical finite defect quotient factors themselves separate
every nonidentity element of the actual initial Galois group.
-/
lemma canonical_defect_ne
    (D : KRData)
    (y : initialGaloisGroup)
    (hy : y ≠ 1) :
    ∃ n : ℕ, D.canonicalDefectFactor n y ≠ 1 := by
  rcases D.defect_shadow_ne hy with
    ⟨n, hn⟩
  change D.canonicalDefectFactor n y ≠ 1 at hn
  exact ⟨n, hn⟩

/--
Unconditionally, the corrected canonical finite defect ambient quotient maps
recover exactly the actual initial Koch kernel.
-/
lemma defect_ambient_residual
    (D : KRData) :
    initialKochQuotient.ker =
      D.CanonicalDefectAmbient := by
  exact D.CanonicalDefectSystem.quotient_separates_nontrivial
    initialKochQuotient
    D.canonicalDefectFactor
    D.canonical_defect_ne

/--
Every word outside the actual initial Koch kernel survives in one corrected
canonical finite defect ambient quotient.
-/
lemma koch_fin_defect
    (D : KRData)
    {x : initialKochFree.Carrier}
    (hx : x ∉ initialKochQuotient.ker) :
    ∃ n : ℕ, D.canonicalDefectAmbient n x ≠ 1 := by
  exact D.CanonicalDefectSystem.pullback_coord_not
    initialKochQuotient
    D.canonicalDefectFactor
    D.canonical_defect_ne
    hx

/--
The kernel invisible to all uncorrected canonical Zassenhaus finite relator
quotient maps from the initial free pro-`3` group.
-/
def RelatorResidualKernel
    (D : KRData) :
    Subgroup initialKochFree.Carrier :=
  sInf (Set.range fun n : ℕ =>
    (D.ZassenhausRelatorQuotient n).map.ker)

/--
The uncorrected canonical relator residual kernel lies in every canonical
Zassenhaus finite relator quotient kernel.
-/
lemma zassenhaus_residual_kernel
    (D : KRData)
    (n : ℕ) :
    D.RelatorResidualKernel ≤
      (D.ZassenhausRelatorQuotient n).map.ker := by
  exact sInf_le ⟨n, rfl⟩

/--
Membership in the uncorrected canonical relator residual kernel is pointwise
triviality in every canonical Zassenhaus finite relator quotient.
-/
lemma zassenhaus_relator_residual
    (D : KRData)
    (x : initialKochFree.Carrier) :
    x ∈ D.RelatorResidualKernel ↔
      ∀ n : ℕ, (D.ZassenhausRelatorQuotient n).map x = 1 := by
  constructor
  · intro hx n
    exact MonoidHom.mem_ker.mp
      (D.zassenhaus_residual_kernel n hx)
  · intro hx
    change x ∈ sInf (Set.range fun n : ℕ =>
      (D.ZassenhausRelatorQuotient n).map.ker)
    rw [Subgroup.mem_sInf]
    rintro K ⟨n, rfl⟩
    exact MonoidHom.mem_ker.mpr (hx n)

/--
The canonical Zassenhaus finite relator quotient tower is kernel-cofinal, so
its residual kernel is exactly the full finite `3` tame-relator residual
kernel.
-/
lemma relator_residual_kernel
    (D : KRData) :
    D.RelatorResidualKernel =
      relatorKernel 3 (initialTameRelator D.frobeniusLift) := by
  change OCQuotie.relatorFamilyKernel
      D.ZassenhausRelatorQuotient =
    relatorKernel 3 (initialTameRelator D.frobeniusLift)
  exact OCQuotie.relator_kernel_cofinal
    D.ZassenhausRelatorQuotient
    D.zassenhaus_relator_kernel

/--
Every word invisible to all uncorrected canonical relator quotients is already
invisible to every corrected canonical finite defect ambient quotient.
-/
lemma finDefectAmbient
    (D : KRData) :
    D.RelatorResidualKernel ≤
      D.CanonicalDefectAmbient := by
  rw [D.ambient_inf_kernels]
  apply le_sInf
  rintro K ⟨n, rfl⟩
  intro x hx
  apply MonoidHom.mem_ker.mpr
  have hxrelator := MonoidHom.mem_ker.mp
    (D.zassenhaus_residual_kernel n hx)
  have hambient := DFunLike.congr_fun
    (D.koch_fin_ambient
      n)
    x
  calc
    D.canonicalDefectAmbient n x =
        D.canonicalKochDefect n
          ((D.ZassenhausRelatorQuotient n).map x) := by
      simpa only [MonoidHom.comp_apply] using hambient
    _ = D.canonicalKochDefect n 1 :=
      congrArg (D.canonicalKochDefect n) hxrelator
    _ = 1 := map_one _

/--
Unconditionally, the kernel invisible to all uncorrected canonical relator
quotients is contained in the actual initial Koch kernel.
-/
lemma residual_initial_koch
    (D : KRData) :
    D.RelatorResidualKernel ≤
      initialKochQuotient.ker := by
  rw [D.defect_ambient_residual]
  exact D.finDefectAmbient

/--
Unconditionally, every word invisible to all finite `3`-group tame-relator
shadows already lies in the actual initial Koch kernel.
-/
lemma initial_koch_quotient
    (D : KRData) :
    relatorKernel 3 (initialTameRelator D.frobeniusLift) ≤
      initialKochQuotient.ker := by
  rw [← D.relator_residual_kernel]
  exact D.residual_initial_koch

/--
The desired finite quotient Koch theorem is exactly the assertion that the
uncorrected canonical relator quotient tower has residual kernel equal to the
actual initial Koch kernel.
-/
lemma fin_koch_factorization
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.RelatorResidualKernel =
        initialKochQuotient.ker := by
  constructor
  · intro hfactor
    apply le_antisymm
    · exact D.residual_initial_koch
    · apply le_sInf
      rintro K ⟨n, rfl⟩
      exact (D.fin_factorization_forall.mp
        hfactor)
        n
  · intro hkernel
    apply D.fin_factorization_forall.mpr
    intro n
    rw [← hkernel]
    exact D.zassenhaus_residual_kernel n

/--
Equivalently, the desired theorem says the actual initial Koch kernel is
exactly the full finite `3` tame-relator residual kernel.
-/
lemma koch_factorization_kernel
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      relatorKernel 3 (initialTameRelator D.frobeniusLift) =
        initialKochQuotient.ker := by
  rw [← D.relator_residual_kernel]
  exact D.fin_koch_factorization

/--
Using the algebraic finite-layer description of the finite relator residual
kernel, the desired theorem is exactly equality between the algebraic
finite-layer tame-relator kernel and the actual initial Koch kernel.
-/
lemma fin_factorization_kernel
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ONFact.algebraicOpenKernel
          (initialTameRelator D.frobeniusLift) =
        initialKochQuotient.ker := by
  rw [← D.relator_algebraic_layer]
  exact D.koch_factorization_kernel

/--
Equivalently, the desired theorem says the uncorrected canonical relator tower
and the corrected canonical finite defect ambient tower have the same residual
kernel in the initial free pro-`3` group.
-/
lemma fin_defect_ambient
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      D.RelatorResidualKernel =
        D.CanonicalDefectAmbient := by
  rw [D.fin_koch_factorization,
    D.defect_ambient_residual]

/--
Failure of the desired finite quotient Koch theorem is exactly existence of an
actual initial Koch kernel element outside the uncorrected canonical relator
residual kernel.
-/
lemma not_fin_koch
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ x : initialKochFree.Carrier,
        x ∈ initialKochQuotient.ker ∧
          x ∉ D.RelatorResidualKernel := by
  rw [D.fin_koch_factorization]
  constructor
  · intro hneq
    have hnotle :
        ¬ initialKochQuotient.ker ≤
          D.RelatorResidualKernel := by
      intro hle
      exact hneq (le_antisymm
        D.residual_initial_koch
        hle)
    rcases SetLike.not_le_iff_exists.mp hnotle with ⟨x, hxker, hxnot⟩
    exact ⟨x, hxker, hxnot⟩
  · rintro ⟨x, hxker, hxnot⟩ hkernel
    apply hxnot
    rw [hkernel]
    exact hxker

/--
Failure of the desired finite quotient Koch theorem is exactly existence of a
word killed by every corrected canonical finite defect ambient quotient but not
by the whole uncorrected canonical relator quotient tower.
-/
lemma not_koch_ambient
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ x : initialKochFree.Carrier,
        x ∈ D.CanonicalDefectAmbient ∧
          x ∉ D.RelatorResidualKernel := by
  rw [D.not_fin_koch]
  exact exists_congr fun x => by
    rw [D.defect_ambient_residual]

/--
Failure of the desired finite quotient Koch theorem is exactly existence of a
word trivial in every corrected canonical finite defect ambient quotient but
surviving in one uncorrected canonical relator quotient layer.
-/
lemma ambient_invisible_visible
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ x : initialKochFree.Carrier,
        (∀ n : ℕ, D.canonicalDefectAmbient n x = 1) ∧
          ∃ n : ℕ, (D.ZassenhausRelatorQuotient n).map x ≠ 1 := by
  rw [D.not_koch_ambient]
  exact exists_congr fun x => by
    rw [D.canonical_defect_ambient,
      D.zassenhaus_relator_residual]
    simp only [not_forall]

end KRData

end TBluepr
end Submission
