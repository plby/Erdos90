import Towers.Group.FiniteQuotientTower.KernelSeparation


noncomputable section

namespace Towers
namespace Group

universe u v w

namespace cSQuotie

variable
    (S : cSQuotie.{u})
    {F : Type v}
    {G : Type w}
    [Group F]
    [Group G]

/--
The subgroup of a source group invisible to every coordinate of one family of
maps into a compatible finite quotient tower.
-/
def ambientKernel
    (f : ∀ n : ℕ, F →* S.obj n) :
    Subgroup F :=
  sInf (Set.range fun n : ℕ => (f n).ker)

/--
The ambient kernel lies in the kernel of every finite-level coordinate.
-/
lemma ambient_kernel
    (f : ∀ n : ℕ, F →* S.obj n)
    (n : ℕ) :
    S.ambientKernel f ≤ (f n).ker := by
  exact sInf_le ⟨n, rfl⟩

/--
Membership in an ambient tower kernel is exactly coordinatewise triviality.
-/
lemma mem_ambient_iff
    (f : ∀ n : ℕ, F →* S.obj n)
    (x : F) :
    x ∈ S.ambientKernel f ↔ ∀ n : ℕ, f n x = 1 := by
  constructor
  · intro hx n
    exact MonoidHom.mem_ker.mp (S.ambient_kernel f n hx)
  · intro hx
    change x ∈ sInf (Set.range fun n : ℕ => (f n).ker)
    rw [Subgroup.mem_sInf]
    rintro K ⟨n, rfl⟩
    exact MonoidHom.mem_ker.mpr (hx n)

/--
A family of finite-level coordinates separates nonidentity source elements
exactly when its ambient kernel is trivial.
-/
lemma ambient_separates_nontrivial
    (f : ∀ n : ℕ, F →* S.obj n) :
    S.ambientKernel f = ⊥ ↔
      ∀ x : F, x ≠ 1 → ∃ n : ℕ, f n x ≠ 1 := by
  constructor
  · intro hkernel x hxne
    by_contra hnot
    push Not at hnot
    apply hxne
    exact Subgroup.mem_bot.mp (hkernel ▸ (S.mem_ambient_iff f x).mpr hnot)
  · intro hseparates
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_bot]
      by_contra hxne
      rcases hseparates x hxne with ⟨n, hn⟩
      exact hn ((S.mem_ambient_iff f x).mp hx n)
    · exact bot_le

/--
The pullback to an ambient source of the subgroup invisible to every
finite-level coordinate of a quotient target.
-/
def pullbackAmbientKernel
    (q : F →* G)
    (f : ∀ n : ℕ, G →* S.obj n) :
    Subgroup F :=
  S.ambientKernel fun n : ℕ => (f n).comp q

/--
The kernel of the ambient quotient map lies in every pulled-back finite-level
coordinate kernel.
-/
lemma quotient_pullback_ambient
    (q : F →* G)
    (f : ∀ n : ℕ, G →* S.obj n) :
    q.ker ≤ S.pullbackAmbientKernel q f := by
  rw [pullbackAmbientKernel]
  apply le_sInf
  rintro K ⟨n, rfl⟩
  intro x hx
  apply MonoidHom.mem_ker.mpr
  change f n (q x) = 1
  rw [MonoidHom.mem_ker.mp hx]
  exact map_one _

/--
Membership in a pulled-back ambient tower kernel is exactly triviality after
the ambient quotient map in every finite-level coordinate.
-/
lemma pullback_ambient_kernel
    (q : F →* G)
    (f : ∀ n : ℕ, G →* S.obj n)
    (x : F) :
    x ∈ S.pullbackAmbientKernel q f ↔
      ∀ n : ℕ, f n (q x) = 1 := by
  exact S.mem_ambient_iff (fun n : ℕ => (f n).comp q) x

/--
If the finite-level coordinates separate the quotient target, then their
pulled-back ambient kernel is contained in the original quotient kernel.
-/
lemma pullback_separates_nontrivial
    (q : F →* G)
    (f : ∀ n : ℕ, G →* S.obj n)
    (hseparates : ∀ y : G, y ≠ 1 → ∃ n : ℕ, f n y ≠ 1) :
    S.pullbackAmbientKernel q f ≤ q.ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  by_contra hxq
  rcases hseparates (q x) hxq with ⟨n, hn⟩
  exact hn ((S.pullback_ambient_kernel q f x).mp hx n)

/--
Finite-level coordinates separating the quotient target recover the original
ambient quotient kernel exactly after pullback.
-/
lemma quotient_separates_nontrivial
    (q : F →* G)
    (f : ∀ n : ℕ, G →* S.obj n)
    (hseparates : ∀ y : G, y ≠ 1 → ∃ n : ℕ, f n y ≠ 1) :
    q.ker = S.pullbackAmbientKernel q f := by
  apply le_antisymm
  · exact S.quotient_pullback_ambient q f
  · exact S.pullback_separates_nontrivial
      q f hseparates

/--
An ambient element outside the original quotient kernel is detected by one
finite-level coordinate whenever those coordinates separate the quotient.
-/
lemma pullback_coord_not
    (q : F →* G)
    (f : ∀ n : ℕ, G →* S.obj n)
    (hseparates : ∀ y : G, y ≠ 1 → ∃ n : ℕ, f n y ≠ 1)
    {x : F}
    (hx : x ∉ q.ker) :
    ∃ n : ℕ, f n (q x) ≠ 1 := by
  apply hseparates (q x)
  intro hxq
  exact hx (MonoidHom.mem_ker.mpr hxq)

end cSQuotie

end Group
end Towers
