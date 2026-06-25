import Submission.Group.NilpotentProducts.GeneralBasis


/-!
# Generation of the arbitrary-rank equation-(18) coordinates

The unit coordinate axes generate the integral coordinate group.  The proof
successively eliminates each finite coordinate family.
-/

namespace Struik
namespace P1960

open Submission

section Elimination

variable {G : Type*} [Group G] {ι κ : Type*} [DecidableEq ι]

/-- Successively right-multiply by axes that kill the listed coordinates. -/
def eliminateCoordinates
    (coordinate : G → ι → ℤ) (axis : ι → ℤ → G) :
    List ι → G → G
  | [], c => c
  | i :: l, c =>
      eliminateCoordinates coordinate axis l
        (c * axis i (-coordinate c i))

private theorem eliminateCoordinates_coordinate
    (coordinate : G → ι → ℤ) (axis : ι → ℤ → G)
    (hmul :
      ∀ (c : G) (i : ι) (n : ℤ) (j : ι),
        coordinate (c * axis i n) j =
          coordinate c j + if j = i then n else 0)
    {l : List ι} (hl : l.Nodup) (c : G) (j : ι) :
    coordinate (eliminateCoordinates coordinate axis l c) j =
      if j ∈ l then 0 else coordinate c j := by
  induction l generalizing c with
  | nil =>
      simp [eliminateCoordinates]
  | cons i l ih =>
      have hil : i ∉ l := (List.nodup_cons.mp hl).1
      have hlnodup : l.Nodup := (List.nodup_cons.mp hl).2
      rw [eliminateCoordinates, ih hlnodup]
      by_cases hjl : j ∈ l
      · simp [hjl]
      · by_cases hji : j = i
        · subst j
          simp [hjl, hmul]
        · simp [hjl, hji, hmul]

omit [DecidableEq ι] in
private theorem eliminateCoordinates_preserves
    (coordinate : G → ι → ℤ) (axis : ι → ℤ → G)
    (other : G → κ)
    (hmul :
      ∀ (c : G) (i : ι) (n : ℤ),
        other (c * axis i n) = other c)
    (l : List ι) (c : G) :
    other (eliminateCoordinates coordinate axis l c) = other c := by
  induction l generalizing c with
  | nil =>
      rfl
  | cons i l ih =>
      rw [eliminateCoordinates, ih, hmul]

omit [DecidableEq ι] in
private theorem eliminate_coordinates
    (coordinate : G → ι → ℤ) (axis : ι → ℤ → G)
    (H : Subgroup G)
    (haxis : ∀ (i : ι) (n : ℤ), axis i n ∈ H)
    (l : List ι) (c : G) :
    eliminateCoordinates coordinate axis l c ∈ H ↔ c ∈ H := by
  induction l generalizing c with
  | nil =>
      rfl
  | cons i l ih =>
      rw [eliminateCoordinates, ih]
      exact H.mul_mem_cancel_right (haxis i _)

end Elimination

section CoordinateElimination

variable {t : ℕ}

private abbrev singleAxis (i : Fin t) (n : ℤ) :=
  generalAxis (.single i) n

private abbrev pairAxis (q : Pair t) (n : ℤ) :=
  generalAxis (.pair q) n

private abbrev pairLeftAxis (q : Pair t) (n : ℤ) :=
  generalAxis (.pairLeft q) n

private abbrev pairRightAxis (q : Pair t) (n : ℤ) :=
  generalAxis (.pairRight q) n

private abbrev tripleFirstAxis (q : Triple t) (n : ℤ) :=
  generalAxis (.tripleFirst q) n

private abbrev tripleSecondAxis (q : Triple t) (n : ℤ) :=
  generalAxis (.tripleSecond q) n

private theorem mul_single_axis
    (c : GCoordi t) (i : Fin t) (n : ℤ)
    (j : Fin t) :
    (c * singleAxis i n).single j =
      c.single j + if j = i then n else 0 := by
  rfl

private theorem pair_axis
    (c : GCoordi t) (q : Pair t) (n : ℤ)
    (r : Pair t) :
    (c * pairAxis q n).pair r =
      c.pair r + if r = q then n else 0 := by
  change
    (GCoordi.mul c
      (generalAxis (.pair q) n)).pair r =
        c.pair r + if r = q then n else 0
  simp [generalAxis,
    GCoordi.mul,
    GCoordi.zero]

private theorem pair_left_axis
    (c : GCoordi t) (q : Pair t) (n : ℤ)
    (r : Pair t) :
    (c * pairLeftAxis q n).pairLeft r =
      c.pairLeft r + if r = q then n else 0 := by
  change
    (GCoordi.mul c
      (generalAxis (.pairLeft q) n)).pairLeft r =
        c.pairLeft r + if r = q then n else 0
  simp [generalAxis,
    GCoordi.mul,
    GCoordi.zero]

private theorem mul_pair_axis
    (c : GCoordi t) (q : Pair t) (n : ℤ)
    (r : Pair t) :
    (c * pairRightAxis q n).pairRight r =
      c.pairRight r + if r = q then n else 0 := by
  change
    (GCoordi.mul c
      (generalAxis (.pairRight q) n)).pairRight r =
        c.pairRight r + if r = q then n else 0
  simp [generalAxis,
    GCoordi.mul,
    GCoordi.zero]

private theorem triple_first_axis
    (c : GCoordi t) (q : Triple t) (n : ℤ)
    (r : Triple t) :
    (c * tripleFirstAxis q n).tripleFirst r =
      c.tripleFirst r + if r = q then n else 0 := by
  change
    (GCoordi.mul c
      (generalAxis (.tripleFirst q) n)).tripleFirst r =
        c.tripleFirst r + if r = q then n else 0
  simp [generalAxis,
    GCoordi.mul,
    GCoordi.zero]

private theorem triple_second_axis
    (c : GCoordi t) (q : Triple t) (n : ℤ)
    (r : Triple t) :
    (c * tripleSecondAxis q n).tripleSecond r =
      c.tripleSecond r + if r = q then n else 0 := by
  change
    (GCoordi.mul c
      (generalAxis (.tripleSecond q) n)).tripleSecond r =
        c.tripleSecond r + if r = q then n else 0
  simp [generalAxis,
    GCoordi.mul,
    GCoordi.zero]

private theorem eliminate_pair_single
    (l : List (Pair t)) (c : GCoordi t) :
    (eliminateCoordinates
      GCoordi.pair pairAxis l c).single =
        c.single := by
  apply eliminateCoordinates_preserves
  intro d q n
  funext i
  change
    (GCoordi.mul d
      (generalAxis (.pair q) n)).single i =
        d.single i
  simp [generalAxis,
    GCoordi.mul,
    GCoordi.zero]

private theorem eliminate_pair_preserves
    (l : List (Pair t)) (c : GCoordi t) :
    ((eliminateCoordinates
      GCoordi.pairLeft pairLeftAxis l c).single,
        (eliminateCoordinates
          GCoordi.pairLeft pairLeftAxis l c).pair) =
      (c.single, c.pair) := by
  refine eliminateCoordinates_preserves
    GCoordi.pairLeft pairLeftAxis
    (fun d => (d.single, d.pair)) ?_ l c
  intro d q n
  apply Prod.ext
  · funext i
    change
      (GCoordi.mul d
        (generalAxis (.pairLeft q) n)).single i =
          d.single i
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]
  · funext r
    change
      (GCoordi.mul d
        (generalAxis (.pairLeft q) n)).pair r =
          d.pair r
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]

private theorem eliminate_preserves_single
    (l : List (Pair t)) (c : GCoordi t) :
    let d := eliminateCoordinates
      GCoordi.pairRight pairRightAxis l c
    (d.single, d.pair, d.pairLeft) =
      (c.single, c.pair, c.pairLeft) := by
  refine eliminateCoordinates_preserves
    GCoordi.pairRight pairRightAxis
    (fun d => (d.single, d.pair, d.pairLeft)) ?_ l c
  intro d q n
  ext i
  · change
      (GCoordi.mul d
        (generalAxis (.pairRight q) n)).single i =
          d.single i
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]
  · change
      (GCoordi.mul d
        (generalAxis (.pairRight q) n)).pair i =
          d.pair i
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]
  · change
      (GCoordi.mul d
        (generalAxis (.pairRight q) n)).pairLeft i =
          d.pairLeft i
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]

private theorem eliminate_triple_prior
    (l : List (Triple t)) (c : GCoordi t) :
    let d := eliminateCoordinates
      GCoordi.tripleFirst tripleFirstAxis l c
    (d.single, d.pair, d.pairLeft, d.pairRight) =
      (c.single, c.pair, c.pairLeft, c.pairRight) := by
  refine eliminateCoordinates_preserves
    GCoordi.tripleFirst tripleFirstAxis
    (fun d => (d.single, d.pair, d.pairLeft, d.pairRight)) ?_ l c
  intro d q n
  ext i
  · change
      (GCoordi.mul d
        (generalAxis (.tripleFirst q) n)).single i =
          d.single i
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]
  · change
      (GCoordi.mul d
        (generalAxis (.tripleFirst q) n)).pair i =
          d.pair i
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]
  · change
      (GCoordi.mul d
        (generalAxis (.tripleFirst q) n)).pairLeft i =
          d.pairLeft i
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]
  · change
      (GCoordi.mul d
        (generalAxis (.tripleFirst q) n)).pairRight i =
          d.pairRight i
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]

private theorem eliminate_preserves_prior
    (l : List (Triple t)) (c : GCoordi t) :
    let d := eliminateCoordinates
      GCoordi.tripleSecond tripleSecondAxis l c
    (d.single, d.pair, d.pairLeft, d.pairRight, d.tripleFirst) =
      (c.single, c.pair, c.pairLeft, c.pairRight, c.tripleFirst) := by
  refine eliminateCoordinates_preserves
    GCoordi.tripleSecond tripleSecondAxis
    (fun d =>
      (d.single, d.pair, d.pairLeft, d.pairRight, d.tripleFirst))
    ?_ l c
  intro d q n
  ext i
  · change
      (GCoordi.mul d
        (generalAxis (.tripleSecond q) n)).single i =
          d.single i
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]
  · change
      (GCoordi.mul d
        (generalAxis (.tripleSecond q) n)).pair i =
          d.pair i
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]
  · change
      (GCoordi.mul d
        (generalAxis (.tripleSecond q) n)).pairLeft i =
          d.pairLeft i
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]
  · change
      (GCoordi.mul d
        (generalAxis (.tripleSecond q) n)).pairRight i =
          d.pairRight i
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]
  · change
      (GCoordi.mul d
        (generalAxis (.tripleSecond q) n)).tripleFirst i =
          d.tripleFirst i
    simp [generalAxis,
      GCoordi.mul,
      GCoordi.zero]

/-- Every integral equation-(18) tuple belongs to any subgroup containing
all unit coordinate axes. -/
theorem general_coordinates_axes
    (H : Subgroup (GCoordi t))
    (haxis :
      ∀ i : GeneralBasisIndex t,
        generalAxis i 1 ∈ H)
    (c : GCoordi t) :
    c ∈ H := by
  classical
  have haxisZ :
      ∀ (i : GeneralBasisIndex t) (n : ℤ),
        generalAxis i n ∈ H := by
    intro i n
    rw [← general_axis_one]
    exact H.zpow_mem (haxis i) n
  let singleList := (Finset.univ : Finset (Fin t)).toList
  let pairList := (Finset.univ : Finset (Pair t)).toList
  let tripleList := (Finset.univ : Finset (Triple t)).toList
  let c₁ := eliminateCoordinates
    GCoordi.single singleAxis singleList c
  let c₂ := eliminateCoordinates
    GCoordi.pair pairAxis pairList c₁
  let c₃ := eliminateCoordinates
    GCoordi.pairLeft pairLeftAxis pairList c₂
  let c₄ := eliminateCoordinates
    GCoordi.pairRight pairRightAxis pairList c₃
  let c₅ := eliminateCoordinates
    GCoordi.tripleFirst tripleFirstAxis tripleList c₄
  let c₆ := eliminateCoordinates
    GCoordi.tripleSecond tripleSecondAxis tripleList c₅
  have hc₁single (i : Fin t) : c₁.single i = 0 := by
    dsimp [c₁, singleList]
    rw [eliminateCoordinates_coordinate
      GCoordi.single singleAxis
      mul_single_axis
      (Finset.univ.nodup_toList) c i]
    simp
  have hc₂single : c₂.single = c₁.single := by
    exact eliminate_pair_single pairList c₁
  have hc₂pair (q : Pair t) : c₂.pair q = 0 := by
    dsimp [c₂, pairList]
    rw [eliminateCoordinates_coordinate
      GCoordi.pair pairAxis
      pair_axis
      (Finset.univ.nodup_toList) c₁ q]
    simp
  have hc₃prior : (c₃.single, c₃.pair) = (c₂.single, c₂.pair) := by
    exact eliminate_pair_preserves pairList c₂
  have hc₃pairLeft (q : Pair t) : c₃.pairLeft q = 0 := by
    dsimp [c₃, pairList]
    rw [eliminateCoordinates_coordinate
      GCoordi.pairLeft pairLeftAxis
      pair_left_axis
      (Finset.univ.nodup_toList) c₂ q]
    simp
  have hc₄prior :
      (c₄.single, c₄.pair, c₄.pairLeft) =
        (c₃.single, c₃.pair, c₃.pairLeft) := by
    exact eliminate_preserves_single pairList c₃
  have hc₄pairRight (q : Pair t) : c₄.pairRight q = 0 := by
    dsimp [c₄, pairList]
    rw [eliminateCoordinates_coordinate
      GCoordi.pairRight pairRightAxis
      mul_pair_axis
      (Finset.univ.nodup_toList) c₃ q]
    simp
  have hc₅prior :
      (c₅.single, c₅.pair, c₅.pairLeft, c₅.pairRight) =
        (c₄.single, c₄.pair, c₄.pairLeft, c₄.pairRight) := by
    exact eliminate_triple_prior tripleList c₄
  have hc₅tripleFirst (q : Triple t) :
      c₅.tripleFirst q = 0 := by
    dsimp [c₅, tripleList]
    rw [eliminateCoordinates_coordinate
      GCoordi.tripleFirst tripleFirstAxis
      triple_first_axis
      (Finset.univ.nodup_toList) c₄ q]
    simp
  have hc₆prior :
      (c₆.single, c₆.pair, c₆.pairLeft, c₆.pairRight,
          c₆.tripleFirst) =
        (c₅.single, c₅.pair, c₅.pairLeft, c₅.pairRight,
          c₅.tripleFirst) := by
    exact eliminate_preserves_prior tripleList c₅
  have hc₆tripleSecond (q : Triple t) :
      c₆.tripleSecond q = 0 := by
    dsimp [c₆, tripleList]
    rw [eliminateCoordinates_coordinate
      GCoordi.tripleSecond tripleSecondAxis
      triple_second_axis
      (Finset.univ.nodup_toList) c₅ q]
    simp
  have hc₆ : c₆ = 1 := by
    change c₆ = GCoordi.zero t
    ext i
    · have h65 := congrArg (fun x => x.1) hc₆prior
      have h54 := congrArg (fun x => x.1) hc₅prior
      have h43 := congrArg (fun x => x.1) hc₄prior
      have h32 := congrArg (fun x => x.1) hc₃prior
      simp only at h65 h54 h43 h32
      rw [h65, h54, h43, h32, hc₂single]
      exact hc₁single i
    · have h65 := congrArg (fun x => x.2.1) hc₆prior
      have h54 := congrArg (fun x => x.2.1) hc₅prior
      have h43 := congrArg (fun x => x.2.1) hc₄prior
      have h32 := congrArg (fun x => x.2) hc₃prior
      simp only at h65 h54 h43 h32
      rw [h65, h54, h43, h32]
      exact hc₂pair i
    · have h65 := congrArg (fun x => x.2.2.1) hc₆prior
      have h54 := congrArg (fun x => x.2.2.1) hc₅prior
      have h43 := congrArg (fun x => x.2.2) hc₄prior
      simp only at h65 h54 h43
      rw [h65, h54, h43]
      exact hc₃pairLeft i
    · have h65 := congrArg (fun x => x.2.2.2.1) hc₆prior
      have h54 := congrArg (fun x => x.2.2.2) hc₅prior
      simp only at h65 h54
      rw [h65, h54]
      exact hc₄pairRight i
    · have h65 := congrArg (fun x => x.2.2.2.2) hc₆prior
      simp only at h65
      rw [h65]
      exact hc₅tripleFirst i
    · exact hc₆tripleSecond i
  have hc₆mem : c₆ ∈ H := by
    rw [hc₆]
    exact H.one_mem
  have hc₅mem : c₅ ∈ H := by
    exact (eliminate_coordinates
      GCoordi.tripleSecond tripleSecondAxis H
      (fun q n => haxisZ (.tripleSecond q) n)
      tripleList c₅).mp hc₆mem
  have hc₄mem : c₄ ∈ H := by
    exact (eliminate_coordinates
      GCoordi.tripleFirst tripleFirstAxis H
      (fun q n => haxisZ (.tripleFirst q) n)
      tripleList c₄).mp hc₅mem
  have hc₃mem : c₃ ∈ H := by
    exact (eliminate_coordinates
      GCoordi.pairRight pairRightAxis H
      (fun q n => haxisZ (.pairRight q) n)
      pairList c₃).mp hc₄mem
  have hc₂mem : c₂ ∈ H := by
    exact (eliminate_coordinates
      GCoordi.pairLeft pairLeftAxis H
      (fun q n => haxisZ (.pairLeft q) n)
      pairList c₂).mp hc₃mem
  have hc₁mem : c₁ ∈ H := by
    exact (eliminate_coordinates
      GCoordi.pair pairAxis H
      (fun q n => haxisZ (.pair q) n)
      pairList c₁).mp hc₂mem
  exact (eliminate_coordinates
    GCoordi.single singleAxis H
    (fun i n => haxisZ (.single i) n)
    singleList c).mp hc₁mem

end CoordinateElimination

end P1960
end Struik
