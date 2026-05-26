import Mathlib
import LeanPlanarGraphs.ListColoring
import LeanPlanarGraphs.CombinatorialMap
import LeanPlanarGraphs.PlanarGraph
import LeanPlanarGraphs.MaxPlaneIffTriang

variable {V : Type} [Fintype V] [DecidableEq V]

/-
-- alternate formulation of Thomassen 1994
theorem IsPlanar_imp_fiveListColorable (G : SimpleGraph V) [DecidableRel G.Adj]
(hG : IsPlanar G) : G.ListColorable 5 := by
  sorry
-/


/-- G has at least three vertices/C contains at least three vertices, G has one face bounded by
vertices in C, and all other faces are triangles
Note: `(G.cm.Φ.cycleOf d₀).support.image (fun d => d.fst) = C.toFinset` is a set equality so we lose
the cyclic ordering, this might need fixing -/
def PlanarGraph.isCycleAndTriangles (G : PlanarGraph V) (C : List V) : Prop :=
  -- Below could propably be derived from `C.Nodup ∧ C.length ≥ 3`
  -- G.cm.σ.cycleType.card + (Fintype.card G.og.Dart - G.cm.σ.support.card) ≥ 3 -- safety first
  C.Nodup
  ∧ C.length ≥ 3
  ∧ ∃ d₀ : G.og.Dart, (G.cm.Φ.cycleOf d₀).support.image (fun d => d.fst) = C.toFinset
          ∧ ∀ d : G.og.Dart, d ∉ (G.cm.Φ.cycleOf d₀).support →
          (G.cm.Φ.cycleOf d).support.card = 3

/-- Just checks all possible combinations for being consecutive -/
def areConsecutive (C : List V) (u v : V) : Prop :=
  (∃ i, C[i]? = some u ∧ C[i + 1]? = some v) ∨
  (∃ i, C[i]? = some v ∧ C[i + 1]? = some u) ∨
  (C.head? = some u ∧ C.getLast? = some v) ∨
  (C.head? = some v ∧ C.getLast? = some u)

def hasChord (G : PlanarGraph V) (C : List V) : Prop :=
  ∃ u v : V, u ∈ C ∧ v ∈ C ∧ G.og.Adj u v ∧ ¬ areConsecutive C u v

/-- This pulls out the `n : ℕ` from `PlanarGraph.isCycleAndTriangles` to perform induction -/
theorem listColor_isCycleAndTriangles' (n : ℕ) :
    ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : PlanarGraph V) (C : List V),
      Fintype.card V = n →
      G.isCycleAndTriangles C →
      ∀ (v₁ v₂ : V),
        v₁ ≠ v₂ →
        G.og.Adj v₁ v₂ →
        v₁ ∈ C → v₂ ∈ C →
      ∀ (f : V → Finset ℕ) (c₁ c₂ : ℕ),
        c₁ ≠ c₂ →
        c₁ ∈ f v₁ → c₂ ∈ f v₂ →
        (∀ v, v ∈ C → v ≠ v₁ → v ≠ v₂ → 3 ≤ (f v).card) →
        (∀ v, v ∉ C → 5 ≤ (f v).card) →
      ∃ (LC : G.og.ListColoring ℕ f), LC.coloring v₁ = c₁ ∧ LC.coloring v₂ = c₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ G C hcard hCT v₁ v₂ hv₁v₂ hAdj hv₁C hv₂C f c₁ c₂ hcc hc₁ hc₂ h3 h5
    match n, hcard with
    | 0, _ => sorry -- contradiction with hCT
    | 1, _ => sorry -- contradiction with hCT
    | 2, _ => sorry -- contradiction with hCT
    | 3, hcard => sorry -- the base case
    | k + 4, hcard => -- inductive step (n ≥ 4)
      by_cases hChord : hasChord G C
      · -- chord case
        obtain ⟨u, v, huC, hvC, hAdj, hNotConsec⟩ := hChord
        sorry
      · -- no chord case
        sorry

/-- statement of (*) -/
theorem PlanarGraph.listColor_isCycleAndTriangles (G : PlanarGraph V) (C : List V)
  (hCT : G.isCycleAndTriangles C)
  (v₁ v₂ : V) -- distinguished vertices in C with predetermined valid coloring
  (hv₁v₂ : v₁ ≠ v₂)
  (h_adj_v₁v₂ : G.Adj v₁ v₂)
  (hv₁inC : v₁ ∈ C) (hv₂inC : v₂ ∈ C)
  (f : V → Finset ℕ) -- assignment of lists of allowed colors to vertices;
  (c₁ c₂ : ℕ) (hcc : c₁ ≠ c₂)
  (hv₁valcol : c₁ ∈ f v₁) (hv₂valcol : c₂ ∈ f v₂)
  (hCgte3col : ∀ v, v ∈ C → v ≠ v₁ → v ≠ v₂ → 3 ≤ (f v).card)
  (hGminCgte5col : ∀ v, v ∉ C → 5 ≤ (f v).card) :
  ∃ (LC : G.og.ListColoring ℕ f), LC.coloring v₁ = c₁ ∧ LC.coloring v₂ = c₂ :=
    listColor_isCycleAndTriangles' (Fintype.card V) G C rfl hCT
    v₁ v₂ hv₁v₂ h_adj_v₁v₂ hv₁inC hv₂inC f c₁ c₂ hcc hv₁valcol hv₂valcol
    hCgte3col hGminCgte5col


/-- Pick any face to be outer and two adjacent vertices on it -/
lemma pickOuterFace (G : PlanarGraph V) (isTr : G.IsPlaneTriangulation) :
    ∃ C : List V, G.isCycleAndTriangles C ∧
      ∃ v₁ v₂ : V, v₁ ≠ v₂ ∧ G.og.Adj v₁ v₂ ∧ v₁ ∈ C ∧ v₂ ∈ C := by
  -- Darts are non-empty from isTr.1
  have hNE : Nonempty G.og.Dart := by
    exact G.TriangleHasDarts isTr
  obtain ⟨d₀⟩ := hNE
  -- The face through d₀ has 3 darts
  have hFace : (G.cm.Φ.cycleOf d₀).support.card = 3 := isTr.2 d₀
  let d₁ := G.cm.Φ d₀
  let d₂ := G.cm.Φ d₁
  -- Build C from their .fst
  let v₀ := d₀.fst
  let v₁ := d₁.fst
  let v₂ := d₂.fst
  let C : List V := [v₀, v₁, v₂]
  refine ⟨C, ?_, v₀, v₁, ?_, ?_, ?_, ?_⟩
  -- isCycleAndTriangles C:
  · refine ⟨?_, ?_, ⟨d₀, ?_, ?_⟩⟩
    · -- C.Nodup, i.e. v₀, v₁, v₂ pairwise distinct
      apply List.Nodup.cons
      · apply List.not_mem_cons_of_ne_of_not_mem
        · simp [v₀, v₁, d₁]
          rw[cm_Φ_fst_eq_snd G.repG d₀]
          simp
        · simp [v₀, v₂]
          have : G.cm.Φ d₂ = d₀ := by
            simp [d₂, d₁]
            sorry -- prove that φ φ φ d₀ = d₀, which follows
                  -- from the cycle of d₀ under φ having support 3
          rw[←this]
          rw[cm_Φ_fst_eq_snd G.repG d₂]
          simp

      · apply List.Nodup.cons
        · apply List.not_mem_cons_of_ne_of_not_mem
          · simp [v₁, v₂]
            rw[cm_Φ_fst_eq_snd G.repG d₁]
            simp
          · simp
        simp
    · simp [C]   -- length is 3
    · -- (cycleOf d₀).support.image (·.fst) = C.toFinset
      -- support = {d₀, d₁, d₂} (since cycle of length 3 starting at d₀)
      ext x
      simp
      constructor
      · rintro ⟨a, aoncycle, a_fst_x⟩
        obtain aoncycle : a ∈ (G.cm.Φ.cycleOf d₀).support := by simp; assumption
        rw[←a_fst_x]
        sorry -- consider cases that a is d₀ d₁ or d₂
              -- then obvious in each case
      · intro xinc
        by_cases eqv₀ : x = v₀
        use d₀
        constructor
        · simp
          apply Equiv.Perm.support_cycleOf_nonempty.mp
          apply Finset.card_pos.mp
          exact Nat.lt_of_sub_eq_succ hFace
        rw[eqv₀]
        by_cases eqv₁ : x = v₁
        use d₁
        constructor
        · have :  G.cm.Φ.cycleOf d₁ = G.cm.Φ.cycleOf d₀ := by
            exact Equiv.Perm.cycleOf_self_apply G.cm.Φ d₀
          rw[←this]
          simp
          apply Equiv.Perm.support_cycleOf_nonempty.mp
          apply Finset.card_pos.mp
          rw[this]
          exact Nat.lt_of_sub_eq_succ hFace
        rw[eqv₁]
        by_cases eqv₂ : x = v₂
        use d₂
        constructor
        · have :  G.cm.Φ.cycleOf d₂ = G.cm.Φ.cycleOf d₀ := by
            refine Equiv.Perm.SameCycle.cycleOf_eq ?_
            repeat
              apply Equiv.Perm.SameCycle.apply_left
            exact Equiv.Perm.SameCycle.refl G.cm.Φ d₀
          rw[←this]
          simp
          apply Equiv.Perm.support_cycleOf_nonempty.mp
          apply Finset.card_pos.mp
          rw[this]
          exact Nat.lt_of_sub_eq_succ hFace
        rw[eqv₂]
        have : x ∉ C := by
          apply List.not_mem_cons_of_ne_of_not_mem eqv₀
          apply List.not_mem_cons_of_ne_of_not_mem eqv₁
          simp
          assumption
        contradiction
    · -- every other face is a triangle
      intro d hd
      exact isTr.2 d
  -- v₀ ≠ v₁
  · simp [v₀, v₁, d₁]
    rw[cm_Φ_fst_eq_snd G.repG d₀]
    simp
  -- adjacency of v₀ and v₁
  · have h : v₁ = d₀.snd := cm_Φ_fst_eq_snd G.repG d₀
    rw [h]
    exact d₀.adj
  -- v₀ ∈ C
  · simp [C]
  -- v₁ ∈ C
  · simp [C]

/-- pick two distinct colors from two 5-color lists -/
lemma pickTwoColors (list : SimpleGraph.KList ℕ 5) (v₁ v₂ : V) :
    ∃ c₁ c₂ : ℕ, c₁ ≠ c₂ ∧ c₁ ∈ list.f v₁ ∧ c₂ ∈ list.f v₂ := by
  --choose an element in list.f v₁
  have : (list.f v₁).Nonempty := by
    apply Finset.card_ne_zero.mp
    have : (list.f v₁).card = 5 := by
      exact list.cardinality_K v₁
    linarith
  let a₁ : ℕ := this.choose

  --choose an element in list.f v₂ \ {a₁}
  have : (list.f v₂ \ {a₁}).Nonempty := by
    apply Finset.sdiff_nonempty_of_card_lt_card
    have : (list.f v₂).card = 5 := by
      exact list.cardinality_K v₂
    rw[this]
    have : ({a₁} : Finset ℕ).card = 1 := by
      exact Finset.card_singleton a₁
    linarith
  let a₂ : ℕ := this.choose
  have : a₂ ∈ list.f v₂ \ {a₁} := by
      apply Classical.choose_spec _

  use a₁
  use a₂

  refine ⟨?_,?_,?_⟩
  · have : a₁ ∉ list.f v₂ \ {a₁} := by
      apply Finset.notMem_sdiff_of_mem_right
      exact Finset.mem_singleton.mpr rfl
    contrapose this
    nth_rw 2[this]
    assumption

  · simp only [a₁]
    exact Classical.choose_spec _

  · simp at this
    exact this.1

/-- Thomassen 1994 as given in Diestel: every planar graph is five list-colorable -/
theorem PlanarGraph.fiveListColorable (G : PlanarGraph V) : G.ListColorable 5 := by
  intro list_c
  -- can only prove a triangulation exists if V ≥ 3
  by_cases threePoints : G.cm.σ.cycleType.card + (Fintype.card G.Dart - G.cm.σ.support.card) ≥ 3
  · obtain ⟨Gtr, isSubg, isTr⟩ := triangulationExists G threePoints
    obtain ⟨C, hCT, v₁, v₂, hv₁v₂, hAdj, hv₁C, hv₂C⟩ := pickOuterFace Gtr isTr
    obtain ⟨c₁, c₂, hcc_neq, hc₁, hc₂⟩ := pickTwoColors list_c v₁ v₂
    -- apply (*)
    obtain ⟨LC, _, _⟩ :=
      Gtr.listColor_isCycleAndTriangles C hCT v₁ v₂ hv₁v₂ hAdj hv₁C hv₂C
        list_c.f c₁ c₂ hcc_neq hc₁ hc₂
        (fun v _ _ _ => by rw [list_c.cardinality_K]; norm_num)
        (fun v _   => by rw [list_c.cardinality_K])
    -- Transfer the coloring of Gtr to original G
    let c : G.og.Coloring ℕ := Coloring.subcoloring isSubg LC.coloring
    have h_mem : ∀ v, c v ∈ list_c.f v := by
      intro v
      exact LC.color_mem_f v
    exact ⟨{ coloring := c, color_mem_f := h_mem }⟩
  · sorry -- in this case we have that V < 5, and thus it can
          -- be colored with any list of 5-colors

/-- simple collorary that planar graphs are 5-colorable
-/
theorem PlanarGraph.fiveColorable (G : PlanarGraph V) : G.Colorable 5 := by
  obtain Glistcolorable := G.fiveListColorable
  exact SimpleGraph.ListColoring.ListColorable_imp_colorable G.og 5 Glistcolorable
