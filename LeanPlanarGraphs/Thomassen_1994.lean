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
vertices in C, and all other faces are triangles -/
def PlanarGraph.isCycleAndTriangles (G : PlanarGraph V) (C : List V) : Prop :=
  G.cm.σ.cycleType.card + (Fintype.card G.og.Dart - G.cm.σ.support.card) ≥ 3 -- safety first
  ∧ C.Nodup
  ∧ C.length ≥ 3
  ∧ ∃ d₀ : G.og.Dart, (G.cm.Φ.cycleOf d₀).support.image (fun d => d.fst) = C.toFinset
          ∧ ∀ d : G.og.Dart, d ∉ (G.cm.Φ.cycleOf d₀).support →
          (G.cm.Φ.cycleOf d).support.card = 3

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
  ∃ (LC : G.og.ListColoring ℕ f), LC.coloring v₁ = c₁ ∧ LC.coloring v₂ = c₂ := by
    sorry

/-- Pick any face to be outer and two adjacent vertices on it -/
lemma pickOuterFace (G : PlanarGraph V) (hTri : G.IsPlaneTriangulation) :
    ∃ C : List V, G.isCycleAndTriangles C ∧
      ∃ v₁ v₂ : V, v₁ ≠ v₂ ∧ G.og.Adj v₁ v₂ ∧ v₁ ∈ C ∧ v₂ ∈ C := by
  sorry

/-- pick two distinct colors from two 5-color lists -/
lemma pickTwoColors (list : SimpleGraph.KList ℕ 5) (v₁ v₂ : V) :
    ∃ c₁ c₂ : ℕ, c₁ ≠ c₂ ∧ c₁ ∈ list.f v₁ ∧ c₂ ∈ list.f v₂ := by
  sorry

/-- Thomassen 1994 as given in Diestel: every planar graph is five list-colorable -/
theorem PlanarGraph.fiveListColorable (G : PlanarGraph V) : G.ListColorable 5 := by
  intro list_c
  obtain ⟨Gtr, isSubg, isTr⟩ := triangulationExists G
  -- Picking any face to be the outer face
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
