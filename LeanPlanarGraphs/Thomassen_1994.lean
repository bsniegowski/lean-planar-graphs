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

-- Thomassen 1994 as given in Diestel: every planar graph is five list-colorable
theorem PlanarGraph.fiveListColorable (G : PlanarGraph V) : G.ListColorable 5 := by
  sorry

-- G has at least three vertices/C contains at least three vertices, G has one face bounded by
-- vertices in C, and all other faces are triangles
def PlanarGraph.isCycleAndTriangles (G : PlanarGraph V) (C : List V) : Prop :=
  G.cm.σ.cycleType.card + (Fintype.card G.og.Dart - G.cm.σ.support.card) ≥ 3 -- safety first
  ∧ C.Nodup
  ∧ C.length ≥ 3
  ∧ ∃ d₀ : G.og.Dart, (G.cm.Φ.cycleOf d₀).support.image (fun d => d.fst) = C.toFinset
          ∧ ∀ d : G.og.Dart, d ∉ (G.cm.Φ.cycleOf d₀).support →
          (G.cm.Φ.cycleOf d).support.card = 3

-- statement of (*)
theorem PlanarGraph.listColor_isCycleAndTriangles (α : Type*) (G : PlanarGraph V) (C : List V)
  (hCT : G.isCycleAndTriangles C)
  (v₁ v₂ : V) -- distinguished vertices in C with predetermined valid coloring
  (hv₁inC : v₁ ∈ C) (hv₂inC : v₂ ∈ C)
  (f : V → Finset ℕ) -- assignment of lists of allowed colors to vertices;
  -- should consider use of ℕ, makes using 1 and 2 easy ...
  (hv₁valcol : 1 ∈ f v₁) (hv₂valcol : 2 ∈ f v₂)
  (hCgte3col : ∀ v, v ∈ C → v ≠ v₁ → v ≠ v₂ → 3 ≤ (f v).card)
  (hGminCgte5col : ∀ v, v ∉ C → 5 ≤ (f v).card) :
  ∃ (LC : G.og.ListColoring ℕ f), LC.coloring v₁ = 1 ∧ LC.coloring v₂ = 2 := by
    sorry
