import Mathlib
import LeanPlanarGraphs.ListColoring
import LeanPlanarGraphs.CombinatorialMap
import LeanPlanarGraphs.PlanarGraph

/-
Goal of this file is to address Proposition 4.2.8 from Diestel: A planar graph of order
at least three is maximally planar if and only if it is a plane triangulation
-/

variable {V : Type} [Fintype V] [DecidableEq V]

-- define plane triangulation for PlanarGraph term
-- order at least 3 and all faces have 3 sides
def PlanarGraph.IsPlaneTriangulation (G : PlanarGraph V) : Prop :=
  G.cm.σ.cycleType.card + (Fintype.card G.og.Dart - G.cm.σ.support.card) ≥ 3
  ∧ ∀ d : G.og.Dart, (G.cm.Φ.cycleOf d).support.card = 3

/- def IsPlaneTriangulationMap {D} [Fintype D] [DecidableEq D]
(cm : CombinatorialMap D) : Prop :=
  -- IsPlanarMap cm
  cm.σ.cycleType.card + (Fintype.card D - cm.σ.support.card) ≥ 3
  ∧ ∀ d : D, (cm.Φ.cycleOf d).support.card = 3
 -/

-- define maximally planar for PlanarGraph term
-- must be planar and cannot be subgraph of planar graph not equal to self
def PlanarGraph.IsMaximal (G : PlanarGraph V) : Prop :=
  ∀ (H : SimpleGraph V) [DecidableRel H.Adj], G.og ≤ H → IsPlanar H → H = G.og

/- def IsMaximallyPlanar {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
[DecidableRel G.Adj] : Prop :=
  IsPlanar G
  ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj], G ≤ H → IsPlanar H → H = G
-/

/-
-- define maximally planar for CombinatorialMap
-- CombinatorialMap must represent maximally planar SimpleGraph
def CombinatorialMapRepresentsMaximallyPlanar {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) [DecidableRel G.Adj] (cm : CombinatorialMap G.Dart) : Prop :=
  CombinatorialMapRepresentsGraph G cm
  -- ∧ PlanarMap cm
  ∧ IsMaximallyPlanar G
 -/

-- state Proposition 4.2.8
theorem PlanarGraph.IsMaximal_iff_IsPlaneTriangulation (G : PlanarGraph V) :
G.IsMaximal ↔ G.IsPlaneTriangulation := by
  constructor
  · intro h
    sorry
  · intro h
    sorry

/- theorem CombinatorialMap.IsMaximallyPlanar_iff_IsPlaneTriangulationMap {V : Type}
[Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.Dart]
[DecidableEq G.Dart] (cm : CombinatorialMap G.Dart) :
CombinatorialMapRepresentsMaximallyPlanar G cm ↔
CombinatorialMapRepresentsGraph G cm ∧ IsPlaneTriangulationMap cm := by
  sorry
 -/

theorem triangulationExists (G : PlanarGraph V)
: ∃ G' : PlanarGraph V, G.og ≤ G'.og ∧ G'.IsPlaneTriangulation := by
  sorry
