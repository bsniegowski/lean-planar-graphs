import Mathlib
import LeanPlanarGraphs.ListColoring
import LeanPlanarGraphs.CombinatorialMap

/-
Goal of this file is to adress Proposition 4.2.8 from Diestel: A planar graph of order
at least three is maximally planar if and only if it is a plane triangulation
-/

-- define plane triangulation
-- must be planar, order at least 3,, and all faces have 3 sides
def IsPlaneTriangulationMap {D} [Fintype D] [DecidableEq D]
(cm : CombinatorialMap D) : Prop :=
  IsPlanarMap cm
  ∧ cm.σ.cycleType.card + (Fintype.card D - cm.σ.support.card) ≥ 3
  ∧ ∀ d : D, (cm.Φ.cycleOf d).support.card = 3

-- define maximally planar for SimpleGraph term
-- must be planar and cannot be subgraph of planar graph not equal to self
def IsMaximallyPlanar {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
[DecidableRel G.Adj] : Prop :=
  IsPlanar G
  ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj], G ≤ H → IsPlanar H → H = G

-- define maximally planar for CombinatorialMap
-- CombinatorialMap must represent maximally planar SimpleGraph
def CombinatorialMapRepresentsMaximallyPlanar {V : Type} [Fintype V] [DecidableEq V]
(G : SimpleGraph V) [DecidableRel G.Adj] (cm : CombinatorialMap G.Dart) : Prop :=
  CombinatorialMapRepresentsGraph G cm
  ∧ IsPlanarMap cm
  ∧ IsMaximallyPlanar G

-- state Proposition 4.2.8
theorem CombinatorialMap.IsMaximallyPlanar_iff_IsPlaneTriangulationMap {V : Type}
[Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.Dart]
[DecidableEq G.Dart] (cm : CombinatorialMap G.Dart) :
CombinatorialMapRepresentsMaximallyPlanar G cm ↔
CombinatorialMapRepresentsGraph G cm ∧ IsPlaneTriangulationMap cm := by
  constructor
  · sorry
  · sorry
