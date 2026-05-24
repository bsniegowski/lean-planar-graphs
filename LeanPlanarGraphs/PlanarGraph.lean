import Mathlib
import LeanPlanarGraphs.CombinatorialMap

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A PlanarGraph extends a SimpleGraph by also containing a planar CombinatorialMap representing
the original graph (the `og`) -/
structure PlanarGraph (V : Type) [Fintype V] [DecidableEq V] extends og : SimpleGraph V where
  cm : CombinatorialMap og.Dart
  decRel : DecidableRel og.Adj
  isConnected : og.Connected
  repG : CombinatorialMapRepresentsGraph og cm
  isPlanar : cm.IsPlanar

instance (G : PlanarGraph V) : DecidableRel G.og.Adj := G.decRel

def IsPlanar [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ cm : CombinatorialMap G.Dart, CombinatorialMapRepresentsGraph G cm ∧ cm.IsPlanar

theorem subgraphIsPlanar (G : PlanarGraph V) (H : SimpleGraph V) [DecidableRel H.Adj]
(isSubgraph : H ≤ G.og) : IsPlanar H := by
  let cmH := CombinatorialMapOfSubgraph G.og H isSubgraph G.cm G.repG
  use cmH.val
  constructor
  · exact cmH.prop.left
  simp [CombinatorialMap.IsPlanar]
  calc cmH.val.genus = G.cm.genus := by exact cmH.prop.right.symm
    _ = 0 := G.isPlanar
