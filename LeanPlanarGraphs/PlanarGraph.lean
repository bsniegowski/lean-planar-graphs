import Mathlib
import LeanPlanarGraphs.CombinatorialMap

variable {V : Type} [Fintype V] [DecidableEq V]

structure PlanarGraph (V : Type) [Fintype V] [DecidableEq V] extends og : SimpleGraph V where
  cm : CombinatorialMap og.Dart
  decRel : DecidableRel og.Adj
  isConnected : og.Connected
  repG : CombinatorialMapRepresentsGraph og cm
  isPlanar : cm.IsPlanar

def IsPlanar [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ cm : CombinatorialMap G.Dart, CombinatorialMapRepresentsGraph G cm ∧ cm.IsPlanar

theorem subgraphIsPlanar (G : PlanarGraph V) (H : SimpleGraph V) [DecidableRel H.Adj]
(isSubgraph : H ≤ G.og) : IsPlanar H := by
  sorry
