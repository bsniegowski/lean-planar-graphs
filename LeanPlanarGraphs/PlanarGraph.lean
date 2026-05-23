import Mathlib
import LeanPlanarGraphs.CombinatorialMap

variable {V : Type} [Fintype V] [DecidableEq V]

structure PlanarGraph extends G : SimpleGraph V where
  cm : CombinatorialMap G.Dart
  decRel : DecidableRel G.Adj
  isConnected : G.Connected
  repG : CombinatorialMapRepresentsGraph G cm
  isPlanar : cm.IsPlanar
