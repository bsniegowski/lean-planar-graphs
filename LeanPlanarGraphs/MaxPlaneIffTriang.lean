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

-- construct maximal planar supergraph of type PlanarGraph V
lemma PlanarGraph.existsMaximalPlanarSupergraph (G : PlanarGraph V) :
∃ G' : PlanarGraph V, G.og ≤ G'.og ∧ G'.IsMaximal := by
  classical -- makes IsPlanar H work
  let S : Set (SimpleGraph V) := { H | G.og ≤ H ∧ IsPlanar H }

  have hSnonempty : ∃ H, H ∈ S := by
    use G.og
    constructor
    · exact le_rfl
    · refine ⟨G.cm, G.repG, ?_⟩
      -- exact G.isPlanar; issue with agreement of decidability of relations?
      sorry

  have hSfinite : S.Finite := by
    have huniv : (Set.univ : Set (SimpleGraph V)).Finite := Set.finite_univ
    have hSsub : S ⊆ Set.univ := by
      simp
    exact huniv.subset hSsub

  -- Set.Finite.exists_maximalFor gives maximum of
  -- finite set of SimpleGraphs S w.r.t. cardinality of edge set
  obtain ⟨H, hHinS, hmax⟩ := Set.Finite.exists_maximalFor
    (fun H : SimpleGraph V => H.edgeFinset.card)
    S
    hSfinite
    hSnonempty

  obtain ⟨cm, hrepG, hplanar⟩ := hHinS.2 -- hHinS : G.og ≤ H ∧ IsPlanar H
  let G' : PlanarGraph V :=
  { og := H,
    cm := cm,
    decRel := inferInstance,
    isConnected := sorry,
    repG := hrepG,
    isPlanar := hplanar }

  have hsubG : G.og ≤ G'.og := hHinS.1

  have hmax' : G'.IsMaximal := by
    intro K decrelK hG'leqK hKplanar

    have hKinS : K ∈ S := by
      have hSdef : G.og ≤ K ∧ IsPlanar K := by
        constructor
        · exact le_trans hHinS.1 hG'leqK
        · exact hKplanar
      sorry -- again, issue with agreement of decidability of relations?

    have hcardHK : H.edgeFinset.card ≤ K.edgeFinset.card := by
      have hedgesub : H.edgeFinset ⊆ K.edgeFinset := by
        exact SimpleGraph.edgeFinset_mono hG'leqK
      apply Finset.card_mono
      exact hedgesub

    have heqKH : K = H := by
      sorry
      
    simp [G', heqKH]
  exact ⟨G', hsubG, hmax'⟩

-- assuming maximal planar supergraph exists, triangulation exists
theorem PlanarGraph.triangulationExists (G : PlanarGraph V) :
∃ G' : PlanarGraph V, G.og ≤ G'.og ∧ G'.IsPlaneTriangulation := by
  obtain ⟨G', hsub, hmax⟩ := PlanarGraph.existsMaximalPlanarSupergraph G
  have htriang : G'.IsPlaneTriangulation :=
  (PlanarGraph.IsMaximal_iff_IsPlaneTriangulation G').mp hmax
  exact ⟨G', hsub, htriang⟩
