import Mathlib

/-
  A combinatorial map consists of a finite set D, a permutation σ: D → D,
  and a fixed-point-free involution α: D → D.
  When representing a graph G = (V, E), the set D becomes the set of G's darts,
  σ's orbits decompose D into maximal sets of darts with the same origin, and α
  assigns dart (u, v) to a dart (v, u).
-/
structure CombinatorialMap (D : Type) where
  σ : Equiv.Perm D
  α : Equiv.Perm D
  α_inv : α * α = 1
  α_fpf : ∀ x : D, α x ≠ x

-- using '*' group notation since ∘ forces coercion to plain function types and makes ⁻¹ unavailable
def CombinatorialMap.Φ {D : Type} (cm : CombinatorialMap D) := cm.α * cm.σ⁻¹

/-
  Combinatorial map represents a graph G if α is an involution on its darts and two darts are on the
  same orbit of σ iff they have the same origin vertex
-/
def CombinatorialMapRepresentsGraph (G : SimpleGraph V) (cm : CombinatorialMap G.Dart) : Prop :=
  ∀ d : G.Dart, cm.α d = d.symm ∧
  ∀ d1 d2 : G.Dart, Equiv.Perm.SameCycle cm.σ d1 d2 ↔ d1.fst = d2.fst


-- Limiting planarity considerations only to finite graphs, for now

def CombinatorialMap.genus {D : Type} [Fintype D] [DecidableEq D] (cm : CombinatorialMap D) : Nat :=
  -- `cycleType.card` does not count fixed points but for α we do not have them by definition
  let E := cm.α.cycleType.card
  let V := cm.σ.cycleType.card + (Fintype.card D - cm.σ.support.card)
  let F := cm.Φ.cycleType.card + (Fintype.card D - cm.Φ.support.card)
  1 - (V - E + F) / 2

def CombinatorialMap.IsPlanar {D} [Fintype D] [DecidableEq D] (cm : CombinatorialMap D) : Prop
  := cm.genus = 0

def IsPlanar [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ cm : CombinatorialMap G.Dart, CombinatorialMapRepresentsGraph G cm ∧ IsPlanarMap cm
