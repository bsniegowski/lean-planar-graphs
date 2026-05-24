import Mathlib

/-- A combinatorial map consists of a finite set D, a permutation σ: D → D,
and a fixed-point-free involution α: D → D.
When representing a graph G = (V, E), the set D becomes the set of G's darts,
σ's orbits decompose D into maximal sets of darts with the same origin, and α
assigns dart (u, v) to a dart (v, u). -/
structure CombinatorialMap (D : Type) where
  σ : Equiv.Perm D
  α : Equiv.Perm D
  α_inv : α * α = 1
  α_fpf : ∀ x : D, α x ≠ x

/-- using '*' group notation since ∘ forces coercion to plain function types and makes ⁻¹
unavailable -/
def CombinatorialMap.Φ {D : Type} (cm : CombinatorialMap D) := cm.σ * cm.α

/-- Combinatorial map represents a connected graph G if α is an involution on its darts and two
darts are on the same orbit of σ iff they have the same origin vertex -/
def CombinatorialMapRepresentsGraph (G : SimpleGraph V) (cm : CombinatorialMap G.Dart) : Prop :=
  ∀ d : G.Dart, cm.α d = d.symm ∧
  ∀ d1 d2 : G.Dart, Equiv.Perm.SameCycle cm.σ d1 d2 ↔ d1.fst = d2.fst


-- Limiting planarity considerations only to finite, connected graphs

def CombinatorialMap.genus {D : Type} [Fintype D] [DecidableEq D] (cm : CombinatorialMap D) : Nat :=
  -- `cycleType.card` does not count fixed points but for α we do not have them by definition
  let E := cm.α.cycleType.card
  let V := cm.σ.cycleType.card + (Fintype.card D - cm.σ.support.card) -- Or just `Fintype.card D`?
  let F := cm.Φ.cycleType.card + (Fintype.card D - cm.Φ.support.card)
  1 - (V - E + F) / 2

def CombinatorialMap.IsPlanar {D} [Fintype D] [DecidableEq D] (cm : CombinatorialMap D) : Prop
  := cm.genus = 0

/-- Dart in a subgraph is also a dart in supergraph -/
def SimpleGraph.Dart.ofLE {G1 G2 : SimpleGraph V} (h : G1 ≤ G2) (d : G1.Dart) : G2.Dart :=
  ⟨d.toProd, h d.adj⟩

/-- Construct the CombinatorialMap of a subgraph in the case when both of them have the same set of
vertices. The definition is noncomputable because of using `Equiv.ofBijective`. We might want/need
to rewrite the proof to use explicit inverses -/
noncomputable def CombinatorialMapOfSubgraph (G H : SimpleGraph V) [DecidableRel H.Adj]
[Fintype G.Dart] [DecidableEq G.Dart] [Fintype H.Dart] [DecidableEq H.Dart]
(hSubgraphG : H ≤ G) (cm : CombinatorialMap G.Dart) (cmRepG : CombinatorialMapRepresentsGraph G cm)
: {cmSubgraph : CombinatorialMap H.Dart // CombinatorialMapRepresentsGraph H cmSubgraph ∧ cm.genus = cmSubgraph.genus} :=
  -- We construct σ on a subgraph by skipping the darts outside of the subgraph
  -- i.e. for d dart in the subgraph `cmSubgraph.σ d = cm.σ ^ n d` where `n` is smallest postiive
  -- such that `cm.σ ^ n d` is a dart in the subgraph
  let σ_subG_fun : H.Dart → H.Dart := fun d =>
    let d_in_G := (d.ofLE hSubgraphG) -- translate d to G.Dart so we can apply cm.σ
    have existsN : ∃ n ≥ 1, H.Adj ((cm.σ ^ n) d_in_G).fst ((cm.σ ^ n) d_in_G).snd := by
      sorry
    let n := Nat.find existsN
    let hn := Nat.find_spec existsN
    ⟨((cm.σ ^ n) d_in_G).toProd, hn.right⟩
  have σ_subG_fun_surj : Function.Surjective σ_subG_fun := by
    sorry
  have σ_subG_fun_inj : Function.Injective σ_subG_fun := by
    sorry
  let σ_subG : Equiv.Perm H.Dart := Equiv.ofBijective σ_subG_fun ⟨σ_subG_fun_inj, σ_subG_fun_surj⟩
  -- Now α
  let α_subG_fun : H.Dart → H.Dart := fun d => d.symm
  have α_subG_fun_surj : Function.Surjective α_subG_fun := by
    sorry
  have α_subG_fun_inj : Function.Injective α_subG_fun := by
    sorry
  let α_subG : Equiv.Perm H.Dart := Equiv.ofBijective α_subG_fun ⟨α_subG_fun_inj, α_subG_fun_surj⟩
  let cm_subG : CombinatorialMap H.Dart := {
    σ := σ_subG
    α := α_subG
    α_inv := by sorry
    α_fpf := by sorry
  }
  have cm_subG_rep_subG : CombinatorialMapRepresentsGraph H cm_subG := by
    sorry
  /- This should be true since when both are connected, the subgraph is created by removing edges
  and each edge removal also remove one face, and number of vertices stays constant -/
  have genus_unchanged : cm.genus = cm_subG.genus := by
    sorry
  ⟨cm_subG, And.intro cm_subG_rep_subG genus_unchanged⟩
