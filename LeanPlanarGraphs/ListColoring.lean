import Mathlib


namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- an `α`-List coloring of a simple graph is an `α`-coloring with
the added condition that the colors for each vertex are restricted to
some finite set of elements in `α`
-/
structure ListColoring (α : Type*) (f : V → Finset α) where
  coloring : G.Coloring α
  color_mem_f : ∀(v : V), (coloring v) ∈ f v

variable {α : Type*} {f : V → Finset α} (LC : G.ListColoring α f)

/- extends Coloring.valid to ListColoring
-/
theorem ListColoring.colorValid {v w : V} (h : G.Adj v w) : LC.coloring v ≠ LC.coloring w := by
  exact LC.coloring.valid h


/- proof that the colors in the ListColoring are in the lists
-/
theorem ListColoring.listValid {v : V} : LC.coloring v ∈ f v := by
  exact LC.color_mem_f v

/- a KList is defined as a function f : V → Finset α where f v has cardinality k
  for all v ∈ V
-/
structure KList {V : Type*} (α : Type*) (k : ℕ) where
  f : V → Finset α
  cardinality_K : ∀(v : V), (f v).card = k

/- a SimpleGraph G is k list-colorable if for every list assinging k colors
to every vertex there exists an `ℕ`list-coloring
-/
def ListColorable (k : ℕ) : Prop := ∀(list : KList ℕ k), Nonempty (G.ListColoring ℕ list.f)

/- the KList which assigns to every vertex the set Finset.range k
-/
def range_Klist (k : ℕ) : @KList V ℕ k where
  f := fun v ↦ Finset.range k
  cardinality_K := by
    intro v
    apply Finset.card_range

/- a proof of the fact that if G is n-ListColorable that G is also n-Colorable for some  n > 0
-/
theorem ListColoring.ListColorable_imp_colorable_pos_n (n : ℕ) [NeZero n]
        : G.ListColorable n → G.Colorable n := by
  intro ListColorable
  let fₙ := @range_Klist V n

  have existsfₙColoring : Nonempty (G.ListColoring ℕ fₙ.f) := by
    exact ListColorable fₙ

  let fₙListColoring := existsfₙColoring.some

  apply (SimpleGraph.colorable_iff_exists_bdd_nat_coloring n).mpr
  use fₙListColoring.coloring

  intro v

  have : fₙListColoring.coloring v ∈ Finset.range n := by
    exact fₙListColoring.color_mem_f v

  exact Finset.mem_range.mp this

end SimpleGraph
