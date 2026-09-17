import Mathlib

/-
# Linear Algebra and Basic Graph Theory
This section will cover the required linear algebra and basic graph theory concepts needed
-/

namespace SpectraOfGraphs

--Defining our vertex set over this namespace
variable {V : Type*} [Fintype V] [DecidableEq V]


--We consider simple undirected graphs and begin defining key terms in that context
abbrev E (G : SimpleGraph V) := G.edgeSet

noncomputable def adjMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  Matrix.of (fun x y => if G.Adj x y then 1 else 0)

theorem adjMatrix_symmetric (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) :
  adjMatrix G i j = adjMatrix G j i := by
  unfold adjMatrix
  simp [Matrix.of_apply, G.adj_comm]

theorem adjMatrix_row_sum (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) :
  ∑ c, (adjMatrix G) r c = G.degree r := by
  unfold adjMatrix
  simp only [Matrix.of_apply]
  rw [SimpleGraph.degree, Finset.sum_boole]
  simp [SimpleGraph.neighborFinset]

noncomputable def degMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  Matrix.of (fun x y => if x = y then G.degree x else 0)

theorem degMatrix_symmetric (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) :
  degMatrix G i j = degMatrix G j i := by
    unfold degMatrix
    simp only [Matrix.of_apply]
    by_cases h : i = j
    · subst h
      rfl
    · simp [h]
      simp [Ne.symm h]

noncomputable def lapMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  degMatrix G - adjMatrix G

theorem lapMatrix_symmetric (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) :
  lapMatrix G i j = lapMatrix G j i := by
  unfold lapMatrix
  simp_rw [Matrix.sub_apply]
  simp_rw [degMatrix_symmetric, adjMatrix_symmetric]

noncomputable def sLapMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  degMatrix G + adjMatrix G

theorem sLapMatrix_symmetric (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) :
  sLapMatrix G i j = sLapMatrix G j i := by
  unfold sLapMatrix
  simp_rw [Matrix.add_apply]
  simp_rw [degMatrix_symmetric, adjMatrix_symmetric]

noncomputable def incMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V (E G) ℝ :=
  Matrix.of (fun v e => if v ∈ (e : Sym2 V) then 1 else 0)

noncomputable def getTarget (G : SimpleGraph V) : (e : G.edgeSet) → {v : V // v ∈ e.val} :=
  fun e =>
    let pair := e.val.out
    ⟨pair.2, Sym2.out_snd_mem e.val⟩

noncomputable def getSource (G : SimpleGraph V) : (e : G.edgeSet) → {v : V // v ∈ e.val} :=
  fun e =>
    let pair := e.val.out
    ⟨pair.1, Sym2.out_fst_mem e.val⟩

noncomputable def dirIncMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V (E G) ℝ :=
  let source := getSource G
  let target := getTarget G
  Matrix.of (fun v e =>
   if v = (source e).val then -1
   else if v = (target e).val then 1
   else 0
  )

end SpectraOfGraphs
