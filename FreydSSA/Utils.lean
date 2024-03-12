import Mathlib.Data.List.MinMax

theorem List.argmax_map [Preorder β] [DecidableRel λ l r : β => l < r] (Γ : List α) (f : α → β)
  : (Γ.argmax f).map f = (Γ.map f).maximum := by
  simp only [map_cons, maximum, argmax, foldl]
  generalize hbase: @none α = base
  have hbase': @none β = base.map f := by simp [<-hbase]
  rw [hbase']
  clear hbase hbase'
  induction Γ generalizing base with
  | nil => rfl
  | cons a Γ I =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, I]
    congr
    cases base with
    | some base =>
      simp only [argAux, id_eq, Option.map_some']
      split <;> rfl
    | none => rfl
