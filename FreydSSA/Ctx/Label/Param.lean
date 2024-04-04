import FreydSSA.Ctx.Var.Fun

variable {ν ν' κ κ' α β}
  [DecidableEq ν] [DecidableEq ν']
  [DecidableEq κ] [DecidableEq κ']
  [DecidableEq α] [DecidableEq β]

structure PFCtx (ν : Type _) (α : Type _) extends FCtx ν α where
  params : Finset ν
  params_sub_support : params ⊆ support

structure PFCtx.Wk (Γ Δ : PFCtx ν α) : Prop where
  live : Γ.toFCtx.Wk Δ.toFCtx
  params : Γ.params ⊇ Δ.params -- todo: check direction, or if equality is necessary

def PFCtx.cons (x : ν) (a : α) (Γ : PFCtx ν α) : PFCtx ν α where
  toFCtx := Γ.toFCtx.cons x a
  params := Γ.params.erase x
  params_sub_support := by
    intro y hy
    apply Finset.mem_union_left
    apply Finset.mem_of_subset
    exact Γ.params_sub_support
    apply Finset.mem_of_mem_erase
    exact hy

def PFCtx.cons_param (x : ν) (a : α) (Γ : PFCtx ν α) : PFCtx ν α where
  toFCtx := Γ.toFCtx.cons x a
  params := Γ.params ∪ {x}
  params_sub_support := by
    intro y hy
    apply Finset.mem_of_subset
    apply Finset.union_subset_union_left
    exact Γ.params_sub_support
    exact hy

-- TODO: lattice structure

structure PFLCtx (κ : Type _) (ν : Type _) (α : Type _) where
  toFun : κ → WithTop (PFCtx ν α)
  support : Finset κ
  mem_support_toFun : ∀x, x ∈ support ↔ toFun x ≠ ⊤

theorem PFLCtx.toFun_inj_mp {L K : PFLCtx κ ν α} (h : L.toFun = K.toFun)
  : L = K
  := match L, K with
  | ⟨fΓ, n, hm⟩, ⟨fΔ, n', hm'⟩ => by
    cases h
    simp only [mk.injEq, true_and]
    apply Finset.ext
    intro x
    rw [hm, hm']

theorem PFLCtx.toFun_inj {L K : PFLCtx κ ν α}
  : L = K ↔ L.toFun = K.toFun
  := ⟨(λh => by cases h; rfl), PFLCtx.toFun_inj_mp⟩

instance PFLCtx.instFunLike : FunLike (PFLCtx κ ν α) κ (WithTop (PFCtx ν α)) where
  coe := PFLCtx.toFun
  coe_injective' := by intro Γ Δ; apply PFLCtx.toFun_inj_mp

theorem PFLCtx.ext {L K : PFLCtx κ ν α} (h : ∀x, L x = K x)
  : L = K
  := DFunLike.coe_injective' (by funext x; apply h)

-- def PFLCtx.Wk (L K : PFLCtx κ ν α) : Prop := ∀x, L x ≥ K x

-- TODO: lattice structure
