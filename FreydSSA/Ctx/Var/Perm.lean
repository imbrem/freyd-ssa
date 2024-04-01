import FreydSSA.Ctx.Var

inductive Ctx.TPerm : Ctx ν α → Ctx ν α → Prop
  | nil : TPerm [] []
  | cons : TPerm Γ Δ → TPerm (⟨n, a⟩::Γ) (⟨n, a⟩::Δ)
  | swap (v v' Γ) : v.name ≠ v'.name -> TPerm (v::v'::Γ) (v'::v::Γ)
  | trans : TPerm Γ Δ → TPerm Δ Ξ → TPerm Γ Ξ

theorem Ctx.TPerm.perm {Γ Δ : Ctx ν α} (h : Γ.TPerm Δ) : Γ.Perm Δ := by
  induction h <;> constructor <;> assumption

theorem Ctx.TPerm.refl {Γ : Ctx ν α} : Γ.TPerm Γ := by
  induction Γ with
  | nil => exact TPerm.nil
  | cons v Γ I => exact TPerm.cons I

theorem Ctx.TPerm.symm {Γ Δ : Ctx ν α} (h : Γ.TPerm Δ) : Δ.TPerm Γ := by
  induction h with
  | swap _ _ _ h => exact swap _ _ _ h.symm
  | trans _ _ Il Ir => exact trans Ir Il
  | _ => constructor <;> assumption

-- theorem Ctx.TPerm.tail {Γ Δ : Ctx ν α} (h : TPerm Γ Δ) (h' : Γ.head? = Δ.head?)
--   : TPerm Γ.tail Δ.tail := by
--   induction Γ generalizing Δ with
--   | nil => induction Δ with
--     | nil => exact TPerm.nil
--     | cons => cases h'
--   | cons v Γ I => sorry

-- theorem Ctx.TPerm.uncons {v : Var ν α} {Γ Δ : Ctx ν α} (h : TPerm (v::Γ) (v::Δ))
--   : TPerm Γ Δ := h.tail rfl

-- theorem Ctx.TPerm.comp {Γ Δ : Ctx ν α} (h : Γ.TPerm Δ) (h' : Γ.Comp Δ) : Γ = Δ := by
--   cases h' with | mk base wl wr =>
--   induction wl generalizing Δ with
--   | nil => cases wr; rfl
--   | cons vl wl I => cases wr with
--     | cons _ wr =>
--       cases I h.uncons wr
--       rfl
--     | skip hvr wr => sorry -- contradiction by perm...
--   | skip hvl wl I => cases wr with
--     | cons vr wr => sorry -- contradiction by perm...
--     | skip hvr wr => exact I h wr
