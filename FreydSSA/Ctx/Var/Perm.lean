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

theorem Ctx.perm_nodup_iff {Γ Δ : Ctx ν α} (h : Γ.Perm Δ) : Γ.Nodup ↔ Δ.Nodup := by
  apply List.Perm.nodup_iff
  apply List.Perm.map
  exact h

theorem Ctx.Nodup.of_perm {Γ Δ : Ctx ν α} (h : Γ.Perm Δ)  (h' : Γ.Nodup) : Δ.Nodup
  := (perm_nodup_iff h).mp h'

theorem Ctx.Nodup.of_tperm {Γ Δ : Ctx ν α} (h : Γ.TPerm Δ) (h' : Γ.Nodup) : Δ.Nodup
  := h'.of_perm h.perm

theorem Ctx.Nodup.tperm {Γ Δ : Ctx ν α} (h : Γ.Nodup) (h' : Γ.Perm Δ) : Γ.TPerm Δ := by
  induction h' with
  | nil => exact TPerm.nil
  | cons v _ I => exact TPerm.cons (I h.tail)
  | swap v v' I => exact TPerm.swap _ _ _ (λh' => h.not_mem (by simp [h']))
  | trans l _ Il Ir => exact TPerm.trans (Il h) (Ir (h.of_perm l))

theorem Ctx.Nodup.tperm_iff {Γ Δ : Ctx ν α} (h: Γ.Nodup) : Γ.TPerm Δ ↔ Γ.Perm Δ :=
  ⟨Ctx.TPerm.perm, h.tperm⟩

-- theorem Ctx.TPerm.tail {Γ Δ : Ctx ν α} (h : TPerm Γ Δ) (h' : Γ.head? = Δ.head?)
--   : TPerm Γ.tail Δ.tail := by
--   induction Γ generalizing Δ with
--   | nil => induction Δ with
--     | nil => exact TPerm.nil
--     | cons => cases h'
--   | cons v Γ I => sorry

-- theorem Ctx.TPerm.uncons {v : Var ν α} {Γ Δ : Ctx ν α} (h : TPerm (v::Γ) (v::Δ))
--   : TPerm Γ Δ := h.tail rfl

theorem Ctx.Fresh.perm {Γ Δ : Ctx ν α} (h : Γ.Fresh v) (h' : Γ.Perm Δ) : Δ.Fresh v
  := by
   apply of_not_mem_names
   intro c
   apply h.not_mem_names
   apply (h'.map Var.name).mem_iff.mpr c

theorem Ctx.Comp.perm_eq {Γ Δ : Ctx ν α} (h : Γ.Comp Δ) (h' : Γ.Perm Δ) : Γ = Δ := by
  cases h with | mk base wl wr =>
  induction wl generalizing Δ with
  | nil => cases wr; rfl
  | cons vl _ I => cases wr with
    | cons _ wr =>
      cases I ((List.perm_cons _).mp h') wr
      rfl
    | skip hvr wr => exact ((hvr.perm h'.symm).head rfl).elim
  | skip hvl _ I => cases wr with
    | cons vr wr => exact ((hvl.perm h').head rfl).elim
    | skip hvr wr => exact I h' wr
