import FreydSSA.Ctx.Label
import FreydSSA.Ctx.Var.Perm

inductive LCtx.LPerm : LCtx ν κ α → LCtx ν κ α → Prop
  | nil : LPerm [] []
  | cons : LPerm L K → LPerm (ℓ::L) (ℓ::K)
  | swap (ℓ ℓ') (L) : ℓ.name ≠ ℓ'.name -> LPerm (ℓ::ℓ'::L) (ℓ'::ℓ::L)
  | trans : LPerm Γ Δ → LPerm Δ Ξ → LPerm Γ Ξ

theorem LCtx.LPerm.perm {L K : LCtx ν κ α} (h : L.LPerm K) : L.Perm K := by
  induction h <;> constructor <;> assumption

theorem LCtx.perm_nodup_iff {L K : LCtx ν κ α} (h : L.Perm K) : L.Nodup ↔ K.Nodup := by
  apply List.Perm.nodup_iff
  apply List.Perm.map
  exact h

theorem LCtx.Nodup.of_perm {L K : LCtx ν κ α} (h : L.Perm K)  (h' : L.Nodup) : K.Nodup
  := (perm_nodup_iff h).mp h'

theorem LCtx.Nodup.of_lperm {L K : LCtx ν κ α} (h : L.LPerm K)  (h' : L.Nodup)
  : K.Nodup
  := h'.of_perm h.perm

theorem LCtx.Nodup.lperm {L K : LCtx ν κ α} (h : L.Nodup) (h' : L.Perm K) : L.LPerm K
  := by
  induction h' with
  | nil => exact LPerm.nil
  | cons v _ I => exact LPerm.cons (I h.tail)
  | swap v v' I => exact LPerm.swap _ _ _ (λh' => h.not_mem (by simp [h']))
  | trans l _ Il Ir => exact LPerm.trans (Il h) (Ir (h.of_perm l))

theorem LCtx.Nodup.lperm_iff {L K : LCtx ν κ α} (h: L.Nodup) : L.LPerm K ↔ L.Perm K :=
  ⟨LPerm.perm, h.lperm⟩

theorem LCtx.Fresh.perm {L K : LCtx ν κ α} (h : L.Fresh ℓ) (h' : L.Perm K) : K.Fresh ℓ
  := by
   apply of_not_mem
   intro c
   apply h.not_mem
   apply (h'.map Label.name).mem_iff.mpr c

-- In this case, we simply have _pointwise_ comparability, probably, or smt...
-- theorem LCtx.Comp.perm_eq {L K : LCtx ν κ α} (h : L.Comp K) (h' : L.Perm K) : L = K := by
--   cases h with | mk base wl wr =>
--   induction wl generalizing K with
--   | nil => cases wr; rfl
--   | cons hℓ _ I => cases wr with
--     | cons hℓ' wr =>

--       cases I ((List.perm_cons _).mp sorry) wr
--       rfl
--     | skip hvr wr => exact ((hvr.perm h'.symm).head rfl).elim
--   | skip hvl _ I => cases wr with
--     | cons vr wr => exact ((hvl.perm h').head rfl).elim
--     | skip hvr wr => exact I h' wr

structure Label.TPerm (ℓ : Label ν κ α) (ℓ' : Label ν κ α) :=
  name : ℓ.name = ℓ'.name
  param : ℓ.param = ℓ'.param
  live : ℓ.live.TPerm ℓ'.live

inductive LCtx.PPerm : LCtx ν κ α → LCtx ν κ α → Prop
  | nil : PPerm [] []
  | cons : ℓ.TPerm ℓ' → PPerm L K → PPerm (ℓ::L) (ℓ'::K)

inductive LCtx.LTPerm : LCtx ν κ α → LCtx ν κ α → Prop
  | nil : LTPerm [] []
  | cons : ℓ.TPerm ℓ' → LTPerm L K → LTPerm (ℓ::L) (ℓ'::K)
  | swap (ℓ ℓ') (L) : ℓ.name ≠ ℓ'.name -> LTPerm (ℓ::ℓ'::L) (ℓ'::ℓ::L)
  | trans : LTPerm Γ Δ → LTPerm Δ Ξ → LTPerm Γ Ξ
