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

structure Label.Comp (ℓ : Label ν κ α) (ℓ' : Label ν κ α) :=
  name : ℓ.name = ℓ'.name
  param : ℓ.param = ℓ'.param
  live : ℓ.live.Comp ℓ'.live

structure Label.Comp' (ℓ : Label ν κ α) (ℓ' : Label ν κ α) :=
  base : Label ν κ α
  left : base.Wk ℓ
  right : base.Wk ℓ'

def Label.Comp.ofComp' {ℓ ℓ' : Label ν κ α} (h : ℓ.Comp' ℓ') : ℓ.Comp ℓ' where
  name := h.left.name.symm.trans h.right.name
  param := h.left.param.symm.trans h.right.param
  live := ⟨h.base.live, h.left.live, h.right.live⟩

def Label.Comp'.ofComp {ℓ ℓ' : Label ν κ α} (h : ℓ.Comp ℓ') : ℓ.Comp' ℓ' where
  base := ⟨ℓ.name, ℓ.param, h.live.base⟩
  left := ⟨rfl, rfl, h.live.left⟩
  right := ⟨h.name, h.param, h.live.right⟩

inductive LCtx.PComp : LCtx ν κ α → LCtx ν κ α → Type _
  | nil : PComp [] []
  | cons : ℓ.Comp ℓ' → PComp L K → PComp (ℓ::L) (ℓ'::K)

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

-- theorem LCtx.SJoin.perm {L K M M' : LCtx ν κ α}
--   (h : L.SJoin K M) (h' : L.SJoin K M') : M.Perm M' := by
--   induction h generalizing M' with
--   | nil => cases h'; constructor
--   | left hℓ j I => cases h' with
--     | left hℓ' j' =>
--       constructor
--       apply I
--       assumption
--     | right hℓ' j' => sorry
--     | both _ j' => exact (hℓ.head rfl).elim
--   | right hℓ j I => cases h' with
--     | left hℓ' j' =>
--       sorry
--     | right =>
--       constructor
--       apply I
--       assumption
--     | both _ j' => exact (hℓ.head rfl).elim
--   | both _ j I => cases h' with
--     | left hℓ' => exact (hℓ'.head rfl).elim
--     | right hℓ' => exact (hℓ'.head rfl).elim
--     | both =>
--       constructor
--       apply I
--       assumption

-- theorem LCtx.SJoin.perm_left {L L' K M M' : LCtx ν κ α}
--   (hL : L.Perm L') (h : L.SJoin K M) (h' : L'.SJoin K M') : L.Perm M := by
--   induction hL generalizing K M M' with
--   | nil => sorry
--   | cons => sorry
--   | swap => sorry
--   | trans hl hr Il Ir =>
--     apply List.Perm.trans (Il h sorry) sorry

-- theorem LCtx.SJoin.perm₂ {L K L' K' M M' : LCtx ν κ α}
--   (h : L.SJoin K M) (h' : L'.SJoin K' M')
--   (hL : L.Perm L') (hK : K.Perm K') : M.Perm M' := by
--   induction h generalizing L' K' M' with
--   | nil => cases h' <;> simp at *
--   | @left _ _ _ ℓ hℓ j I => cases h' with
--     | nil => simp at hL
--     | @left _ _ _ ℓ' hℓ' j' =>
--       if hℓe : ℓ = ℓ' then
--         cases hℓe
--         constructor
--         apply I
--         assumption
--         apply (List.perm_cons _).mp hL
--         exact hK
--       else
--         sorry
--     | @right _ _ _ ℓ' hℓ' j' => sorry
--     | both ℓ j => sorry
--   | right hℓ j I => sorry
--   | both ℓ j I => cases h' with
--     | nil => simp at hL
--     | left hℓ' j' => sorry
--     | right hℓ' j' => sorry
--     | both ℓ j => sorry
