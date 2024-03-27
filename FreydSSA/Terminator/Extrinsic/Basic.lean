import FreydSSA.Term.Extrinsic.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

inductive UTerminator.Wf : Ctx ν (Ty α) → UTerminator φ ν κ → LCtx ν κ (Ty α) → Type _
  | br : LCtx.Wk [⟨ℓ, A, Γ⟩] L → e.Wf 1 Γ A → Wf Γ (br ℓ e) L
  | ite : c.Wf 1 Γ Ty.bool → t.Wf Γ L → f.Wf Γ L → Wf Γ (ite c t f) L

inductive UGRegion.WfTerminator : Ctx ν (Ty α) → UGRegion φ α ν κ → LCtx ν κ (Ty α) → Type _
  | br : LCtx.Wk [⟨ℓ, A, Γ⟩] L → e.Wf 1 Γ A → WfTerminator Γ (br ℓ e) L
  | ite : c.Wf 1 Γ Ty.bool → t.WfTerminator Γ L → f.WfTerminator Γ L → WfTerminator Γ (ite c t f) L

def UTerminator.Wf.wk_entry {Γ Δ : Ctx ν (Ty α)} {t : UTerminator φ ν κ} (w : Γ.Wk Δ)
  : Wf Δ t L → Wf Γ t L
  | br hℓ e => br ((w.to_lctx _ _).comp hℓ) (e.wk w)
  | ite c t f => ite (c.wk w) (t.wk_entry w) (f.wk_entry w)

def UTerminator.Wf.wk_exit {L K : LCtx ν κ (Ty α)} {t : UTerminator φ ν κ}
  : Wf Γ t L → L.Wk K → Wf Γ t K
  | br hℓ e, w => br (hℓ.comp w) e
  | ite c t f, w => ite c (t.wk_exit w) (f.wk_exit w)

theorem UTerminator.Wf.allEq {Γ : Ctx ν (Ty α)} {t : UTerminator φ ν κ}
  (dt : Wf Γ t L) (dt' : Wf Γ t L) : dt = dt'
  := by
  induction dt <;> cases dt'
  case br.br de _ de' _ =>
    cases de.tyEq de'
    congr
    apply LCtx.Wk.allEq
    apply de.allEq
  case ite.ite =>
    congr
    apply UTm.Wf.allEq
    apply_assumption
    apply_assumption

inductive UTerminator.WfM : Ctx ν (Ty α) → UTerminator φ ν κ → LCtx ν κ (Ty α) → Type _
  | br ℓ : e.Wf 1 Γ A → WfM Γ (br ℓ e) [⟨ℓ, A, Γ⟩]
  | ite : c.Wf 1 Γ Ty.bool → t.WfM Γ L → f.WfM Γ K → L.SJoin K M → WfM Γ (ite c t f) M

def UTerminator.WfM.toWf {Γ : Ctx ν (Ty α)} {t : UTerminator φ ν κ}
  : WfM Γ t L → Wf Γ t L
  | br ℓ e => Wf.br (LCtx.Wk.refl _) e
  | ite c t f j => Wf.ite c (t.toWf.wk_exit j.left_wk) (f.toWf.wk_exit j.right_wk)

theorem UTerminator.WfM.trgEq {Γ : Ctx ν (Ty α)} {t : UTerminator φ ν κ}
  (hL: L.Comp L')
  : WfM Γ t L → WfM Γ t L' →  L = L'
  | br _ de, br _ de' => by cases de.tyEq de'; rfl
  | ite c dt df j, ite c' dt' df' j' => by
    cases dt.trgEq ⟨_, j.left_wk.comp hL.left, j'.left_wk.comp hL.right⟩ dt'
    cases df.trgEq ⟨_, j.right_wk.comp hL.left, j'.right_wk.comp hL.right⟩ df'
    exact j.trgEq j' hL

theorem UTerminator.WfM.allEq {Γ : Ctx ν (Ty α)} {t : UTerminator φ ν κ}
  (dt : WfM Γ t L) (dt' : WfM Γ t L) : dt = dt'
  := by
  induction dt with
  | br _ de => cases dt' with | br _ de' => cases de.tyEq de'; cases de.allEq de'; rfl
  | ite dc dt df j It If => cases dt' with | ite dc' dt' df' j' =>
    cases dc.allEq dc'
    cases dt.trgEq ⟨_, j.left_wk, j'.left_wk⟩ dt'
    cases df.trgEq ⟨_, j.right_wk, j'.right_wk⟩ df'
    cases It dt'
    cases If df'
    cases j.allEq j'
    rfl

structure UTerminator.Wf' (Γ : Ctx ν (Ty α)) (t : UTerminator φ ν κ) (L : LCtx ν κ (Ty α)) where
  base : LCtx ν κ (Ty α)
  wfM : WfM Γ t base
  wk : base.Wk L

theorem UTerminator.Wf'.allEq {Γ : Ctx ν (Ty α)} {t : UTerminator φ ν κ}
  {L : LCtx ν κ (Ty α)} : (dt : Wf' Γ t L) →  (dt' : Wf' Γ t L) → dt = dt'
  | ⟨_, dtM, dtw⟩, ⟨_, dtM', dtw'⟩ => by
    cases dtM.trgEq ⟨_, dtw, dtw'⟩ dtM'
    cases dtM.allEq dtM'
    cases dtw.allEq dtw'
    rfl

-- def UTerminator.Wf.toMin {Γ : Ctx ν (Ty α)} {t : UTerminator φ ν κ}
--   : Wf Γ t L → (L': LCtx ν κ (Ty α)) × Wf Γ t L' × L'.Wk L
--   | br hℓ de => ⟨_, br (LCtx.Wk.refl _) de, hℓ⟩
--   | ite dc dt df =>
--     let ⟨Lt, dt', wt⟩ := dt.toMin
--     let ⟨Lf, df', wf⟩ := df.toMin
--     --TODO: lattice ops...
--     sorry

--TODO: Wf.toUGRegion

--TODO: WfTerminator.wk_entry

--TODO: WfTerminator.wk_exit
