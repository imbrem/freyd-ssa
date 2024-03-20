import FreydSSA.Term.Extrinsic.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

inductive UTerminator.Wf : Ctx ν (Ty α) → UTerminator φ ν κ → LCtx ν κ (Ty α) → Type _
  | br : LCtx.Wk [⟨ℓ, A, Γ⟩] L → e.Wf 1 Γ A → Wf Γ (br ℓ e) L
  | ite : c.Wf 1 Γ Ty.bool → t.Wf Γ L → f.Wf Γ L → Wf Γ (ite c t f) L

inductive UGRegion.WfTerminator : Ctx ν (Ty α) → UGRegion φ α ν κ → LCtx ν (Ty α) κ → Type _
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

--TODO: Wf.toUGRegion

--TODO: WfTerminator.wk_entry

--TODO: WfTerminator.wk_exit
