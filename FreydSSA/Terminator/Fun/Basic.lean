import FreydSSA.Term.Fun.Basic
import FreydSSA.Ctx.Label.Fun

variable {φ ν κ α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

inductive UTerminator.FWf : FCtx ν (Ty α) → UTerminator φ ν κ → FLCtx κ ν (Ty α) → Type _
  | br : FLCtx.Wk (FLCtx.singleton ℓ ⟨Γ, A⟩) L → e.FWf 1 Γ A → (br ℓ e).FWf Γ L
  | ite : e.FWf 1 Γ Ty.bool → s.FWf Γ L → t.FWf Γ L → (ite e s t).FWf Γ L

theorem UTerminator.FWf.allEq {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} : (dt dt' : t.FWf Γ L) → dt = dt'
  | br _ de, br _ de' => by cases de.tyEq de'; cases de.allEq de'; rfl
  | ite de ds dt, ite de' ds' dt' => by cases de.allEq de'; cases dt.allEq dt'; cases ds.allEq ds'; rfl

-- TODO: research automatic generalization of stuff like this...
inductive UTerminator.FWfM : FCtx ν (Ty α) → UTerminator φ ν κ → FLCtx κ ν (Ty α) → Type _
  | br ℓ : e.FWf 1 Γ A → L' = FLCtx.singleton ℓ ⟨Γ, A⟩ → (br ℓ e).FWfM Γ L'
  | ite : e.FWf 1 Γ Ty.bool → s.FWfM Γ L → t.FWfM Γ K → L.Cmp K → S = L.lsup K → (ite e s t).FWfM Γ S

theorem UTerminator.FWfM.trgEq {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} : t.FWfM Γ L → t.FWfM Γ L' → L = L'
  | br ℓ de rfl, br _ de' rfl => by cases de.tyEq de'; rfl
  | ite _ ds dt _ rfl, ite _ ds' dt' _ rfl => by cases ds.trgEq ds'; cases dt.trgEq dt'; rfl

theorem UTerminator.FWfM.allEq {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} : (dt dt' : t.FWfM Γ L) → dt = dt'
  | br _ de _, br _ de' _ => by cases de.tyEq de'; cases de.allEq de'; rfl
  | ite de ds dt h p, ite de' ds' dt' h' p' => by
    cases ds.trgEq ds'; cases dt.trgEq dt'; cases de.allEq de'; cases ds.allEq ds'; cases dt.allEq dt'; rfl

structure UTerminator.FWf' (Γ : FCtx ν (Ty α)) (t : UTerminator φ ν κ) (L : FLCtx κ ν (Ty α)) where
  base : FLCtx κ ν (Ty α)
  FWfM : t.FWfM Γ base
  wk : base.Wk L

--TODO: FWf', factorization, etc...

--TODO: FLCtx "Γ multiplication"...
