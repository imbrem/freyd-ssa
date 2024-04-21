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

def UTerminator.FWf.wkEntry {Γ Δ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} (hΓ : Γ.Wk Δ) : t.FWf Δ L → t.FWf Γ L
  | br w de => br ((hΓ.toSingleton _ _).comp w) (de.wk hΓ)
  | ite de ds dt => ite (de.wk hΓ) (ds.wkEntry hΓ) (dt.wkEntry hΓ)

def UTerminator.FWf.wkExit {L K : FLCtx κ ν (Ty α)} {t : UTerminator φ ν κ} (dt : t.FWf Γ L) (hL : L.Wk K) : t.FWf Γ K
  := match dt with
  | br w de => br (w.comp hL) de
  | ite de ds dt => ite de (ds.wkExit hL) (dt.wkExit hL)

def UTerminator.FWf.minTrg {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} : t.FWf Γ L → FLCtx κ ν (Ty α)
  | @br _ _ _ _ _ _ ℓ Γ A _ _ _ _ => FLCtx.singleton ℓ ⟨Γ, A⟩
  | ite _ ds dt => ds.minTrg.lsup dt.minTrg

theorem UTerminator.FWf.minTrg_wk {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} : (dt : t.FWf Γ L) → dt.minTrg.Wk L
  | br w _ => w
  | ite _ ds dt => ds.minTrg_wk.lsup_wk dt.minTrg_wk

theorem UTerminator.FWf.minTrg_LEq {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} : (dt : t.FWf Γ L) → Γ.LEq dt.minTrg
  | br _ _ => Γ.singletonLEq _ _
  | ite _ ds dt => ds.minTrg_LEq.lsup dt.minTrg_LEq

theorem UTerminator.FWf.toMinTrg {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} : (dt : t.FWf Γ L) → t.FWf Γ dt.minTrg
  | br _ de => br (FLCtx.Wk.refl _) de
  | ite de ds dt => ite de (ds.toMinTrg.wkExit (FLCtx.lsup_wk _ _)) (dt.toMinTrg.wkExit (
    (ds.minTrg_LEq.toLWk.cmp₂ dt.minTrg_LEq.toLWk ds.minTrg_wk dt.minTrg_wk).lsup_wk_right
  ))

-- def UTerminator.FWf.minTrg_targets {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
--   : (dt : t.FWf Γ L) → (L.restrict t.targets).PWk dt.minTrg
--   | br w de => by
--     apply FLCtx.ext
--     intro x
--     simp only [minTrg, FLCtx.singleton_app, targets, FLCtx.restrict_app, Finset.mem_singleton]
--     split
--     . rename_i h
--       have h' := w x
--       cases h
--       simp only [FLCtx.singleton_app, ↓reduceIte, ge_iff_le] at h'
--       sorry
--     . rfl
--   | ite de ds dt => sorry

theorem UTerminator.FWf.minTrg_eq {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
  : (dt : t.FWf Γ L) → (dt' : t.FWf Γ L') → dt.minTrg = dt'.minTrg
  | br _ de, br _ de' => by cases de.tyEq de'; rfl
  | ite _ ds dt, ite _ ds' dt' => by simp only [minTrg, ds.minTrg_eq ds', dt.minTrg_eq dt']

-- TODO: lsup, rsup lore...

-- TODO: research automatic generalization of stuff like this...
inductive UTerminator.FWfM : FCtx ν (Ty α) → UTerminator φ ν κ → FLCtx κ ν (Ty α) → Type _
  | br ℓ : e.FWf 1 Γ A → L' = FLCtx.singleton ℓ ⟨Γ, A⟩ → (br ℓ e).FWfM Γ L'
  | ite : e.FWf 1 Γ Ty.bool → s.FWfM Γ L → t.FWfM Γ K → L.Cmp K → S = L.lsup K → (ite e s t).FWfM Γ S

-- TODO: FWfM ==> FWf

theorem UTerminator.FWfM.trgEq {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} : t.FWfM Γ L → t.FWfM Γ L' → L = L'
  | br ℓ de rfl, br _ de' rfl => by cases de.tyEq de'; rfl
  | ite _ ds dt _ rfl, ite _ ds' dt' _ rfl => by cases ds.trgEq ds'; cases dt.trgEq dt'; rfl

theorem UTerminator.FWfM.allEq {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} : (dt dt' : t.FWfM Γ L) → dt = dt'
  | br _ de _, br _ de' _ => by cases de.tyEq de'; cases de.allEq de'; rfl
  | ite de ds dt h p, ite de' ds' dt' h' p' => by
    cases ds.trgEq ds'; cases dt.trgEq dt'; cases de.allEq de'; cases ds.allEq ds'; cases dt.allEq dt'; rfl

theorem UTerminator.FWfM.trgLEq {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
  : t.FWfM Γ L → Γ.LEq L
  | br _ _ rfl => Γ.singletonLEq _ _
  | ite _ ds dt _ rfl => ds.trgLEq.lsup dt.trgLEq

def UTerminator.FWf.toFWfM {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} : (dt : t.FWf Γ L) → t.FWfM Γ dt.minTrg
  | br _ de => FWfM.br _ de rfl
  | ite de ds dt => FWfM.ite de ds.toFWfM dt.toFWfM
    (ds.minTrg_LEq.toLWk.cmp₂ dt.minTrg_LEq.toLWk ds.minTrg_wk dt.minTrg_wk) rfl

def UTerminator.FWfM.toFWf {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} : (dt : t.FWfM Γ L) → t.FWf Γ L
  | br _ de p => FWf.br (p ▸ FLCtx.Wk.refl _) de
  | ite de ds dt h p => FWf.ite de
    (ds.toFWf.wkExit (p ▸ FLCtx.lsup_wk _ _))
    (dt.toFWf.wkExit (p ▸ h.lsup_wk_right))

structure UTerminator.FWf' (Γ : FCtx ν (Ty α)) (t : UTerminator φ ν κ) (L : FLCtx κ ν (Ty α)) where
  base : FLCtx κ ν (Ty α)
  FWfM : t.FWfM Γ base
  wk : base.Wk L

def UTerminator.FWf'.toFWf {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} (dt : t.FWf' Γ L) : t.FWf Γ L
  := dt.FWfM.toFWf.wkExit dt.wk

def UTerminator.FWf'.allEq {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} (dt dt' : t.FWf' Γ L) : dt = dt'
  := match dt, dt' with
  | ⟨base, dt, w⟩, ⟨base', dt', w'⟩ => by cases dt.trgEq dt'; cases dt.allEq dt'; rfl

def UTerminator.FWf.factor {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ} (dt : t.FWf Γ L) : t.FWf' Γ L
  where
  base := dt.minTrg
  FWfM := dt.toFWfM
  wk := dt.minTrg_wk

--TODO: FLCtx "Γ multiplication", and so on... might be useful for resources...
