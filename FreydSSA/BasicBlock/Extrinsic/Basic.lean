import FreydSSA.Body.Extrinsic.Basic
import FreydSSA.Terminator.Extrinsic.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

structure UBB.Wf (p : Purity) (Γ : Ctx ν (Ty α)) (β : UBB φ ν κ) (L : LCtx ν κ (Ty α))
  : Type _ where
  maxTrg : Ctx ν (Ty α)
  body : β.body.WfM p Γ maxTrg
  terminator : β.terminator.Wf maxTrg L

def UBB.Wf.wk_entry {Γ Δ : Ctx ν (Ty α)} {β : UBB φ ν κ}
  (w : Γ.Wk Δ) (dβ : Wf p Δ β L) : Wf p Γ β L :=
  let ⟨maxTrg, body, w'⟩ := dβ.body.wk_entry w;
  {
    maxTrg := maxTrg
    body := body
    terminator := dβ.terminator.wk_entry w'
  }

def UBB.Wf.wk_exit {L K : LCtx ν κ (Ty α)} {β : UBB φ ν κ}
  (dβ : Wf p Γ β L) (w : L.Wk K) : Wf p Γ β K where
  maxTrg := dβ.maxTrg
  body := dβ.body
  terminator := dβ.terminator.wk_exit w

theorem UBB.Wf.allEq {Γ : Ctx ν (Ty α)} {β : UBB φ ν κ}
  : (dβ dβ' : UBB.Wf p Γ β L) → dβ = dβ' :=
  by
    intro ⟨Γ, db, dt⟩ ⟨Γ', db', dt'⟩
    cases db.trgEq db'
    simp only [mk.injEq, heq_eq_eq, true_and]
    exact ⟨db.allEq db', dt.allEq dt'⟩

def UBody.WfM.compBB {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν} {β : UBB φ ν κ}
  (db : b.WfM p Γ Δ) (dβ : β.Wf p Δ L) : UBB.Wf p Γ (b.compBB β) L where
  maxTrg := dβ.maxTrg
  body := db.comp dβ.body
  terminator := dβ.terminator

def UBody.Wf'.compBB {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν} {β : UBB φ ν κ}
  (db : b.Wf' p Γ Δ) (dβ : β.Wf p Δ L) : UBB.Wf p Γ (b.compBB β) L
  := db.wfM.compBB (dβ.wk_entry db.wk)

def UBody.Wf.compBB {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν} {β : UBB φ ν κ}
  (db : b.Wf p Γ Δ) (dβ : β.Wf p Δ L) : UBB.Wf p Γ (b.compBB β) L
  := db.toWf'.compBB dβ

structure UBB.WfM (p : Purity) (Γ : Ctx ν (Ty α)) (β : UBB φ ν κ) (L : LCtx ν κ (Ty α))
  : Type _ where
  maxTrg : Ctx ν (Ty α)
  body : β.body.WfM p Γ maxTrg
  terminator : β.terminator.WfM maxTrg L

theorem UBB.WfM.allEq {Γ : Ctx ν (Ty α)} {β : UBB φ ν κ}
  : (dβ dβ' : UBB.WfM p Γ β L) → dβ = dβ' := by
    intro ⟨Γ, db, dt⟩ ⟨Γ', db', dt'⟩
    cases db.trgEq db'
    cases db.allEq db'
    cases dt.allEq dt'
    rfl

theorem UBB.WfM.trgEq {Γ : Ctx ν (Ty α)} {L L' : LCtx ν κ (Ty α)} {β : UBB φ ν κ}
  (hL: L.Comp L')
  : WfM p Γ β L → WfM p Γ β L' → L = L' := by
    intro ⟨Γ, db, dt⟩ ⟨Γ', db', dt'⟩
    cases db.trgEq db'
    cases dt.trgEq hL dt'
    exact rfl
