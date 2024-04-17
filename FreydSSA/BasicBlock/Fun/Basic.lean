import FreydSSA.Body.Fun.Basic
import FreydSSA.Terminator.Fun.Basic

variable {φ : Type u₁} {ν : Type u₂} {κ : Type u₃} {α : Type u₄} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

structure UBB.FWf (p : Purity) (Γ : FCtx ν (Ty α)) (β : UBB φ ν κ) (L : FLCtx κ ν (Ty α)) : Type _ :=
  (live : FCtx ν (Ty α))
  (body : β.body.FWfM p Γ live)
  (terminator : β.terminator.FWf live L)

def UBB.FWf.wkEntry {p : Purity} {Γ Δ : FCtx ν (Ty α)} {β : UBB φ ν κ} {L : FLCtx κ ν (Ty α)}
  (wk : Γ.Wk Δ) (dβ : UBB.FWf p Δ β L) : UBB.FWf p Γ β L :=
  let db := (dβ.body.toFWf.wkEntry wk).factor;
  {
    live := db.live,
    body := db.FWfM,
    terminator := dβ.terminator.wkEntry db.wk
  }

def UBB.FWf.wkExit {p : Purity} {Γ : FCtx ν (Ty α)} {β : UBB φ ν κ} {L K : FLCtx κ ν (Ty α)}
  (dβ : UBB.FWf p Γ β L) (wk : L.Wk K) : UBB.FWf p Γ β K :=
  {
    live := dβ.live,
    body := dβ.body,
    terminator := dβ.terminator.wkExit wk
  }

structure UBB.FWfM (p : Purity) (Γ : FCtx ν (Ty α)) (β : UBB φ ν κ) (L : FLCtx κ ν (Ty α)) : Type _ :=
  (live : FCtx ν (Ty α))
  (body : β.body.FWfM p Γ live)
  (terminator : β.terminator.FWfM live L)

def UBB.FWfM.toFWf {p : Purity} {Γ : FCtx ν (Ty α)} {β : UBB φ ν κ} {L : FLCtx κ ν (Ty α)} (dβ : UBB.FWfM p Γ β L) : UBB.FWf p Γ β L
  where
  live := dβ.live
  body := dβ.body
  terminator := dβ.terminator.toFWf

structure UBB.FWf' (p : Purity) (Γ : FCtx ν (Ty α)) (β : UBB φ ν κ) (L : FLCtx κ ν (Ty α)) : Type _ :=
  (trg : FLCtx κ ν (Ty α))
  (FWfM : β.FWfM p Γ trg)
  (wk : trg.Wk L)

def UBB.FWf'.toFWf {p : Purity} {Γ : FCtx ν (Ty α)} {β : UBB φ ν κ} {L : FLCtx κ ν (Ty α)} (dβ : UBB.FWf' p Γ β L) : UBB.FWf p Γ β L
  where
  live := dβ.FWfM.live
  body := dβ.FWfM.body
  terminator := dβ.FWfM.terminator.toFWf.wkExit dβ.wk

def UBB.FWf.factor {p : Purity} {Γ : FCtx ν (Ty α)} {β : UBB φ ν κ} {L : FLCtx κ ν (Ty α)} (dβ : UBB.FWf p Γ β L) : UBB.FWf' p Γ β L :=
  let dt := dβ.terminator.factor;
  {
    trg := _,
    FWfM := {
      live := dβ.live
      body := dβ.body
      terminator := dt.FWfM
    },
    wk := dt.wk
  }
