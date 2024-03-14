import Mathlib.Data.List.Basic
import Std.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Init.Classical

import FreydSSA.Term.Extrinsic.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

inductive UBody.Wf : Purity → Ctx ν (Ty α) → UBody φ ν → Ctx ν (Ty α) → Type _
  | nil (p) : Γ.Wk Δ → Wf p Γ nil Δ
  | let1 : e.Wf p Γ A → Wf p (⟨x, A⟩::Γ) b Δ → Wf p Γ (let1 x e b) Δ
  | let2 : e.Wf p Γ (A.pair B) → Wf p (⟨x, A⟩::⟨y, B⟩::Γ) b Δ → Wf p Γ (let2 x y e b) Δ

def UBody.Wf.src {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν} (_: b.Wf p Γ Δ) : Ctx ν (Ty α) := Γ
def UBody.Wf.trg {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν} (_: b.Wf p Γ Δ) : Ctx ν (Ty α) := Δ

theorem UBody.Wf.allEq {Γ Δ : Ctx ν (Ty α)} [Φc : CohInstSet φ (Ty α)] {b : UBody φ ν}
  : (db db' : b.Wf p Γ Δ) → db = db'
  | nil _ w, nil _ w' => by rw [w.allEq w']
  | let1 de db, let1 de' db' => by cases de.ty_eq de'; rw [de.allEq de', db.allEq db']
  | let2 de db, let2 de' db' => by cases de.ty_eq de'; rw [de.allEq de', db.allEq db']

def UBody.Wf.wk_entry {Γ Δ Ξ : Ctx ν (Ty α)} {b : UBody φ ν} (w : Γ.Wk Δ)
  : b.Wf p Δ Ξ → b.Wf p Γ Ξ
  | nil p w' => nil p (w.comp w')
  | let1 de db => let1 (de.wk w) (db.wk_entry (w.cons _))
  | let2 de db => let2 (de.wk w) (db.wk_entry ((w.cons _).cons _))

def UBody.Wf.wk_exit {Γ Δ Ξ : Ctx ν (Ty α)} {b : UBody φ ν}
  : b.Wf p Γ Δ → (w : Δ.Wk Ξ) → b.Wf p Γ Ξ
  | nil p w, w' => nil p (w.comp w')
  | let1 de db, w => let1 de (db.wk_exit w)
  | let2 de db, w => let2 de (db.wk_exit w)

--TODO: wk_{entry, exit} is iso-preserving

inductive UBody.Wf.Iso
  : {Γ Δ : Ctx ν (Ty α)} → {Γ' Δ' : Ctx ν' (Ty α)}
  → {b : UBody φ ν} → {b' : UBody φ ν'} → b.Wf p Γ Δ → b'.Wf p Γ' Δ' → Prop
  | nil {w w'} : w.Iso w' → Iso (nil p w) (nil p w')
  | let1 : de.Iso de' → db.Iso db' → Iso (let1 de db) (let1 de' db')
  | let2 : de.Iso de' → db.Iso db' → Iso (let2 de db) (let2 de' db')

inductive UBody.WfM : Purity → Ctx ν (Ty α) → UBody φ ν → Ctx ν (Ty α) → Type _
  | nil (p Γ) : WfM p Γ nil Γ
  | let1 : e.Wf p Γ A → WfM p (⟨x, A⟩::Γ) b Δ → WfM p Γ (let1 x e b) Δ
  | let2 : e.Wf p Γ (A.pair B) → WfM p (⟨x, A⟩::⟨y, B⟩::Γ) b Δ → WfM p Γ (let2 x y e b) Δ

def UBody.WfM.src {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν} (_: b.WfM p Γ Δ) : Ctx ν (Ty α) := Γ
def UBody.WfM.trg {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν} (_: b.WfM p Γ Δ) : Ctx ν (Ty α) := Δ

theorem UBody.WfM.allEq {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν}
  : (db db' : b.WfM p Γ Δ) → db = db'
  | nil _ _, nil _ _ => rfl
  | let1 de db, let1 de' db' => by cases de.ty_eq de'; rw [de.allEq de', db.allEq db']
  | let2 de db, let2 de' db' => by cases de.ty_eq de'; rw [de.allEq de', db.allEq db']

theorem UBody.WfM.trgEq {Γ Δ Δ' : Ctx ν (Ty α)}  {b : UBody φ ν}
  : (db : b.WfM p Γ Δ) → (db' : b.WfM p Γ Δ') → Δ = Δ'
  | nil _ _, nil _ _ => rfl
  | let1 de db, let1 de' db' => by cases de.ty_eq de'; rw [UBody.WfM.trgEq db db']
  | let2 de db, let2 de' db' => by cases de.ty_eq de'; rw [UBody.WfM.trgEq db db']

inductive UBody.WfM.Iso
  : {Γ Δ : Ctx ν (Ty α)} → {Γ' Δ' : Ctx ν' (Ty α)}
  → {b : UBody φ ν} → {b' : UBody φ ν'} → b.WfM p Γ Δ → b'.WfM p Γ' Δ' → Prop
  | nil {w w'} : w.Iso w' → Iso (nil p w) (nil p w')
  | let1 : de.Iso de' → db.Iso db' → Iso (let1 de db) (let1 de' db')
  | let2 : de.Iso de' → db.Iso db' → Iso (let2 de db) (let2 de' db')

def UBody.WfM.toWf {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν}
  : b.WfM p Γ Δ → b.Wf p Γ Δ
  | nil p Γ => Wf.nil p (Ctx.Wk.refl Γ)
  | let1 de db => Wf.let1 de (db.toWf)
  | let2 de db => Wf.let2 de (db.toWf)

--TODO: toWf is iso-preserving

def UBody.Wf.maxTrg {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν}
  : b.Wf p Γ Δ → Ctx ν (Ty α)
  | nil p w => w.src
  | let1 _ db => db.maxTrg
  | let2 _ db => db.maxTrg

def UBody.Wf.wkMaxTrg {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν}
  : (db : b.Wf p Γ Δ) → db.maxTrg.Wk Δ
  | nil p w => w
  | let1 _ db => db.wkMaxTrg
  | let2 _ db => db.wkMaxTrg

--TODO: SSA means maxTrg also weakens to Γ

def UBody.Wf.toMaxTrg {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν}
  : (db : b.Wf p Γ Δ) → b.Wf p Γ db.maxTrg
  | nil p _ => Wf.nil p (Ctx.Wk.refl _)
  | let1 de db => Wf.let1 de (db.toMaxTrg)
  | let2 de db => Wf.let2 de (db.toMaxTrg)

def UBody.Wf.toWfM {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν}
  : (db : b.Wf p Γ Δ) → b.WfM p Γ db.maxTrg
  | nil p _ => WfM.nil p _
  | let1 de db => WfM.let1 de (db.toWfM)
  | let2 de db => WfM.let2 de (db.toWfM)

--TODO: toWfM is iso-preserving

structure UBody.Wf' (p : Purity) (Γ) (b : UBody φ ν) (Δ : Ctx ν (Ty α)) : Type _ :=
  maxTrg : Ctx ν (Ty α)
  wfM : b.WfM p Γ maxTrg
  wk : maxTrg.Wk Δ

def UBody.Wf.toWf' {p} {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν} (db : b.Wf p Γ Δ) : b.Wf' p Γ Δ :=
  ⟨_, db.toWfM, db.wkMaxTrg⟩

def UBody.Wf'.toWf {p} {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν} (db : b.Wf' p Γ Δ) : b.Wf p Γ Δ :=
  db.wfM.toWf.wk_exit db.wk

theorem UBody.Wf'.allEq {p} {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν}
  : (db db' : b.Wf' p Γ Δ) → db = db'
  | ⟨_, db, w⟩, ⟨_, db', w'⟩ => by cases db.trgEq db'; cases db.allEq db'; cases w.allEq w'; rfl

theorem UBody.Wf'.wk_exit {p} {Γ Δ Ξ : Ctx ν (Ty α)} {b : UBody φ ν}
  (db : b.Wf' p Γ Δ) (w : Δ.Wk Ξ) : b.Wf' p Γ Ξ where
  maxTrg := db.maxTrg
  wfM := db.wfM
  wk := db.wk.comp w

theorem UBody.Wf'.wk_entry {p} {Γ Δ Ξ : Ctx ν (Ty α)} {b : UBody φ ν}
  (w : Γ.Wk Δ) (db : b.Wf' p Δ Ξ) : b.Wf' p Γ Ξ
  := (db.toWf.wk_entry w).toWf'

structure UBody.Wf'.Iso {p} {Γ Δ : Ctx ν (Ty α)} {Γ' Δ' : Ctx ν' (Ty α)}
  {b : UBody φ ν} {b' : UBody φ ν'}
  (db : Wf' p Γ b Δ) (db' : Wf' p Γ' b' Δ') : Prop :=
  wfM : db.wfM.Iso db'.wfM
  wk : db.wk.Iso db'.wk

--TODO: toWf', toWf are iso-preserving
