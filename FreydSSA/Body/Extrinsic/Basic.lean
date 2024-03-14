import Mathlib.Data.List.Basic
import Std.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Init.Classical

import FreydSSA.Term.Extrinsic.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)]

inductive UBody.Wf : Purity → Ctx ν (Ty α) → UBody φ ν → Ctx ν (Ty α) → Type _
  | nil (p) : Γ.Wk Δ → Wf p Γ nil Δ
  | let1 : e.Wf p Γ A → Wf p (⟨x, A⟩::Γ) b Δ → Wf p Γ (let1 x e b) Δ
  | let2 : e.Wf p Γ (A.pair B) → Wf p (⟨x, A⟩::⟨y, B⟩::Γ) b Δ → Wf p Γ (let2 x y e b) Δ

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
