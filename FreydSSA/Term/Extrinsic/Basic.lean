import Mathlib.Data.List.Basic
import Std.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Init.Classical

import FreydSSA.Ctx
import FreydSSA.InstSet
import FreydSSA.Untyped

variable {φ ν α} [Φ : InstSet φ (Ty α)]

inductive UTm.Wf : Purity → Ctx ν (Ty α) → UTm φ ν → Ty α → Type _
  | var (p) : Γ.Wk [⟨x, A⟩] → Wf p Γ (var x) A
  | op : Φ.Op f p A B → Wf 1 Γ e A → Wf p Γ (op f e) B
  | pair (p) : Wf 1 Γ l A → Wf 1 Γ r B → Wf p Γ (pair l r) (A.pair B)
  | unit (p) : Wf p Γ unit Ty.unit
  | bool (p b) : Wf p Γ (bool b) Ty.bool

variable {Γ Δ : Ctx ν (Ty α)}

theorem UTm.Wf.ty_eq [Φc : CohInstSet φ (Ty α)] {e : UTm φ ν}
  (de : e.Wf p Γ A) (de' : e.Wf p' Γ A') : A = A' := by induction de generalizing p' A' with
  | var _ w => cases de' with | var _ w' => exact w.ty_eq w'
  | op hf _ I => cases de' with | op hf' de' => exact Φc.coh_trg' hf hf' (I de')
  | pair _ _ _ I1 I2 => cases de' with | pair _ dl' dr' => rw [I1 dl', I2 dr']
  | _ => cases de'; rfl

theorem UTm.Wf.allEq [Φc : CohInstSet φ (Ty α)] {e : UTm φ ν}
  (de : e.Wf p Γ A) (de' : e.Wf p Γ A) : de = de' := by induction de with
  | var _ w => cases de' with | var _ w' => rw [Ctx.Wk.allEq w w']
  | op hf de I => cases de' with | op hf' de' =>
    cases de.ty_eq de'
    rw [I de']
  | pair _ dl dr Il Ir => cases de' with | pair _ dl' dr' => rw [Il dl', Ir dr']
  | _ => cases de'; rfl

def UTm.Wf.wk {e : UTm φ ν} (w : Γ.Wk Δ) : e.Wf p Δ A → e.Wf p Γ A
  | var p w' => var p (w.comp w')
  | op hf de => op hf (de.wk w)
  | pair p dl dr => pair p (dl.wk w) (dr.wk w)
  | unit p => unit p
  | bool p b => bool p b
