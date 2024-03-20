import Mathlib.Logic.Lemmas

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

def UTm.Wf.of_pure {e : UTm φ ν} : e.Wf 1 Γ A → e.Wf p Γ A
  | Wf.var _ w => Wf.var p w
  | Wf.op hf de => Wf.op hf.of_pure (de.of_pure)
  | Wf.pair _ dl dr => Wf.pair p (dl.of_pure) (dr.of_pure)
  | Wf.unit _ => Wf.unit p
  | Wf.bool _ b => Wf.bool p b

theorem UTm.Wf.tyEq [Φc : CohInstSet φ (Ty α)] {e : UTm φ ν}
  (de : e.Wf p Γ A) (de' : e.Wf p' Γ A') : A = A' := by induction de generalizing p' A' with
  | var _ w => cases de' with | var _ w' => exact w.tyEq w'
  | op hf _ I => cases de' with | op hf' de' => exact Φc.coh_trg' hf hf' (I de')
  | pair _ _ _ I1 I2 => cases de' with | pair _ dl' dr' => rw [I1 dl', I2 dr']
  | _ => cases de'; rfl

theorem UTm.Wf.allEq [Φc : CohInstSet φ (Ty α)] {e : UTm φ ν}
  (de : e.Wf p Γ A) (de' : e.Wf p Γ A) : de = de' := by induction de with
  | var _ w => cases de' with | var _ w' => rw [Ctx.Wk.allEq w w']
  | op hf de I => cases de' with | op hf' de' =>
    cases de.tyEq de'
    rw [I de']
  | pair _ dl dr Il Ir => cases de' with | pair _ dl' dr' => rw [Il dl', Ir dr']
  | _ => cases de'; rfl

theorem UTm.Wf.allHeq [Φc : CohInstSet φ (Ty α)] {e : UTm φ ν}
  (de : e.Wf p Γ A) (de' : e.Wf p Γ A') : HEq de de'
  := by cases de.tyEq de'; apply Eq.heq; apply allEq

def UTm.Wf.wk {e : UTm φ ν} (w : Γ.Wk Δ) : e.Wf p Δ A → e.Wf p Γ A
  | var p w' => var p (w.comp w')
  | op hf de => op hf (de.wk w)
  | pair p dl dr => pair p (dl.wk w) (dr.wk w)
  | unit p => unit p
  | bool p b => bool p b

inductive UTm.Wf.Iso {Γ' : Ctx ν' (Ty α)}
  : {e : UTm φ ν} → {e' : UTm φ ν'} → e.Wf p Γ A → e'.Wf p Γ' A → Prop
  | var (p) : w.Iso w' → Iso (var p w) (var p w')
  | op (hf) : de.Iso de' → Iso (op hf de) (op hf de')
  | pair (p) : dl.Iso dl' → dr.Iso dr' → Iso (pair p dl dr) (pair p dl' dr')
  | unit (p) : Iso (unit p) (unit p)
  | bool (p b) : Iso (bool p b) (bool p b)

theorem UTm.Wf.Iso.refl {Γ : Ctx ν (Ty α)} {e : UTm φ ν} : (de : e.Wf p Γ A) → de.Iso de
  | Wf.var p w => var p (Ctx.Wk.Iso.refl w)
  | Wf.op hf de => op hf (refl de)
  | Wf.pair p dl dr => pair p (refl dl) (refl dr)
  | Wf.unit p => unit p
  | Wf.bool p b => bool p b

theorem UTm.Wf.Iso.symm {Γ : Ctx ν (Ty α)} {Γ' : Ctx ν' (Ty α)} {e : UTm φ ν} {e' : UTm φ ν'}
  {de : e.Wf p Γ A} {de' : e'.Wf p Γ' A} : de.Iso de' → de'.Iso de
  | var p w => var p w.symm
  | op hf de => op hf (symm de)
  | pair p dl dr => pair p (symm dl) (symm dr)
  | unit p => unit p
  | bool p b => bool p b

theorem UTm.Wf.Iso.trans
  {Γ : Ctx ν (Ty α)} {Γ' : Ctx ν' (Ty α)} {Γ'' : Ctx ν'' (Ty α)}
  {e : UTm φ ν} {e' : UTm φ ν'} {e'' : UTm φ ν''}
  {de : e.Wf p Γ A} {de' : e'.Wf p Γ' A} {de'' : e''.Wf p Γ'' A}
  : de.Iso de' → de'.Iso de'' → de.Iso de''
  | var p w, var _ w' => var p (w.trans w')
  | op hf de, op _ de' => op hf (de.trans de')
  | pair p dl dr, pair _ dl' dr' => pair p (dl.trans dl') (dr.trans dr')
  | unit _, unit _ => unit _
  | bool _ _, bool _ _ => bool _ _

theorem UTm.Wf.Iso.wk
  {Γ Δ : Ctx ν (Ty α)} {Γ' Δ' : Ctx ν' (Ty α)} {e : UTm φ ν} {e' : UTm φ ν'}
  {w : Γ.Wk Δ} {w' : Γ'.Wk Δ'}
  {de : e.Wf p Δ A} {de' : e'.Wf p Δ' A}
  (hw : w.Iso w')
  : de.Iso de' → (de.wk w).Iso (de'.wk w')
  | var p hw' => var p (hw.comp hw')
  | op hf de => op hf (de.wk hw)
  | pair p dl dr => pair p (dl.wk hw) (dr.wk hw)
  | unit p => unit p
  | bool p b => bool p b
