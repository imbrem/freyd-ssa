import Mathlib.Logic.Lemmas

import FreydSSA.Ctx.Var.Fun
import FreydSSA.InstSet
import FreydSSA.Untyped

variable {φ ν α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq α]

inductive UTm.FWf : Purity → FCtx ν (Ty α) → UTm φ ν → Ty α → Type _
  | var {x} {A : Ty α} (p)  : Γ x = (A : WithBot _) → FWf p Γ (var x) A
  | op : Φ.Op f p A B → FWf 1 Γ e A → FWf p Γ (op f e) B
  | pair (p) : FWf 1 Γ l A → FWf 1 Γ r B → FWf p Γ (pair l r) (A.pair B)
  | unit (p) : FWf p Γ unit Ty.unit
  | bool (p b) : FWf p Γ (bool b) Ty.bool

variable {Γ Δ : FCtx ν (Ty α)}

def UTm.FWf.of_pure {e : UTm φ ν} : e.FWf 1 Γ A → e.FWf p Γ A
  | var _ w => var p w
  | op hf de => op hf.of_pure (de.of_pure)
  | pair _ dl dr => pair p (dl.of_pure) (dr.of_pure)
  | unit _ => unit p
  | bool _ b => bool p b

theorem FCtx.Cmp.tyEq {Γ Δ : FCtx ν (Ty α)} {e : UTm φ ν}
  (c : Γ.Cmp Δ) (de : UTm.FWf p Γ e A) (de' : UTm.FWf p' Δ e A') : A = A'
  := by induction de generalizing p' Δ A' with
  | var _ w => cases de' with | var _ w' => exact c.var_eq _ _ _ w w'
  | op hf _ I => cases de' with | op hf' de' => exact Φc.coh_trg' hf hf' (I c de')
  | pair _ _ _ I1 I2 => cases de' with | pair _ dl' dr' => rw [I1 c dl', I2 c dr']
  | _ => cases de'; rfl

theorem UTm.FWf.tyEq {e : UTm φ ν} (de : e.FWf p Γ A) (de' : e.FWf p' Γ A')
  : A = A' := (FCtx.Cmp.refl Γ).tyEq de de'

theorem UTm.FWf.allEq {e : UTm φ ν}
  (de : e.FWf p Γ A) (de' : e.FWf p Γ A) : de = de' := by induction de with
  | var _ w => cases de' with | var _ w' => rfl
  | op hf de I => cases de' with | op hf' de' =>
    cases de.tyEq de'
    rw [I de']
  | pair _ dl dr Il Ir => cases de' with | pair _ dl' dr' => rw [Il dl', Ir dr']
  | _ => cases de'; rfl

theorem UTm.FWf.allHeq {e : UTm φ ν}
  (de : e.FWf p Γ A) (de' : e.FWf p Γ A') : HEq de de'
  := by cases de.tyEq de'; apply Eq.heq; apply allEq

def UTm.FWf.wk {e : UTm φ ν} (w : Γ.Wk Δ) : e.FWf p Δ A → e.FWf p Γ A
  | var p w' => var p (w.var _ _ w')
  | op hf de => op hf (de.wk w)
  | pair p dl dr => pair p (dl.wk w) (dr.wk w)
  | unit p => unit p
  | bool p b => bool p b

def UTm.FWf.linf {e : UTm φ ν} : e.FWf p Γ A → e.FWf p' Δ A' → e.FWf p (Γ.linf Δ) A
  | var p w, var _ w' => var p (by rw [FCtx.linf_right_var_eq_left _ _ w']; exact w)
  | op hf de, op _ de' => op hf (de.linf de')
  | pair p dl dr, pair _ dl' dr' => pair p (dl.linf dl') (dr.linf dr')
  | unit p, _ => unit p
  | bool p b, _ => bool p b

def UTm.FWf.rinf {e : UTm φ ν} : e.FWf p Γ A → e.FWf p' Δ A' → e.FWf p' (Γ.rinf Δ) A'
  | var _ w, var p' w' => var p' (by rw [FCtx.rinf_left_var_eq_right _ _ w]; exact w')
  | op _ de, op hf' de' => op hf' (de.rinf de')
  | pair _ dl dr, pair p' dl' dr' => pair p' (dl.rinf dl') (dr.rinf dr')
  | _, unit p' => unit p'
  | _, bool p' b => bool p' b

def FCtx.Cmp.wfInf {e : UTm φ ν} (c : Γ.Cmp Δ) : e.FWf p Γ A → e.FWf p' Δ A' → e.FWf p (Γ.inf Δ) A
  | UTm.FWf.var p w, UTm.FWf.var _ w' => UTm.FWf.var p
    (by rw [c.inf_eq_linf, linf_right_var_eq_left _ _ w']; exact w)
  | UTm.FWf.op hf de, UTm.FWf.op _ de' => UTm.FWf.op hf (c.wfInf de de')
  | UTm.FWf.pair p dl dr, UTm.FWf.pair _ dl' dr' => UTm.FWf.pair p (c.wfInf dl dl') (c.wfInf dr dr')
  | UTm.FWf.unit p, _ => UTm.FWf.unit p
  | UTm.FWf.bool p b, _ => UTm.FWf.bool p b

def UTm.FWf.restrict {e : UTm φ ν} : e.FWf p Γ A → e.FWf p (Γ.restrict e.vars) A
  | var p w => var p (by simp [vars, FCtx.restrict_app, w])
  | op hf de => op hf de.restrict
  | pair p dl dr => pair p
    (dl.restrict.wk (FCtx.Wk.restrict_union_left _ _ _))
    (dr.restrict.wk (FCtx.Wk.restrict_union_right _ _ _))
  | unit p => unit p
  | bool p b => bool p b

def UTm.FWf.vars_sub_support {e : UTm φ ν} : e.FWf p Γ A → e.vars ⊆ Γ.support
  | var p w => by simp [vars, FCtx.mem_support, w]
  | op hf de => de.vars_sub_support
  | pair p dl dr => Finset.union_subset dl.vars_sub_support dr.vars_sub_support
  | unit p => by simp [vars]
  | bool p b => by simp [vars]

--TODO: cmp ==> inf = linf without alleq, rinf with
