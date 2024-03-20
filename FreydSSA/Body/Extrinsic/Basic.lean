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
  | let1 de db, let1 de' db' => by cases de.tyEq de'; rw [de.allEq de', db.allEq db']
  | let2 de db, let2 de' db' => by cases de.tyEq de'; rw [de.allEq de', db.allEq db']

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

def UBody.Wf.comp {Γ Δ Ξ : Ctx ν (Ty α)} {b b' : UBody φ ν}
  : b.Wf p Γ Δ → b'.Wf p Δ Ξ → (b.comp b').Wf p Γ Ξ
  | nil p w, db' => wk_entry w db'
  | let1 de db, db' => let1 de (db.comp db')
  | let2 de db, db' => let2 de (db.comp db')

inductive UBody.Wf.Iso
  : {Γ Δ : Ctx ν (Ty α)} → {Γ' Δ' : Ctx ν' (Ty α)}
  → {b : UBody φ ν} → {b' : UBody φ ν'} → b.Wf p Γ Δ → b'.Wf p Γ' Δ' → Prop
  | nil (p) {w w'} : w.Iso w' → Iso (nil p w) (nil p w')
  | let1 : de.Iso de' → db.Iso db' → Iso (let1 de db) (let1 de' db')
  | let2 : de.Iso de' → db.Iso db' → Iso (let2 de db) (let2 de' db')

theorem UBody.Wf.Iso.wk_entry {Γ Δ Ξ : Ctx ν (Ty α)} {Γ' Δ' Ξ' : Ctx ν' (Ty α)}
  {b : UBody φ ν} {b' : UBody φ ν'}
  {w : Γ.Wk Δ} {w' : Γ'.Wk Δ'}
  {db : b.Wf p Δ Ξ} {db' : b'.Wf p Δ' Ξ'}
  (hw : w.Iso w') : db.Iso db' → (db.wk_entry w).Iso (db'.wk_entry w')
  | nil p hw' => nil p (hw.comp hw')
  | let1 he hb => let1 (he.wk hw) (hb.wk_entry hw.cons)
  | let2 he hb => let2 (he.wk hw) (hb.wk_entry hw.cons.cons)

theorem UBody.Wf.Iso.wk_exit {Γ Δ Ξ : Ctx ν (Ty α)} {Γ' Δ' Ξ' : Ctx ν' (Ty α)}
  {b : UBody φ ν} {b' : UBody φ ν'}
  {w : Δ.Wk Ξ} {w' : Δ'.Wk Ξ'}
  {db : b.Wf p Γ Δ} {db' : b'.Wf p Γ' Δ'}
  (hw : w.Iso w') : db.Iso db' → (db.wk_exit w).Iso (db'.wk_exit w')
  | nil p hw' => nil p (hw'.comp hw)
  | let1 he hb => let1 he (hb.wk_exit hw)
  | let2 he hb => let2 he (hb.wk_exit hw)

theorem UBody.Wf.Iso.comp {Γ Δ Ξ : Ctx ν (Ty α)} {Γ' Δ' Ξ' : Ctx ν' (Ty α)}
  {b₁ b₂ : UBody φ ν} {b₁' b₂' : UBody φ ν'}
  {db₁ : b₁.Wf p Γ Δ} {db₁' : b₁'.Wf p Γ' Δ'}
  {db₂ : b₂.Wf p Δ Ξ} {db₂' : b₂'.Wf p Δ' Ξ'}
  : db₁.Iso db₁' → db₂.Iso db₂' → (db₁.comp db₂).Iso (db₁'.comp db₂')
  | nil _p hw, db' => db'.wk_entry hw
  | let1 he hb, db' => let1 he (hb.comp db')
  | let2 he hb, db' => let2 he (hb.comp db')

inductive UBody.WfM : Purity → Ctx ν (Ty α) → UBody φ ν → Ctx ν (Ty α) → Type _
  | nil (p Γ) : WfM p Γ nil Γ
  | let1 : e.Wf p Γ A → WfM p (⟨x, A⟩::Γ) b Δ → WfM p Γ (let1 x e b) Δ
  | let2 : e.Wf p Γ (A.pair B) → WfM p (⟨x, A⟩::⟨y, B⟩::Γ) b Δ → WfM p Γ (let2 x y e b) Δ

def UBody.WfM.src {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν} (_: b.WfM p Γ Δ) : Ctx ν (Ty α) := Γ
def UBody.WfM.trg {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν} (_: b.WfM p Γ Δ) : Ctx ν (Ty α) := Δ

theorem UBody.WfM.allEq {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν}
  : (db db' : b.WfM p Γ Δ) → db = db'
  | nil _ _, nil _ _ => rfl
  | let1 de db, let1 de' db' => by cases de.tyEq de'; rw [de.allEq de', db.allEq db']
  | let2 de db, let2 de' db' => by cases de.tyEq de'; rw [de.allEq de', db.allEq db']

theorem UBody.WfM.trgEq {Γ Δ Δ' : Ctx ν (Ty α)}  {b : UBody φ ν}
  : (db : b.WfM p Γ Δ) → (db' : b.WfM p Γ Δ') → Δ = Δ'
  | nil _ _, nil _ _ => rfl
  | let1 de db, let1 de' db' => by cases de.tyEq de'; rw [UBody.WfM.trgEq db db']
  | let2 de db, let2 de' db' => by cases de.tyEq de'; rw [UBody.WfM.trgEq db db']

theorem UBody.WfM.allHeq {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν}
  (db : b.WfM p Γ Δ) (db' : b.WfM p Γ Δ') : HEq db db' :=
  by cases db.trgEq db'; exact (db.allEq db').heq

inductive UBody.WfM.Iso
  : {Γ Δ : Ctx ν (Ty α)} → {Γ' Δ' : Ctx ν' (Ty α)}
  → {b : UBody φ ν} → {b' : UBody φ ν'} → b.WfM p Γ Δ → b'.WfM p Γ' Δ' → Prop
  | nil (p) : Γ.length = Γ'.length → Iso (nil p Γ) (nil p Γ')
  | let1 : de.Iso de' → db.Iso db' → Iso (let1 de db) (let1 de' db')
  | let2 : de.Iso de' → db.Iso db' → Iso (let2 de db) (let2 de' db')

def UBody.WfM.toWf {Γ Δ : Ctx ν (Ty α)} {b : UBody φ ν}
  : b.WfM p Γ Δ → b.Wf p Γ Δ
  | nil p Γ => Wf.nil p (Ctx.Wk.refl Γ)
  | let1 de db => Wf.let1 de (db.toWf)
  | let2 de db => Wf.let2 de (db.toWf)

theorem UBody.WfM.Iso.toWf {Γ Δ : Ctx ν (Ty α)}
  {Γ' Δ' : Ctx ν' (Ty α)}  {b : UBody φ ν} {b' : UBody φ ν'}
  {db : b.WfM p Γ Δ} {db' : b'.WfM p Γ' Δ'}
  : db.Iso db' → db.toWf.Iso db'.toWf
  | nil p hΓ => Wf.Iso.nil p (Ctx.Wk.Iso.of_length_eq hΓ)
  | let1 he hb => Wf.Iso.let1 he hb.toWf
  | let2 he hb => Wf.Iso.let2 he hb.toWf

--TODO: why the unused variable warning otherwise
set_option linter.unusedVariables false in
def UBody.WfM.comp {Γ Δ Ξ : Ctx ν (Ty α)} {b b' : UBody φ ν}
  : b.WfM p Γ Δ → b'.WfM p Δ Ξ → (b.comp b').WfM p Γ Ξ
  | nil _ _, db' => db'
  | let1 de db, db' => let1 de (db.comp db')
  | let2 de db, db' => let2 de (db.comp db')

def UBody.WfM.wk_entry {Γ Δ Ξ : Ctx ν (Ty α)} {b : UBody φ ν} (w : Γ.Wk Δ)
  : b.WfM p Δ Ξ → (Ξ' : Ctx ν (Ty α)) × (b.WfM p Γ Ξ') × (Ξ'.Wk Ξ)
  | nil p Γ => ⟨_, nil p _, w⟩
  | let1 de db =>
    let ⟨Ξ', db', w'⟩ := db.wk_entry (w.cons _);
    ⟨Ξ', let1 (de.wk w) db', w'⟩
  | let2 de db =>
    let ⟨Ξ', db', w'⟩ := db.wk_entry ((w.cons _).cons _);
    ⟨Ξ', let2 (de.wk w) db', w'⟩

theorem UBody.WfM.Iso.comp {Γ Δ Ξ : Ctx ν (Ty α)} {Γ' Δ' Ξ' : Ctx ν' (Ty α)}
  {b₁ b₂ : UBody φ ν} {b₁' b₂' : UBody φ ν'}
  {db₁ : b₁.WfM p Γ Δ} {db₁' : b₁'.WfM p Γ' Δ'}
  {db₂ : b₂.WfM p Δ Ξ} {db₂' : b₂'.WfM p Δ' Ξ'}
  : db₁.Iso db₁' → db₂.Iso db₂' → (db₁.comp db₂).Iso (db₁'.comp db₂')
  | nil _p _, db' => db'
  | let1 he hb, db' => let1 he (hb.comp db')
  | let2 he hb, db' => let2 he (hb.comp db')

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

theorem UBody.Wf.maxTrgEq {Γ Δ Δ' : Ctx ν (Ty α)} {b : UBody φ ν}
  (db : b.Wf p Γ Δ) (db' : b.Wf p Γ Δ') : db.maxTrg = db'.maxTrg
  := db.toWfM.trgEq db'.toWfM

theorem UBody.Wf.Iso.toWfM {Γ Δ : Ctx ν (Ty α)}
  {Γ' Δ' : Ctx ν' (Ty α)}  {b : UBody φ ν} {b' : UBody φ ν'}
  {db : b.Wf p Γ Δ} {db' : b'.Wf p Γ' Δ'}
  : db.Iso db' → db.toWfM.Iso db'.toWfM
  | nil p hΓ => WfM.Iso.nil p hΓ.length_eq_src
  | let1 he hb => WfM.Iso.let1 he hb.toWfM
  | let2 he hb => WfM.Iso.let2 he hb.toWfM

theorem UBody.Wf.Iso.wkMaxTrg {Γ Δ : Ctx ν (Ty α)}
  {Γ' Δ' : Ctx ν' (Ty α)}  {b : UBody φ ν} {b' : UBody φ ν'}
  {db : b.Wf p Γ Δ} {db' : b'.Wf p Γ' Δ'}
  : db.Iso db' → db.wkMaxTrg.Iso db'.wkMaxTrg
  | nil p hΓ => hΓ
  | let1 _ hb => hb.wkMaxTrg
  | let2 _ hb => hb.wkMaxTrg

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

def UBody.Wf'.wk_exit {p} {Γ Δ Ξ : Ctx ν (Ty α)} {b : UBody φ ν}
  (db : b.Wf' p Γ Δ) (w : Δ.Wk Ξ) : b.Wf' p Γ Ξ where
  maxTrg := db.maxTrg
  wfM := db.wfM
  wk := db.wk.comp w

def UBody.Wf'.wk_entry {p} {Γ Δ Ξ : Ctx ν (Ty α)} {b : UBody φ ν}
  (w : Γ.Wk Δ) (db : b.Wf' p Δ Ξ) : b.Wf' p Γ Ξ
  := (db.toWf.wk_entry w).toWf'

def UBody.WfM.comp' {p} {Γ Δ Ξ : Ctx ν (Ty α)} {b b' : UBody φ ν}
  (db : b.WfM p Γ Δ) (db' : b'.Wf' p Δ Ξ) : (b.comp b').Wf' p Γ Ξ where
  maxTrg := db'.maxTrg
  wfM := db.comp db'.wfM
  wk := db'.wk

def UBody.Wf'.comp {p} {Γ Δ Ξ : Ctx ν (Ty α)} {b b' : UBody φ ν}
  (db : b.Wf' p Γ Δ) (db' : b'.Wf' p Δ Ξ) : (b.comp b').Wf' p Γ Ξ
  := db.wfM.comp' (db'.wk_entry db.wk)

structure UBody.Wf'.Iso {p} {Γ Δ : Ctx ν (Ty α)} {Γ' Δ' : Ctx ν' (Ty α)}
  {b : UBody φ ν} {b' : UBody φ ν'}
  (db : Wf' p Γ b Δ) (db' : Wf' p Γ' b' Δ') : Prop :=
  wfM : db.wfM.Iso db'.wfM
  wk : db.wk.Iso db'.wk

theorem UBody.Wf.Iso.toWf' {p} {Γ Δ : Ctx ν (Ty α)} {Γ' Δ' : Ctx ν' (Ty α)}
  {b : UBody φ ν} {b' : UBody φ ν'}
  {db : b.Wf p Γ Δ} {db' : b'.Wf p Γ' Δ'}
  (hb : db.Iso db') : db.toWf'.Iso db'.toWf' where
  wfM := hb.toWfM
  wk := hb.wkMaxTrg

theorem UBody.Wf'.Iso.toWf {p} {Γ Δ : Ctx ν (Ty α)} {Γ' Δ' : Ctx ν' (Ty α)}
  {b : UBody φ ν} {b' : UBody φ ν'}
  {db : b.Wf' p Γ Δ} {db' : b'.Wf' p Γ' Δ'}
  (hb : db.Iso db') : db.toWf.Iso db'.toWf
  := hb.wfM.toWf.wk_exit hb.wk
