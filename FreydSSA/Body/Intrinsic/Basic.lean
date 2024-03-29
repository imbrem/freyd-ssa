import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lattice
import Std.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Init.Classical

import FreydSSA.Ctx
import FreydSSA.InstSet
import FreydSSA.Term.Intrinsic.Basic

--TODO: do we need a version which forbids shadowing? but still need SSA reasoning...

inductive InstSet.Body {ν : Type u} {α : Type v} [Φ : InstSet φ (Ty α)]
  : Purity → Ctx ν (Ty α) → Ctx ν (Ty α) → Type _ where
  | nil (p) : Γ.Wk Δ → Φ.Body p Γ Δ
  | let1 : Φ.Tm p Γ a → Φ.Body p (⟨x, a⟩::Γ) Δ → Φ.Body p Γ Δ
  | let2 : Φ.Tm p Γ (Ty.pair A B)
    → Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ
    → Φ.Body p Γ Δ

inductive InstSet.Body.Iso [Φ : InstSet φ (Ty α)]: Φ.Body p Γ Δ → Φ.Body p Γ' Δ' → Prop
  | nil (p) : w.Iso w' → Iso (Body.nil p w) (Body.nil p w')
  | let1 : Tm.Iso e e' → Body.Iso b b' → Iso (Body.let1 e b) (Body.let1 e' b')
  | let2 : Tm.Iso e e' → Body.Iso b b' → Iso (Body.let2 e b) (Body.let2 e' b')

theorem InstSet.Body.Iso.refl [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)} {p}
  (e : Φ.Body p Γ Δ)
  : e.Iso e
  := by induction e with
  | nil _ I => constructor; exact I.iso_refl
  | _ =>
    constructor
    . apply Tm.Iso.refl
    . apply_assumption

theorem InstSet.Body.Iso.symm [Φ : InstSet φ (Ty α)]
  {e : Φ.Body p Γ Δ} {e' : Φ.Body p Γ' Δ'}
  (h : e.Iso e') : e'.Iso e
  := by induction h with
  | nil _ I => constructor; exact I.symm
  | _ =>
    constructor
    . apply Tm.Iso.symm; assumption
    . apply_assumption

theorem InstSet.Body.Iso.trans [Φ : InstSet φ (Ty α)]
  {e : Φ.Body p Γ Δ} {e' : Φ.Body p Γ' Δ'} {e'' : Φ.Body p Γ'' Δ''}
  (h : e.Iso e') (h' : e'.Iso e'') : e.Iso e''
  := by induction h generalizing Γ'' Δ'' with
  | nil _ I => cases h'; constructor; apply I.trans; assumption
  | _ =>
    cases h'
    constructor
    . apply Tm.Iso.trans <;> assumption
    . apply_assumption; assumption

def InstSet.Body.to_impure [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  : Φ.Body p Γ Δ → Φ.Body 0 Γ Δ
  | nil _ h => nil 0 h
  | let1 e b => let1 e.to_impure b.to_impure
  | let2 e b => let2 e.to_impure b.to_impure

def InstSet.Body.wk_entry [Φ : InstSet φ (Ty α)] {Γ Δ Ξ : Ctx ν (Ty α)}
  : Γ.Wk Δ → Φ.Body p Δ Ξ → Φ.Body p Γ Ξ
  | h, nil p h' => nil p (h.comp h')
  | h, let1 e b => let1 (Tm.wk h e) (wk_entry (h.cons _) b)
  | h, let2 e b => let2 (Tm.wk h e) (wk_entry ((h.cons _).cons _) b)

def InstSet.Body.wk_exit [Φ : InstSet φ (Ty α)] {Γ Δ Ξ : Ctx ν (Ty α)}
  : Φ.Body p Γ Δ → Δ.Wk Ξ → Φ.Body p Γ Ξ
  | nil p h, h' => nil p (h.comp h')
  | let1 e b, h' => let1 e (wk_exit b h')
  | let2 e b, h' => let2 e (wk_exit b h')

def InstSet.Body.comp [Φ : InstSet φ (Ty α)] {Γ Δ Ξ : Ctx ν (Ty α)}
  : Φ.Body p Γ Δ → Φ.Body p Δ Ξ → Φ.Body p Γ Ξ
  | nil p h, b => wk_entry h b
  | let1 e b, b' => let1 e (comp b b')
  | let2 e b, b' => let2 e (comp b b')

theorem InstSet.Body.Iso.wk_entry [Φ : InstSet φ (Ty α)]
  {Γ Δ Ξ : Ctx ν (Ty α)} {Γ' Δ' Ξ' : Ctx ν' (Ty α)}
  {w: Γ.Wk Δ} {w': Γ'.Wk Δ'} {b: Φ.Body p Δ Ξ} {b': Φ.Body p Δ' Ξ'}
  (hw: w.Iso w') (hb: b.Iso b')
  : (wk_entry w b).Iso (wk_entry w' b')
  := by induction hb with
  | nil => simp only [Body.wk_entry]; constructor; apply Ctx.Wk.Iso.comp <;> assumption
  | _ =>
    simp only [Body.wk_entry]
    constructor
    . apply Tm.Iso.wk <;> assumption
    . apply_assumption
      repeat constructor
      assumption

theorem InstSet.Body.Iso.wk_exit [Φ : InstSet φ (Ty α)]
  {Γ Δ Ξ' : Ctx ν (Ty α)} {Γ' Δ' Ξ' : Ctx ν' (Ty α)}
  {b: Φ.Body p Γ Δ} {b': Φ.Body p Γ' Δ'} {w: Δ.Wk Ξ} {w': Δ'.Wk Ξ'}
  (hw: w.Iso w') (hb: b.Iso b')
  : (wk_exit b w).Iso (wk_exit b' w')
  := by induction hb with
  | nil => simp only [Body.wk_exit]; constructor; apply Ctx.Wk.Iso.comp <;> assumption
  | _ =>
    simp only [Body.wk_exit]
    constructor
    . assumption
    . apply_assumption <;> assumption

theorem InstSet.Body.Iso.comp [Φ : InstSet φ (Ty α)]
  {l: Φ.Body p Γ Δ} {l': Φ.Body p Γ' Δ'}
  {r: Φ.Body p Δ Ξ} {r': Φ.Body p Δ' Ξ'}
  (hl: l.Iso l') (hr: r.Iso r')
  : (l.comp r).Iso (l'.comp r')
  := by induction hl with
  | nil _ hw => simp only [Body.comp]; exact wk_entry hw hr
  | _ =>
    simp only [Body.comp]
    constructor
    . assumption
    . apply_assumption; assumption

inductive InstSet.Body.InjOn [Φ : InstSet φ (Ty α)] (ρ : ν → ν')
  : {Γ Δ: Ctx ν (Ty α)} → Φ.Body p Γ Δ → Prop
  | nil {Γ Δ: Ctx ν (Ty α)} (h: Γ.Wk Δ): Γ.InjOn ρ → Body.InjOn ρ (Body.nil p h)
  | let1 {b: Φ.Body p (⟨x, A⟩::Γ) Δ} (e: Φ.Tm p Γ A): b.InjOn ρ → (b.let1 e).InjOn ρ
  | let2 {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ} (e: Φ.Tm p Γ (Ty.pair A B)):
    b.InjOn ρ → (b.let2 e).InjOn ρ

def InstSet.Body.InjOn.entry [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)} {p}
  {b : Φ.Body p Γ Δ} {ρ : ν → ν'} : b.InjOn ρ → Γ.InjOn ρ
  | nil _ h => h
  | let1 _ h => h.entry.tail
  | let2 _ h => h.entry.tail.tail

def InstSet.Body.InjOn.exit [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)} {p}
  {b : Φ.Body p Γ Δ} {ρ : ν → ν'} : b.InjOn ρ → Δ.InjOn ρ
  | nil w h => h.wk w
  | let1 _ h => h.exit
  | let2 _ h => h.exit

inductive InstSet.Body.Fresh [Φ : InstSet φ (Ty α)] (n: ν)
  : {Γ Δ: Ctx ν (Ty α)} → Φ.Body p Γ Δ → Prop
  | nil {Γ Δ: Ctx ν (Ty α)} (h: Γ.Wk Δ): Γ.Fresh n → Body.Fresh n (Body.nil p h)
  | let1 {b: Φ.Body p (⟨x, A⟩::Γ) Δ} (e: Φ.Tm p Γ A): b.Fresh n → (b.let1 e).Fresh n
  | let2 {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ} (e: Φ.Tm p Γ (Ty.pair A B)):
    b.Fresh n → (b.let2 e).Fresh n

theorem InstSet.Body.Fresh.entry [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)} {p}
  {b : Φ.Body p Γ Δ} {n} : b.Fresh n → Γ.Fresh n
  | nil _ h => h
  | let1 _ h => h.entry.tail
  | let2 _ h => h.entry.tail.tail

theorem InstSet.Body.Fresh.exit [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)} {p}
  {b : Φ.Body p Γ Δ} {n} : b.Fresh n → Δ.Fresh n
  | nil w h => h.wk w
  | let1 _ h => h.exit
  | let2 _ h => h.exit

def InstSet.Body.defs [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  : Φ.Body p Γ Δ → List ν
  | nil _ _ => []
  | @let1 _ _ _ _ _ _ _ x _ _ b => x::b.defs
  | @let2 _ _ _ _ _ _ _ _ x y _ _ b => y::x::b.defs

inductive InstSet.Body.NotDef [Φ : InstSet φ (Ty α)] (n: ν)
  : {Γ Δ : Ctx ν (Ty α)} → Φ.Body p Γ Δ → Prop
  | nil {Γ Δ: Ctx ν (Ty α)} (h: Γ.Wk Δ): Body.NotDef n (Body.nil p h)
  | let1 {b: Φ.Body p (⟨x, A⟩::Γ) Δ}: x ≠ n → (e: Φ.Tm p Γ A) →
    b.NotDef n → (b.let1 e).NotDef n
  | let2 {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ}: x ≠ n → y ≠ n →
    (e: Φ.Tm p Γ (Ty.pair A B)) → b.NotDef n → (b.let2 e).NotDef n

theorem InstSet.Body.NotDef.not_mem_defs [Φ : InstSet φ (Ty α)] {b: Φ.Body p Γ Δ}
  : b.NotDef n → n ∉ b.defs
  | nil _ => by simp [defs]
  | let1 hx e b => by
    simp only [defs, List.mem_cons, not_or]
    exact ⟨hx.symm, b.not_mem_defs⟩
  | let2 hx hy e b => by
    simp only [defs, List.mem_cons, not_or]
    exact ⟨hy.symm, hx.symm, b.not_mem_defs⟩

theorem InstSet.Body.NotDef.of_not_mem_defs [Φ : InstSet φ (Ty α)] {b: Φ.Body p Γ Δ}
  : n ∉ b.defs → b.NotDef n
  := by induction b with
  | nil => exact λ_ => NotDef.nil _
  | let1 _ _ I =>
    simp only [defs, List.mem_cons, not_or, and_imp]
    intro hx hn
    constructor
    exact Ne.symm hx
    exact I hn
  | let2 _ _ I =>
    simp only [defs, List.mem_cons, not_or, and_imp]
    intro hx hy hn
    constructor
    exact Ne.symm hy
    exact Ne.symm hx
    exact I hn

theorem InstSet.Body.NotDef.iff_not_mem_defs [Φ : InstSet φ (Ty α)] {b: Φ.Body p Γ Δ}
  : b.NotDef n ↔ n ∉ b.defs
  := ⟨not_mem_defs, of_not_mem_defs⟩

theorem InstSet.Body.Fresh.notDef [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)} {p}
  {b : Φ.Body p Γ Δ} {n} : b.Fresh n → b.NotDef n
  | nil _ h => NotDef.nil _
  | let1 _ h => NotDef.let1 h.entry.head _ h.notDef
  | let2 _ h => NotDef.let2 h.entry.head h.entry.tail.head _ h.notDef

theorem InstSet.Body.NotDef.toFresh [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)} {p}
  {b: Φ.Body p Γ Δ} {n} (hb: b.NotDef n) (hΓ: Γ.Fresh n): b.Fresh n
  := by induction hb with
  | _ =>
    constructor
    apply_assumption
    repeat first | apply Ctx.Fresh.cons | assumption

inductive InstSet.Body.SSA [Φ : InstSet φ (Ty α)]
  : {Γ Δ: Ctx ν (Ty α)} → Φ.Body p Γ Δ → Prop
  | nil {Γ Δ: Ctx ν (Ty α)} (h: Γ.Wk Δ): Body.SSA (Body.nil p h)
  | let1 {b: Φ.Body p (⟨x, A⟩::Γ) Δ}:
    Ctx.Fresh x Γ → (e: Φ.Tm p Γ A) → b.SSA → (b.let1 e).SSA
  | let2 {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ}:
      x ≠ y →
      Ctx.Fresh x Γ →
      Ctx.Fresh y Γ →
      (e: Φ.Tm p Γ (Ty.pair A B)) →
      b.SSA →
      (b.let2 e).SSA

theorem InstSet.Body.SSA.of_let1 [Φ : InstSet φ (Ty α)] {Γ Δ: Ctx ν (Ty α)} {p}
  {b: Φ.Body p (⟨x, A⟩::Γ) Δ} {e: Φ.Tm p Γ A} (h: (b.let1 e).SSA) : b.SSA
  := by cases h; assumption

theorem InstSet.Body.SSA.fresh [Φ : InstSet φ (Ty α)] {Γ Δ: Ctx ν (Ty α)} {p}
  {b: Φ.Body p (⟨x, A⟩::Γ) Δ} {e: Φ.Tm p Γ A} (h: (b.let1 e).SSA) : Γ.Fresh x
  := by cases h; assumption

theorem InstSet.Body.SSA.of_let2 [Φ : InstSet φ (Ty α)] {Γ Δ: Ctx ν (Ty α)} {p}
  {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ} {e: Φ.Tm p Γ (A.pair B)} (h: (b.let2 e).SSA) : b.SSA
  := by cases h; assumption

theorem InstSet.Body.SSA.freshl [Φ : InstSet φ (Ty α)] {Γ Δ: Ctx ν (Ty α)} {p}
  {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ} {e: Φ.Tm p Γ (A.pair B)} (h: (b.let2 e).SSA) : Γ.Fresh x
  := by cases h; assumption

theorem InstSet.Body.SSA.freshr [Φ : InstSet φ (Ty α)] {Γ Δ: Ctx ν (Ty α)} {p}
  {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ} {e: Φ.Tm p Γ (A.pair B)} (h: (b.let2 e).SSA) : Γ.Fresh y
  := by cases h; assumption

theorem InstSet.Body.SSA.entry_disjoint_defs [Φ : InstSet φ (Ty α)] {Γ Δ: Ctx ν (Ty α)} {p}
  {b: Φ.Body p Γ Δ} (h: b.SSA) : Γ.names.Disjoint b.defs
  := by induction h with
  | nil => simp [defs]
  | let1 hx e b I =>
    simp only [defs, Ctx.names, List.disjoint_cons_right, not_or, and_imp]
    exact ⟨hx.not_mem_names, List.disjoint_of_disjoint_cons_left I⟩
  | let2 hxy hx hy e b I =>
    simp only [defs, Ctx.names, List.disjoint_cons_right, not_or, and_imp]
    exact ⟨hy.not_mem_names, hx.not_mem_names,
      List.disjoint_of_disjoint_cons_left $ List.disjoint_of_disjoint_cons_left I⟩

theorem InstSet.Body.SSA.nodup_defs [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)} {p}
  {b: Φ.Body p Γ Δ} (h: b.SSA) : b.defs.Nodup
  := by induction h with
  | nil _ => simp [defs]
  | let1 hx e b I =>
    simp only [defs, List.nodup_cons, not_or, and_imp]
    exact ⟨entry_disjoint_defs b (by simp), I⟩
  | let2 hxy hx hy e b I =>
    simp only [defs, List.nodup_cons, List.mem_cons, not_or]
    exact ⟨⟨hxy.symm, entry_disjoint_defs b (by simp)⟩, entry_disjoint_defs b (by simp), I⟩

--TODO: SSA of entry_disjoint_defs and nodup_defs; iff

theorem InstSet.Body.SSA.notdef [Φ : InstSet φ (Ty α)] {Γ Δ: Ctx ν (Ty α)} {p}
  {b: Φ.Body p (⟨x, A⟩::Γ) Δ} (h: b.SSA) : x ∉ b.defs
  := by
    have h' := h.entry_disjoint_defs;
    simp only [Ctx.names, List.map_cons, List.disjoint_cons_left] at h'
    exact h'.1

theorem InstSet.Body.SSA.notdefl [Φ : InstSet φ (Ty α)] {Γ Δ: Ctx ν (Ty α)} {p}
  {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ} (h: b.SSA) : x ∉ b.defs
  := by
    have h' := h.entry_disjoint_defs;
    simp only [Ctx.names, List.map_cons, List.disjoint_cons_left] at h'
    exact h'.1

theorem InstSet.Body.SSA.notdefr [Φ : InstSet φ (Ty α)] {Γ Δ: Ctx ν (Ty α)} {p}
  {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ} (h: b.SSA) : y ∉ b.defs
  := by
    have h' := h.entry_disjoint_defs;
    simp only [Ctx.names, List.map_cons, List.disjoint_cons_left] at h'
    exact h'.2.1

theorem InstSet.Body.SSA.notdef' [Φ : InstSet φ (Ty α)] {Γ Δ: Ctx ν (Ty α)} {p}
  {b: Φ.Body p (⟨x, A⟩::Γ) Δ} {e: Φ.Tm p Γ A} (h: (b.let1 e).SSA) : x ∉ b.defs
  := h.of_let1.notdef

theorem InstSet.Body.SSA.notdefl' [Φ : InstSet φ (Ty α)] {Γ Δ: Ctx ν (Ty α)} {p}
  {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ} {e: Φ.Tm p Γ (A.pair B)} (h: (b.let2 e).SSA) : x ∉ b.defs
  := h.of_let2.notdefl

theorem InstSet.Body.SSA.notdefr' [Φ : InstSet φ (Ty α)] {Γ Δ: Ctx ν (Ty α)} {p}
  {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ} {e: Φ.Tm p Γ (A.pair B)} (h: (b.let2 e).SSA) : y ∉ b.defs
  := h.of_let2.notdefr

theorem InstSet.Body.SSA.l_ne_r [Φ : InstSet φ (Ty α)] {Γ Δ: Ctx ν (Ty α)} {p}
  {b: Φ.Body p (⟨x, A⟩::⟨y, B⟩::Γ) Δ} {e: Φ.Tm p Γ (A.pair B)} (h: (b.let2 e).SSA) : x ≠ y
  := by cases h; assumption

def InstSet.Body.αSSA [Φ : InstSet φ (Ty α)] (b: Φ.Body p Γ Δ): Prop
  := ∃b' : Φ.Body p Γ Δ, b'.SSA ∧ b.Iso b'

structure InstSet.Body.Renaming [Φ : InstSet φ (Ty α)]
  {Γ Δ : Ctx ν (Ty α)} (b: Φ.Body p Γ Δ) (Γ' Δ': Ctx ν' (Ty α))
  where
  val : Φ.Body p Γ' Δ'
  isIso : b.Iso val

structure InstSet.SSABody [Φ : InstSet φ (Ty α)] (p: Purity) (Γ Δ: Ctx ν (Ty α)) where
  val : Φ.Body p Γ Δ
  isSSA : val.SSA

structure InstSet.Body.SSAForm [Φ : InstSet φ (Ty α)]
  {Γ Δ : Ctx ν (Ty α)} (b: Φ.Body p Γ Δ) (Γ' Δ': Ctx ν' (Ty α))
  extends Renaming b Γ' Δ', SSABody p Γ' Δ'

-- TODO: every body, w/ de-Bruijn indices, can be placed into SSA...

-- TODO: in particular, if ν is infinite (or actually, just > |b| + |Γ|), then every body from Γ to
--Δ is in αSSA

--TODO: InstSet.InjOn case helpers?
def InstSet.Body.rename [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  {ρ : ν → ν'} : {b : Φ.Body p Γ Δ} → b.InjOn ρ → Φ.Body p (Γ.rename ρ) (Δ.rename ρ)
  | nil _ h, hρ => nil _ (h.rename (by cases hρ; assumption))
  | let1 e b, hρ => let1 (e.rename hρ.entry) (b.rename (by cases hρ; assumption))
  | let2 e b, hρ => let2 (e.rename hρ.entry) (b.rename (by cases hρ; assumption))

theorem InstSet.Body.rename_iso [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  {ρ : ν → ν'} {b : Φ.Body p Γ Δ} (hb: b.InjOn ρ): b.Iso (b.rename hb)
  := by induction b with
  | nil _ h =>
    simp only [rename]
    constructor
    exact h.rename_iso (hb.entry)
  | let1 e b I =>
    simp only [rename]
    constructor
    exact e.rename_iso (hb.entry)
    apply I
  | let2 e b I =>
    simp only [rename]
    constructor
    exact e.rename_iso (hb.entry)
    apply I

def InstSet.Body.head_var [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  (_: Φ.Body p (v::Γ) Δ) : Var ν (Ty α) := v

def InstSet.Body.head2_var [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  (_: Φ.Body p (v'::v::Γ) Δ) : Var ν (Ty α) := v

def InstSet.Body.inner_ctx [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  : (b: Φ.Body p Γ Δ) → Ctx ν (Ty α)
  | nil _ _ => Γ
  | let1 _ b => b.inner_ctx
  | let2 _ b => b.inner_ctx

--TODO: why the poor defeq?
def InstSet.Body.target_inner_ctx [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  : (b: Φ.Body p Γ Δ) → Φ.Body p Γ b.inner_ctx
  | nil _ w => by simp only [inner_ctx]; exact nil _ (Ctx.Wk.refl _)
  | let1 e b => by simp only [inner_ctx]; exact let1 e b.target_inner_ctx
  | let2 e b => by simp only [inner_ctx]; exact let2 e b.target_inner_ctx

def InstSet.Body.inner_ctx_wk_exit [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  : (b: Φ.Body p Γ Δ) → b.inner_ctx.Wk Δ
  | nil _ w => by simp only [inner_ctx]; exact w
  | let1 _ b => by simp only [inner_ctx]; exact b.inner_ctx_wk_exit
  | let2 _ b => by simp only [inner_ctx]; exact b.inner_ctx_wk_exit

def InstSet.Body.inner_ctx_wk_entry [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  : {b: Φ.Body p Γ Δ} → b.SSA → b.inner_ctx.Wk Γ
  | nil _ _, _=> by simp only [inner_ctx]; exact Ctx.Wk.refl Γ
  | let1 _ b, h => by
    simp only [inner_ctx]
    apply Ctx.Wk.comp
    apply inner_ctx_wk_entry (by cases h; assumption)
    apply Ctx.Wk.skip
    cases h
    assumption
    apply Ctx.Wk.refl
  | let2 _ b, h => by
    simp only [inner_ctx]
    apply Ctx.Wk.comp
    apply inner_ctx_wk_entry (by cases h; assumption)
    apply Ctx.Wk.skip
    cases h
    assumption
    apply Ctx.Wk.skip
    cases h
    assumption
    apply Ctx.Wk.refl

def InstSet.Body.def_ctx [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  : (b: Φ.Body p Γ Δ) → Ctx ν (Ty α)
  | nil _ _ => []
  | @let1 _ _ _ _ _ _ A x _ _ b => ⟨x, A⟩::b.def_ctx
  | @let2 _ _ _ _ _ _ A B x y _ _ b => ⟨y, B⟩::⟨x, A⟩::b.def_ctx

theorem InstSet.Body.def_ctx_names_eq_defs [Φ : InstSet φ (Ty α)] {Γ Δ : Ctx ν (Ty α)}
  (b: Φ.Body p Γ Δ) : b.def_ctx.names = b.defs
  := by induction b with
  | nil _ _ => simp [defs, def_ctx, Ctx.names]
  | let1 _ b I =>
    simp only [defs, def_ctx, Ctx.names, <-I]
    rfl
  | let2 _ b I =>
    simp only [defs, def_ctx, Ctx.names, <-I]
    rfl

theorem InstSet.Body.inner_ctx_eq_def_ctx_reverse_append_entry [Φ : InstSet φ (Ty α)]
  {Γ Δ : Ctx ν (Ty α)} (b: Φ.Body p Γ Δ) : b.inner_ctx = b.def_ctx.reverse ++ Γ
  := by induction b with
  | nil _ _ => simp [inner_ctx, def_ctx, List.nil_append _, Ctx.reverse]
  | let1 _ b I =>
    simp only [inner_ctx, I, Ctx.reverse, def_ctx, List.reverse_cons]
    rw [List.append_assoc]
    rfl
  | let2 _ b I =>
    simp only [inner_ctx, I, Ctx.reverse, def_ctx, List.reverse_cons]
    rw [List.append_assoc, List.append_assoc]
    rfl
