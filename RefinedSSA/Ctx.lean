import RefinedSSA.Ty

import Discretion.Vector.Basic
import Discretion.Wk.Nat

namespace RefinedSSA

open HasQuant

structure Var (α ε) where
  ty : Ty α
  q : Quant
  eff : ε

@[ext]
theorem Var.ext {v w : Var α ε}
  (h : v.ty = w.ty) (h' : v.q = w.q) (h'' : v.eff = w.eff) : v = w :=
  by cases v; cases w; cases h; cases h'; cases h''; rfl

def Ctx (α : Type _) (ε : Type _) := List (Var α ε)

@[match_pattern]
def Ctx.nil {α ε} : Ctx α ε := []

@[match_pattern]
def Ctx.cons {α ε} (Γ : Ctx α ε) (v : Var α ε) : Ctx α ε := List.cons v Γ

@[match_pattern]
abbrev Ctx.cons' {α ε} (Γ : Ctx α ε) (A : Ty α) (q : Quant) (e : ε) : Ctx α ε := Γ.cons ⟨A, q, e⟩

@[elab_as_elim, cases_eliminator]
def Ctx.casesOn {α ε} {motive : Ctx α ε → Sort _} (Γ : Ctx α ε)
  (nil : motive .nil)
  (cons : ∀ Γ v, motive (.cons Γ v))
  : motive Γ := match Γ with | .nil => nil | .cons Γ v => cons Γ v

@[elab_as_elim, induction_eliminator]
def Ctx.inductionOn {α ε} {motive : Ctx α ε → Sort _} (Γ : Ctx α ε)
  (nil : motive .nil)
  (cons : ∀ Γ v, motive Γ → motive (Ctx.cons Γ v))
  : motive Γ := match Γ with | .nil => nil | .cons Γ v => cons Γ v (inductionOn Γ nil cons)

def Ctx.length {α ε} (Γ : Ctx α ε) : ℕ := List.length Γ

@[simp]
theorem Ctx.length_nil {α ε} : Ctx.length (.nil : Ctx α ε) = 0 := rfl

@[simp]
theorem Ctx.length_cons {α ε} (Γ : Ctx α ε) (v : Var α ε)
  : Ctx.length (Ctx.cons Γ v) = Ctx.length Γ + 1 := rfl

@[simp]
theorem Ctx.length_cons' {α ε} (Γ : Ctx α ε) (A : Ty α) (q : Quant) (e : ε)
  : Ctx.length (Ctx.cons' Γ A q e) = Ctx.length Γ + 1 := rfl

variable {α : Type u} {ε : Type v}

section HasQuant

variable [HasQuant α]

open HasQuant

instance Var.hasQuant : HasQuant (Var α ε) where
  quant v := v.q ⊓ quant v.ty

structure Var.del (v : Var α ε) : Prop where
  q : .del ≤ v.q
  ty : .del ≤ v.ty.q

structure Var.copy (v : Var α ε) : Prop where
  q : .copy ≤ v.q
  ty : .copy ≤ v.ty.q

end HasQuant

variable [PartialOrder ε]

structure Var.Wk (v w : Var α ε) : Prop where
  ty : v.ty = w.ty
  q : w.q ≤ v.q
  eff : v.eff ≤ w.eff

instance Var.instLE : LE (Var α ε) := ⟨Wk⟩

instance Var.instPartialOrder : PartialOrder (Var α ε) where
  le_refl _ := ⟨rfl, le_refl _, le_refl _⟩
  le_trans _ _ _ h h' :=
    ⟨h.ty.trans h'.ty, h'.q.trans h.q, h.eff.trans h'.eff⟩
  le_antisymm _ _ h h' := ext h.ty (le_antisymm h'.q h.q) (le_antisymm h.eff h'.eff)

inductive Ctx.PWk : Ctx α ε → Ctx α ε → Prop where
  | nil : Ctx.PWk .nil .nil
  | cons {Γ Δ v w} (h : Ctx.PWk Γ Δ) (hvw : v ≤ w) : Ctx.PWk (.cons Γ v) (.cons Δ w)

theorem Ctx.PWk.head {Γ Δ v w} (h : PWk (α := α) (ε := ε) (.cons Γ v) (.cons Δ w)) : v ≤ w
  := match h with | Ctx.PWk.cons _ hvw => hvw

theorem Ctx.PWk.tail {Γ Δ v w} (h : PWk (α := α) (ε := ε) (.cons Γ v) (.cons Δ w)) : PWk Γ Δ
  := match h with | Ctx.PWk.cons h _ => h

@[simp]
theorem Ctx.PWk.cons_iff {Γ Δ v w} : PWk (α := α) (ε := ε) (.cons Γ v) (.cons Δ w) ↔ PWk Γ Δ ∧ v ≤ w
  := ⟨λ h => ⟨Ctx.PWk.tail h, Ctx.PWk.head h⟩, λ ⟨h, h'⟩ => Ctx.PWk.cons h h'⟩

def Ctx.PWk.inductionOn {Γ Δ} (h : PWk Γ Δ) {motive : (Γ Δ : Ctx α ε) → PWk Γ Δ → Sort _}
  (nil : motive .nil .nil .nil)
  (cons : ∀ {Γ Δ v w} (h : PWk Γ Δ) (hvw : v ≤ w),
    motive Γ Δ h →
    motive (Ctx.cons Γ v) (Ctx.cons Δ w) (Ctx.PWk.cons h hvw))
  : motive Γ Δ h := match Γ, Δ, h with
  | .nil, .nil, _ => nil
  | .cons _ _, .cons _ _, h => cons h.tail h.head (inductionOn h.tail nil cons)

@[simp]
theorem Ctx.PWk.refl (Γ : Ctx α ε) : PWk Γ Γ := by induction Γ <;> simp [Ctx.PWk.nil, *]

theorem Ctx.PWk.trans {Γ Δ Ξ : Ctx α ε} (h : PWk Γ Δ) (h' : PWk Δ Ξ) : PWk Γ Ξ := by
  induction h generalizing Ξ <;> cases h'
  simp only [refl]
  simp only [cons_iff, true_and, *]
  apply le_trans <;> assumption

theorem Ctx.PWk.antisymm {Γ Δ : Ctx α ε} (h : PWk Γ Δ) (h' : PWk Δ Γ) : Γ = Δ := by
  induction h with
  | nil => rfl
  | cons h hvw I => cases h' with
  | cons h' hwv => rw [I h', le_antisymm hvw hwv]

theorem Ctx.PWk.length {Γ Δ : Ctx α ε} (h : PWk Γ Δ) : Ctx.length Γ = Ctx.length Δ
  := by induction h <;> simp [*]

variable [HasQuant α]

theorem Var.del.anti {v w : Var α ε} (h : v ≤ w) (hw : w.del) : v.del where
  q := hw.q.trans h.q
  ty := h.ty ▸ hw.ty

theorem Var.copy.anti {v w : Var α ε} (h : v ≤ w) (hw : w.copy) : v.copy where
  q := hw.q.trans h.q
  ty := h.ty ▸ hw.ty

inductive Ctx.Wk : Ctx α ε → Ctx α ε → Type _ where
  | nil : Ctx.Wk .nil .nil
  | cons {Γ Δ v w} (h : Ctx.Wk Γ Δ) (hvw : v ≤ w) : Ctx.Wk (Ctx.cons Γ v) (Ctx.cons Δ w)
  | skip {Γ Δ v} (h : Ctx.Wk Γ Δ) (hv : v.del) : Ctx.Wk (Ctx.cons Γ v) Δ

theorem Ctx.Wk.length {Γ Δ : Ctx α ε} (h : Wk Γ Δ) : Ctx.length Δ ≤ Ctx.length Γ
  := by induction h <;> simp <;> omega

def Ctx.PWk.toWk {Γ Δ : Ctx α ε} (h : PWk Γ Δ) : Wk Γ Δ
  := h.inductionOn (motive := λΓ Δ _ => Wk Γ Δ) .nil (λ_ h m => .cons m h)

theorem Ctx.Wk.toPWk {Γ Δ : Ctx α ε} (h : Wk Γ Δ) (h' : Γ.length = Δ.length) : Γ.PWk Δ
  := by induction h with
  | nil => exact .nil
  | cons h v I => exact .cons (I (by convert h' using 0; simp)) v
  | skip h =>
    have hl := h.length
    rw [<-h', length_cons] at hl
    omega

theorem Ctx.Wk.antisymm {Γ Δ : Ctx α ε} (h : Wk Γ Δ) (h' : Wk Δ Γ) : Γ = Δ :=
  have hl := le_antisymm h'.length h.length
  PWk.antisymm (h.toPWk hl) (h'.toPWk (hl.symm))

-- toPWk is a faithful functor
theorem Ctx.Wk.eq_pwk {Γ Δ : Ctx α ε} (h : Wk Γ Δ) (h' : Γ.length = Δ.length)
  : h = (h.toPWk h').toWk := by induction h with
  | nil => rfl
  | cons h v I =>
    rw [I]
    rfl
    convert h' using 0
    simp
  | skip h =>
    have hl := h.length
    rw [<-h', length_cons] at hl
    omega

def Ctx.Wk.refl (Γ : Ctx α ε) : Wk Γ Γ := (Ctx.PWk.refl Γ).toWk

theorem Ctx.Wk.eq_refl {Γ : Ctx α ε} (h : Wk Γ Γ) : h = Wk.refl Γ := eq_pwk h rfl

def Ctx.Wk.comp {Γ Δ Ξ : Ctx α ε} : Wk Γ Δ → Wk Δ Ξ → Wk Γ Ξ
  | .nil, .nil => .nil
  | .cons h hv, .cons h' hv' => .cons (h.comp h') (hv.trans hv')
  | .cons h hv, .skip h' hv' => .skip (h.comp h') (hv'.anti hv)
  | .skip h hv, h' => .skip (h.comp h') hv

theorem Ctx.Wk.comp_assoc {Γ Δ Ξ Θ : Ctx α ε} (h : Wk Γ Δ) (h' : Wk Δ Ξ) (h'' : Wk Ξ Θ)
  : h.comp (h'.comp h'') = (h.comp h').comp h'' := by induction h generalizing Ξ Θ with
  | nil => cases h'; cases h''; rfl
  | cons _ _ I => cases h' <;> cases h'' <;> simp [comp, I]
  | skip _ _ I => simp [comp, I]

def Ctx.Wk.ix {Γ Δ : Ctx α ε} : Wk Γ Δ → ℕ → ℕ
  | .nil => id
  | .cons h _ => Nat.liftWk h.ix
  | .skip h _ => Nat.stepWk h.ix

@[simp]
theorem Ctx.Wk.ix_increasing {Γ Δ : Ctx α ε} (h : Wk Γ Δ) (i : ℕ) : i ≤ h.ix i := by
  induction h generalizing i with
  | nil => simp [ix]
  | cons _ _ I => cases i <;> simp [ix, *]
  | skip _ _ I => simp [ix]; have I := I i; omega

theorem Ctx.Wk.ix_comp_applied {Γ Δ Ξ : Ctx α ε} (h : Wk Γ Δ) (h' : Wk Δ Ξ) (i : ℕ)
  : (h.comp h').ix i = h.ix (h'.ix i) := by induction h generalizing Ξ i with
  | nil => cases h'; rfl
  | cons _ _ I => cases h' <;> cases i <;> simp [comp, ix, I]
  | skip _ _ I => simp [comp, ix, I]

theorem Ctx.Wk.ix_comp {Γ Δ Ξ : Ctx α ε} (h : Wk Γ Δ) (h' : Wk Δ Ξ)
  : (h.comp h').ix = h.ix ∘ h'.ix := funext (λi => Wk.ix_comp_applied h h' i)

theorem Ctx.Wk.ix_length_eq_applied {Γ Δ : Ctx α ε}
  (h : Γ.Wk Δ) (hl : Γ.length = Δ.length) (i : ℕ) : h.ix i = i := by induction h generalizing i with
  | nil => rfl
  | cons _ _ I =>
    cases i; rfl; simp only [ix, Nat.liftWk_succ, add_left_inj]; apply I; convert hl using 0; simp
  | skip h _ => have hl' := h.length; rw [<-hl] at hl'; simp at hl'

theorem Ctx.Wk.ix_length_eq {Γ Δ : Ctx α ε} (h : Γ.Wk Δ) (hl : Γ.length = Δ.length)
  : h.ix = id := funext (λi => ix_length_eq_applied h hl i)

theorem Ctx.Wk.ix_refl {Γ : Ctx α ε} (h : Γ.Wk Γ) : h.ix = id := ix_length_eq _ rfl

-- TODO: ix is an injection...

theorem Ctx.Wk.ix_bounded {Γ Δ : Ctx α ε} (h : Γ.Wk Δ) (i : ℕ)
  (hi : i < Δ.length) : h.ix i < Γ.length
  := by induction h generalizing i with
  | nil => simp at hi
  | cons _ _ I =>
    cases i
    · simp [ix]
    · simp only [ix, Nat.liftWk_succ, length_cons, add_lt_add_iff_right]
      apply I; convert hi using 0; simp
  | skip _ _ I => simp [ix, *]

def Ctx.Wk.skips {Γ Δ : Ctx α ε} (h : Wk Γ Δ) : ℕ := h.ix 0

def Ctx.choose_drop (Γ : Ctx α ε) (h : Nonempty (Γ.Wk .nil)) : Γ.Wk .nil := match Γ with
  | .nil => .nil
  | .cons Γ v => .skip
    (Γ.choose_drop (have ⟨h⟩ := h; by cases h; constructor; assumption))
    (have ⟨h⟩ := h; by cases h; assumption)

def Var.Ix (Γ : Ctx α ε) (v : Var α ε) : Type _ := Γ.Wk [v]

@[match_pattern]
def Var.zero_le {Γ : Ctx α ε} (x : Γ.Wk .nil) {v w : Var α ε} (h : v ≤ w) : Ix (Γ.cons v) w
  := x.cons h

@[match_pattern]
abbrev Var.zero {Γ : Ctx α ε} (x : Γ.Wk .nil) (v : Var α ε) : Ix (Γ.cons v) v
  := zero_le x (le_refl v)

@[match_pattern]
def Var.Ix.succ {Γ : Ctx α ε} {v : Var α ε} (h : v.del) {w} (x : Ix Γ w) : Ix (Γ.cons v) w
  := x.skip h

@[elab_as_elim, cases_eliminator]
def Var.Ix.casesOn {motive : ∀ {Γ v}, Ix Γ v → Sort _}
  {Γ v} (x : Ix Γ v)
  (zero_le : ∀ {Γ : Ctx α ε} (d : Γ.Wk .nil) {v w} (hv : v ≤ w), motive (zero_le d hv))
  (succ : ∀ {Γ} {v : Var α ε} (h : v.del) {w} (x : Ix Γ w), motive (succ h x))
  : motive x := match x with
  | .cons d hv => zero_le d hv
  | .skip x hv => succ hv x

@[elab_as_elim, induction_eliminator]
def Var.Ix.inductionOn {motive : ∀ {Γ v}, Ix Γ v → Sort _}
  {Γ v} (x : Ix Γ v)
  (zero_le : ∀ {Γ : Ctx α ε} (d : Γ.Wk .nil) {v w} (hv : v ≤ w), motive (zero_le d hv))
  (succ : ∀ {Γ} {v : Var α ε} (h : v.del) {w} (x : Ix Γ w), motive x → motive (succ h x))
  : motive x := match x with
  | .cons d hv => zero_le d hv
  | .skip x hv => succ hv x (inductionOn x zero_le succ)

def Var.Ix.ix {Γ : Ctx α ε} {v} (x : Ix Γ v) : ℕ := x.skips

@[simp]
theorem Var.ix_zero_le {Γ : Ctx α ε} {v w : Var α ε} (h : v ≤ w) (x : Γ.Wk .nil)
  : (zero_le x h).ix = 0 := rfl

@[simp]
theorem Var.Ix.ix_succ {Γ : Ctx α ε} {v : Var α ε} (h : v.del) {w} (x : Ix Γ w)
  : (succ h x).ix = x.ix + 1 := rfl

def Var.Ix.wk {Γ Δ : Ctx α ε} (h : Γ.Wk Δ) {v} (x : Ix Δ v) : Ix Γ v := h.comp x

theorem Var.Ix.wk_wk {Γ Δ Ξ : Ctx α ε} (h : Γ.Wk Δ) (h' : Δ.Wk Ξ) {v} (x : Ix Ξ v)
  : (x.wk h').wk h = x.wk (h.comp h') := Ctx.Wk.comp_assoc h h' x

theorem Var.Ix.wk_comp {Γ Δ Ξ : Ctx α ε} (h : Γ.Wk Δ) (h' : Δ.Wk Ξ) {v} (x : Ix Ξ v)
  : x.wk (h.comp h') = (x.wk h').wk h := (x.wk_wk h h').symm

@[simp]
theorem Var.Ix.succ_wk_cons {Γ Δ : Ctx α ε} (h : Γ.Wk Δ)
  {v v' : Var α ε} (hv : v ≤ v') (hv' : v'.del) {w} (x : Ix Δ w)
  : (succ hv' x).wk (h.cons hv) = (succ (hv'.anti hv) (x.wk h)) := rfl

@[simp]
theorem Var.Ix.wk_skip {Γ Δ : Ctx α ε} (h : Γ.Wk Δ)
  {v : Var α ε} (hv : v.del) {w} (x : Ix Δ w)
  : x.wk (h.skip hv) = (x.wk h).succ hv := rfl

@[simp]
theorem Var.Ix.ix_wk {Γ Δ : Ctx α ε} (h : Γ.Wk Δ) {v} (x : Ix Δ v) : (x.wk h).ix = h.ix x.ix
  := by rw [ix, Ctx.Wk.skips, wk, Ctx.Wk.ix_comp]; rfl

theorem Var.Ix.ix_wk_le {Γ Δ : Ctx α ε} (h : Γ.Wk Δ) {v} (x : Ix Δ v) : x.ix ≤ (x.wk h).ix
  := by simp

-- TODO: ix is an injection on variables...

inductive Ctx.At (v : Var α ε) : Ctx α ε → ℕ → Prop where
  | here {Γ} (d : Ctx.Wk Γ .nil) {w} : w ≤ v → Ctx.At v (Ctx.cons Γ w) 0
  | there {Γ w} (x : Ctx.At v Γ n) (hw : w.del) : Ctx.At v (Ctx.cons Γ w) (n + 1)

theorem Ctx.At.zero_cons_head {Γ : Ctx α ε} {v} (h : (Γ.cons w).At v 0) : w ≤ v
  := by cases h; assumption

def Ctx.At.zero_cons_tail {Γ : Ctx α ε} {v} (h : (Γ.cons w).At v 0) : Γ.Wk .nil
  := Γ.choose_drop (by cases h; constructor; assumption)

theorem Ctx.At.succ_cons_head {Γ : Ctx α ε} {v w} (h : (Γ.cons w).At v (n + 1)) : w.del
  := by cases h; assumption

theorem Ctx.At.succ_cons_tail {Γ : Ctx α ε} {v w} (h : (Γ.cons w).At v (n + 1)) : Γ.At v n
  := by cases h; assumption

theorem Ctx.At.succ_cons_iff (Γ : Ctx α ε) (v w) : (Γ.cons w).At v (n + 1) ↔ w.del ∧ Γ.At v n
  := ⟨λh => ⟨h.succ_cons_head, h.succ_cons_tail⟩, λ⟨h, h'⟩ => At.there h' h⟩

@[elab_as_elim, induction_eliminator]
def Ctx.At.inductionOn {v : Var α ε} {motive : ∀ (Γ n), Ctx.At v Γ n → Sort _}
  (h : Ctx.At v Γ n)
  (here : ∀ (Γ : Ctx α ε) (d : Γ.Wk .nil) (w) (hw : w ≤ v), motive (Γ.cons w) 0 (here d hw))
  (there : ∀ (Γ) (w : Var α ε) (n) (x : Ctx.At v Γ n) (hw : w.del),
    motive Γ n x → motive (Γ.cons w) (n + 1) (there x hw))
  : motive Γ n h := match Γ, n, h with
  | .cons Γ w, 0, h => here Γ h.zero_cons_tail w h.zero_cons_head
  | .cons Γ w, n + 1, h
    => there Γ w n h.succ_cons_tail h.succ_cons_head (h.succ_cons_tail.inductionOn here there)

def Ctx.At.ix {Γ : Ctx α ε} {v n} (h : Γ.At v n) : v.Ix Γ
  := h.inductionOn (λ_ d _ h => Var.zero_le d h) (λ_ _ _ _ hv I => I.succ hv)

@[simp]
theorem Ctx.At.ix_ix {Γ : Ctx α ε} {v n} (h : Γ.At v n) : h.ix.ix = n
  := by induction h <;> simp [ix, inductionOn]; assumption

theorem Var.Ix.at {Γ : Ctx α ε} {v} (x : Ix Γ v) : Γ.At v x.ix
  := by induction x <;> constructor <;> assumption

-- TODO: so therefore at_ix is just the identity

-- ChatGPT's attempt: https://chatgpt.com/share/678eb088-a5fc-8005-b6e9-eae717a74750

inductive Ctx.Split : Ctx α ε → Ctx α ε → Ctx α ε → Type _ where
  | nil : Split .nil .nil .nil
  | left {Γ Δ Ξ w} : Split Γ Δ Ξ → (w ≤ w') → Split (Ctx.cons Γ w) (Ctx.cons Δ w') Ξ
  | right {Γ Δ Ξ w} : Split Γ Δ Ξ → (w ≤ w') → Split (Ctx.cons Γ w) Δ (Ctx.cons Ξ w')
  | both {Γ Δ Ξ w} : Split Γ Δ Ξ → w.copy → (w ≤ wl) → (w ≤ wr)
                                 → Split (Ctx.cons Γ w) (Ctx.cons Δ wl) (Ctx.cons Ξ wr)
  | skip {Γ Δ Ξ w} : Split Γ Δ Ξ → w.del → Split (Ctx.cons Γ w) Δ Ξ

def Ctx.Split.comm {Γ Δ Ξ : Ctx α ε} : Split Γ Δ Ξ → Split Γ Ξ Δ
  | .nil => .nil
  | .left h hw => .right (comm h) hw
  | .right h hw => .left (comm h) hw
  | .both h hw hl hr => .both (comm h) hw hr hl
  | .skip h hw => .skip (comm h) hw

-- def Ctx.Split.wk {Γ' Γ Δ Ξ : Ctx α ε} : Wk Γ' Γ → Split Γ Δ Ξ → Split Γ' Δ' Ξ'
--   := sorry

def Ctx.Split.ctx23 {Γ123 Γ12 Γ1 Γ2 Γ3 : Ctx α ε} : Split Γ123 Γ12 Γ3 → Split Γ12 Γ1 Γ2 → Ctx α ε
  | .nil, .nil => .nil
  | .left h123 _, .left h12 _
  | .left h123 _, .skip h12 _
  | .skip h123 _, h12 => h123.ctx23 h12
  | .left h123 _, .right (w := w) h12 _
  | .left h123 _, .both (w := w) h12 _ _ _
  | .right (w := w) h123 _, h12
  | .both (w := w) h123 _ _ _, .left h12 _
  | .both (w := w) h123 _ _ _, .right h12 _
  | .both (w := w) h123 _ _ _, .both h12 _ _ _
  | .both (w := w) h123 _ _ _, .skip h12 _ => (h123.ctx23 h12).cons w

def Ctx.Split.s123_23 {Γ123 Γ12 Γ1 Γ2 Γ3 : Ctx α ε}
  : (h123_12 : Split Γ123 Γ12 Γ3) → (h12 : Split Γ12 Γ1 Γ2) → Split Γ123 Γ1 (ctx23 h123_12 h12)
  | .nil, .nil => .nil
  | .left h123_12 hw, .left h12 hw' => .left (s123_23 h123_12 h12) (hw.trans hw')
  | .left h123_12 hw, .right h12 _ => .right (s123_23 h123_12 h12) hw
  | .left h123_12 hw, .both h12 hw' hl hr
    => .both (s123_23 h123_12 h12) (hw'.anti hw) (hw.trans hl) hw
  | .right h123_12 _, h12 => .right (s123_23 h123_12 h12) (le_refl _)
  | .both h123_12 hw hl hr, .left h12 hw'
    => .both (s123_23 h123_12 h12) hw (hl.trans hw') (le_refl _)
  | .both h123_12 _ _ hr, .right h12 hw' => .right (s123_23 h123_12 h12) (le_refl _)
  | .both h123_12 hw hl _, .both h12 hw' hl' hr'
    => .both (s123_23 h123_12 h12) hw (hl.trans hl') (le_refl _)
  | .both h123_12 hw hl hr, .skip h12 hw' => .right (s123_23 h123_12 h12) (le_refl _)
  | .skip h123_12 hw, h12 => .skip (s123_23 h123_12 h12) hw
  | .left h123_12 hw, .skip h12 hw' => .skip (s123_23 h123_12 h12) (hw'.anti hw)

def Ctx.Split.s23 {Γ123 Γ12 Γ1 Γ2 Γ3 : Ctx α ε}
  : (h123_12 : Split Γ123 Γ12 Γ3) → (h12 : Split Γ12 Γ1 Γ2) → Split (ctx23 h123_12 h12) Γ2 Γ3
  | .nil, .nil => .nil
  | .left h123_12 _, .left h12 _ => s23 h123_12 h12
  | .left h123_12 _, .right h12 hw' => .left (s23 h123_12 h12) hw'
  | .left h123_12 _, .both h12 _ _ hr => .left (s23 h123_12 h12) hr
  | .left h123_12 _, .skip h12 _ => s23 h123_12 h12
  | .right h123_12 hw, h12 => .right (s23 h123_12 h12) hw
  | .both h123_12 _ _ hr, .left h12 _ => .right (s23 h123_12 h12) hr
  | .both h123_12 hw hl hr, .right h12 hw' => .both (s23 h123_12 h12) hw (hl.trans hw') hr
  | .both h123_12 hw hl hr, .both h12 _ _ hr' => .both (s23 h123_12 h12) hw (hl.trans hr') hr
  | .both h123_12 _ _ hr, .skip h12 _ => .right (s23 h123_12 h12) hr
  | .skip h123_12 _, h12 => s23 h123_12 h12

def Ctx.Split.ctx12 {Γ123 Γ1 Γ23 Γ2 Γ3 : Ctx α ε}
  : Split Γ123 Γ1 Γ23 → Split Γ23 Γ2 Γ3 → Ctx α ε
  | .nil, .nil => .nil
  | .left (w := w) h123_23 _, h23 =>
    (ctx12 h123_23 h23).cons w
  | .right (w := w) h123_23 _, .left h23 _
  | .right (w := w) h123_23 _, .both (w := _) h23 _ _ _ =>
    (ctx12 h123_23 h23).cons w
  | .right (w := _) h123_23 _, .right h23 _
  | .right (w := _) h123_23 _, .skip (w := _) h23 _ =>
    ctx12 h123_23 h23
  | .both (w := w) h123_23 _ _ _, .left h23 _
  | .both (w := w) h123_23 _ _ _, .right h23 _
  | .both (w := w) h123_23 _ _ _, .both (w := _) h23 _ _ _
  | .both (w := w) h123_23 _ _ _, .skip (w := _) h23 _ =>
    (ctx12 h123_23 h23).cons w
  | .skip (w := _) h123_23 _, h23 =>
    ctx12 h123_23 h23

def Ctx.Split.s123_12 {Γ123 Γ1 Γ23 Γ2 Γ3 : Ctx α ε}
  : (h123_23 : Split Γ123 Γ1 Γ23) → (h23 : Split Γ23 Γ2 Γ3) → Split Γ123 (ctx12 h123_23 h23) Γ3
  | .nil, .nil => .nil
  | .left h123_23 _, h23 => .left (s123_12 h123_23 h23) (le_refl _)
  | .right h123_23 hw, .left  h23 hw' => .left  (s123_12 h123_23 h23) (le_refl _)
  | .right h123_23 hw, .right h23 hw' => .right (s123_12 h123_23 h23) (hw.trans hw')
  | .right h123_23 hw, .both h23 hw' hl hr
    => .both (s123_12 h123_23 h23) (hw'.anti hw) (le_refl _) (hw.trans hr)
  | .right h123_23 hw, .skip h23 hw' => (s123_12 h123_23 h23).skip (hw'.anti hw)
  | .both h123_23 _ _ _, .left h23 _ => .left (s123_12 h123_23 h23) (le_refl _)
  | .both h123_23 hw _ hr, .right h23 hw'
    => .both (s123_12 h123_23 h23) hw (le_refl _) (hr.trans hw')
  | .both h123_23 hw _ hr, .both h23 hw' hl' hr'
    => .both (s123_12 h123_23 h23) hw (le_refl _) (hr.trans hr')
  | .both h123_23 hw hl hr, .skip h23 _ => .left (s123_12 h123_23 h23) (le_refl _)
  | .skip h123_23 hw, h23 => .skip (s123_12 h123_23 h23) hw

def Ctx.Split.s12 {Γ123 Γ1 Γ23 Γ2 Γ3 : Ctx α ε}
  : (h123_23 : Split Γ123 Γ1 Γ23) → (h23 : Split Γ23 Γ2 Γ3) → Split (ctx12 h123_23 h23) Γ1 Γ2
  | .nil, .nil =>
    .nil
  | .left h123_23 hw, h23 =>
    .left (s12 h123_23 h23) hw
  | .right h123_23 hw, .left h23 hw' => .right (s12 h123_23 h23) (hw.trans hw')
  | .right h123_23 _, .right h23 _ => s12 h123_23 h23
  | .right h123_23 hw, .both h23 _ hl hr => .right (s12 h123_23 h23) (hw.trans hl)
  | .right h123_23 _, .skip h23 _ => s12 h123_23 h23
  | .both h123_23 hw hl hr, .left h23 hw' => .both (s12 h123_23 h23) hw hl (hr.trans hw')
  | .both h123_23 _ hl hr, .right h23 hw' => .left (s12 h123_23 h23) hl
  | .both h123_23 hw hl hr, .both h23 hw' hl' hr' => .both (s12 h123_23 h23) hw hl (hr.trans hl')
  | .both h123_23 hw hl hr, .skip h23 _ => .left (s12 h123_23 h23) hl
  | .skip h123_23 hw, h23 => (s12 h123_23 h23)

inductive Ctx.SSplit : Ctx α ε → Ctx α ε → Ctx α ε → Type _ where
  | nil : SSplit .nil .nil .nil
  | left {Γ Δ Ξ w} : SSplit Γ Δ Ξ → SSplit (Ctx.cons Γ w) (Ctx.cons Δ w) Ξ
  | right {Γ Δ Ξ w} : SSplit Γ Δ Ξ → SSplit (Ctx.cons Γ w) Δ (Ctx.cons Ξ w)
  | both {Γ Δ Ξ w} : SSplit Γ Δ Ξ → w.copy → SSplit (Ctx.cons Γ w) (Ctx.cons Δ w) (Ctx.cons Ξ w)

def Ctx.SSplit.comm {Γ Δ Ξ : Ctx α ε} : SSplit Γ Δ Ξ → SSplit Γ Ξ Δ
  | .nil => .nil
  | .left h => .right (comm h)
  | .right h => .left (comm h)
  | .both h hw => .both (comm h) hw

def Ctx.SSplit.toSplit {Γ Δ Ξ : Ctx α ε} : SSplit Γ Δ Ξ → Split Γ Δ Ξ
  | .nil => .nil
  | .left h => .left (toSplit h) (le_refl _)
  | .right h => .right (toSplit h) (le_refl _)
  | .both h hw => .both (toSplit h) hw (le_refl _) (le_refl _)

-- TODO: coercion, injective, etc...

def Ctx.SSplit.ctx23 {Γ123 Γ12 Γ1 Γ2 Γ3 : Ctx α ε} : SSplit Γ123 Γ12 Γ3 → SSplit Γ12 Γ1 Γ2 → Ctx α ε
  | .nil, .nil => .nil
  | .left h123, .left h12 => h123.ctx23 h12
  | .left h123, .right (w := w) h12
  | .left h123, .both (w := w) h12 _
  | .right (w := w) h123, h12
  | .both (w := w) h123 _, .left h12
  | .both (w := w) h123 _, .right h12
  | .both (w := w) h123 _, .both h12 _ => (h123.ctx23 h12).cons w

def Ctx.SSplit.s123_23 {Γ123 Γ12 Γ1 Γ2 Γ3 : Ctx α ε}
  : (h123_12 : SSplit Γ123 Γ12 Γ3) → (h12 : SSplit Γ12 Γ1 Γ2) → SSplit Γ123 Γ1 (ctx23 h123_12 h12)
  | .nil, .nil => .nil
  | .left h123_12, .left h12 => .left (s123_23 h123_12 h12)
  | .left h123_12, .right h12 => .right (s123_23 h123_12 h12)
  | .left h123_12, .both h12 hw => .both (s123_23 h123_12 h12) hw
  | .right h123_12, h12 => .right (s123_23 h123_12 h12)
  | .both h123_12 hw, .left h12 => .both (s123_23 h123_12 h12) hw
  | .both h123_12 _, .right h12 => .right (s123_23 h123_12 h12)
  | .both h123_12 hw, .both h12 hw' => .both (s123_23 h123_12 h12) hw

def Ctx.SSplit.s23 {Γ123 Γ12 Γ1 Γ2 Γ3 : Ctx α ε}
  : (h123_12 : SSplit Γ123 Γ12 Γ3) → (h12 : SSplit Γ12 Γ1 Γ2) → SSplit (ctx23 h123_12 h12) Γ2 Γ3
  | .nil, .nil => .nil
  | .left h123_12, .left h12 => s23 h123_12 h12
  | .left h123_12, .right h12 => .left (s23 h123_12 h12)
  | .left h123_12, .both h12 hw => .left (s23 h123_12 h12)
  | .right h123_12, h12 => .right (s23 h123_12 h12)
  | .both h123_12 hw, .left h12 => .right (s23 h123_12 h12)
  | .both h123_12 hw, .right h12 => .both (s23 h123_12 h12) hw
  | .both h123_12 hw, .both h12 hw' => .both (s23 h123_12 h12) hw

def Ctx.SSplit.ctx12 {Γ123 Γ1 Γ23 Γ2 Γ3 : Ctx α ε}
  : SSplit Γ123 Γ1 Γ23 → SSplit Γ23 Γ2 Γ3 → Ctx α ε
  | .nil, .nil => .nil
  | .left (w := w) h123_23, h23 =>
    (ctx12 h123_23 h23).cons w
  | .right (w := w) h123_23, .left h23
  | .right (w := w) h123_23, .both (w := _) h23 _ =>
    (ctx12 h123_23 h23).cons w
  | .right (w := _) h123_23, .right h23 =>
    ctx12 h123_23 h23
  | .both (w := w) h123_23 _, .left h23
  | .both (w := w) h123_23 _, .right h23
  | .both (w := w) h123_23 _, .both (w := _) h23 _ =>
    (ctx12 h123_23 h23).cons w

def Ctx.SSplit.s123_12 {Γ123 Γ1 Γ23 Γ2 Γ3 : Ctx α ε}
  : (h123_23 : SSplit Γ123 Γ1 Γ23) → (h23 : SSplit Γ23 Γ2 Γ3) → SSplit Γ123 (ctx12 h123_23 h23) Γ3
  | .nil, .nil => .nil
  | .left h123_23, h23 =>
    .left (s123_12 h123_23 h23)
  | .right h123_23, .left  h23      => .left  (s123_12 h123_23 h23)
  | .right h123_23, .right h23      => .right (s123_12 h123_23 h23)
  | .right h123_23, .both h23 hw    => .both (s123_12 h123_23 h23) hw
  | .both h123_23 hw, .left  h23     => .left  (s123_12 h123_23 h23)
  | .both h123_23 hw, .right h23     => .both (s123_12 h123_23 h23) hw
  | .both h123_23 hw, .both h23 _    => .both (s123_12 h123_23 h23) hw

def Ctx.SSplit.s12 {Γ123 Γ1 Γ23 Γ2 Γ3 : Ctx α ε}
  : (h123_23 : SSplit Γ123 Γ1 Γ23) → (h23 : SSplit Γ23 Γ2 Γ3) → SSplit (ctx12 h123_23 h23) Γ1 Γ2
  | .nil, .nil =>
    .nil
  | .left h123_23, h23 =>
    .left (s12 h123_23 h23)
  | .right h123_23, .left  h23    => .right (s12 h123_23 h23)
  | .right h123_23, .right h23    => s12 h123_23 h23
  | .right h123_23, .both h23 _   => .right (s12 h123_23 h23)
  | .both h123_23 hw, .left  h23     => .both (s12 h123_23 h23) hw
  | .both h123_23 hw, .right h23     => .left (s12 h123_23 h23)
  | .both h123_23 hw, .both h23 _    => .both (s12 h123_23 h23) hw
