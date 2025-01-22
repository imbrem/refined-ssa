import RefinedSSA.Ctx

namespace RefinedSSA

structure Var? (α : Type u) (ε : Type v) where
  ty : Ty α
  q : EQuant
  eff : ε

abbrev Var?.ety {α ε} (v : Var? α ε) : Ty α := match v.q with
  | 0 => .unit
  | (_ : Quant) => v.ty

def Ctx? (α : Type u) (ε : Type v) := List (Var? α ε)

variable {α ε}

@[ext]
theorem Var?.ext {v w : Var? α ε}
  (h : v.ty = w.ty) (h' : v.q = w.q) (h'' : v.eff = w.eff) : v = w :=
  by cases v; cases w; cases h; cases h'; cases h''; rfl

instance Var.coeToVar? : Coe (Var α ε) (Var? α ε) where
  coe v := ⟨v.ty, v.q, v.eff⟩

theorem Var.coe_var_inj {v w : Var α ε} (h : (v : Var? α ε) = w) : v = w :=
  by cases v; cases w; cases h; rfl

@[simp]
theorem Var.coe_eq_coe {v w : Var α ε} : (v : Var? α ε) = w ↔ v = w :=
  ⟨Var.coe_var_inj, λh => congrArg Var.coeToVar?.coe h⟩

@[match_pattern]
def Ctx?.nil {α ε} : Ctx? α ε := []

@[match_pattern]
def Ctx?.cons {α ε} (Γ : Ctx? α ε) (v : Var? α ε) : Ctx? α ε := List.cons v Γ

instance Ctx.coeToCtx? : Coe (Ctx α ε) (Ctx? α ε) where
  coe Γ := let rec go : Ctx α ε → Ctx? α ε
    | .nil => .nil
    | .cons Γ v => .cons (go Γ) v
  go Γ

@[simp]
theorem Ctx.coe_nil : (Ctx.nil (α := α) (ε := ε) : Ctx? α ε) = Ctx?.nil := rfl

@[simp]
theorem Ctx.coe_cons {Γ : Ctx α ε} {v : Var α ε} : (Ctx.cons Γ v : Ctx? α ε) = Ctx?.cons Γ v := rfl

@[match_pattern]
abbrev Ctx?.cons' {α ε} (Γ : Ctx? α ε) (A : Ty α) (q : EQuant) (e : ε) : Ctx? α ε := Γ.cons ⟨A, q, e⟩

@[elab_as_elim, cases_eliminator]
def Ctx?.casesOn {α ε} {motive : Ctx? α ε → Sort _} (Γ : Ctx? α ε)
  (nil : motive .nil)
  (cons : ∀ Γ v, motive (.cons Γ v))
  : motive Γ := match Γ with | .nil => nil | .cons Γ v => cons Γ v

@[elab_as_elim, induction_eliminator]
def Ctx?.inductionOn {α ε} {motive : Ctx? α ε → Sort _} (Γ : Ctx? α ε)
  (nil : motive .nil)
  (cons : ∀ Γ v, motive Γ → motive (Ctx?.cons Γ v))
  : motive Γ := match Γ with | .nil => nil | .cons Γ v => cons Γ v (inductionOn Γ nil cons)

def Ctx?.length {α ε} (Γ : Ctx? α ε) : ℕ := List.length Γ

@[simp]
theorem Ctx?.length_nil {α ε} : Ctx?.length (.nil : Ctx? α ε) = 0 := rfl

@[simp]
theorem Ctx?.length_cons {α ε} (Γ : Ctx? α ε) (v : Var? α ε)
  : Ctx?.length (Ctx?.cons Γ v) = Ctx?.length Γ + 1 := rfl

theorem Ctx?.length_cons' {α ε} (Γ : Ctx? α ε) (A : Ty α) (q : EQuant) (e : ε)
  : Ctx?.length (Ctx?.cons' Γ A q e) = Ctx?.length Γ + 1 := rfl

def Ctx?.thin {α ε} : Ctx? α ε → Ctx α ε
  | .nil => .nil
  | .cons Γ v => match v.q with
    | 0 => thin Γ
    | (q : Quant) => (thin Γ).cons' v.ty q v.eff

theorem Ctx?.length_thin {α ε} (Γ : Ctx? α ε) : Γ.thin.length ≤ Γ.length
  := by induction Γ with | nil => rfl | cons Γ v =>
    simp only [thin, length_cons]
    split
    omega
    simp [*]

abbrev Var?.unused (v : Var? α ε) : Prop := v.q = 0

abbrev Var?.used (v : Var? α ε) : Prop := 1 ≤ v.q

theorem Var?.used_iff (v : Var? α ε) : v.used ↔ ¬v.unused := EQuant.one_le_iff_ne_zero _

theorem Var?.unused_iff (v : Var? α ε) : v.unused ↔ ¬v.used := by simp [used_iff]

variable [HasQuant α]

open HasQuant

instance Var?.hasQuant : HasQuant (Var? α ε) where
  quant v := match v.q with | 0 => ⊤ | (q : Quant) => q ⊓ quant v.ty

structure Var?.del (v : Var? α ε) : Prop where
  q : 0 ≤ v.q
  ty : v.used → (0 : EQuant) ≤ v.ty.q

structure Var?.copy (v : Var? α ε) : Prop where
  q : EQuant.copy ≤ v.q
  ty : EQuant.copy ≤ v.ty.q

def Var?.scopy (v : Var? α ε) : Prop := v.used → v.copy

theorem Var?.unused.del {v : Var? α ε} (h : v.unused) : v.del
  := ⟨le_of_eq h.symm, λh' => False.elim ((v.used_iff.mp h') h)⟩

theorem Var?.unused.scopy {v : Var? α ε} (h : v.unused) : v.scopy
  := λh' => False.elim ((v.used_iff.mp h') h)

theorem Var?.copy.scopy {v : Var? α ε} (h : v.copy) : v.scopy := λ_ => h

theorem Var?.del.is_aff {v : Var? α ε} (h : v.del) : IsAff v.ety := match v with
  | ⟨A, (_ : Quant), e⟩ => ⟨h.ty (by simp)⟩
  | ⟨A, 0, e⟩ => inferInstance

theorem Var?.copy.is_rel {v : Var? α ε} (h : v.copy) : IsRel v.ety := match v with
  | ⟨_, (_ : Quant), _⟩ => ⟨h.ty⟩
  | ⟨_, 0, _⟩ => inferInstance

theorem Var?.scopy.is_rel {v : Var? α ε} (h : v.scopy) : IsRel v.ety := match v with
  | ⟨_, (_ : Quant), _⟩ => ⟨(h (by simp)).ty⟩
  | ⟨_, 0, _⟩ => inferInstance

inductive Var?.PSSplit : Var? α ε → Var? α ε → Var? α ε → Type _
  | left (A q e) : PSSplit ⟨A, q, e⟩ ⟨A, q, e⟩ ⟨A, 0, e⟩
  | right (A q e) : PSSplit ⟨A, q, e⟩ ⟨A, 0, e⟩ ⟨A, q, e⟩
  | both {v} : v.copy → PSSplit v v v

def Var?.PSSplit.sboth {v : Var? α ε} (h : v.scopy) : PSSplit v v v := if hv : v.used then
    PSSplit.both (h hv)
  else by
    rw [<-Var?.unused_iff] at hv
    convert PSSplit.left v.ty v.q v.eff

inductive Ctx?.PSSplit : Ctx? α ε → Ctx? α ε → Ctx? α ε → Type _ where
  | nil : Ctx?.PSSplit [] [] []
  | cons {Γ Δ Ξ v l r} (h : PSSplit Γ Δ Ξ) (hvw : v.PSSplit l r)
    : PSSplit (Ctx?.cons Γ v) (Ctx?.cons Δ l) (Ctx?.cons Ξ r)

theorem Ctx?.PSSplit.left_length {Γ Δ Ξ : Ctx? α ε} (h : Ctx?.PSSplit Γ Δ Ξ)
  : Ctx?.length Γ = Ctx?.length Δ
  := by induction h <;> simp [*]

theorem Ctx?.PSSplit.right_length {Γ Δ Ξ : Ctx? α ε} (h : Ctx?.PSSplit Γ Δ Ξ)
  : Ctx?.length Γ = Ctx?.length Ξ
  := by induction h <;> simp [*]

theorem Ctx?.PSSplit.target_length {Γ Δ Ξ : Ctx? α ε} (h : Ctx?.PSSplit Γ Δ Ξ)
  : Ctx?.length Δ = Ctx?.length Ξ := h.left_length.symm.trans h.right_length

variable [PartialOrder ε]

structure Var?.Wk (v w : Var? α ε) : Prop where
  ty : v.ty = w.ty
  q : w.q ≤ v.q
  eff : v.eff ≤ w.eff
  unused_del : w.unused → v.del

instance Var?.instLE : LE (Var? α ε) := ⟨Wk⟩

theorem Var?.used.anti {v w : Var? α ε} (h : v ≤ w) (hw : w.used) : v.used := hw.trans h.q

theorem Var?.unused.mono {v w : Var? α ε} (h : v ≤ w) : (hv : v.unused) → w.unused
  := by simp only [unused_iff, not_imp_not]; exact used.anti h

theorem Var?.del.anti {v w : Var? α ε} (h : v ≤ w) (hw : w.del) : v.del := open Classical in
  if hw' : w.used then
    ⟨hw.q.trans h.q, λ_ => h.ty ▸ hw.ty hw'⟩
  else
    h.unused_del ((unused_iff w).mpr hw')

theorem Var?.copy.anti {v w : Var? α ε} (h : v ≤ w) (hw : w.copy) : v.copy where
  q := hw.q.trans h.q
  ty := h.ty ▸ hw.ty

theorem Var?.scopy.anti_copy {v w : Var? α ε} (h : v ≤ w) (hw : w.scopy) (hw' : w.used) : v.copy
  := (hw hw').anti h

theorem Var?.scopy.anti {v w : Var? α ε} (h : v ≤ w) (hw : w.scopy) (hw' : w.used) : v.scopy
  := (hw.anti_copy h hw').scopy

instance Var?.instPartialOrder : PartialOrder (Var? α ε) where
  le_refl _ := ⟨rfl, le_refl _, le_refl _, λh => h.del⟩
  le_trans _ _ _ h h' :=
    ⟨h.ty.trans h'.ty, h'.q.trans h.q, h.eff.trans h'.eff, λx => (x.del.anti h').anti h⟩
  le_antisymm _ _ h h' := ext h.ty (le_antisymm h'.q h.q) (le_antisymm h.eff h'.eff)

inductive Ctx?.PWk : Ctx? α ε → Ctx? α ε → Prop where
  | nil : Ctx?.PWk .nil .nil
  | cons {Γ Δ v w} (h : Ctx?.PWk Γ Δ) (hvw : v ≤ w) : Ctx?.PWk (Ctx?.cons Γ v) (Ctx?.cons Δ w)

theorem Ctx?.PWk.head {Γ Δ v w} (h : PWk (α := α) (ε := ε) (.cons Γ v) (.cons Δ w)) : v ≤ w
  := match h with | Ctx?.PWk.cons _ hvw => hvw

theorem Ctx?.PWk.tail {Γ Δ v w} (h : PWk (α := α) (ε := ε) (.cons Γ v) (.cons Δ w)) : PWk Γ Δ
  := match h with | Ctx?.PWk.cons h _ => h

@[simp]
theorem Ctx?.PWk.cons_iff {Γ Δ v w} : PWk (α := α) (ε := ε) (.cons Γ v) (.cons Δ w) ↔ PWk Γ Δ ∧ v ≤ w
  := ⟨λ h => ⟨Ctx?.PWk.tail h, Ctx?.PWk.head h⟩, λ ⟨h, h'⟩ => Ctx?.PWk.cons h h'⟩

def Ctx?.PWk.inductionOn {Γ Δ} (h : PWk Γ Δ) {motive : (Γ Δ : Ctx? α ε) → PWk Γ Δ → Sort _}
  (nil : motive .nil .nil .nil)
  (cons : ∀ {Γ Δ v w} (h : PWk Γ Δ) (hvw : v ≤ w),
    motive Γ Δ h →
    motive (Ctx?.cons Γ v) (Ctx?.cons Δ w) (Ctx?.PWk.cons h hvw))
  : motive Γ Δ h := match Γ, Δ, h with
  | .nil, .nil, _ => nil
  | .cons _ _, .cons _ _, h => cons h.tail h.head (inductionOn h.tail nil cons)

@[simp]
theorem Ctx?.PWk.refl (Γ : Ctx? α ε) : PWk Γ Γ := by induction Γ <;> simp [Ctx?.PWk.nil, *]

theorem Ctx?.PWk.trans {Γ Δ Ξ : Ctx? α ε} (h : PWk Γ Δ) (h' : PWk Δ Ξ) : PWk Γ Ξ := by
  induction h generalizing Ξ <;> cases h'
  simp only [refl]
  simp only [cons_iff, true_and, *]
  apply le_trans <;> assumption

theorem Ctx?.PWk.antisymm {Γ Δ : Ctx? α ε} (h : PWk Γ Δ) (h' : PWk Δ Γ) : Γ = Δ := by
  induction h with
  | nil => rfl
  | cons h hvw I => cases h' with
  | cons h' hwv => rw [I h', le_antisymm hvw hwv]

theorem Ctx?.PWk.length {Γ Δ : Ctx? α ε} (h : PWk Γ Δ) : Ctx?.length Γ = Ctx?.length Δ
  := by induction h <;> simp [*]

inductive Ctx?.Wk : Ctx? α ε → Ctx? α ε → Type where
  | nil : Ctx?.Wk .nil .nil
  | cons {Γ Δ v w} (h : Ctx?.Wk Γ Δ) (hvw : v ≤ w) : Ctx?.Wk (Ctx?.cons Γ v) (Ctx?.cons Δ w)
  | skip {Γ Δ v} (h : Ctx?.Wk Γ Δ) (hv : v.del) : Ctx?.Wk (Ctx?.cons Γ v) Δ

theorem Ctx?.Wk.length {Γ Δ : Ctx? α ε} (h : Wk Γ Δ) : Ctx?.length Δ ≤ Ctx?.length Γ
  := by induction h <;> simp <;> omega

def Ctx?.PWk.toWk {Γ Δ : Ctx? α ε} (h : PWk Γ Δ) : Wk Γ Δ
  := h.inductionOn (motive := λΓ Δ _ => Wk Γ Δ) .nil (λ_ h m => .cons m h)

theorem Ctx?.Wk.toPWk {Γ Δ : Ctx? α ε} (h : Wk Γ Δ) (h' : Γ.length = Δ.length) : Γ.PWk Δ
  := by induction h with
  | nil => exact .nil
  | cons h v I => exact .cons (I (by convert h' using 0; simp)) v
  | skip h =>
    have hl := h.length
    rw [<-h', length_cons] at hl
    omega

theorem Ctx?.Wk.antisymm {Γ Δ : Ctx? α ε} (h : Wk Γ Δ) (h' : Wk Δ Γ) : Γ = Δ :=
  have hl := le_antisymm h'.length h.length
  PWk.antisymm (h.toPWk hl) (h'.toPWk (hl.symm))

-- toPWk is a faithful functor
theorem Ctx?.Wk.eq_pwk {Γ Δ : Ctx? α ε} (h : Wk Γ Δ) (h' : Γ.length = Δ.length)
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

def Ctx?.Wk.refl (Γ : Ctx? α ε) : Wk Γ Γ := (Ctx?.PWk.refl Γ).toWk

theorem Ctx?.Wk.eq_refl {Γ : Ctx? α ε} (h : Wk Γ Γ) : h = Wk.refl Γ := eq_pwk h rfl

def Ctx?.Wk.comp {Γ Δ Ξ : Ctx? α ε} : Wk Γ Δ → Wk Δ Ξ → Wk Γ Ξ
  | .nil, .nil => .nil
  | .cons h hv, .cons h' hv' => .cons (h.comp h') (hv.trans hv')
  | .cons h hv, .skip h' hv' => .skip (h.comp h') (hv'.anti hv)
  | .skip h hv, h' => .skip (h.comp h') hv

theorem Ctx?.Wk.comp_assoc {Γ Δ Ξ Θ : Ctx? α ε} (h : Wk Γ Δ) (h' : Wk Δ Ξ) (h'' : Wk Ξ Θ)
  : h.comp (h'.comp h'') = (h.comp h').comp h'' := by induction h generalizing Ξ Θ with
  | nil => cases h'; cases h''; rfl
  | cons _ _ I => cases h' <;> cases h'' <;> simp [comp, I]
  | skip _ _ I => simp [comp, I]

def Ctx?.Wk.ix {Γ Δ : Ctx? α ε} : Wk Γ Δ → ℕ → ℕ
  | .nil => id
  | .cons h _ => Nat.liftWk h.ix
  | .skip h _ => Nat.stepWk h.ix

@[simp]
theorem Ctx?.Wk.ix_increasing {Γ Δ : Ctx? α ε} (h : Wk Γ Δ) (i : ℕ) : i ≤ h.ix i := by
  induction h generalizing i with
  | nil => simp [ix]
  | cons _ _ I => cases i <;> simp [ix, *]
  | skip _ _ I => simp [ix]; have I := I i; omega

theorem Ctx?.Wk.ix_comp_applied {Γ Δ Ξ : Ctx? α ε} (h : Wk Γ Δ) (h' : Wk Δ Ξ) (i : ℕ)
  : (h.comp h').ix i = h.ix (h'.ix i) := by induction h generalizing Ξ i with
  | nil => cases h'; rfl
  | cons _ _ I => cases h' <;> cases i <;> simp [comp, ix, I]
  | skip _ _ I => simp [comp, ix, I]

theorem Ctx?.Wk.ix_comp {Γ Δ Ξ : Ctx? α ε} (h : Wk Γ Δ) (h' : Wk Δ Ξ)
  : (h.comp h').ix = h.ix ∘ h'.ix := funext (λi => Wk.ix_comp_applied h h' i)

theorem Ctx?.Wk.ix_length_eq_applied {Γ Δ : Ctx? α ε}
  (h : Γ.Wk Δ) (hl : Γ.length = Δ.length) (i : ℕ) : h.ix i = i := by induction h generalizing i with
  | nil => rfl
  | cons _ _ I =>
    cases i; rfl; simp only [ix, Nat.liftWk_succ, add_left_inj]; apply I; convert hl using 0; simp
  | skip h _ => have hl' := h.length; rw [<-hl] at hl'; simp at hl'

theorem Ctx?.Wk.ix_length_eq {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ) (hl : Γ.length = Δ.length)
  : h.ix = id := funext (λi => ix_length_eq_applied h hl i)

theorem Ctx?.Wk.ix_refl {Γ : Ctx? α ε} (h : Γ.Wk Γ) : h.ix = id := ix_length_eq _ rfl

-- TODO: ix is an injection...

theorem Ctx?.Wk.ix_bounded {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ) (i : ℕ)
  (hi : i < Δ.length) : h.ix i < Γ.length
  := by induction h generalizing i with
  | nil => simp at hi
  | cons _ _ I =>
    cases i
    · simp [ix]
    · simp only [ix, Nat.liftWk_succ, length_cons, add_lt_add_iff_right]
      apply I; convert hi using 0; simp
  | skip _ _ I => simp [ix, *]

def Ctx?.Wk.skips {Γ Δ : Ctx? α ε} (h : Wk Γ Δ) : ℕ := h.ix 0

def Ctx?.choose_drop (Γ : Ctx? α ε) (h : Nonempty (Γ.Wk .nil)) : Γ.Wk .nil := match Γ with
  | .nil => .nil
  | .cons Γ v => .skip
    (Γ.choose_drop (have ⟨h⟩ := h; by cases h; constructor; assumption))
    (have ⟨h⟩ := h; by cases h; assumption)

def Var?.Ix (Γ : Ctx? α ε) (v : Var? α ε) : Type _ := Γ.Wk [v]

@[match_pattern]
def Var?.zero_le {Γ : Ctx? α ε} (x : Γ.Wk .nil) {v w : Var? α ε} (h : v ≤ w) : Ix (Γ.cons v) w
  := x.cons h

@[match_pattern]
abbrev Var?.zero {Γ : Ctx? α ε} (x : Γ.Wk .nil) (v : Var? α ε) : Ix (Γ.cons v) v
  := zero_le x (le_refl v)

@[match_pattern]
def Var?.Ix.succ {Γ : Ctx? α ε} {v : Var? α ε} (h : v.del) {w} (x : Ix Γ w) : Ix (Γ.cons v) w
  := x.skip h

@[elab_as_elim, cases_eliminator]
def Var?.Ix.casesOn {motive : ∀ {Γ v}, Ix Γ v → Sort _}
  {Γ v} (x : Ix Γ v)
  (zero_le : ∀ {Γ : Ctx? α ε} (d : Γ.Wk .nil) {v w} (hv : v ≤ w), motive (zero_le d hv))
  (succ : ∀ {Γ} {v : Var? α ε} (h : v.del) {w} (x : Ix Γ w), motive (succ h x))
  : motive x := match x with
  | .cons d hv => zero_le d hv
  | .skip x hv => succ hv x

@[elab_as_elim, induction_eliminator]
def Var?.Ix.inductionOn {motive : ∀ {Γ v}, Ix Γ v → Sort _}
  {Γ v} (x : Ix Γ v)
  (zero_le : ∀ {Γ : Ctx? α ε} (d : Γ.Wk .nil) {v w} (hv : v ≤ w), motive (zero_le d hv))
  (succ : ∀ {Γ} {v : Var? α ε} (h : v.del) {w} (x : Ix Γ w), motive x → motive (succ h x))
  : motive x := match x with
  | .cons d hv => zero_le d hv
  | .skip x hv => succ hv x (inductionOn x zero_le succ)

def Var?.Ix.ix {Γ : Ctx? α ε} {v} (x : Ix Γ v) : ℕ := x.skips

@[simp]
theorem Var?.ix_zero_le {Γ : Ctx? α ε} {v w : Var? α ε} (h : v ≤ w) (x : Γ.Wk .nil)
  : (zero_le x h).ix = 0 := rfl

@[simp]
theorem Var?.Ix.ix_succ {Γ : Ctx? α ε} {v : Var? α ε} (h : v.del) {w} (x : Ix Γ w)
  : (succ h x).ix = x.ix + 1 := rfl

def Var?.Ix.wk {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ) {v} (x : Ix Δ v) : Ix Γ v := h.comp x

theorem Var?.Ix.wk_wk {Γ Δ Ξ : Ctx? α ε} (h : Γ.Wk Δ) (h' : Δ.Wk Ξ) {v} (x : Ix Ξ v)
  : (x.wk h').wk h = x.wk (h.comp h') := Ctx?.Wk.comp_assoc h h' x

theorem Var?.Ix.wk_comp {Γ Δ Ξ : Ctx? α ε} (h : Γ.Wk Δ) (h' : Δ.Wk Ξ) {v} (x : Ix Ξ v)
  : x.wk (h.comp h') = (x.wk h').wk h := (x.wk_wk h h').symm

@[simp]
theorem Var?.Ix.succ_wk_cons {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ)
  {v v' : Var? α ε} (hv : v ≤ v') (hv' : v'.del) {w} (x : Ix Δ w)
  : (succ hv' x).wk (h.cons hv) = (succ (hv'.anti hv) (x.wk h)) := rfl

@[simp]
theorem Var?.Ix.wk_skip {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ)
  {v : Var? α ε} (hv : v.del) {w} (x : Ix Δ w)
  : x.wk (h.skip hv) = (x.wk h).succ hv := rfl

@[simp]
theorem Var?.Ix.ix_wk {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ) {v} (x : Ix Δ v) : (x.wk h).ix = h.ix x.ix
  := by rw [ix, Ctx?.Wk.skips, wk, Ctx?.Wk.ix_comp]; rfl

theorem Var?.Ix.ix_wk_le {Γ Δ : Ctx? α ε} (h : Γ.Wk Δ) {v} (x : Ix Δ v) : x.ix ≤ (x.wk h).ix
  := by simp

-- TODO: ix is an injection on variables...

inductive Ctx?.At (v : Var? α ε) : Ctx? α ε → ℕ → Prop where
  | here {Γ} (d : Ctx?.Wk Γ .nil) {w} : w ≤ v → Ctx?.At v (Ctx?.cons Γ w) 0
  | there {Γ w} (x : Ctx?.At v Γ n) (hw : w.del) : Ctx?.At v (Ctx?.cons Γ w) (n + 1)

theorem Ctx?.At.zero_cons_head {Γ : Ctx? α ε} {v} (h : (Γ.cons w).At v 0) : w ≤ v
  := by cases h; assumption

def Ctx?.At.zero_cons_tail {Γ : Ctx? α ε} {v} (h : (Γ.cons w).At v 0) : Γ.Wk .nil
  := Γ.choose_drop (by cases h; constructor; assumption)

theorem Ctx?.At.succ_cons_head {Γ : Ctx? α ε} {v w} (h : (Γ.cons w).At v (n + 1)) : w.del
  := by cases h; assumption

theorem Ctx?.At.succ_cons_tail {Γ : Ctx? α ε} {v w} (h : (Γ.cons w).At v (n + 1)) : Γ.At v n
  := by cases h; assumption

theorem Ctx?.At.succ_cons_iff (Γ : Ctx? α ε) (v w) : (Γ.cons w).At v (n + 1) ↔ w.del ∧ Γ.At v n
  := ⟨λh => ⟨h.succ_cons_head, h.succ_cons_tail⟩, λ⟨h, h'⟩ => At.there h' h⟩

@[elab_as_elim, induction_eliminator]
def Ctx?.At.inductionOn {v : Var? α ε} {motive : ∀ (Γ n), Ctx?.At v Γ n → Sort _}
  (h : Ctx?.At v Γ n)
  (here : ∀ (Γ : Ctx? α ε) (d : Γ.Wk .nil) (w) (hw : w ≤ v), motive (Γ.cons w) 0 (here d hw))
  (there : ∀ (Γ) (w : Var? α ε) (n) (x : Ctx?.At v Γ n) (hw : w.del),
    motive Γ n x → motive (Γ.cons w) (n + 1) (there x hw))
  : motive Γ n h := match Γ, n, h with
  | .cons Γ w, 0, h => here Γ h.zero_cons_tail w h.zero_cons_head
  | .cons Γ w, n + 1, h
    => there Γ w n h.succ_cons_tail h.succ_cons_head (h.succ_cons_tail.inductionOn here there)

def Ctx?.At.ix {Γ : Ctx? α ε} {v n} (h : Γ.At v n) : v.Ix Γ
  := h.inductionOn (λ_ d _ h => Var?.zero_le d h) (λ_ _ _ _ hv I => I.succ hv)

@[simp]
theorem Ctx?.At.ix_ix {Γ : Ctx? α ε} {v n} (h : Γ.At v n) : h.ix.ix = n
  := by induction h <;> simp [ix, inductionOn]; assumption

theorem Var?.Ix.at {Γ : Ctx? α ε} {v} (x : Ix Γ v) : Γ.At v x.ix
  := by induction x <;> constructor <;> assumption

-- TODO: so therefore at_ix is just the identity

inductive Var?.PSplit : Var? α ε → Var? α ε → Var? α ε → Type _
  | left {v w} (h : v ≤ w) (e) : PSplit v w ⟨v.ty, 0, e⟩
  | right {v w} (h : v ≤ w) (e) : PSplit v ⟨v.ty, 0, e⟩ w
  | both {u v w} : u.copy → u ≤ v → u ≤ w → PSplit u v w

inductive Ctx?.PSplit : Ctx? α ε → Ctx? α ε → Ctx? α ε → Type _ where
  | nil : Ctx?.PSplit [] [] []
  | cons {Γ Δ Ξ v l r} (h : PSplit Γ Δ Ξ) (hvw : v.PSplit l r)
    : PSplit (Ctx?.cons Γ v) (Ctx?.cons Δ l) (Ctx?.cons Ξ r)

def Var?.PSSplit.toPSplit {u v w : Var? α ε} (h : u.PSSplit v w) : u.PSplit v w := match h with
  | Var?.PSSplit.left A q e => Var?.PSplit.left (le_refl _) e
  | Var?.PSSplit.right A q e => Var?.PSplit.right (le_refl _) e
  | Var?.PSSplit.both hu => Var?.PSplit.both hu (le_refl _) (le_refl _)

def Ctx?.PSSplit.toPSplit {Γ Δ Ξ : Ctx? α ε} : Ctx?.PSSplit Γ Δ Ξ → Ctx?.PSplit Γ Δ Ξ
  | .nil => .nil
  | .cons h hvw => .cons h.toPSplit hvw.toPSplit
