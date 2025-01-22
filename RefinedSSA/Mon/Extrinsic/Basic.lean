import RefinedSSA.OptCtx
import RefinedSSA.Syntax
import RefinedSSA.Signature

namespace RefinedSSA

namespace Term

variable {φ : Type _} {α : Type _} {ε : Type _} [S : Signature φ α ε]

inductive MonD : ε → Ctx? α ε → Ty α → Term φ → Type _
  | var {Γ} : Γ.At ⟨A, 1, e⟩ n → MonD e Γ A (.var n)
  | op {Γ e A B f a} : S.IsFn f e A B → MonD e Γ A a → MonD e Γ B (.op f a)
  | let₁ {Γ Γl Γr e A B a b} :
    Γ.PSSplit Γr Γl →
    MonD e Γl A a → MonD e (Γr.cons ⟨A, ⊤, ⊥⟩) B b → MonD e Γ B (.let₁ a b)
  | unit {Γ} : Γ.Wk .nil → MonD e Γ .unit .unit
  | pair {Γ Γl Γr e A B a b} :
    Γ.PSSplit Γl Γr →
    MonD e Γl A a → MonD e Γr B b → MonD e Γ (.tensor A B) (.pair a b)
  | let₂ {Γ Γl Γr e A B C a b} :
    Γ.PSSplit Γr Γl →
    MonD e Γl (.tensor A B) a → MonD e ((Γr.cons ⟨A, ⊤, ⊥⟩).cons ⟨B, ⊤, ⊥⟩) C b
      → MonD e Γ C (.let₂ a b)

notation Γ "⊢" a ":" A "@D" e => MonD e Γ A a

inductive MonW : ε → Ctx? α ε → Ty α → Term φ → Prop
  | var {Γ} : Γ.At ⟨A, 1, e⟩ n → MonW e Γ A (.var n)
  | op {Γ e A B f a} : S.IsFn f e A B → MonW e Γ A a → MonW e Γ B (.op f a)
  | let₁ {Γ Γl Γr e A B a b} :
    Γ.PSSplit Γl Γr →
    MonW e Γr A a → MonW e (Γl.cons ⟨A, ⊤, ⊥⟩) B b → MonW e Γ B (.let₁ a b)
  | unit {Γ} : Γ.Wk .nil → MonW e Γ .unit .unit
  | pair {Γ Γl Γr e A B a b} :
    Γ.PSSplit Γl Γr →
    MonW e Γl A a → MonW e Γr B b → MonW e Γ (.tensor A B) (.pair a b)
  | let₂ {Γ Γl Γr e A B C a b} :
    Γ.PSSplit Γl Γr →
    MonW e Γr (.tensor A B) a → MonW e ((Γl.cons ⟨A, ⊤, ⊥⟩).cons ⟨B, ⊤, ⊥⟩) C b
      → MonW e Γ C (.let₂ a b)

theorem MonD.wf (h : MonD (φ := φ) e Γ A t) : MonW e Γ A t
  := by induction h <;> constructor <;> assumption

theorem MonW.op_fn {e Γ B f a} (h : MonW e Γ B (.op f a)) : S.IsFn f e (S.src f) B
  := by cases h with | op h h' => cases h.src; exact h

theorem MonW.op_arg {e Γ B f a} (h : MonW e Γ B (.op f a)) : MonW e Γ (S.src f) a
  := by cases h with | op h h' => cases h.src; exact h'

theorem MonW.nonempty (h : MonW (φ := φ) e Γ A t) : Nonempty (MonD e Γ A t)
  := by induction h <;> constructor <;> constructor
  <;> first | assumption | (apply Classical.choice; assumption)

theorem MonW.nonempty_iff : Nonempty (MonD (φ := φ) e Γ A t) ↔ MonW e Γ A t
  := ⟨λ⟨d⟩ => d.wf, MonW.nonempty⟩

-- TODO: need to synthesize left-biased context decompositions...
-- def MonW.choose (h : MonW (φ := φ) e Γ A t) : MonD e Γ A t := match t with
--   | .var n => .var (by cases h; assumption)
--   | .op f a => .op h.op_fn h.op_arg.choose
--   | .let₁ a b => sorry
--   | .unit => sorry
--   | .pair a b => sorry
--   | .let₂ a b => sorry
