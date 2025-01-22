import RefinedSSA.Mon.Extrinsic.Basic
import RefinedSSA.Mon.Semantics.OptCtx

namespace RefinedSSA

open CategoryTheory

open Monoidal

open MonoidalCategory

variable {φ : Type _} {α : Type _} {ε : Type _} [S : Signature φ α ε]
  {C : Type _}
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  [AddMonoidalCategory C] [E : EffectfulStruct C ε]
  [∀X Y : C, LE (X ⟶ Y)]
  [MonModel φ α ε C]

namespace Term

def MonD.den {e : ε} {Γ : Ctx? α ε} {A : Ty α} {a : Term φ}
  : (Γ ⊢ a : A @D e) → ((g⟦ Γ ⟧ : C) ⟶ t⟦ A ⟧)
  | .var hv => hv.den
  | .op hf da => da.den ≫ hf.den
  | .let₁ dΓ da db => dΓ.den ≫ (_ ◁ da.den) ≫ db.den
  | .unit dΓ => dΓ.den
  | .pair dΓ da db => dΓ.den ≫ (da.den ⋉ db.den)
  | .let₂ dΓ da db => dΓ.den ≫ (_ ◁ da.den) ≫ (α_ _ _ _).inv ≫ db.den
