import RefinedSSA.Signature

import Discretion.EffectSystem.Basic
import Discretion.Premonoidal.Effectful
import Discretion.AddMonoidalCategory.Basic
import Discretion.Utils.Category

namespace RefinedSSA

open CategoryTheory

open MonoidalCategory

open Monoidal

class TyModel
  (α : Type _) [HasQuant α]
  (C : Type _) [Category C] [MC : MonoidalCategoryStruct C] [AddMonoidalCategory C]
  where
  den_base : α → C

variable {φ : Type _} {α : Type _} {ε : Type _}
         {C : Type _} [Category C] [MonoidalCategoryStruct C] [AddMonoidalCategory C]

open TyModel

section TyModel

variable [HasQuant α] [TyModel α C]

def Ty.den : Ty α → C
  | .of A => TyModel.den_base A
  | .unit => 𝟙_ C
  | .tensor A B => den A ⊗ den B
  | .empty => 𝟘_ C
  | .coprod A B => den A +ₒ den B

notation "t⟦" A "⟧" => Ty.den A

end TyModel

class VarModel
  (α : Type _) [HasQuant α]
  (C : Type _) [Category C] [MC : MonoidalCategoryStruct C] [AddMonoidalCategory C]
  extends TyModel α C where
  drop (A : Ty α) [IsAff A] : t⟦ A ⟧ ⟶ 𝟙_ C
  copy (A : Ty α) [IsRel A] : (t⟦ A ⟧ : C) ⟶ t⟦ A ⟧ ⊗ t⟦ A ⟧

notation "!_" => VarModel.drop

notation "Δ_" => VarModel.copy

-- TODO: do the categories in an EffectfulStruct need to be closed under LE for this to work???

class SigModel
  (φ : Type _) (α : Type _) (ε : Type _) [S : Signature φ α ε]
  (C : Type _) [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  [AddMonoidalCategory C] [E : EffectfulStruct C ε]
  extends VarModel α C
  where
  den_inst (f : φ) : (t⟦S.src f⟧ : C) ⟶ t⟦S.trg f⟧
  den_eff (f : φ) : E.eff (S.eff f) (den_inst f)

variable [BraidedCategoryStruct C] [Signature φ α ε] [EffectfulStruct C ε] [SigModel φ α ε C]

notation "i⟦" f "⟧" => SigModel.den_inst f

def Signature.IsFn.den {f : φ} {e : ε} {A B : Ty α} (h : IsFn f e A B)
  : (t⟦ A ⟧ : C) ⟶ t⟦ B ⟧ := eq_hom (by rw [h.src]) ≫ i⟦ f ⟧ ≫ eq_hom (by rw [h.trg])

end RefinedSSA
