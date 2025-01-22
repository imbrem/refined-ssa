import RefinedSSA.Signature
import RefinedSSA.Model

import Discretion.EffectSystem.Basic
import Discretion.Premonoidal.Effectful
import Discretion.Premonoidal.BraidedHelpers

namespace RefinedSSA

open CategoryTheory

open MonoidalCategory

open Monoidal

open HasPQuant

class MonModel
  (φ : Type _) (α : Type _) (ε : Type _) [S : Signature φ α ε]
  (C : Type _)
  [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
  [AddMonoidalCategory C] [E : EffectfulStruct C ε]
  [∀X Y : C, LE (X ⟶ Y)]
  extends SigModel φ α ε C
  where
  copy_swap {A : Ty α} [IsRel A] : copy A ≫ σ_ _ _ = copy A
  copy_assoc {A : Ty α} [IsRel A] :
    Δ_ A ≫ Δ_ A ▷ (t⟦ A ⟧ : C) ≫ (α_ _ _ _).hom = Δ_ A ≫ t⟦ A ⟧ ◁ Δ_ A
  drop_pure {A} [IsAff A] : E.eff ⊥ (drop A)
  copy_pure {A} [IsRel A] : E.eff ⊥ (copy A)
  drop_unit : drop .unit = 𝟙 (𝟙_ C)
  drop_tensor {A B} [IsAff A] [IsAff B] : drop (.tensor A B) = (drop A ⊗ drop B) ≫ (λ_ _).hom
  copy_unit : copy .unit = (λ_ _).inv
  copy_tensor {A B} [IsRel A] [IsRel B]
    : copy (.tensor A B) = (copy A ⊗ copy B) ≫ swap_inner _ _ _ _
  drop_rem {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsAff A] [IsAff B] [hf : IsRem e] : f ≫ drop _ ≤ drop _
  copy_drop_left_rem {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsRel A] [IsAff B] [hf : IsRem e] : copy _ ≫ (f ≫ drop _) ▷ t⟦ A ⟧ ≤ (λ_ _).inv
  copy_dup_ltimes {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsRel A] [IsRel B] [hf : IsDup e] : f ≫ copy _ ≤ copy _ ≫ (f ⋉ f)
  copy_dup_rtimes {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsRel A] [IsRel B] [hf : IsDup e] : f ≫ copy _ ≤ copy _ ≫ (f ⋊ f)
  drop_add {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsAff A] [IsAff B] [hf : IsAdd e] : f ≫ drop _ ≥ drop _
  copy_drop_left_add {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsRel A] [IsAff B] [hf : IsAdd e] : copy _ ≫ (f ≫ drop _) ▷ t⟦ A ⟧ ≥ (λ_ _).inv
  copy_fuse_ltimes {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsRel A] [IsRel B] [hf : IsFuse e] : f ≫ copy _ ≥ copy _ ≫ (f ⋉ f)
  copy_fuse_rtimes {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
    [IsRel A] [IsRel B] [hf : IsFuse e] : f ≫ copy _ ≥ copy _ ≫ (f ⋊ f)

namespace MonModel

attribute [simp] copy_swap

variable {φ : Type _} {α : Type _} {ε : Type _} [S : Signature φ α ε]
         {C : Type _} [Category C] [MonoidalCategoryStruct C] [BraidedCategoryStruct C]
         [AddMonoidalCategory C] [E : EffectfulStruct C ε]

section Direct

variable [∀X Y : C, LE (X ⟶ Y)] [M : MonModel φ α ε C]

theorem copy_assoc_inv {A : Ty α} [IsRel A] :
  Δ_ A ≫ (t⟦ A ⟧ : C) ◁ Δ_ A ≫ (α_ _ _ _).inv = Δ_ A ≫ Δ_ A ▷ _ := by
  rw [<-cancel_mono (α_ _ _ _).hom]
  simp [MonModel.copy_assoc]

end Direct

section PartialOrder

variable [∀X Y : C, PartialOrder (X ⟶ Y)] [M : MonModel φ α ε C]

@[simp]
theorem drop_aff {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
  [IsAff A] [IsAff B] [hf : IsAff e] : f ≫ !_ B = !_ A
  := le_antisymm (drop_rem f h) (drop_add f h)

@[simp]
theorem copy_drop_left_aff {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
  [IsRel A] [IsAff B] [hf : IsAff e] : M.copy A ≫ (f ≫ !_ B) ▷ t⟦ A ⟧ = (λ_ (_ : C)).inv
  := le_antisymm (copy_drop_left_rem f h) (copy_drop_left_add f h)

theorem copy_rel_ltimes {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
  [IsRel A] [IsRel B] [hf : IsRel e] : f ≫ M.copy B = M.copy A ≫ (f ⋉ f)
  := le_antisymm (copy_dup_ltimes f h) (copy_fuse_ltimes f h)

theorem copy_rel_rtimes {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
  [IsRel A] [IsRel B] [hf : IsRel e] : f ≫ M.copy B = M.copy A ≫ (f ⋊ f)
  := le_antisymm (copy_dup_rtimes f h) (copy_fuse_rtimes f h)

theorem copy_rel_ltimes_eq_rtimes
  {A B : Ty α} {e : ε} (f : t⟦ A ⟧ ⟶ t⟦ B ⟧) (h : E.eff e f)
  [IsRel A] [IsRel B] [hf : IsRel e]
  : M.copy A ≫ (f ⋉ f) = M.copy A ≫ (f ⋊ f)
  := by rw [<-copy_rel_ltimes f h, copy_rel_rtimes f h]

end PartialOrder

end MonModel

end RefinedSSA
