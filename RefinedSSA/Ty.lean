import Discretion.Quant.Class

namespace RefinedSSA

open HasQuant

inductive Ty (α : Type u) : Type u where
  | of : α → Ty α
  | unit : Ty α
  | empty : Ty α
  | tensor : Ty α → Ty α → Ty α
  | coprod : Ty α → Ty α → Ty α

def Ty.map {α β : Type u} (f : α → β) : Ty α → Ty β
  | Ty.of a => Ty.of (f a)
  | Ty.unit => Ty.unit
  | Ty.empty => Ty.empty
  | Ty.tensor A B => Ty.tensor (A.map f) (B.map f)
  | Ty.coprod A B => Ty.coprod (A.map f) (B.map f)

def Ty.bind {α β : Type u} (f : α → Ty β) : Ty α → Ty β
  | Ty.of a => f a
  | Ty.unit => Ty.unit
  | Ty.empty => Ty.empty
  | Ty.tensor A B => Ty.tensor (A.bind f) (B.bind f)
  | Ty.coprod A B => Ty.coprod (A.bind f) (B.bind f)

def Ty.flatten {α : Type u} : Ty (Ty α) → Ty α
  | Ty.of A => A
  | Ty.unit => Ty.unit
  | Ty.empty => Ty.empty
  | Ty.tensor A B => Ty.tensor (Ty.flatten A) (Ty.flatten B)
  | Ty.coprod A B => Ty.coprod (Ty.flatten A) (Ty.flatten B)

def Ty.q [HasQuant α] : Ty α → Quant
  | Ty.of a => quant a
  | Ty.unit => ⊤
  | Ty.empty => ⊤
  | Ty.tensor A B => A.q ⊓ B.q
  | Ty.coprod A B => A.q ⊓ B.q

instance Ty.instHasQuant [HasQuant α] : HasQuant (Ty α) := ⟨q⟩

@[simp] theorem Ty.quant_unit [HasQuant α] : quant (Ty.unit : Ty α) = ⊤ := rfl

@[simp] theorem Ty.quant_empty [HasQuant α] : quant (Ty.empty : Ty α) = ⊤ := rfl

@[simp] theorem Ty.quant_of [HasQuant α] (a : α) : quant (Ty.of a : Ty α) = quant a := rfl

@[simp]
theorem Ty.quant_tensor [HasQuant α] (A B : Ty α) : quant (Ty.tensor A B) = quant A ⊓ quant B := rfl

@[simp]
theorem Ty.quant_coprod [HasQuant α] (A B : Ty α) : quant (Ty.coprod A B) = quant A ⊓ quant B := rfl

instance IsAff.of [HasQuant α] (a : α) [ha : IsAff a] : IsAff (Ty.of a)
  := ⟨ha.del_le_quant⟩

instance IsRel.of [HasQuant α] (a : α) [ha : IsRel a] : IsRel (Ty.of a)
  := ⟨ha.copy_le_quant⟩

instance IsAff.unit [HasQuant α] : IsAff (Ty.unit (α := α)) := ⟨by simp⟩

instance IsRel.unit [HasQuant α] : IsRel (Ty.unit (α := α)) := ⟨by simp⟩

instance IsAff.empty [HasQuant α] : IsAff (Ty.empty (α := α)) := ⟨by simp⟩

instance IsRel.empty [HasQuant α] : IsRel (Ty.empty (α := α)) := ⟨by simp⟩

instance IsAff.tensor
  [HasQuant α] (A B : Ty α) [hA : IsAff A] [hB : IsAff B] : IsAff (Ty.tensor A B)
  := ⟨by simp⟩

instance IsRel.tensor
  [HasQuant α] (A B : Ty α) [hA : IsRel A] [hB : IsRel B] : IsRel (Ty.tensor A B)
  := ⟨by simp⟩

instance IsAff.coprod
  [HasQuant α] (A B : Ty α) [hA : IsAff A] [hB : IsAff B] : IsAff (Ty.coprod A B)
  := ⟨by simp⟩

instance IsRel.coprod
  [HasQuant α] (A B : Ty α) [hA : IsRel A] [hB : IsRel B] : IsRel (Ty.coprod A B)
  := ⟨by simp⟩

theorem IsAff.of_inv [HasQuant α] (a : α) [ha : IsAff (Ty.of a)] : IsAff a := ⟨ha.del_le_quant⟩

theorem IsAff.tensor_left [HasQuant α] (A B : Ty α) [hAB : IsAff (Ty.tensor A B)] : IsAff A
  := ⟨(le_inf_iff.mp hAB.del_le_quant).1⟩

theorem IsAff.tensor_right [HasQuant α] (A B : Ty α) [hAB : IsAff (Ty.tensor A B)] : IsAff B
  := ⟨(le_inf_iff.mp hAB.del_le_quant).2⟩

theorem IsAff.coprod_left [HasQuant α] (A B : Ty α) [hAB : IsAff (Ty.coprod A B)] : IsAff A
  := ⟨(le_inf_iff.mp hAB.del_le_quant).1⟩

theorem IsAff.coprod_right [HasQuant α] (A B : Ty α) [hAB : IsAff (Ty.coprod A B)] : IsAff B
  := ⟨(le_inf_iff.mp hAB.del_le_quant).2⟩

theorem IsRel.of_inv [HasQuant α] (a : α) [ha : IsRel (Ty.of a)]
  : IsRel a := ⟨ha.copy_le_quant⟩

theorem IsRel.tensor_left [HasQuant α] (A B : Ty α) [hAB : IsRel (Ty.tensor A B)]
  : IsRel A := ⟨(le_inf_iff.mp hAB.copy_le_quant).1⟩

theorem IsRel.tensor_right [HasQuant α] (A B : Ty α) [hAB : IsRel (Ty.tensor A B)]
  : IsRel B := ⟨(le_inf_iff.mp hAB.copy_le_quant).2⟩

theorem IsRel.coprod_left [HasQuant α] (A B : Ty α) [hAB : IsRel (Ty.coprod A B)]
  : IsRel A := ⟨(le_inf_iff.mp hAB.copy_le_quant).1⟩

theorem IsRel.coprod_right [HasQuant α] (A B : Ty α) [hAB : IsRel (Ty.coprod A B)]
  : IsRel B := ⟨(le_inf_iff.mp hAB.copy_le_quant).2⟩
