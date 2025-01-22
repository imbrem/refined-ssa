import Discretion.Wk.Nat
import Discretion.Wk.Finset

namespace RefinedSSA

inductive Term (φ : Type u) : Type u
  -- Basic symmetric monoidal theory
  | var (i : ℕ)
  | op (f : φ) (a : Term φ)
  | let₁ (a : Term φ) (e : Term φ)
  | unit
  | pair (a : Term φ) (b : Term φ)
  | let₂ (a : Term φ) (e : Term φ)
  -- Distributive theory
  | inl (a : Term φ)
  | inr (a : Term φ)
  | case (a : Term φ) (l : Term φ) (r : Term φ)
  | abort (a : Term φ)
  -- Iteration theory
  | iter (a : Term φ) (b : Term φ)
  -- Meta
  | invalid

namespace Term

def fvu : Term φ → ℕ → Bool
  | .var i, j => i = j
  | .let₁ a e, j => a.fvu j ∨ e.fvu (j + 1)
  | .pair a b, j => a.fvu j ∨ b.fvu j
  | .let₂ a e, j => a.fvu j ∨ e.fvu (j + 2)
  | .op _ a, j
  | .inl a, j
  | .inr a, j
  | .abort a, j => a.fvu j
  | .case a l r, j => a.fvu j ∨ l.fvu (j + 1) ∨ r.fvu (j + 1)
  | .iter a b, j => a.fvu j ∨ b.fvu (j + 1)
  | _, _ => false

def fvs : Term φ → Finset ℕ
  | .var i => {i}
  | .let₁ a e => a.fvs ∪ Finset.liftFv e.fvs
  | .pair a b => a.fvs ∪ b.fvs
  | .let₂ a e => a.fvs ∪ Finset.liftFv (Finset.liftFv e.fvs)
  | .op _ a
  | .inl a
  | .inr a
  | .abort a => a.fvs
  | .case a l r => a.fvs ∪ Finset.liftFv l.fvs ∪ Finset.liftFv r.fvs
  | .iter a b => a.fvs ∪ Finset.liftFv b.fvs
  | _ => ∅

-- TODO: mem fvs iff fvu

def fvm : Term φ → ℕ
  | .var i => i + 1
  | .let₁ a e => a.fvm ⊔ (e.fvm - 1)
  | .pair a b => a.fvm ⊔ b.fvm
  | .let₂ a e => a.fvm ⊔ (e.fvm - 2)
  | .op _ a
  | .inl a
  | .inr a
  | .abort a => a.fvm
  | .case a l r => a.fvm ⊔ (l.fvm - 1) ⊔ (r.fvm - 1)
  | .iter a b => a.fvm ⊔ (b.fvm - 1)
  | _ => 0

-- TODO: ∀i ∈ fvs, i < fvm

-- TODO: fvm = n + 1 => fvu n i.e. fvm n ==> n ≠ 0 ==> fvu (n - 1)

def ren (ρ : ℕ → ℕ) : Term φ → Term φ
  | var i => var (ρ i)
  | op f a => op f (a.ren ρ)
  | let₁ a e => let₁ (a.ren ρ) (e.ren (Nat.liftWk ρ))
  | pair a b => pair (a.ren ρ) (b.ren ρ)
  | let₂ a e => let₂ (a.ren ρ) (e.ren (Nat.liftWk (Nat.liftWk ρ)))
  | inl a => inl (a.ren ρ)
  | inr a => inr (a.ren ρ)
  | case a l r => case (a.ren ρ) (l.ren (Nat.liftWk ρ)) (r.ren (Nat.liftWk ρ))
  | iter a b => iter (a.ren ρ) (b.ren (Nat.liftWk ρ))
  | t => t

@[simp] theorem ren_id {a : Term φ} : a.ren id = a := by induction a <;> simp [ren, *]

theorem ren_comp {ρ σ : ℕ → ℕ} {a : Term φ} : a.ren (ρ ∘ σ) = (a.ren σ).ren ρ :=
  by induction a generalizing ρ σ <;> simp [ren, Nat.liftWk_comp, *]

theorem ren_ren {ρ σ : ℕ → ℕ} {a : Term φ} : (a.ren σ).ren ρ = a.ren (ρ ∘ σ) := ren_comp.symm

def wk0 : Term φ → Term φ := ren Nat.succ

def Subst (φ : Type u) := ℕ → Term φ

def Subst.lift (σ : Subst φ) : Subst φ
  | 0 => .var 0
  | i + 1 => (σ i).wk0

@[simp]
theorem Subst.lift_zero (σ : Subst φ) : σ.lift 0 = .var 0 := rfl

@[simp]
theorem Subst.lift_succ (σ : Subst φ) (i : ℕ) : σ.lift (i + 1) = (σ i).wk0 := rfl

def subst (σ : Subst φ) : Term φ → Term φ
  | .var i => σ i
  | op f a => op f (subst σ a)
  | let₁ a e => let₁ (subst σ a) (subst (σ.lift) e)
  | pair a b => pair (subst σ a) (subst σ b)
  | let₂ a e => let₂ (subst σ a) (subst (σ.lift.lift) e)
  | inl a => inl (subst σ a)
  | inr a => inr (subst σ a)
  | case a l r => case (subst σ a) (subst (σ.lift) l) (subst (σ.lift) r)
  | iter a b => iter (subst σ a) (subst (σ.lift) b)
  | t => t

instance Subst.instOne : One (Subst φ) where
  one := λ i => .var i

instance Subst.instMul : Mul (Subst φ) where
  mul σ τ i := (τ i).subst σ

@[simp]
theorem Subst.comp_applied {σ τ : Subst φ} {i : ℕ} : (σ * τ) i = (τ i).subst σ := rfl

@[simp]
theorem Subst.id_applied (i : ℕ) : (1 : Subst φ) i = .var i := rfl

@[simp]
theorem Subst.lift_id : (1 : Subst φ).lift = 1 := by funext i; cases i <;> rfl

@[simp]
theorem subst_id (a : Term φ) : a.subst 1 = a := by induction a <;> simp [subst, *]

@[simp]
theorem Subst.comp_id (σ : Subst φ) : σ * 1 = σ := by funext i; simp [subst]

@[simp]
theorem Subst.id_comp (σ : Subst φ) : 1 * σ = σ := by funext i; simp

def Subst.renIn (ρ : ℕ → ℕ) (σ : Subst φ) : Subst φ := λi => σ (ρ i)

@[simp]
theorem Subst.renIn_applied (ρ : ℕ → ℕ) (σ : Subst φ) (i : ℕ) : (σ.renIn ρ) i = σ (ρ i) := rfl

def Subst.renOut (ρ : ℕ → ℕ) (σ : Subst φ) : Subst φ := λi => (σ i).ren ρ

@[simp]
theorem Subst.renOut_applied (ρ : ℕ → ℕ) (σ : Subst φ) (i : ℕ) : (σ.renOut ρ) i = (σ i).ren ρ := rfl

def Subst.ofRen (σ : ℕ → ℕ) : Subst φ := .var ∘ σ

instance Subst.coeRen : Coe (ℕ → ℕ) (Subst φ) where
  coe := ofRen

@[simp]
theorem Subst.coe_eq_coe (ρ σ : ℕ → ℕ) : (ρ : Subst φ) = (σ : Subst φ) ↔ ρ = σ
  := by constructor
        intro h; ext i; have h := congrFun h i; convert h using 0; simp [ofRen]
        intro h; cases h; rfl

theorem Subst.lift_renIn (σ : Subst φ) (ρ : ℕ → ℕ)
  : (σ.renIn ρ).lift = σ.lift.renIn (Nat.liftWk ρ) := funext (λi => by cases i <;> rfl)

theorem subst_renIn {σ : Subst φ} {ρ : ℕ → ℕ} {a : Term φ}
  : a.subst (σ.renIn ρ) = (a.ren ρ).subst σ
  := by induction a generalizing σ ρ <;> simp [subst, Subst.lift_renIn, ren, *]

theorem Subst.lift_renOut (σ : Subst φ) (ρ : ℕ → ℕ)
  : (σ.renOut ρ).lift = (σ.lift).renOut (Nat.liftWk ρ)
  := funext (λi => by cases i <;> simp [ren, wk0, ren_ren, Nat.liftWk_comp_succ])

theorem subst_renOut {σ : Subst φ} {ρ : ℕ → ℕ} {a : Term φ}
  : a.subst (σ.renOut ρ) = (a.subst σ).ren ρ
  := by induction a generalizing σ ρ <;> simp [subst, Subst.lift_renOut, ren, *]

theorem renIn_succ_lift {σ : Subst φ} : σ.lift.renIn .succ = σ.renOut .succ
  := by funext i; cases i <;> simp [wk0]

theorem Subst.lift_comp (σ τ : Subst φ) : (σ * τ).lift = σ.lift * τ.lift := by
  funext i; cases i <;> simp [wk0, subst, <-subst_renOut, <-subst_renIn, renIn_succ_lift]

theorem subst_comp {σ τ : Subst φ} {a : Term φ} : a.subst (σ * τ) = (a.subst τ).subst σ
  := by induction a generalizing σ τ <;> simp [subst, Subst.lift_comp, *]

theorem subst_subst {σ τ : Subst φ} {a : Term φ} : (a.subst τ).subst σ = a.subst (σ * τ)
  := subst_comp.symm

theorem Subst.comp_assoc (σ τ ρ : Subst φ) : (σ * τ) * ρ = σ * (τ * ρ) := by
  funext i; simp [subst, Subst.comp_applied, subst_comp]

instance Subst.instMonoid : Monoid (Subst φ) where
  one_mul := Subst.id_comp
  mul_one := Subst.comp_id
  mul_assoc := Subst.comp_assoc

end Term

end RefinedSSA
