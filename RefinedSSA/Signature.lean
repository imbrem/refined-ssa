import RefinedSSA.Ty
import Discretion.EffectSystem.Basic

namespace RefinedSSA

class Signature (φ : Type _) (α : outParam (Type _)) (ε : outParam (Type _))
  extends EffectSystem ε, HasQuant α
  where
  src : φ → Ty α
  trg : φ → Ty α
  eff : φ → ε

structure Signature.IsFn [Signature φ α ε] (f : φ) (e : ε) (A B : Ty α) where
  src : A = src f
  trg : B = trg f
  eff : eff f ≤ e
