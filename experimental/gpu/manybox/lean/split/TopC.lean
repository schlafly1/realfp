import ManyBoxTape

/-! Two-level split certificates: a top tree whose leaves are arbitrary certificates (for
example `Gk.t.toCert d` of a group of sub-checks proved in its own file). `TopC.sound` glues
`checkC2` on the leaves into `checkC2` on the whole box. Mathlib-free, no `native_decide`. -/

open Interval64 Interval64.KF

namespace ManyBox

/-- `P` holds for every element (by recursion, so an explicit list unfolds to `∧`s). -/
def AllP {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | x :: xs => P x ∧ AllP P xs

theorem AllP_append {α : Type} (P : α → Prop) :
    ∀ (a b : List α), AllP P (a ++ b) ↔ AllP P a ∧ AllP P b
  | [], b => by simp [AllP]
  | x :: a, b => by simp only [List.cons_append, AllP, AllP_append P a b, and_assoc]

inductive TopC where
  | leaf (c : Cert)
  | split (i m : Nat) (l r : TopC)

def TopC.toCert : TopC → Cert
  | .leaf c => c
  | .split i m l r => .split i m l.toCert r.toCert

def TopC.midsOK : TopC → Bool
  | .leaf _ => true
  | .split _ m l r => !isNaN m && Nat.blt m (2 ^ 64) && l.midsOK && r.midsOK

def TopC.leaves : TopC → List KI → List (Cert × List KI)
  | .leaf c, env => [(c, env)]
  | .split i m l r, env =>
    l.leaves (env.set i ⟨(env.getD i zeroK).lo, m⟩) ++ r.leaves (env.set i ⟨m, (env.getD i zeroK).hi⟩)

theorem TopC.sound [ExtTbl] (fe : FExpr) (g : KI → Bool) :
    ∀ (t : TopC) (env : List KI), t.midsOK = true →
      AllP (fun p => checkC2 fe g p.1 p.2 = true) (t.leaves env) →
      checkC2 fe g t.toCert env = true := by
  intro t
  induction t with
  | leaf c =>
    intro env _ h
    exact h.1
  | split i m l r ihl ihr =>
    intro env hm h
    simp only [TopC.midsOK, Bool.and_eq_true] at hm
    simp only [TopC.leaves] at h
    rw [AllP_append] at h
    simp only [TopC.toCert, checkC2, hm.1.1.1, hm.1.1.2, ihl _ hm.1.2 h.1, ihr _ hm.2 h.2,
      Bool.and_self]

end ManyBox
