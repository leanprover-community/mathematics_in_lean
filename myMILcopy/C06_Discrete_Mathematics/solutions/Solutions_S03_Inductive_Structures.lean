import Mathlib.Tactic

namespace MyListSpace3

variable {α β γ : Type*}
variable (as bs cs : List α)
variable (a b c : α)

open List

def reverse : List α → List α
  | []      => []
  | a :: as => reverse as ++ [a]

theorem reverse_append (as bs : List α) : reverse (as ++ bs) = reverse bs ++ reverse as := by
  induction' as with a as ih
  . rw [nil_append, reverse, append_nil]
  rw [cons_append, reverse, ih, reverse, append_assoc]

theorem reverse_reverse (as : List α) : reverse (reverse as) = as := by
  induction' as with a as ih
  . rfl
  rw [reverse, reverse_append, ih, reverse, reverse, nil_append, cons_append, nil_append]

end MyListSpace3

inductive BinTree where
  | empty : BinTree
  | node  : BinTree → BinTree → BinTree

namespace BinTree

def size : BinTree → ℕ
  | empty    => 0
  | node l r => size l + size r + 1

def depth : BinTree → ℕ
  | empty    => 0
  | node l r => max (depth l) (depth r) + 1

theorem depth_le_size : ∀ t : BinTree, depth t ≤ size t
  | BinTree.empty => Nat.zero_le _
  | BinTree.node l r => by
    simp only [depth, size, add_le_add_iff_right, max_le_iff]
    constructor
    . apply le_add_right
      apply depth_le_size
    . apply le_add_left
      apply depth_le_size

def flip : BinTree → BinTree
  | empty => empty
  | node l r => node (flip r) (flip l)

example: flip  (node (node empty (node empty empty)) (node empty empty)) =
    node (node empty empty) (node (node empty empty) empty) := rfl

theorem size_flip : ∀ t, size (flip t) = size t
  | empty => rfl
  | node l r => by
      dsimp [size, flip]
      rw [size_flip l, size_flip r]; omega

end BinTree

inductive PropForm : Type where
  | var (n : ℕ)           : PropForm
  | fls                   : PropForm
  | conj (A B : PropForm) : PropForm
  | disj (A B : PropForm) : PropForm
  | impl (A B : PropForm) : PropForm
namespace PropForm

def eval : PropForm → (ℕ → Bool) → Bool
  | var n,    v => v n
  | fls,      _ => false
  | conj A B, v => A.eval v && B.eval v
  | disj A B, v => A.eval v || B.eval v
  | impl A B, v => ! A.eval v || B.eval v

def vars : PropForm → Finset ℕ
  | var n    => {n}
  | fls      => ∅
  | conj A B => A.vars ∪ B.vars
  | disj A B => A.vars ∪ B.vars
  | impl A B => A.vars ∪ B.vars

def subst : PropForm → ℕ → PropForm → PropForm
  | var n,    m, C => if n = m then C else var n
  | fls,      _, _ => fls
  | conj A B, m, C => conj (A.subst m C) (B.subst m C)
  | disj A B, m, C => disj (A.subst m C) (B.subst m C)
  | impl A B, m, C => impl (A.subst m C) (B.subst m C)

theorem subst_eq_of_not_mem_vars :
    ∀ (A : PropForm) (n : ℕ) (C : PropForm), n ∉ A.vars → A.subst n C = A
  | var m, n, C, h => by simp_all [subst, vars]; tauto
  | fls, n, C, _ => by rw [subst]
  | conj A B, n, C, h => by
    simp_all [subst, vars, subst_eq_of_not_mem_vars A, subst_eq_of_not_mem_vars B]
  | disj A B, n, C, h => by
    simp_all [subst, vars, subst_eq_of_not_mem_vars A, subst_eq_of_not_mem_vars B]
  | impl A B, n, C, h => by
    simp_all [subst, vars, subst_eq_of_not_mem_vars A, subst_eq_of_not_mem_vars B]

-- alternative proof:
theorem subst_eq_of_not_mem_vars' (A : PropForm) (n : ℕ) (C : PropForm):
    n ∉ A.vars → A.subst n C = A := by
  cases A <;> simp_all [subst, vars, subst_eq_of_not_mem_vars']; tauto

theorem subst_eval_eq : ∀ (A : PropForm) (n : ℕ) (C : PropForm) (v : ℕ → Bool),
  (A.subst n C).eval v = A.eval (fun m => if m = n then C.eval v else v m)
  | var m, n, C, v => by
    simp [subst, eval]
    split <;> simp [eval]
  | fls, n, C, v => by
    simp [subst, eval]
  | conj A B, n, C, v => by
    simp [subst, eval, subst_eval_eq A n C v, subst_eval_eq B n C v]
  | disj A B, n, C, v => by
    simp [subst, eval, subst_eval_eq A n C v, subst_eval_eq B n C v]
  | impl A B, n, C, v => by
    simp [subst, eval, subst_eval_eq A n C v, subst_eval_eq B n C v]

-- alternative proof:
theorem subst_eval_eq' (A : PropForm) (n : ℕ) (C : PropForm) (v : ℕ → Bool) :
    (A.subst n C).eval v = A.eval (fun m => if m = n then C.eval v else v m) := by
  cases A <;> simp [subst, eval, subst_eval_eq'];
    split <;> simp_all [eval]

end PropForm
