import Mathlib.Tactic

namespace MyListSpace

inductive List (α : Type*) where
  | nil  : List α
  | cons : α → List α → List α

end MyListSpace

namespace MyListSpace2

def append {α : Type*} : List α → List α → List α
  | [],      bs => bs
  | a :: as, bs => a :: (append as bs)

def map {α β : Type*} (f : α → β) : List α → List β
  | []      => []
  | a :: as => f a :: map f as

#eval append [1, 2, 3] [4, 5, 6]
#eval map (fun n => n^2) [1, 2, 3, 4, 5]

theorem nil_append {α : Type*} (as : List α) : append [] as = as := rfl

theorem cons_append {α : Type*} (a : α) (as : List α) (bs : List α) :
    append (a :: as) bs = a :: (append as bs) := rfl

theorem map_nil {α β : Type*} (f : α → β) : map f [] = [] := rfl

theorem map_cons {α β : Type*} (f : α → β) (a : α) (as : List α) :
    map f (a :: as) = f a :: map f as := rfl

end MyListSpace2

namespace MyListSpace3

variable {α β γ : Type*}
variable (as bs cs : List α)
variable (a b c : α)

open List

theorem append_nil : ∀ as : List α, as ++ [] = as
  | [] => rfl
  | a :: as => by rw [cons_append, append_nil as]

theorem map_map (f : α → β) (g : β → γ) :
    ∀ as : List α, map g (map f as) = map (g ∘ f) as
  | [] => rfl
  | a :: as => by rw [map_cons, map_cons, map_cons, map_map f g as]; rfl

theorem append_nil' : as ++ [] = as := by
  induction' as with a as ih
  . rfl
  . rw [cons_append, ih]

theorem map_map' (f : α → β) (g : β → γ) (as : List α) :
    map g (map f as) = map (g ∘ f) as := by
  induction' as with a as ih
  . rfl
  . simp [map, ih]

def reverse : List α → List α := sorry

theorem reverse_append (as bs : List α) : reverse (as ++ bs) = reverse bs ++ reverse as := by
  sorry

theorem reverse_reverse (as : List α) : reverse (reverse as) = as := by sorry

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

theorem size_le : ∀ t : BinTree, size t ≤ 2^depth t - 1
  | empty    => Nat.zero_le _
  | node l r => by
    simp only [depth, size]
    calc l.size + r.size + 1
      ≤ (2^l.depth - 1) + (2^r.depth - 1) + 1 := by
          gcongr <;> apply size_le
    _ ≤ (2 ^ max l.depth r.depth - 1) + (2 ^ max l.depth r.depth - 1) + 1 := by
          gcongr <;> simp
    _ ≤ 2 ^ (max l.depth r.depth + 1) - 1 := by
          have : 0 < 2 ^ max l.depth r.depth := by simp
          omega

theorem depth_le_size : ∀ t : BinTree, depth t ≤ size t := by sorry

def flip : BinTree → BinTree := sorry

example: flip  (node (node empty (node empty empty)) (node empty empty)) =
    node (node empty empty) (node (node empty empty) empty) := sorry

theorem size_flip : ∀ t, size (flip t) = size t := by sorry
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

theorem eval_eq_eval : ∀ (A : PropForm) (v1 v2 : ℕ → Bool),
    (∀ n ∈ A.vars, v1 n = v2 n) → A.eval v1 = A.eval v2
  | var n, v1, v2, h    => by simp_all [vars, eval, h]
  | fls, v1, v2, h      => by simp_all [eval]
  | conj A B, v1, v2, h => by
      simp_all [vars, eval, eval_eq_eval A v1 v2, eval_eq_eval B v1 v2]
  | disj A B, v1, v2, h => by
      simp_all [vars, eval, eval_eq_eval A v1 v2, eval_eq_eval B v1 v2]
  | impl A B, v1, v2, h => by
      simp_all [vars, eval, eval_eq_eval A v1 v2, eval_eq_eval B v1 v2]

theorem eval_eq_eval' (A : PropForm) (v1 v2 : ℕ → Bool) (h : ∀ n ∈ A.vars, v1 n = v2 n) :
    A.eval v1 = A.eval v2 := by
  cases A <;> simp_all [eval, vars, fun A => eval_eq_eval' A v1 v2]

def subst : PropForm → ℕ → PropForm → PropForm
  | var n,    m, C => if n = m then C else var n
  | fls,      _, _ => fls
  | conj A B, m, C => conj (A.subst m C) (B.subst m C)
  | disj A B, m, C => disj (A.subst m C) (B.subst m C)
  | impl A B, m, C => impl (A.subst m C) (B.subst m C)

theorem subst_eq_of_not_mem_vars :
    ∀ (A : PropForm) (n : ℕ) (C : PropForm), n ∉ A.vars → A.subst n C = A := sorry

theorem subst_eval_eq : ∀ (A : PropForm) (n : ℕ) (C : PropForm) (v : ℕ → Bool),
  (A.subst n C).eval v = A.eval (fun m => if m = n then C.eval v else v m) := sorry

end PropForm
