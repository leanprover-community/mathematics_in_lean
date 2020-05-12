.. _the_natural_numbers:

The Natural Numbers
===================

Mathematically speaking, the natural numbers are characterized up to isomorphism as
a set with a zero element and an injective successor function
such that zero is not a successor and the entire structure
satisfies the *induction principle*:
any property that holds of zero and is maintained
by successors holds of every natural number.
To introduce the natural numbers formally,
Lean's core library makes use of Lean's foundational framework,
which allows us to declare a new type as follows:

.. code-block:: lean

    namespace my_nat

    -- BEGIN
    inductive nat : Type
    | zero : nat
    | succ : nat → nat
    -- END

    end my_nat

This declares a type ``nat`` with constants
``nat.zero : nat`` and ``nat.succ : nat → nat``,
and provides the associated principles of induction and recursion.

In this chapter, we will explain how the Lean library
establishes the familiar properties of arithmetic on this foundation,
and then we will show you how to use the natural numbers
to prove some interesting theorems.


Defining Arithmetic
-------------------

The principle of recursive definition means that,
once we introduce notation ``ℕ`` for ``nat`` and ``0`` for ``nat.zero``,
and once we open the ``nat`` namespace so that we can write ``succ``
instead of ``nat.succ``,
we can define addition recursively as follows:

.. code-block:: lean

    open nat

    namespace my_nat

    -- BEGIN
    def add : ℕ → ℕ → ℕ
    | m 0 := m
    | m (succ n) := succ (add m n)
    -- END

    end my_nat

Once we introduce the usual notation for addition,
the definition means that we can use the associated
defining equations:

.. code-block:: lean

    open nat

    variables m n : ℕ

    -- BEGIN
    #check (add_zero m   : m + 0 = m)
    #check (add_succ m n : m + (succ n) = succ (m + n))
    -- END

But the computational nature of Lean's foundation gives us more,
namely, that Lean will carry out these reductions
internally in order to make expressions match,
so the equations hold by the reflexivity axiom:

.. code-block:: lean

    open nat

    variables m n : ℕ

    -- BEGIN
    example : m + 0 = m := rfl
    example : m + (succ n) = succ (m + n) := rfl
    -- END

Here, ``rfl`` is a proof term that corresponds to the ``refl`` tactic.
Numerals are also defined in a clever way in Lean so that,
for example, ``1`` reduces to ``succ 0``.
This means in many contexts we can use ``n + 1`` and ``succ n``
interchangeably:

.. code-block:: lean

    open nat

    variable n : ℕ

    -- BEGIN
    example : succ n = n + 1 := rfl
    -- END

Suppose we want to prove the commutativity of addition, ``m + n = n + m``.
We don't have much to work with: we have the defining equations for
addition, but no other facts about it.
But we do have the principle of induction,
which we can invoke with the ``induction`` tactic:

.. code-block:: lean

    variables m n : ℕ

    namespace my_nat

    -- BEGIN
    theorem add_comm : m + n = n + m :=
    begin
      induction n,
      { sorry },
      sorry
    end
    -- END

    end my_nat

In this section, we will continue the strategy of
stating theorems with the same names that are used in the library
but hiding them in a namespace to avoid a naming conflict.
If you move your cursor through the proof,
you will see that the induction tactic leaves two goals:
in the base case, we need to prove ``m + 0 = 0 + m``,
and in the induction step,
we need to prove ``m + succ n = succ n + m``
using the inductive hypothesis ``m + n = n + m``.
You will also see that Lean chose names automatically
for the inductive hypothesis and the variable in the induction step.
We can tell Lean to use ``n`` for the variable name and ``ih``
for the name of the inductive hypothesis by appending ``with n ih``
to the induction command.

How can we prove the base case?
It turns out that this requires another instance of induction.
We could call the induction tactic again in that subproof,
but since the fact that we need, ``0 + m = m``,
is independently useful, we may as well make it a separate theorem.
Similarly, in the inductive hypothesis, we need ``succ m + n = succ (m + n)``,
so we break that out as a separate theorem as well.

.. code-block:: lean

    open nat

    variables m n : ℕ

    namespace my_nat

    -- BEGIN
    theorem zero_add : 0 + m = m :=
    begin
      induction m with m ih,
      { refl },
      rw [add_succ, ih]
    end

    theorem succ_add : succ m + n = succ (m + n) :=
    begin
      induction n with n ih,
      { refl },
      rw [add_succ, ih]
    end

    theorem add_comm : m + n = n + m :=
    begin
      induction n with n ih,
      { rw zero_add, refl },
      rw [succ_add, ←ih]
    end
    -- END

    end my_nat

We can similarly make quick work of associativity:

.. code-block:: lean

    open nat

    variables m n k : ℕ

    namespace my_nat

    -- BEGIN
    theorem add_assoc : m + n + k = m + (n + k) :=
    begin
      induction k with k ih,
      { refl },
      rw [add_succ, ih],
      refl
    end
    -- END

    end my_nat

Because addition is defined by recursion on the second argument,
doing induction on ``k`` will allow us to use the defining equations
for addition in the base case and induction step.
This is a good heuristic when it comes to deciding which variable to use.
We can do on to define multiplication in the expected way:

.. code-block:: lean

    namespace my_nat

    -- BEGIN
    def mul : ℕ → ℕ → ℕ
    | m 0     := 0
    | m (n+1) := mul m n + m
    -- END

    end my_nat

This gives us the defining equations for multiplication:

.. code-block:: lean

    open nat

    variables m n : ℕ

    -- BEGIN
    #check (mul_zero m   : m * 0 = 0)
    #check (mul_succ m n : m * (succ n) = m * n + m)

    example : m * 0 = 0 := rfl
    example : m * (n + 1) = m * n + m := rfl
    -- END

We now challenge you to use nothing more than these defining equations
and the properties of addition we have already established
to prove all of the following:

.. code-block:: lean

    open nat

    variables m n k : ℕ

    namespace my_nat

    -- BEGIN
    theorem mul_add : m * (n + k) = m * n + m * k := sorry

    theorem zero_mul : 0 * n = 0 := sorry

    theorem one_mul : 1 * n = n := sorry

    theorem mul_assoc : m * n * k = m * (n * k) := sorry

    theorem mul_comm : m * n= n * m := sorry
    -- END

    end my_nat

.. exponentiation
.. warning with power
.. cancelation with induction
.. predecessor
.. subtraction
.. less-than or equal,
.. less-than.

.. #. Formalize as many of the identities from :numref:`arithmetic_on_the_natural_numbers` as you can by replacing each `sorry` with a proof.

.. .. code-block:: lean

..     --2.a.
..     example : ∀ m n k : nat, n ≤ m → n + k ≤ m  + k := sorry

..     --2.b.
..     example : ∀ m n k : nat, n + k ≤ m + k → n ≤ m := sorry

..     --2.c.
..     example : ∀ m n k : nat, n ≤ m → n * k ≤ m * k := sorry

..     --2.d.
..     example : ∀ m n : nat, m ≥ n → m = n ∨ m ≥ n+1 := sorry

..     --2.e.
..     example : ∀ n : nat, 0 ≤ n := sorry


Using the Natural Numbers
-------------------------

.. under the hood

.. remark: evaluate.

The command ``#eval`` cannot be used to prove theorems:
Lean extracts bytecode from the definitions and executes them efficiently,
without justifying the computation axiomatically.
But it can be enjoyable to define a function,
prove things about it, and then see it run.
It is also sometimes helpful to get a sense of
what the function does.

But how can we prove ``2 + 2 = 4``?

.. simplifier (as for all the library tactics, including the induction tactic).
   TPiL

Sums and Products
-----------------



Fibonacci Numbers
-----------------

[Watch this space.]


The AM-GM Inequality
--------------------

[Watch this space.]
