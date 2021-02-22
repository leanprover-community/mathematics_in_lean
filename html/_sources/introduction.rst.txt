.. _introduction:

Introduction
============

Getting Started
---------------

So, you are ready to formalize some mathematics.
Maybe you have heard that formalization is the future
(say, from the article `The Mechanization of Mathematics`_,
or the talk `The Future of Mathematics`_),
and you want in.
Maybe you have played the `Natural Number Game`_ and you are hooked.
Maybe you have heard about `Lean`_ and its library `mathlib`_
through online chatter and you want to know what the fuss is about.
Or maybe you like mathematics and you like computers,
and you have some time to spare.
If you are in any of these situations, this book is for you.

Although you can read a pdf or html version of this book online,
it designed to be read interactively,
running Lean from inside the VS Code editor.
To get started:

#. Install Lean, VS Code, and mathlib following the instructions
   in the `community website`_.

#. In a terminal, type ``leanproject get mathematics_in_lean``
   to set up a working directory for this tutorial.

#. Type ``code mathematics_in_lean`` to open that directory in
   ``VS Code``.

Opening the file ``welcome.lean`` will simultaneously open this
tutorial in a VS Code window.

.. Update this when we have a procedure.
   To update to a newer version of
   the tutorial, type ``git pull && leanproject get-mathlib-cache``
   inside the ``mathematics_in_lean`` folder.

Every once in a while, you will see a code snippet like this:

.. code-block:: lean

    #eval "Hello, World!"

Clicking on the ``try it!`` button in the upper right corner will
open a copy in a window
so that you can edit it,
and Lean provides feedback in the ``Lean Goal`` window.
This book provides lots of challenging exercises for you to do that
way.

.. TODO: delete this, or update it

.. You can save your changes from VS Code in the usual way, and come back to the
.. same file by pressing the corresponding ``try it!`` button again.

.. If you want to reset the snippet or exercise to the version in the book,
.. simply delete or rename the file with the changes you have made,
.. and then press ``try it!`` once again.

.. Sometimes in the text we will quote from a longer example, like so:

.. .. code-block:: lean

..     -- Give an example here
..     -- Instead of a ``try it!'' button,
..     -- there should be a ``see more!`` button.

.. In that case, clicking on the ``see more!`` button opens a longer Lean file
.. and takes you to that line.
.. These displays are read only,
.. and you should think of them as part of the main text.
.. This allows us to describe a long development one piece at a time,
.. leaving you free to survey the whole development as you please.

.. Of course, you can create other Lean files to experiment.
.. We have therefore set up the main folder with four subdirectories:

.. * `snippets` contains your edited copies of the snippets in the text.

.. * `exercises` contains your edited copies of the exercises.

.. * `examples` contains the read-only examples we make use of in the text.

.. * `user` is a folder for you use any way you please.

Overview
--------

Put simply, Lean is a tool for building complex expressions in a formal language
known as *dependent type theory*.

.. index:: check, commands ; check

Every expression has a *type*, and you can use the `#check` command to
print it.
Some expressions have types like `ℕ` or `ℕ → ℕ`.
These are mathematical objects.

.. code-block:: lean

    #check 2 + 2

    def f (x : ℕ) := x + 3

    #check f

Some expressions have type `Prop`.
These are mathematical statements.

.. code-block:: lean

    import data.nat.basic

    #check 2 + 2 = 4

    def fermat_last_theorem :=
      ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x^n + y^n ≠ z^n

    #check fermat_last_theorem

Some expressions have a type, `P`, where `P` itself has type `Prop`.
Such an expression is a proof of the proposition `P`.

.. code-block:: lean

    import data.nat.basic

    def fermat_last_theorem :=
      ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x^n + y^n ≠ z^n

    -- BEGIN
    theorem easy : 2 + 2 = 4 := rfl

    #check easy

    theorem hard : fermat_last_theorem := sorry

    #check hard
    -- END

If you manage to construct an expression of type `fermat_last_theorem` and
Lean accepts it as a term of that type,
you have done something very impressive.
(Using ``sorry`` is cheating, and Lean knows it.)
So now you know the game.
All that is left to learn are the rules.

This book is complementary to a companion tutorial, `Theorem Proving in Lean`_,
which provides a more thorough introduction to the underlying logical framework
and core syntax of Lean.
*Theorem Proving in Lean* is for people who prefer to read a user manual cover to cover before
using a new dishwasher.
If you are the kind of person who prefers to hit the *start* button and
figure out how to activate the potscrubber feature later,
it makes more sense to start here and refer back to
*Theorem Proving in Lean* as necessary.

Another thing that distinguishes *Mathematics in Lean* from
*Theorem Proving in Lean* is that here we place a much greater
emphasis on the use of *tactics*.
Given that were are trying to build complex expressions,
Lean offers two ways of going about it:
we can write down the expressions themselves
(that is, suitable text descriptions thereof),
or we can provide Lean with *instructions* as to how to construct them.
For example, the following expression represents a proof of the fact that
if ``n`` is even then so is ``m * n``:

.. code-block:: lean

    import data.nat.parity
    open nat

    example : ∀ m n : nat, even n → even (m * n) :=
    assume m n ⟨k, (hk : n = 2 * k)⟩,
    have hmn : m * n = 2 * (m * k),
      by rw [hk, mul_left_comm],
    show ∃ l, m * n = 2 * l,
      from ⟨_, hmn⟩

The *proof term* can be compressed to a single line:

.. code-block:: lean

    import data.nat.parity
    open nat

    -- BEGIN
    example : ∀ m n : nat, even n → even (m * n) :=
    λ m n ⟨k, hk⟩, ⟨m * k, by rw [hk, mul_left_comm]⟩
    -- END

The following is, instead, a *tactic-style* proof of the same theorem:

.. code-block:: lean

    import data.nat.parity tactic
    open nat

    example : ∀ m n : nat, even n → even (m * n) :=
    begin
      -- say m and n are natural numbers, and assume n=2*k
      rintros m n ⟨k, hk⟩,
      -- We need to prove m*n is twice a natural. Let's show it's twice m*k.
      use m * k,
      -- substitute in for n
      rw hk,
      -- and now it's obvious
      ring
    end

As you enter each line of such a proof in VS Code,
Lean displays the *proof state* in a separate window,
telling you what facts you have already established and what
tasks remain to prove your theorem.
You can replay the proof by stepping through the lines,
since Lean will continue to show you the state of the proof
at the point where the cursor is.
In this example, you will then see that
the first line of the proof introduces ``m`` and ``n``
(we could have renamed them at that point, if we wanted to),
and also decomposes the hypothesis ``even n`` to
a ``k`` and the assumption that ``n = 2 * k``.
The second line, ``use m * k``,
declares that we are going to show that ``m * n`` is even by
showing ``m * n = 2 * (m * k)``.
The next line uses the ``rewrite`` tactic
to replace ``n`` by ``2 * k`` in the goal,
and the `ring` tactic solves the resulting goal ``m * (2 * k) = 2 * (m * k)``.

The ability to build a proof in small steps with incremental feedback
is extremely powerful. For that reason,
tactic proofs are often easier and quicker to write than
proof terms.
There isn't a sharp distinction between the two:
tactic proofs can be inserted in proof terms,
as we did with the phrase ``by rw [hk, mul_left_comm]`` in the example above.
We will also see that, conversely,
it is often useful to insert a short proof term in the middle of a tactic proof.
That said, in this book, our emphasis will be on the use of tactics.

In our example, the tactic proof can also be reduced to a one-liner:

.. code-block:: lean

    import data.nat.parity tactic
    open nat

    -- BEGIN
    example : ∀ m n : nat, even n → even (m * n) :=
    by { rintros m n ⟨k, hk⟩, use m * k, rw hk, ring }
    -- END

Here were have used tactics to carry out small proof steps.
But they can also provide substantial automation,
and justify longer calculations and bigger inferential steps.
For example, we can invoke Lean's simplifier with
specific rules for simplifying statements about parity to
prove our theorem automatically.

.. code-block:: lean

    import data.nat.parity tactic
    open nat

    -- BEGIN
    example : ∀ m n : nat, even n → even (m * n) :=
    by intros; simp * with parity_simps
    -- END

Another big difference between the two introductions is that
*Theorem Proving in Lean* depends only on core Lean and its built-in
tactics, whereas *Mathematics in Lean* is built on top of Lean's
powerful and ever-growing library, *mathlib*.
As a result, we can show you how to use some of the mathematical
objects and theorems in the library,
and some of the very useful tactics.
This book is not meant to be used as an overview of the library;
the community_ web pages contain extensive documentation.
Rather, our goal is to introduce you to the style of thinking that
underlies that formalization,
so that you are comfortable browsing the library and
finding things on your own.

Interactive theorem proving can be frustrating,
and the learning curve is steep.
But the Lean community is very welcoming to newcomers,
and people are available on the `Lean Zulip chat group`_ round the clock
to answer questions.
We hope to see you there, and have no doubt that
soon enough you, too, will be able to answer such questions
and contribute to the development of *mathlib*.

So here is your mission, should you choose to accept it:
dive in, try the exercises, come to Zulip with questions, and have fun.
But be forewarned:
interactive theorem proving will challenge you to think about
mathematics and mathematical reasoning in fundamentally new ways.
Your life may never be the same.

*Acknowledgments.* We are grateful to Gabriel Ebner for setting up the
infrastructure for running this tutorial in VS Code.
We are also grateful for help from
Bryan Gin-ge Chen, Johan Commelin, Julian Külshammer, and Guilherme Silva.

.. _`The Mechanization of Mathematics`: https://www.ams.org/journals/notices/201806/rnoti-p681.pdf
.. _`The Future of Mathematics`: https://www.youtube.com/watch?v=Dp-mQ3HxgDE
.. _Lean: https://leanprover.github.io/people/
.. _mathlib: https://leanprover-community.github.io/
.. _community: https://leanprover-community.github.io/
.. _`Natural Number Game`: https://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/
.. _`community website`: https://leanprover-community.github.io/
.. _`Theorem Proving in Lean`: https://leanprover.github.io/theorem_proving_in_lean/
.. _`Lean Zulip chat group`: https://leanprover.zulipchat.com/
