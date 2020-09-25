.. _basics:

Basics
======

This chapter is designed to introduce you to the nuts and
bolts of mathematical reasoning in Lean: calculating,
applying lemmas and theorems,
and reasoning about generic structures.


.. _calculating:

Calculating
-----------

We generally learn to carry out mathematical calculations
without thinking of them as proofs.
But when we justify each step in a calculation,
as Lean requires us to do,
the net result is a proof that the left-hand side of the calculation
is equal to the right-hand side.

.. index:: rewrite, rw, tactics ; rw and rewrite

In Lean, stating a theorem is tantamount to stating a goal,
namely, the goal of proving the theorem.
Lean provides the ``rewrite`` tactic, abbreviated ``rw``,
to replace the left-hand side of an identity by the right-hand side
in the goal. If ``a``, ``b``, and ``c`` are real numbers,
``mul_assoc a b c``  is the identity ``a * b * c = a * (b * c)``
and ``mul_comm a b`` is the identity ``a * b = b * a``.
Lean provides automation that generally eliminates the need
to refer the facts like these explicitly,
but they are useful for the purposes of illustration.
In Lean, multiplication associates to the left,
so the left-hand side of ``mul_assoc`` could also be written ``(a * b) * c``.
However, it is generally good style to be mindful of Lean's
notational conventions and leave out parentheses when Lean does as well.

Let's try out ``rw``.

.. index:: real numbers

.. code-block:: lean

    import data.real.basic

    example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
    begin
      rw mul_comm a b,
      rw mul_assoc b a c
    end

The ``import`` line at the beginning of the example
imports the theory of the real numbers from ``mathlib``.
For the sake of brevity,
we generally suppress information like this when it
is repeated from example to example.
Clicking the ``try it!`` button displays the full
example as it is meant to be processed and checked by Lean.

You are welcome to make changes to see what happens.
You can type the ``ℝ`` character as ``\R`` or ``\real``
in VS Code.
The symbol doesn't appear until you hit space or the tab key.
If you hover over a symbol when reading a Lean file,
VS Code will show you the syntax that can be used to enter it.
If your keyboard does not have an easily accessible backslash,
you can change the leading character by changing the
``lean.input.leader`` setting.

.. index:: proof state, local context, goal

When a cursor is in the middle of a tactic proof,
Lean reports on the current *proof state* in the
*Lean infoview* window.
As you move your cursor past each step of the proof,
you can see the state change.
A typical proof state in Lean might look as follows:

.. code-block::

    1 goal
    x y : ℕ,
    h₁ : prime x,
    h₂ : ¬even x,
    h₃ : y > x
    ⊢ y ≥ 4

The lines before the one that begins with ``⊢`` denote the *context*:
they are the objects and assumptions currently at play.
In this example, these include two objects, ``x`` and ``y``,
each a natural number.
They also include three assumptions,
labelled ``h₁``, ``h₂``, and ``h₃``.
In Lean, everything in a context is labelled with an identifier.
You can type these subscripted labels as ``h\1``, ``h\2``, and ``h\3``,
but any legal identifiers would do:
you can use ``h1``, ``h2``, ``h3`` instead,
or ``foo``, ``bar``, and ``baz``.
The last line represents the *goal*,
that is, the fact to be proved.
Sometimes people use *target* for the fact to be proved,
and *goal* for the combination of the context and the target.
In practice, the intended meaning is usually clear.

Try proving these identities,
in each case replacing ``sorry`` by a tactic proof.
With the ``rw`` tactic, you can use a left arrow (``\l``)
to reverse an identity.
For example, ``rw ← mul_assoc a b c``
replaces ``a * (b * c)`` by ``a * b * c`` in the current goal.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (a b c : ℝ) : (c * b) * a = b * (a * c) :=
    begin
      sorry
    end

    example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
    begin
      sorry
    end
    -- END

You can also use identities like ``mul_assoc`` and ``mul_comm`` without arguments.
In this case, the rewrite tactic tries to match the left-hand side with
an expression in the goal,
using the first pattern it finds.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (a b c : ℝ) : a * b * c = b * c * a :=
    begin
      rw mul_assoc,
      rw mul_comm
    end
    -- END

You can also provide *partial* information.
For example, ``mul_comm a`` matches any pattern of the form
``a * ?`` and rewrites it to ``? * a``.
Try doing the first of these examples without
providing any arguments at all,
and the second with only one argument.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (a b c : ℝ) : a * (b * c) = b * (c * a) :=
    begin
      sorry
    end

    example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
    begin
      sorry
    end
    -- END

You an also use ``rw`` with facts from the local context.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
      a * (b * e) = c * (d * f) :=
    begin
      rw h',
      rw ←mul_assoc,
      rw h,
      rw mul_assoc
    end
    -- END

Try these:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (a b c d e f : ℝ) (h : b * c = e * f) :
      a * b * c * d = a * e * f * d :=
    begin
      sorry
    end

    example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 :=
    begin
      sorry
    end
    -- END

For the second one, you can use the theorem ``sub_self``,
where ``sub_self a`` is the identity ``a - a = 0``.

We now introduce some useful features of Lean.
First, multiple rewrite commands can be carried out
with a single command,
by listing the relevant identities within square brackets.
Second, when a tactic proof is just a single command,
we can replace the ``begin ... end`` block with a ``by``.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
      a * (b * e) = c * (d * f) :=
    by rw [h', ←mul_assoc, h, mul_assoc]
    -- END

You still see the incremental progress by placing the cursor after
a comma in any list of rewrites.

Another trick is that we can declare variables once and for all outside
an example or theorem.
When Lean sees them mentioned in the statement of the theorem,
it includes them automatically.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    variables a b c d e f g : ℝ

    example (h : a * b = c * d) (h' : e = f) :
      a * (b * e) = c * (d * f) :=
    by rw [h', ←mul_assoc, h, mul_assoc]
    -- END

Inspection of the tactic state at the beginning of the above proof
reveals that Lean indeed included the relevant variables, leaving out
`g` that doesn't feature in the statement.
We can delimit the scope of the declaration by putting it
in a ``section ... end`` block.
Finally, recall from the introduction that Lean provides us with a
command to determine the type of an expression:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    section
    variables a b c : ℝ

    #check a
    #check a + b
    #check (a : ℝ)
    #check mul_comm a b
    #check (mul_comm a b : a * b = b * a)
    #check mul_assoc c a b
    #check mul_comm a
    #check mul_comm
    #check @mul_comm

    end
    -- END

The ``#check`` command works for both objects and facts.
In response to the command ``#check a``, Lean reports that ``a`` has type ``ℝ``.
In response to the command ``#check mul_comm a b``,
Lean reports that ``mul_comm a b`` is a proof of the fact ``a * b = b * a``.
The command ``#check (a : ℝ)`` states our expectation that the
type of ``a`` is ``ℝ``,
and Lean will raise an error if that is not the case.
We will explain the output of the last three ``#check`` commands later,
but in the meanwhile, you can take a look at them,
and experiment with some ``#check`` commands of your own.

Let's try some more examples. The theorem ``two_mul a`` says
that ``a + a = 2 * a``. The theorems ``add_mul`` and ``mul_add``
express the distributivity of multiplication over addition,
and the theorem ``add_assoc`` expresses the associativity of addition.
Use the ``#check`` command to see the precise statements.

.. code-block:: lean

    import data.real.basic

    variables a b : ℝ

    -- BEGIN
    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    begin
      rw [mul_add, add_mul, add_mul],
      rw [←add_assoc, add_assoc (a * a)],
      rw [mul_comm b a, ←two_mul]
    end
    -- END

.. index:: calc, tactics ; calc

Whereas it is possible to figure out what it going on in this proof
by stepping through it in the editor,
it is hard to read on its own.
Lean provides a more structured way of writing proofs like this
using the ``calc`` keyword.

.. code-block:: lean

    import data.real.basic

    variables a b : ℝ

    -- BEGIN
    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    calc
      (a + b) * (a + b)
          = a * a + b * a + (a * b + b * b) :
              by rw [mul_add, add_mul, add_mul]
      ... = a * a + (b * a + a * b) + b * b :
              by rw [←add_assoc, add_assoc (a * a)]
      ... = a * a + 2 * (a * b) + b * b     :
              by rw [mul_comm b a, ←two_mul]
    -- END

Notice that there is no more ``begin ... end`` block:
an expression that begins with ``calc`` is a *proof term*.
A ``calc`` expression can also be used inside a tactic proof,
but Lean interprets it as the instruction to use the resulting
proof term to solve the goal.

The ``calc`` syntax is finicky: the dots and colons and justification
have to be in the format indicated above.
Lean ignores whitespace like spaces, tabs, and returns,
so you have some flexibility to make the calculation look more attractive.
One way to write a ``calc`` proof is to outline it first
using the ``sorry`` tactic for justification,
make sure Lean accepts the expression modulo these,
and then justify the individual steps using tactics.

.. code-block:: lean

    import data.real.basic

    variables a b : ℝ

    -- BEGIN
    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    calc
      (a + b) * (a + b)
          = a * a + b * a + (a * b + b * b) :
        begin
          sorry
        end
      ... = a * a + (b * a + a * b) + b * b : by sorry
      ... = a * a + 2 * (a * b) + b * b     : by sorry
    -- END

Try proving the following identity using both a pure ``rw`` proof
and a more structured ``calc`` proof:

.. code-block:: lean

    import data.real.basic

    variables a b c d : ℝ

    -- BEGIN
    example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
    sorry
    -- END

The following exercise is a little more challenging.
You can use the theorems listed underneath.

.. code-block:: lean

    import data.real.basic

    variables a b c d : ℝ

    -- BEGIN
    example (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 :=
    begin
      sorry
    end

    #check pow_two a
    #check mul_sub a b c
    #check add_mul a b c
    #check add_sub a b c
    #check sub_sub a b c
    #check add_zero a
    -- END

.. index:: rw, tactics ; rw and rewrite

We can also perform rewriting in an assumption in the context.
For example, ``rw mul_comm a b at hyp`` replaces ``a * b`` by ``b * a``
in the assumption ``hyp``.

.. code-block:: lean

    import data.real.basic

    variables a b c d : ℝ

    -- BEGIN
    example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) :
      c = 2 * a * d :=
    begin
      rw hyp' at hyp,
      rw mul_comm d a at hyp,
      rw ← two_mul (a * d) at hyp,
      rw ← mul_assoc 2 a d at hyp,
      exact hyp
    end
    -- END

.. index:: exact, tactics ; exact

In the last step, the ``exact`` tactic can use ``hyp`` to solve the goal
because at that point ``hyp`` matches the goal exactly.

.. index:: ring (tactic), tactics ; ring

We close this section by noting that ``mathlib`` provides a
useful bit of automation with a ``ring`` tactic,
which is designed to prove identities in any commutative ring.

.. code-block:: lean

    import data.real.basic

    variables a b c d : ℝ

    -- BEGIN
    example : (c * b) * a = b * (a * c) :=
    by ring

    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    by ring

    example : (a + b) * (a - b) = a^2 - b^2 :=
    by ring

    example (hyp : c = d * a + b) (hyp' : b = a * d) :
      c = 2 * a * d :=
    begin
      rw [hyp, hyp'],
      ring
    end
    -- END

The ``ring`` tactic is imported indirectly when we
import ``data.real.basic``,
but we will see in the next section that it can be used
for calculations on structures other than the real numbers.
It can be imported explicitly with the command
``import tactic``.
We will see there are similar tactics for other common kind of algebraic
structures.


.. _proving_identities_in_algebraic_structures:

Proving Identities in Algebraic Structures
------------------------------------------

.. index:: ring (algebraic structure)

Mathematically, a ring consists of a collection of objects,
:math:`R`, operations :math:`+` :math:`\times`, and constants :math:`0`
and :math:`1`, and an operation :math:`x \mapsto -x` such that:

* :math:`R` with :math:`+` is an *abelian group*, with :math:`0`
  as the additive identity and negation as inverse.
* Multiplication is associative with identity :math:`1`,
  and multiplication distributes over addition.

In Lean, the collection of objects is represented as a *type*, ``R``.
The ring axioms are as follows:

.. code-block:: lean

    import algebra.ring

    variables (R : Type*) [ring R]

    #check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
    #check (add_comm : ∀ a b : R, a + b = b + a)
    #check (zero_add : ∀ a : R, 0 + a = a)
    #check (add_left_neg : ∀ a : R, -a + a = 0)
    #check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
    #check (mul_one : ∀ a : R, a * 1 = a)
    #check (one_mul : ∀ a : R, 1 * a = a)
    #check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
    #check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

You will learn more about the square brackets in the first line later,
but for the time being,
suffice it to say that the declaration gives us a type, ``R``,
and a ring structure on ``R``.
Lean then allows us to use generic ring notation with elements of ``R``,
and to make use of a library of theorems about rings.

The names of some of the theorems should look familiar:
they are exactly the ones we used to calculate with the real numbers
in the last section.
Lean is good not only for proving things about concrete mathematical
structures like the natural numbers and the integers,
but also for proving things about abstract structures,
characterized axiomatically, like rings.
Moreover, Lean supports *generic reasoning* about
both abstract and concrete structures,
and can be trained to recognized appropriate instances.
So any theorem about rings can be applied to concrete rings
like the integers, ``ℤ``, the rational numbers,  ``ℚ``,
and the complex numbers ``ℂ``.
It can also be applied to any instance of an abstract
structure that extends rings,
such as any *ordered ring* or any *field*.

.. index:: commutative ring

Not all important properties of the real numbers hold in an
arbitrary ring, however.
For example, multiplication on the real numbers
is commutative,
but that does not hold in general.
If you have taken a course in linear algebra,
you will recognize that, for every :math:`n`,
the :math:`n` by :math:`n` matrices of real numbers
form a ring in which commutativity usually fails. If we declare ``R`` to be a
*commutative* ring, in fact, all the theorems
in the last section continue to hold when we replace
``ℝ`` by ``R``.

.. code-block:: lean

    import tactic

    variables (R : Type*) [comm_ring R]
    variables a b c d : R

    example : (c * b) * a = b * (a * c) :=
    by ring

    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    by ring

    example : (a + b) * (a - b) = a^2 - b^2 :=
    by ring

    example (hyp : c = d * a + b) (hyp' : b = a * d) :
      c = 2 * a * d :=
    begin
      rw [hyp, hyp'],
      ring
    end

We leave it to you to check that all the other proofs go through unchanged.

The goal of this section is to strengthen the skills
you have developed in the last section
and apply them to reasoning axiomatically about rings.
We will start with the axioms listed above,
and use them to derive other facts.
Most of the facts we prove are already in ``mathlib``.
We will give the versions we prove the same names
to help you learn the contents of the library
as well as the naming conventions.

.. index:: namespace, open, command ; open

Lean provides an organizational mechanism similar
to those used in programming languages:
when a definition or theorem ``foo`` is introduced in a *namespace*
``bar``, its full name is ``bar.foo``.
The command ``open bar`` later *opens* the namespace,
which allows us to use the shorter name ``foo``.
To avoid errors due to name clashes,
in the next example we put our versions of the library
theorems in a new namespace called ``my_ring.``

The next example shows that we do not need ``add_zero`` or ``add_right_neg``
as ring axioms, because they follow from the other axioms.

.. code-block:: lean

    import algebra.ring

    namespace my_ring

    variables {R : Type*} [ring R]

    theorem add_zero (a : R) : a + 0 = a :=
    by rw [add_comm, zero_add]

    theorem add_right_neg (a : R) : a + -a = 0 :=
    by rw [add_comm, add_left_neg]

    end my_ring

    #check @my_ring.add_zero
    #check @add_zero

The net effect is that we can temporarily reprove a theorem in the library,
and then go on using the library version after that.
But don't cheat!
In the exercises that follow, take care to use only the
general facts about rings that we have proved earlier in this section.

(If you are paying careful attention, you may have noticed that we
changed the round brackets in ``(R : Type*)`` for
curly brackets in ``{R : Type*}``.
This declares ``R`` to be an *implicit argument*.
We will explain what this means in a moment,
but don't worry about it in the meanwhile.)

Here is a useful theorem:

.. code-block:: lean

    import algebra.ring

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b :=
    by rw [←add_assoc, add_left_neg, zero_add]
    -- END

    end my_ring

Prove the companion version:

.. code-block:: lean

    import algebra.ring

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem add_neg_cancel_right (a b : R) : (a + b) + -b = a :=
    sorry
    -- END

    end my_ring

Use these to prove the following:

.. code-block:: lean

    import algebra.ring

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
    sorry

    theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c :=
    sorry
    -- END

    end my_ring

With enough planning, you can do each of them with three rewrites.

.. index:: implicit argument

We can now explain the use of the curly braces.
Imagine you are in a situation where you have ``a``, ``b``, and ``c``
in your context,
as well as a hypothesis ``h : a + b = a + c``,
and you would like to draw the conclusion ``b = c``.
In Lean, you can apply a theorem to hypotheses and facts just
the same way that you can apply them to objects,
so you might think that ``add_left_cancel a b c h`` is a
proof of the fact ``b = c``.
But notice that explicitly writing ``a``, ``b``, and ``c``
is redundant, because the hypothesis ``h`` makes it clear that
those are the objects we have in mind.
In this case, typing a few extra characters is not onerous,
but if we wanted to apply ``add_left_cancel`` to more complicated expressions,
writing them would be tedious.
In cases like these,
Lean allows us to mark arguments as *implicit*,
meaning that they are supposed to be left out and inferred by other means,
such as later arguments and hypotheses.
The curly brackets in ``{a b c : R}`` do exactly that.
So, given the statement of the theorem above,
the correct expression is simply ``add_left_cancel h``.

To illustrate, let us show that ``a * 0 = 0``
follows from the ring axioms.

.. code-block:: lean

    import algebra.ring

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem mul_zero (a : R) : a * 0 = 0 :=
    begin
      have h : a * 0 + a * 0 = a * 0 + 0,
      { rw [←mul_add, add_zero, add_zero] },
      rw add_left_cancel h
    end
    -- END

    end my_ring

.. index:: have, tactics ; have

We have used a new trick!
If you step through the proof,
you can see what is going on.
The ``have`` tactic introduces a new goal,
``a * 0 + a * 0 = a * 0 + 0``,
with the same context as the original goal.
In the next line, we could have omitted the curly brackets,
which serve as an inner ``begin ... end`` pair.
Using them promotes a modular style of proof:
the part of the proof inside the brackets establishes the goal
that was introduced by the ``have``.
After that, we are back to proving the original goal,
except a new hypothesis ``h`` has been added:
having proved it, we are now free to use it.
At this point, the goal is exactly the result of ``add_left_cancel h``.
We could equally well have closed the proof with
``apply add_left_cancel h`` or ``exact add_left_cancel h``.

Remember that multiplication is not assumed to be commutative,
so the following theorem also requires some work.

.. code-block:: lean

    import algebra.ring

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem zero_mul (a : R) : 0 * a = 0 :=
    sorry
    -- END

    end my_ring

By now, you should also be able replace each ``sorry`` in the next
exercise with a proof,
still using only facts about rings that we have
established in this section.

.. code-block:: lean

    import algebra.ring

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b :=
    sorry

    theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b :=
    sorry

    theorem neg_zero : (-0 : R) = 0 :=
    begin
      apply neg_eq_of_add_eq_zero,
      rw add_zero
    end

    theorem neg_neg (a : R) : -(-a) = a :=
    sorry
    -- END

    end my_ring

We had to use the annotation ``(-0 : R)`` instead of ``0`` in the third theorem
because without specifying ``R``
it is impossible for Lean to infer which ``0`` we have in mind,
and by default it would be interpreted as a natural number.

In Lean, subtraction in a ring is defined to be
addition of the additive inverse.

.. code-block:: lean

    import algebra.ring

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem sub_eq_add_neg (a b : R) : a - b = a + -b :=
    rfl

    example (a b : R) : a - b = a + -b :=
    by reflexivity
    -- END

    end my_ring

.. index:: rfl, reflexivity, tactics ; refl and reflexivity, definitional equality

The proof term ``rfl`` is short for ``reflexivity``.
Presenting it as a proof of ``a - b = a + -b`` forces Lean
to unfold the definition and recognize both sides as being the same.
The ``reflexivity`` tactic, which can be abbreviated as ``refl``,
does the same.
This is an instance of what is known as a *definitional equality*
in Lean's underlying logic.
This means that not only can one rewrite with ``sub_eq_add_neg``
to replace ``a - b = a + -b``,
but in some contexts you can use the two sides of the equation
interchangeably.
For example, you now have enough information to prove the theorem
``self_sub`` from the last section:

.. code-block:: lean

    import algebra.ring

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    theorem self_sub (a : R) : a - a = 0 :=
    sorry
    -- END

    end my_ring

Extra points if you do it two different ways:
once using ``rw``,
and once using either ``apply`` or ``exact``.

For another example of definitional equality,
Lean knows that ``1 + 1 = 2`` holds in any ring.
With a bit of effort,
you can use that to prove the theorem ``two_mul`` from
the last section:

.. code-block:: lean

    import algebra.ring

    namespace my_ring

    variables {R : Type*} [ring R]

    -- BEGIN
    lemma one_add_one_eq_two : 1 + 1 = (2 : R) :=
    by refl

    theorem two_mul (a : R) : 2 * a = a + a :=
    sorry
    -- END

    end my_ring

.. index:: group (algebraic structure)

We close this section by noting that some of the facts about
addition and negation that we established above do not
need the full strength of the ring axioms, or even
commutativity of addition. The weaker notion of a *group*
can be axiomatized as follows:

.. code-block:: lean

    import algebra.group

    variables (A : Type*) [add_group A]

    #check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
    #check (zero_add : ∀ a : A, 0 + a = a)
    #check (add_left_neg : ∀ a : A, -a + a = 0)

It is conventional to use additive notation when
the group operation is commutative,
and multiplicative notation otherwise.
So Lean defines a multiplicative version as well as the
additive version (and also their abelian variants,
``add_comm_group`` and ``comm_group``).

.. code-block:: lean

    import algebra.group

    -- BEGIN
    variables (G : Type*) [group G]

    #check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
    #check (one_mul : ∀ a : G, 1 * a = a)
    #check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)
    -- END

If you are feeling cocky, try proving the following facts about
groups, using only these axioms.
You will need to prove a number of helper lemmas along the way.
The proofs we have carried out in this section provide some hints.

.. code-block:: lean

    import algebra.group

    -- BEGIN
    variables {G : Type*} [group G]

    #check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
    #check (one_mul : ∀ a : G, 1 * a = a)
    #check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

    namespace my_group

    theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
    sorry

    theorem mul_one (a : G) : a * 1 = a :=
    sorry

    theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a ⁻¹ :=
    sorry

    end my_group
    -- END

.. index:: group (tactic), tactics ; group, tactics ; noncomm_ring, tactics ; abel

Explicitly invoking those lemmas is tedious, so mathlib provides
tactics similar to `ring` in order to cover most uses: `group`
is for non-commutative multiplicative groups, `abel` for abelian
additive groups, and `noncomm_ring` for non-commutative groups.
It may seem odd that the algebraic structures are called
`ring` and `comm_ring` while the tactics are named
`noncomm_ring` and `ring`. This is partly for historical reasons,
but also for the convenience of using a shorter name for the
tactic that deals with commutative rings, since it is used more often.


.. _using_theorems_and_lemmas:

Using Theorems and Lemmas
-------------------------

.. index:: inequalities

Rewriting is great for proving equations,
but what about other sorts of theorems?
For example, how can we prove an inequality,
like the fact that :math:`a + e^b \le a + e^c` holds whenever :math:`b \le c`?
We have already seen that theorems can be applied to arguments and hypotheses,
and that the ``apply`` and ``exact`` tactics can be used to solve goals.
In this section, we will make good use of these tools.

Consider the library theorems ``le_refl`` and ``le_trans``:

.. code-block:: lean

    import data.real.basic

    variables a b c : ℝ

    #check (le_refl : ∀ a : ℝ, a ≤ a)
    #check (le_trans : a ≤ b → b ≤ c → a ≤ c)

As we explain in more detail in  :numref:`implication_and_the_universal_quantifier`,
the implicit parentheses in the statement of ``le_trans``
associate to the right, so it should be interpreted as ``a ≤ b → (b ≤ c → a ≤ c)``.
The library designers have set the arguments to ``le_trans`` implicit,
so that Lean will *not* let you provide them explicitly (unless you
really insist, as we will discuss later).
Rather, it expects to infer them from the context in which they are used.
For example, when hypotheses ``h : a ≤ b`` and  ``h' : b ≤ c``
are in the context,
all the following work:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    variables a b c : ℝ
    variables (h : a ≤ b) (h' : b ≤ c)

    #check (le_refl : ∀ a : real, a ≤ a)
    #check (le_refl a : a ≤ a)
    #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
    #check (le_trans h : b ≤ c → a ≤ c)
    #check (le_trans h h' : a ≤ c)
    -- END

.. index:: apply, tactics ; apply

The ``apply`` tactic takes a proof of a general statement or implication,
tries to match the conclusion with the current goal,
and leaves the hypotheses, if any, as new goals.
If the given proof matches the goal exactly
(modulo *definitional* equality),
you can use the ``exact`` tactic instead of ``apply``.
So, all of these work:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
    begin
      apply le_trans,
      { apply h₀ },
      apply h₁
    end

    example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
    begin
      apply le_trans h₀,
      apply h₁
    end

    example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
    by exact le_trans h₀ h₁

    example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
    le_trans h₀ h₁

    example (x : ℝ) : x ≤ x :=
    by apply le_refl

    example (x : ℝ) : x ≤ x :=
    by exact le_refl x

    example (x : ℝ) : x ≤ x :=
    le_refl x
    -- END

In the first example, applying ``le_trans``
creates two goals,
and we use the curly braces to enclose the proof
of the first one.
In the fourth example and in the last example,
we avoid going into tactic mode entirely:
``le_trans h₀ h₁`` and ``le_refl x`` are the proof terms we need.

Here are a few more library theorems:

.. code-block:: lean

    import data.real.basic

    variables a b c : ℝ

    -- BEGIN
    #check (le_refl  : ∀ a, a ≤ a)
    #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
    #check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
    #check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
    #check (lt_trans : a < b → b < c → a < c)
    -- END

Use them together with ``apply`` and ``exact`` to prove the following:

.. code-block:: lean

    import data.real.basic

    variables a b c : ℝ

    -- BEGIN
    example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
        (h₃ : d < e) :
      a < e :=
    sorry
    -- END

.. index:: linarith, tactics ; linarith

In fact, Lean has a tactic that does this sort of thing automatically:

.. code-block:: lean

    import data.real.basic

    variables a b c d : ℝ

    -- BEGIN
    example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
        (h₃ : d < e) :
      a < e :=
    by linarith
    -- END

The ``linarith`` tactic is designed to handle *linear arithmetic*.

.. code-block:: lean

    import data.real.basic

    variables a b c d : ℝ

    -- BEGIN
    example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) :
      d + a ≤ 5 * b :=
    by linarith
    -- END

In addition to equations and inequalities in the context,
``linarith`` will use additional inequalities that you pass as arguments.
In the next example, ``exp_le_exp.mpr h'`` is a proof of
``exp b ≤ exp c``, as we will explain in a moment.
Notice that, in Lean, we write ``f x`` to denote the application
of a function ``f`` to the argument ``x``,
exactly the same way we write ``h x`` to denote the result of
applying a fact or theorem ``h`` to the argument ``x``.
Parentheses are only needed for compound arguments,
as in ``f (x + y)``. Without the parentheses, ``f x + y``
would be parsed as ``(f x) + y``.

.. code-block:: lean

    import analysis.special_functions.exp_log

    open real

    variables a b c : ℝ

    -- BEGIN
    example (h : 1 ≤ a) (h' : b ≤ c) :
      2 + a + exp b ≤ 3 * a + exp c :=
    by linarith [exp_le_exp.mpr h']
    -- END

.. index:: exponential, logarithm

Here are some more theorems in the library that can be used to establish
inequalities on the real numbers.

.. code-block:: lean

    import analysis.special_functions.exp_log

    open real

    variables  a b c d : ℝ

    #check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
    #check (exp_lt_exp : exp a < exp b ↔ a < b)
    #check (log_le_log : 0 < a → 0 < b → (log a ≤ log b ↔ a ≤ b))
    #check (log_lt_log : 0 < a → a < b → log a < log b)
    #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
    #check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
    #check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
    #check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
    #check (add_pos : 0 < a → 0 < b → 0 < a + b)
    #check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
    #check (exp_pos : ∀ a, 0 < exp a)

Some of the theorems, ``exp_le_exp``, ``exp_lt_exp``, and ``log_le_log``
use a *bi-implication*, which represents the
phrase "if and only if."
(You can type it in VS Code with ``\lr`` of ``\iff``).
We will discuss this connective in greater detail in the next chapter.
Such a theorem can be used with ``rw`` to rewrite a goal to
an equivalent one:

.. code-block:: lean

    import analysis.special_functions.exp_log

    open real

    -- BEGIN
    example (a b : ℝ) (h : a ≤ b) : exp a ≤ exp b :=
    begin
      rw exp_le_exp,
      exact h
    end
    -- END

In this section, however, we will use the fact that if ``h : A ↔ B``
is such an equivalence,
then ``h.mp`` establishes the forward direction, ``A → B``,
and ``h.mpr`` establishes the reverse direction, ``B → A``.
Here, ``mp`` stands for "modus ponens" and
``mpr`` stands for "modus ponens reverse."
You can also use ``h.1`` and ``h.2`` for ``h.mp`` and ``h.mpr``,
respectively, if you prefer.
Thus the following proof works:

.. code-block:: lean

    import analysis.special_functions.exp_log

    open real

    variables a b c d e : ℝ

    -- BEGIN
    example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e :=
    begin
      apply add_lt_add_of_lt_of_le,
      { apply add_lt_add_of_le_of_lt h₀,
        apply exp_lt_exp.mpr h₁ },
      apply le_refl
    end
    -- END

The first line, ``apply add_lt_add_of_lt_of_le``,
creates two goals,
and once again we use the curly brackets to separate the
proof of the first from the proof of the second.

.. index:: norm_num, tactics ; norm_num

Try the following examples on your own.
The example in the middle shows you that the ``norm_num``
tactic can be used to solve concrete numeric goals.

.. code-block:: lean

    import analysis.special_functions.exp_log

    open real

    variables a b c d e : ℝ

    -- BEGIN
    example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) :=
    begin
      sorry
    end

    example : (0 : ℝ) < 1 :=
    by norm_num

    example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) :=
    begin
      have h₀ : 0 < 1 + exp a,
      { sorry },
      have h₁ : 0 < 1 + exp b,
      { sorry },
      apply (log_le_log h₀ h₁).mpr,
      sorry
    end
    -- END

From these examples, it should be clear that being able to
find the library theorems you need constitutes an important
part of formalization.
There are a number of strategies you can use:

* You can browse mathlib in its
  `GitHub repository <https://github.com/leanprover-community/mathlib>`_.

* You can use the API documentation on the mathlib
  `web pages <https://leanprover-community.github.io/mathlib_docs/>`_.

* You can rely on mathlib naming conventions and tab completion in
  the editor to guess a theorem name.
  In Lean, a theorem named ``A_of_B_of_C`` establishes
  something of the form ``A`` from hypotheses of the form ``B`` and ``C``,
  where ``A``, ``B``, and ``C``
  approximate the way we might read the goals out loud.
  So a theorem establishing something like ``x + y ≤ ...`` will probably
  start with ``add_le``.
  Typing ``add_le`` and hitting tab will give you some helpful choices.

* If you right-click on an existing theorem name in VS Code,
  the editor will show a menu with the option to
  jump to the file where the theorem is defined,
  and you can find similar theorems nearby.

* You can use the ``library_search`` tactic,
  which tries to find the relevant theorem in the library.

.. code-block:: lean

    import data.real.basic
    import tactic

    example (a : ℝ) : 0 ≤ a^2 :=
    begin
      -- library_search,
      exact pow_two_nonneg a
    end

To try out ``library_search`` in this example,
delete the ``exact`` command and uncomment the previous line.
Using these tricks,
see if you can find what you need to do the
next example:

.. code-block:: lean

    import import analysis.special_functions.exp_log
    import tactic

    open real

    variables a b c : ℝ

    -- BEGIN
    example (h : a ≤ b) : c - exp b ≤ c - exp a :=
    begin
      sorry
    end
    -- END

Using the same tricks, confirm that ``linarith`` instead of ``library_search``
can also finish the job.

Here is another example of an inequality:

.. code-block:: lean

    import data.real.basic tactic

    variables a b : ℝ

    -- BEGIN
    example : 2*a*b ≤ a^2 + b^2 :=
    begin
      have h : 0 ≤ a^2 - 2*a*b + b^2,
      calc
        a^2 - 2*a*b + b^2 = (a - b)^2     : by ring
        ... ≥ 0                           : by apply pow_two_nonneg,
      calc
        2*a*b
            = 2*a*b + 0                   : by ring
        ... ≤ 2*a*b + (a^2 - 2*a*b + b^2) : add_le_add (le_refl _) h
        ... = a^2 + b^2                   : by ring
    end
    -- END

Mathlib tends to put spaces around binary operations like ``*`` and ``^``,
but in this example, the more compressed format increases readability.
There are a number of things worth noticing.
First, an expression ``s ≥ t`` is definitionally equivalent to ``t ≤ s``.
In principle, this means one should be able to use them interchangeably.
But some of Lean's automation does not recognize the equivalence,
so mathlib tends to favor ``≤`` over ``≥``.
Second, we have used the ``ring`` tactic extensively.
It is a real timesaver!
Finally, notice that in the second line of the
second ``calc`` proof,
instead of writing ``by exact add_le_add (le_refl _) h``,
we can simply write the proof term ``add_le_add (le_refl _) h``.

In fact, the only cleverness in the proof above is figuring
out the hypothesis ``h``.
Once we have it, the second calculation involves only
linear arithmetic, and ``linarith`` can handle it:

.. code-block:: lean

    import data.real.basic tactic

    variables a b : ℝ

    -- BEGIN
    example : 2*a*b ≤ a^2 + b^2 :=
    begin
      have h : 0 ≤ a^2 - 2*a*b + b^2,
      calc
        a^2 - 2*a*b + b^2 = (a - b)^2 : by ring
        ... ≥ 0                       : by apply pow_two_nonneg,
      linarith
    end
    -- END

How nice! We challenge you to use these ideas to prove the
following theorem. You can use the theorem ``abs_le_of_le_of_neg_le``.

.. code-block:: lean

    import data.real.basic tactic

    variables a b : ℝ

    -- BEGIN
    example : abs (a*b) ≤ (a^2 + b^2) / 2 :=
    sorry

    #check abs_le_of_le_of_neg_le
    -- END

If you managed to solve this, congratulations!
You are well on your way to becoming a master formalizer.


.. more_on_order_and_divisibility:

More on Order and Divisibility
------------------------------

.. index:: min, max

The ``min`` function on the real numbers is uniquely characterized
by the following three facts:

.. code-block:: lean

    import data.real.basic

    variables a b c d : ℝ

    -- BEGIN
    #check (min_le_left a b : min a b ≤ a)
    #check (min_le_right a b : min a b ≤ b)
    #check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
    -- END

Can you guess the names of the theorems that characterize
``max`` in a similar way?

Notice that we have to apply ``min`` to a pair of arguments ``a`` and ``b``
by writing ``min a b`` rather than ``min (a, b)``.
Formally, ``min`` is a function of type ``ℝ → ℝ → ℝ``.
When we write a type like this with multiple arrows,
the convention is that the implicit parentheses associate
to the right, so the type is interpreted as ``ℝ → (ℝ → ℝ)``.
The net effect is that if ``a`` and ``b`` have type ``ℝ``
then ``min a`` has type ``ℝ → ℝ`` and
``min a b`` has type ``ℝ``, so ``min`` acts like a function
of two arguments, as we expect. Handling multiple
arguments in this way is known as *currying*,
after the logician Haskell Curry.

The order of operations in Lean can also take some getting used to.
Function application binds tighter than infix operations, so the
expression ``min a b + c`` is interpreted as ``(min a b) + c``.
With time, these conventions will become second nature.

Using the theorem ``le_antisymm``, we can show that two
real numbers are equal if each is less than or equal to the other.
Using this and the facts above,
we can show that ``min`` is commutative:

.. code-block:: lean

    import data.real.basic

    variables a b : ℝ

    -- BEGIN
    example : min a b = min b a :=
    begin
      apply le_antisymm,
      { show min a b ≤ min b a,
        apply le_min,
        { apply min_le_right },
        apply min_le_left },
      { show min b a ≤ min a b,
        apply le_min,
        { apply min_le_right },
        apply min_le_left }
    end
    -- END

.. index:: show, tactics ; show

Here we have used curly brackets to separate proofs of
different goals.
Our usage is inconsistent:
at the outer level,
we use curly brackets and indentation for both goals,
whereas for the nested proofs,
we use curly brackets only until a single goal remains.
Both conventions are reasonable and useful.
We also use the ``show`` tactic to structure
the proof
and indicate what is being proved in each block.
The proof still works without the ``show`` commands,
but using them makes the proof easier to read and maintain.

It may bother you that the the proof is repetitive.
To foreshadow skills you will learn later on,
we note that one way to avoid the repetition
is to state a local lemma and then use it:

.. code-block:: lean

    import data.real.basic

    variables a b : ℝ

    -- BEGIN
    example : min a b = min b a :=
    begin
      have h : ∀ x y, min x y ≤ min y x,
      { intros x y,
        apply le_min,
        apply min_le_right,
        apply min_le_left },
      apply le_antisymm, apply h, apply h
    end
    -- END

We will say more about the universal quantifier in
:numref:`implication_and_the_universal_quantifier`,
but suffice it to say here that the hypothesis
``h`` says that the desired inequality holds for
any ``x`` and ``y``,
and the ``intros`` tactic introduces an arbitrary
``x`` and ``y`` to establish the conclusion.
The first ``apply`` after ``le_antisymm`` implicitly
uses ``h a b``, whereas the second one uses ``h b a``.

.. index:: repeat, tactics ; repeat

Another solution is to use the ``repeat`` tactic,
which applies a tactic (or a block) as many times
as it can.

.. code-block:: lean

    import data.real.basic

    variables a b : ℝ

    -- BEGIN
    example : min a b = min b a :=
    begin
      apply le_antisymm,
      repeat {
        apply le_min,
        apply min_le_right,
        apply min_le_left }
    end
    -- END

In any case,
whether or not you use these tricks,
we encourage you to prove the following:

.. code-block:: lean

    import data.real.basic

    variables a b c : ℝ

    -- BEGIN
    example : max a b = max b a :=
    begin
      sorry
    end

    example : min (min a b) c = min a (min b c) :=
    sorry
    -- END

Of course, you are welcome to prove the associativity of ``max`` as well.

It is an interesting fact that ``min`` distributes over ``max``
the way that multiplication distributes over addition,
and vice-versa.
In other words, on the real numbers, we have the identity
``min a (max b c) ≤ max (min a b) (min a c)``
as well as the corresponding version with ``max`` and ``min``
switched.
But in the next section we will see that this does *not* follow
from the transitivity and reflexivity of ``≤`` and
the characterizing properties of ``min`` and ``max`` enumerated above.
We need to use the fact that ``≤`` on the real numbers is a *total order*,
which is to say,
it satisfies ``∀ x y, x ≤ y ∨ y ≤ x``.
Here the disjunction symbol, ``∨``, represents "or".
In the first case, we have ``min x y = x``,
and in the second case, we have ``min x y = y``.
We will learn how to reason by cases in :numref:`disjunction`,
but for now we will stick to examples that don't require the case split.

Here is one such example:

.. code-block:: lean

    import data.real.basic

    variables a b c : ℝ

    -- BEGIN
    lemma aux : min a b + c ≤ min (a + c) (b + c) :=
    begin
      sorry
    end

    example : min a b + c = min (a + c) (b + c) :=
    begin
      sorry
    end
    -- END

It is clear that ``aux`` provides one of the two inequalities
needed to prove the equality,
but applying it to suitable values yields the other direction
as well.
As a hint, you can use the theorem ``add_neg_cancel_right``
and the ``linarith`` tactic.

.. index:: absolute value

Lean's naming convention is made manifest
in the library's name for the triangle inequality:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    #check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)
    -- END

Use it to prove the following variant:

.. code-block:: lean

    import data.real.basic

    variables a b : ℝ

    -- BEGIN
    example : abs a - abs b ≤ abs (a - b) :=
    begin
      sorry
    end
    -- END

See if you can do this in three lines or less.
You can use the theorem ``sub_add_cancel``.

.. index:: divisibility

Another important relation that we will make use of
in the sections to come is the divisibility relation
on the natural numbers, ``x ∣ y``.
Be careful: the divisibility symbol is *not* the
ordinary bar on your keyboard.
Rather, it is a unicode character obtained by
typing ``\|`` in VS Code.
By convention, mathlib uses ``dvd``
to refer to it in theorem names.

.. code-block:: lean

    import data.nat.gcd

    variables x y z : ℕ

    example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
    dvd_trans h₀ h₁

    example : x ∣ y * x * z :=
    begin
      apply dvd_mul_of_dvd_left,
      apply dvd_mul_left
    end

    example : x ∣ x^2 :=
    by apply dvd_mul_right

In the last example, the exponent is a natural
number, and applying ``dvd_mul_right``
forces Lean to expand the definition of ``x^2`` to 
``x^1 * x``.
See if you can guess the names of the theorems
you need to prove the following:

.. code-block:: lean

    import data.nat.gcd

    variables w x y z : ℕ

    example (h : x ∣ w) : x ∣ y * (x * z) + x^2 + w^2 :=
    begin
      sorry
    end

.. index:: gcd, lcm

With respect to divisibility, the *greatest common divisor*,
``gcd``, and least common multiple, ``lcm``,
are analogous to ``min`` and ``max``.
Since every number divides ``0``,
``0`` is really the greatest element with respect to divisibility:

.. code-block:: lean

    import data.nat.gcd

    open nat

    variables n : ℕ

    #check (gcd_zero_right n : gcd n 0 = n)
    #check (gcd_zero_left n  : gcd 0 n = n)
    #check (lcm_zero_right n : lcm n 0 = 0)
    #check (lcm_zero_left n  : lcm 0 n = 0)

The functions ``gcd`` and ``lcm`` for natural numbers are in the
``nat`` namespace,
which means that the full identifiers are ``nat.gcd`` and ``nat.lcm``.
Similarly, the names of the theorems listed are prefixed by ``nat``.
The command ``open nat`` opens the namespace,
allowing us to use the shorter names.

See if you can guess the names of the theorems you will need to
prove the following:

.. code-block:: lean

    import data.nat.gcd

    open nat

    variables m n : ℕ

    -- BEGIN
    example : gcd m n = gcd n m :=
    begin
      sorry
    end
    -- END


.. _proving_facts_about_algebraic_structures:

Proving Facts about Algebraic Structures
----------------------------------------

.. index:: order relation, partial order

In :numref:`proving_identities_in_algebraic_structures`,
we saw that many common identities governing the real numbers hold
in more general classes of algebraic structures,
such as commutative rings.
We can use any axioms we want to describe an algebraic structure,
not just equations.
For example, a *partial order* consists of a set with a
binary relation that is reflexive and transitive,
like ``≤`` on the real numbers.
Lean knows about partial orders:

.. code-block:: lean

    variables {α : Type*} [partial_order α]
    variables x y z : α

    #check x ≤ y
    #check (le_refl x : x ≤ x)
    #check (le_trans : x ≤ y → y ≤ z → x ≤ z)

Here we are adopting the mathlib convention of using
letters like ``α``, ``β``, and ``γ``
(entered as ``\a``, ``\b``, and ``\g``)
for arbitrary types.
The library often uses letters like ``R`` and ``G``
for the carries of algebraic structures like rings and groups,
respectively,
but in general Greek letters are used for types,
especially when there is little or no structure
associated with them.

Associated to any partial order, ``≤``,
there is also a *strict partial order*, ``<``,
which acts somewhat like ``<`` on the real numbers.
Saying that ``x`` is less than ``y`` in this order
is equivalent to saying that it is less-than-or-equal to ``y``
and not equal to ``y``.

.. code-block:: lean

    import order.basic

    variables {α : Type*} [partial_order α]
    variables x y z : α

    -- BEGIN
    #check x < y
    #check (lt_irrefl x : ¬ x < x)
    #check (lt_trans : x < y → y < z → x < z)
    #check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
    #check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

    example : x < y ↔ x ≤ y ∧ x ≠ y :=
    lt_iff_le_and_ne
    -- END

In this example, the symbol ``∧`` stands for "and,"
the symbol ``¬`` stands for "not," and
``x ≠ y`` abbreviates ``¬ (x = y)``.
In :numref:`Chapter %s <logic>`, you will learn how to use
these logical connectives to *prove* that ``<``
has the properties indicated.

.. index:: lattice

A *lattice* is a structure that extends a partial
order with operations ``⊓`` and ``⊔`` that are
analogous to ``min`` and ``max`` on the real numbers:

.. code-block:: lean

    import order.lattice

    variables {α : Type*} [lattice α]
    variables x y z : α

    #check x ⊓ y
    #check (inf_le_left : x ⊓ y ≤ x)
    #check (inf_le_right : x ⊓ y ≤ y)
    #check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)

    #check x ⊔ y
    #check (le_sup_left : x ≤ x ⊔ y)
    #check (le_sup_right: y ≤ x ⊔ y)
    #check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

The characterizations of ``⊓`` and ``⊔`` justify calling them
the *greatest lower bound* and *least upper bound*, respectively.
You can type them in VS code using ``\glb`` and ``\lub``.
The symbols are also often called then *infimum* and
the *supremum*,
and mathlib refers to them as ``inf`` and ``sup`` in
theorem names.
To further complicate matters,
they are also often called *meet* and *join*.
Therefore, if you work with lattices,
you have to keep the following dictionary in mind:

* ``⊓`` is the *greatest lower bound*, *infimum*, or *meet*.

* ``⊔`` is the *least upper bound*, *supremum*, or *join*.

Some instances of lattices include:

* ``min`` and ``max`` on any total order, such as the integers or real numbers with ``≤``

* ``∩`` and ``∪`` on the collection of subsets of some domain, with the ordering ``⊆``

* ``∧`` and ``∨`` on boolean truth values, with ordering ``x ≤ y`` if either ``x`` is false or ``y`` is true

* ``gcd`` and ``lcm`` on the natural numbers (or positive natural numbers), with the divisibility ordering, ``∣``

* the collection of linear subspaces of a vector space,
  where the greatest lower bound is given by the intersection,
  the least upper bound is given by the sum of the two spaces,
  and the ordering is inclusion

* the collection of topologies on a set (or, in Lean, a type),
  where the greatest lower bound of two topologies consists of
  the topology that is generated by their union,
  the least upper bound is their intersection,
  and the ordering is reverse inclusion

You can check that, as with ``min`` / ``max`` and ``gcd`` / ``lcm``,
you can prove the commutativity and associativity of the infimum and supremum
using only their characterizing axioms,
together with ``le_refl`` and ``le_trans``.

.. code-block:: lean

    import order.lattice

    variables {α : Type*} [lattice α]
    variables x y z : α

    -- BEGIN
    example : x ⊓ y = y ⊓ x := sorry
    example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := sorry
    example : x ⊔ y = y ⊔ x := sorry
    example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := sorry
    -- END

You can find these theorems in the mathlib as ``inf_comm``, ``inf_assoc``,
``sup_comm``, and ``sup_assoc``, respectively.

Another good exercise is to prove the *absorption laws*
using only those axioms:

.. code-block:: lean

    import order.lattice

    variables {α : Type*} [lattice α]
    variables x y z : α

    -- BEGIN
    example : x ⊓ (x ⊔ y) = x := sorry
    example : x ⊔ (x ⊓ y) = x := sorry
    -- END

These can be found in mathlib with the names ``inf_sup_self`` and ``sup_inf_self``.

A lattice that satisfies the additional identities
``x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)`` and
``x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)``
is called a *distributive lattice*. Lean knows about these too:

.. code-block:: lean

    import order.lattice

    variables {α : Type*} [distrib_lattice α]
    variables x y z : α

    #check (inf_sup_left : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
    #check (inf_sup_right : (x ⊔ y) ⊓ z = (x ⊓ z) ⊔ (y ⊓ z))
    #check (sup_inf_left : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
    #check (sup_inf_right : (x ⊓ y) ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))

The left and right versions are easily shown to be
equivalent, given the commutativity of ``⊓`` and ``⊔``.
It is a good exercise to show that not every lattice
is distributive
by providing an explicit description of a
nondistributive lattice with finitely many elements.
It is also a good exercise to show that in any lattice,
either distributivity law implies the other:

.. code-block:: lean

    import order.lattice

    variables {α : Type*} [lattice α]
    variables a b c : α

    example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) :
      (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) :=
    sorry

    example (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :
      (a ⊓ b) ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
    sorry

It is possible to combine axiomatic structures into larger ones.
For example, an *ordered ring* consists of a ring together with a
partial order on the carrier
satisfying additional axioms that say that the ring operations
are compatible with the order:

.. code-block:: lean

    import algebra.ordered_ring

    variables {R : Type*} [ordered_ring R]
    variables a b c : R

    #check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
    #check (mul_pos : 0 < a → 0 < b → 0 < a * b)
    #check (zero_ne_one : (0 : R) ≠ 1)

:numref:`Chapter %s <logic>` will provide the means to derive the following from ``mul_pos``
and the definition of ``<``:

.. code-block:: lean

    import algebra.ordered_ring

    variables {R : Type*} [ordered_ring R]
    variables a b c : R

    -- BEGIN
    #check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
    -- END

It is then an extended exercise to show that many common facts
used to reason about arithmetic and the ordering on the real
numbers hold generically for any ordered ring.
Here are a couple of examples you can try,
using only properties of rings, partial orders, and the facts
enumerated in the last two examples:

.. code-block:: lean

    import algebra.ordered_ring

    variables {R : Type*} [ordered_ring R]
    variables a b c : R

    -- BEGIN
    example : a ≤ b → 0 ≤ b - a := sorry

    example : 0 ≤ b - a → a ≤ b := sorry

    example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := sorry
    -- END

.. index:: metric space

Finally, here is one last example.
A *metric space* consists of a set equipped with a notion of
distance, ``dist x y``,
mapping any pair of elements to a real number.
The distance function is assumed to satisfy the following axioms:

.. code-block:: lean

    import topology.metric_space.basic

    variables {X : Type*} [metric_space X]
    variables x y z : X

    #check (dist_self x : dist x x = 0)
    #check (dist_comm x y : dist x y = dist y x)
    #check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

Having mastered this section,
you can show that it follows from these axioms that distances are
always nonnegative:

.. code-block:: lean

    import topology.metric_space.basic

    variables {X : Type*} [metric_space X]

    -- BEGIN
    example (x y : X) : 0 ≤ dist x y := sorry
    -- END

We recommend making use of the theorem ``nonneg_of_mul_nonneg_left``.
As you may have guessed, this theorem is called ``dist_nonneg`` in mathlib.
