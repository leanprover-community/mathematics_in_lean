.. _logic:

Logic
=====

In the last chapter, we dealt with equations, inequalities,
and basic mathematical statements like
":math:`x` divides :math:`y`."
Complex mathematical statements are built up from
simple ones like these
using logical terms like "and," "or," "not," and
"if ... then," "every," and "some."
In this chapter, we show you how to work with statements
that are built up in this way.


.. _implication_and_the_universal_quantifier:

Implication and the Universal Quantifier
----------------------------------------

Consider the statement after the ``#check``:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    #check ∀ x : ℝ, 0 ≤ x → abs x = x
    -- END

In words, we would say "for every real number ``x``, if ``0 ≤ x`` then
the absolute value of ``x`` equals ``x``".
We can also have more complicated statements like:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    #check ∀ x y ε : ℝ,
      0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε
    -- END

In words, we would say "for every ``x``, ``y``, and ``ε``,
if ``0 < ε ≤ 1``, the absolute value of ``x`` is less than ``ε``,
and the absolute value of ``y`` is less than ``ε``,
then the absolute value of ``x * y`` is less than ``ε``."
In Lean, in a sequence of implications there are
implicit parentheses grouped to the right.
So the expression above means
"if ``0 < ε`` then if ``ε ≤ 1`` then if ``abs x < ε`` ..."
As a result, the expression says that all the
assumptions together imply the conclusion.

You have already seen that even though the universal quantifier
in this statement
ranges over objects and the implication arrows introduce hypotheses,
Lean treats the two in very similar ways.
In particular, if you have proved a theorem of that form,
you can apply it to objects and hypotheses in the same way:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    lemma my_lemma : ∀ x y ε : ℝ,
      0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
    sorry

    section
      variables a b δ : ℝ
      variables (h₀ : 0 < δ) (h₁ : δ ≤ 1)
      variables (ha : abs a < δ) (hb : abs b < δ)

      #check my_lemma a b δ
      #check my_lemma a b δ h₀ h₁
      #check my_lemma a b δ h₀ h₁ ha hb
    end
    -- END

You have also already seen that it is common in Lean
to use curly brackets to make quantified variables implicit
when they can be inferred from subsequent hypotheses.
When we do that, we can just apply a lemma to the hypotheses without
mentioning the objects.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    lemma my_lemma : ∀ {x y ε : ℝ},
      0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
    sorry

    section
      variables a b δ : ℝ
      variables (h₀ : 0 < δ) (h₁ : δ ≤ 1)
      variables (ha : abs a < δ) (hb : abs b < δ)

      #check my_lemma h₀ h₁ ha hb
    end
    -- END

At this stage, you also know that if you use
the ``apply`` tactic to apply ``my_lemma``
to a goal of the form ``abs (a * b) < δ``,
you are left with new goals that require you to  prove
each of the hypotheses.

.. index:: intros, tactics ; intros

To prove a statement like this, use the ``intros`` tactic.
Take a look at what it does in this example:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    lemma my_lemma : ∀ {x y ε : ℝ},
      0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
    begin
      intros x y ε epos ele1 xlt ylt,
      sorry
    end
    -- END

We can use any names we want for the universally quantified variables;
they do not have to be ``x``, ``y``, and ``ε``.
Notice that we have to introduce the variables
even though they are marked implicit:
making them implicit means that we leave them out when
we write an expression *using* ``my_lemma``,
but they are still an essential part of the statement
that we are proving.
After the ``intros`` command,
the goal is what it would have been at the start if we
listed all the variables and hypotheses *before* the colon,
as we did in the last section.
In a moment, we will see why it is sometimes necessary to
introduce variables and hypotheses after the proof begins.

To help you prove the lemma, we will start you off:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    lemma my_lemma : ∀ {x y ε : ℝ},
      0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
    begin
      intros x y ε epos ele1 xlt ylt,
      calc
        abs (x * y) = abs x * abs y : sorry
        ... ≤ abs x * ε             : sorry
        ... < 1 * ε                 : sorry
        ... = ε                     : sorry
    end
    -- END

.. TODO: delete this eventually, but remember to
   introduce ``suffices`` eventually

.. We have introduced another new tactic here:
   ``suffices`` works like ``have`` in reverse,
   asking you to prove the goal using the
   stated fact,
   and then leaving you the new goal of proving that fact.

Finish the proof using the theorems
``abs_mul``, ``mul_le_mul``, ``abs_nonneg``,
``mul_lt_mul_right``, and ``one_mul``.
Remember that you can find theorems like these using
tab completion.
Remember also that you can use ``.mp`` and ``.mpr``
or ``.1`` and ``.2`` to extract the two directions
of an if-and-only-if statement.

Universal quantifiers are often hidden in definitions,
and Lean will unfold definitions to expose them when necessary.
For example, let's define two predicates,
``fn_ub f a`` and ``fn_lb f a``,
where ``f`` is a function from the real numbers to the real
numbers and ``a`` is a real number.
The first says that ``a`` is an upper bound on the
values of ``f``,
and the second says that ``a`` is a lower bound
on the values of ``f``.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x
    -- END

.. index:: lambda abstraction

In the next example, ``λ x, f x + g x`` is a name for the
function that maps ``x`` to ``f x + g x``.
Computer scientists refer to this as "lambda abstraction,"
whereas a mathematician might describe it as the function
:math:`x \mapsto f(x) + g(x)`.

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

    variables (f g : ℝ → ℝ) (a b : ℝ)

    -- BEGIN
    example (hfa : fn_ub f a) (hgb : fn_ub g b) :
      fn_ub (λ x, f x + g x) (a + b) :=
    begin
      intro x,
      dsimp,
      apply add_le_add,
      apply hfa,
      apply hgb
    end
    -- END

.. index:: dsimp, tactics ; dsimp, change, tactics ; change

Applying ``intro`` to the goal ``fn_ub (λ x, f x + g x) (a + b)``
forces Lean to unfold the definition of ``fn_ub``
and introduce ``x`` for the universal quantifier.
The goal is then ``(λ (x : ℝ), f x + g x) x ≤ a + b``.
But applying ``(λ x, f x + g x)`` to ``x`` should result in ``f x + g x``,
and the ``dsimp`` command performs that simplification.
(The "d" stands for "definitional.")
You can delete that command and the proof still works;
Lean would have to perform that contraction anyhow to make
sense of the next ``apply``.
The ``dsimp`` command simply makes the goal more readable
and helps us figure out what to do next.
Another option is to use the ``change`` tactic
by writing ``change f x + g x ≤ a + b``.
This helps make the proof more readable,
and gives you more control over how the goal is transformed.

The rest of the proof is routine.
The last two ``apply`` commands force Lean to unfold the definitions
of ``fn_ub`` in the hypotheses.
Try carrying out similar proofs of these:

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

    variables (f g : ℝ → ℝ) (a b : ℝ)

    -- BEGIN
    example (hfa : fn_lb f a) (hgb : fn_lb g b) :
      fn_lb (λ x, f x + g x) (a + b) :=
    sorry

    example (nnf : fn_lb f 0) (nng : fn_lb g 0) :
      fn_lb (λ x, f x * g x) 0 :=
    sorry

    example (hfa : fn_ub f a) (hfb : fn_ub g b)
        (nng : fn_lb g 0) (nna : 0 ≤ a) :
      fn_ub (λ x, f x * g x) (a * b) :=
    sorry
    -- END

Even though we have defined ``fn_ub`` and ``fn_lb`` for functions
from the reals to the reals,
you should recognize that the definitions and proofs are much
more general.
The definitions make sense for functions between any two types
for which there is a notion of order on the codomain.
Checking the type of the theorem ``add_le_add`` shows that it holds
of any structure that is an "ordered additive commutative monoid";
the details of what that means don't matter now,
but it is worth knowing that the natural numbers, integers, rationals,
and real numbers are all instances.
So if we prove the theorem ``fn_ub_add`` at that level of generality,
it will apply in all these instances.

.. code-block:: lean

    import algebra.ordered_group

    variables {α : Type*} {R : Type*} [ordered_cancel_add_comm_monoid R]

    #check @add_le_add

    def fn_ub (f : α → R) (a : R) : Prop := ∀ x, f x ≤ a

    theorem fn_ub_add {f g : α → R} {a b : R}
        (hfa : fn_ub f a) (hgb : fn_ub g b) :
      fn_ub (λ x, f x + g x) (a + b) :=
    λ x, add_le_add (hfa x) (hgb x)

You have already seen square brackets like these in
Section :numref:`proving_identities_in_algebraic_structures`,
though we still haven't explained what they mean.
For concreteness, we will stick to the real numbers
for most of our examples,
but it is worth knowing that mathlib contains definitions and theorems
that work at a high level of generality.

.. index:: monotone function

For another example of a hidden universal quantifier,
mathlib defines a predicate ``monotone``,
which says that a function is nondecreasing in its arguments:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (f : ℝ → ℝ) (h : monotone f) :
      ∀ {a b}, a ≤ b → f a ≤ f b := h
    -- END

Proving statements about monotonicity
involves using ``intros`` to introduce two variables,
say, ``a`` and ``b``, and the hypothesis ``a ≤ b``.
To *use* a monotonicity hypothesis,
you can apply it to suitable arguments and hypotheses,
and then apply the resulting expression to the goal.
Or you can apply it to the goal and let Lean help you
work backwards by displaying the remaining hypotheses
as new subgoals.

.. code-block:: lean

    import data.real.basic

    variables (f g : ℝ → ℝ)

    -- BEGIN
    example (mf : monotone f) (mg : monotone g) :
      monotone (λ x, f x + g x) :=
    begin
      intros a b aleb,
      apply add_le_add,
      apply mf aleb,
      apply mg aleb
    end
    -- END

When a proof is this short, it is often convenient
to give a proof term instead.
To describe a proof that temporarily introduces objects
``a`` and ``b`` and a hypothesis ``aleb``,
Lean uses the notation ``λ a b aleb, ...``.
This is analogous to the way that a lambda abstraction
like ``λ x, x^2`` describes a function
by temporarily naming an object, ``x``,
and then using it to describe a value.
So the ``intros`` command in the previous proof
corresponds to the lambda abstraction in the next proof term.
The ``apply`` commands then correspond to building
the application of the theorem to its arguments.

.. code-block:: lean

    import data.real.basic

    variables (f g : ℝ → ℝ)

    -- BEGIN
    example (mf : monotone f) (mg : monotone g) :
      monotone (λ x, f x + g x) :=
    λ a b aleb, add_le_add (mf aleb) (mg aleb)
    -- END

Here is a useful trick: if you start writing
the proof term ``λ a b aleb, _`` using
an underscore where the rest of the
expression should go,
Lean will flag an error,
indicating that it can't guess the value of that expression.
If you check the Lean Goal window in VS Code or
hover over the squiggly error marker,
Lean will show you the goal that the remaining
expression has to solve.

Try proving these, with either tactics or proof terms:

.. code-block:: lean

    import data.real.basic

    variables (f g : ℝ → ℝ)

    -- BEGIN
    example {c : ℝ} (mf : monotone f) (nnc : 0 ≤ c) :
      monotone (λ x, c * f x) :=
    sorry

    example (mf : monotone f) (mg : monotone g) :
      monotone (λ x, f (g x)) :=
    sorry
    -- END

Here are some more examples.
A function :math:`f` from :math:`\Bbb R` to
:math:`\Bbb R` is said to be *even* if
:math:`f(-x) = f(x)` for every :math:`x`,
and *odd* if :math:`f(-x) = -f(x)` for every :math:`x`.
The following example defines these two notions formally
and establishes one fact about them.
You can complete the proofs of the others.

.. code-block:: lean

    import data.real.basic

    variables (f g : ℝ → ℝ)

    -- BEGIN
    def even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
    def odd (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

    example (ef : even f) (eg : even g) : even (λ x, f x + g x) :=
    begin
      intro x,
      calc
        (λ x, f x + g x) x = f x + g x       : rfl
                       ... = f (-x) + g (-x) : by rw [ef, eg]
    end

    example (of : odd f) (og : odd g) : even (λ x, f x * g x) :=
    sorry

    example (ef : even f) (og : odd g) : odd (λ x, f x * g x) :=
    sorry

    example (ef : even f) (og : odd g) : even (λ x, f (g x)) :=
    sorry
    -- END

.. index:: erw, tactics ; erw

The first proof can be shortened using ``dsimp`` or ``change``
to get rid of the lambda.
But you can check that the subsequent ``rw`` won't work
unless we get rid of the lambda explicitly,
because otherwise it cannot find the patterns ``f x`` and ``g x``
in the expression.
Contrary to some other tactics, ``rw`` operates on the syntactic level,
it won't unfold definitions or apply reductions for you
(it has a variant called ``erw`` that tries a little harder in this
direction, but not much harder).

You can find implicit universal quantifiers all over the place,
once you know how to spot them.
Mathlib includes a good library for rudimentary set theory.
Lean's logical foundation imposes the restriction that when
we talk about sets, we are always talking about sets of
elements of some type. If ``x`` has type ``α`` and ``s`` has
type ``set α``, then ``x ∈ s`` is a proposition that
asserts that ``x`` is an element of ``s``.
If ``s`` and ``t`` are of type ``set α``,
then the subset relation ``s ⊆ t`` is defined to mean
``∀ {x : α}, x ∈ s → x ∈ t``.
The variable in the quantifier is marked implicit so that
given ``h : s ⊆ t`` and ``h' : x ∈ s``,
we can write ``h h'`` as justification for ``x ∈ t``.
The following example provides a tactic proof and a proof term
justifying the reflexivity of the subset relation,
and asks you to do the same for transitivity.

.. code-block:: lean

    variables {α : Type*} (r s t : set α)

    example : s ⊆ s :=
    by { intros x xs, exact xs }

    example : s ⊆ s := λ x xs, xs

    example : r ⊆ s → s ⊆ t → r ⊆ t :=
    begin
      sorry
    end

    example : r ⊆ s → s ⊆ t → r ⊆ t :=
    sorry

Just as we defined ``fn_ub`` for functions,
we can define ``set_ub s a`` to mean that ``a``
is an upper bound on the set ``s``,
assuming ``s`` is a set of elements of some type that
has an order associated with it.
In the next example, we ask you to prove that
if ``a`` is a bound on ``s`` and ``a ≤ b``,
then ``b`` is a bound on ``s`` as well.

.. code-block:: lean

    variables {α : Type*} [partial_order α]
    variables (s : set α) (a b : α)

    def set_ub (s : set α) (a : α) := ∀ x, x ∈ s → x ≤ a

    example (h : set_ub s a) (h' : a ≤ b) : set_ub s b :=
    sorry

.. index:: injective function

We close this section with one last important example.
A function :math:`f` is said to be *injective* if for
every :math:`x_1` and :math:`x_2`,
if :math:`f(x_1) = f(x_2)` then :math:`x_1 = x_2`.
Mathlib defines ``function.injective f`` with
``x₁`` and ``x₂`` implicit.
The next example shows that, on the real numbers,
any function that adds a constant is injective.
We then ask you to show that multiplication by a nonzero
constant is also injective.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    open function

    example (c : ℝ) : injective (λ x, x + c) :=
    begin
      intros x₁ x₂ h',
      exact (add_left_inj c).mp h',
    end

    example {c : ℝ} (h : c ≠ 0) : injective (λ x, c * x) :=
    sorry
    -- END

Finally, show that the composition of two injective functions is injective:

.. code-block:: lean

    open function

    -- BEGIN
    variables {α : Type*} {β : Type*} {γ : Type*}
    variables {g : β → γ} {f : α → β}

    example (injg : injective g) (injf : injective f) :
      injective (λ x, g (f x)) :=
    begin
      sorry
    end
    -- END

.. solution:
   intros x₁ x₂ h,
   apply injf,
   apply injg,
   apply h

.. _the_existential_quantifier:

The Existential Quantifier
--------------------------

.. TODO: add section reference for "and"

The existential quantifier, which can be entered as ``\ex`` in VS Code,
is used to represent the phrase "there exists."
The formal expression ``∃ x : ℝ, 2 < x ∧ x < 3`` in Lean says
that there is a real number between 2 and 3.
(We will discuss the conjunction symbol, ``∧``, below.)
The canonical way to prove such a statement is to exhibit a real number
and show that it has the stated property.
The number 2.5, which we can enter as ``5 / 2``
or ``(5 : ℝ) / 2`` when Lean cannot infer from context that we have
the real numbers in mind, has the required property,
and the ``norm_num`` tactic can prove that it meets the description.

.. index:: use, tactics ; use

There are a few ways we can put the information together.
Given a goal that begins with an existential quantifier,
the ``use`` tactic is used to provide the object,
leaving the goal of proving the property.

.. code-block:: lean

    import data.real.basic

    example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
    begin
      use 5 / 2,
      norm_num
    end

.. index:: anonyomous constructor

Alternatively, we can use Lean's *anonyomous constructor* notation
to construct the proof.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
    begin
      have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3,
        by norm_num,
      exact ⟨5 / 2, h⟩
    end
    -- END

The left and right angle brackets,
which can be entered as ``\<`` and ``\>`` respectively,
tell Lean to put together the given data using
whatever construction is appropriate
for the current goal.
We can use the notation without going first into tactic mode:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
    ⟨5 / 2, by norm_num⟩
    -- END

So now we know how to *prove* an exists statement.
But how do we *use* one?
If we know that there exists an object with a certain property,
we should be able to give a name to an arbitrary one
and reason about it.
For example, remember the predicates ``fn_ub f a`` and ``fn_lb f a``
from the last section,
which say that ``a`` is an upper bound or lower bound on ``f``,
respectively.
We can use the existential quantifier to say that "``f`` is bounded"
without specifying the bound:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

    def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
    def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a
    -- END

We can use the theorem ``fn_ub_add`` from the last section
to prove that if ``f`` and ``g`` have upper bounds,
then so does ``λ x, f x + g x``.

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

    def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
    def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

    theorem fn_ub_add {f g : ℝ → ℝ} {a b : ℝ}
        (hfa : fn_ub f a) (hgb : fn_ub g b) :
      fn_ub (λ x, f x + g x) (a + b) :=
    λ x, add_le_add (hfa x) (hgb x)

    variables {f g : ℝ → ℝ}

    -- BEGIN
    example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
      fn_has_ub (λ x, f x + g x) :=
    begin
      cases ubf with a ubfa,
      cases ubg with b ubfb,
      use a + b,
      apply fn_ub_add ubfa ubfb
    end
    -- END

.. index:: cases, tactics ; cases

The ``cases`` tactic unpacks the information
in the existential quantifier.
Given the hypothesis ``ubf`` that there is an upper bound
for ``f``,
``cases`` adds a new variable for an upper
bound to the context,
together with the hypothesis that it has the given property.
The ``with`` clause allows us to specify the names
we want Lean to use.
The goal is left unchanged;
what *has* changed is that we can now use
the new object and the new hypothesis
to prove the goal.
This is a common pattern in mathematics:
we unpack objects whose existence is asserted or implied
by some hypothesis, and then use it to establish the existence
of something else.

Try using this pattern to establish the following.
You might find it useful to turn some of the examples
from the last section into named theorems,
as we did with ``fn_ub_add``,
or you can insert the arguments directly
into the proofs.

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

    def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
    def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

    variables {f g : ℝ → ℝ}

    -- BEGIN
    example (lbf : fn_has_lb f) (lbg : fn_has_lb g) :
      fn_has_lb (λ x, f x + g x) :=
    sorry

    example {c : ℝ} (ubf : fn_has_ub f) (h : c ≥ 0):
      fn_has_ub (λ x, c * f x) :=
    sorry
    -- END

.. index:: rintros, tactics ; rintros, rcases, tactics ; rcases

The task of unpacking information in a hypothesis is
so important that Lean and mathlib provide a number of
ways to do it.
A cousin of the ``cases`` tactic, ``rcases``, is more
flexible in that it allows us to unpack nested data.
(The "r" stands for "recursive.")
In the ``with`` clause for unpacking an existential quantifier,
we name the object and the hypothesis by presenting
them as a pattern ``⟨a, h⟩`` that ``rcases`` then tries to match.
The ``rintro`` tactic (which can also be written ``rintros``)
is a combination of ``intros`` and ``rcases``.
These examples illustrate their use:

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

    def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
    def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

    variables {f g : ℝ → ℝ}

    theorem fn_ub_add {f g : ℝ → ℝ} {a b : ℝ}
        (hfa : fn_ub f a) (hgb : fn_ub g b) :
        fn_ub (λ x, f x + g x) (a + b) :=
    λ x, add_le_add (hfa x) (hgb x)

    -- BEGIN
    example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
      fn_has_ub (λ x, f x + g x) :=
    begin
      rcases ubf with ⟨a, ubfa⟩,
      rcases ubg with ⟨b, ubfb⟩,
      exact ⟨a + b, fn_ub_add ubfa ubfb⟩
    end

    example : fn_has_ub f → fn_has_ub g →
      fn_has_ub (λ x, f x + g x) :=
    begin
      rintros ⟨a, ubfa⟩ ⟨b, ubfb⟩,
      exact ⟨a + b, fn_ub_add ubfa ubfb⟩
    end
    -- END

In fact, Lean also supports a pattern-matching lambda
in expressions and proof terms:

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

    def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
    def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

    variables {f g : ℝ → ℝ}

    theorem fn_ub_add {f g : ℝ → ℝ} {a b : ℝ}
        (hfa : fn_ub f a) (hgb : fn_ub g b) :
        fn_ub (λ x, f x + g x) (a + b) :=
    λ x, add_le_add (hfa x) (hgb x)

    -- BEGIN
    example : fn_has_ub f → fn_has_ub g →
      fn_has_ub (λ x, f x + g x) :=
    λ ⟨a, ubfa⟩ ⟨b, ubfb⟩, ⟨a + b, fn_ub_add ubfa ubfb⟩
    -- END

These are power-user moves, and there is no harm
in favoring the use of ``cases`` until you are more comfortable
with the existential quantifier.
But we will come to learn that all of these tools,
including ``cases``, use, and the anonymous constructors,
are like Swiss army knives when it comes to theorem proving.
They can be used for a wide range of purposes,
not just for unpacking exists statements.

To illustrate one way that ``rcases`` can be used,
we prove an old mathematical chestnut:
if two integers ``x`` and ``y`` can each be written as
a sum of two squares,
then so can their product, ``x * y``.
In fact, the statement is true for any commutative
ring, not just the integers.
In the next example, ``rcases`` unpacks two existential
quantifiers at once.
We then provide the magic values needed to express ``x * y``
as a sum of squares as a list to the ``use`` statement,
and we use ``ring`` to verify that they work.

.. code-block:: lean

    import tactic

    variables {α : Type*} [comm_ring α]

    def sum_of_squares (x : α) := ∃ a b, x = a^2 + b^2

    theorem sum_of_squares_mul {x y : α}
        (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
      sum_of_squares (x * y) :=
    begin
      rcases sosx with ⟨a, b, xeq⟩,
      rcases sosy with ⟨c, d, yeq⟩,
      rw [xeq, yeq],
      use [a*c - b*d, a*d + b*c],
      ring
    end

This proof doesn't provide much insight,
but here is one way to motivate it.
A *Gaussian integer* is a number of the form :math:`a + bi`
where :math:`a` and :math:`b` are integers and :math:`i = \sqrt{-1}`.
The *norm* of the Gaussian integer :math:`a + bi` is, by definition,
:math:`a^2 + b^2`.
So the norm of a Gaussian integer is a sum of squares,
and any sum of squares can be expressed in this way.
The theorem above reflects the fact that norm of a product of
Gaussian integers is the product of their norms:
if :math:`x` is the norm of :math:`a + bi` and
:math:`y` in the norm of :math:`c + di`,
then :math:`xy` is the norm of :math:`(a + bi) (c + di)`.
Our cryptic proof illustrates the fact that
the proof that is easiest to formalize isn't always
the most perspicuous one.
In the chapters to come,
we will provide you with the means to define the Gaussian
integers and use them to provide an alternative proof.

The pattern of unpacking an equation inside a existential quantifier
and then using it to rewrite an expression in the goal
comes up often,
so much so that the ``rcases`` tactic provides
an abbreviation:
if you use the keyword ``rfl`` in place of a new identifier,
``rcases`` does the rewriting automatically (this trick doesn't work
with pattern-matching lambdas).

.. code-block:: lean

    import tactic

    variables {α : Type*} [comm_ring α]

    def sum_of_squares (x : α) := ∃ a b, x = a^2 + b^2

    -- BEGIN
    theorem sum_of_squares_mul {x y : α}
        (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
      sum_of_squares (x * y) :=
    begin
      rcases sosx with ⟨a, b, rfl⟩,
      rcases sosy with ⟨c, d, rfl⟩,
      use [a*c - b*d, a*d + b*c],
      ring
    end
    -- END

As with the universal quantifier,
you can find existential quantifiers hidden all over
if you know how to spot them.
For example, divisibility is implicitly an "exists" statement.

.. code-block:: lean

    import tactic

    variables {a b c : ℕ}

    -- BEGIN
    example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c :=
    begin
      cases divab with d beq,
      cases divbc with e ceq,
      rw [ceq, beq],
      use (d * e), ring
    end
    -- END

And once again, this provides a nice setting for using
``rcases`` with ``rfl``.
Try it out in the proof above.
It feels pretty good!

Then try proving the following:

.. code-block:: lean

    import tactic

    variables {a b c : ℕ}

    -- BEGIN
    example (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
    sorry
    -- END

.. index:: surjective function

For another important example, a function :math:`f : \alpha \to \beta`
is said to be *surjective* if for every :math:`y` in the
codomain, :math:`\beta`,
there is an :math:`x` in the domain, :math:`\alpha`,
such that :math:`f(x) = y`.
Notice that this statement includes both a universal
and an existential quantifier, which explains
why the next example makes use of both ``intro`` and ``use``.

.. code-block:: lean

    import data.real.basic

    open function

    -- BEGIN
    example {c : ℝ} : surjective (λ x, x + c) :=
    begin
      intro x,
      use x - c,
      dsimp, ring
    end
    -- END

Try this example yourself:

.. code-block:: lean

    import data.real.basic

    open function

    -- BEGIN
    example {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
    sorry
    -- END

You can use the theorem ``div_mul_cancel``.
The next example uses a surjectivity hypothesis
by applying it to a suitable value.
Note that you can use ``cases`` with any expression,
not just a hypothesis.

.. code-block:: lean

    import data.real.basic

    open function

    -- BEGIN
    example {f : ℝ → ℝ} (h : surjective f) : ∃ x, (f x)^2 = 4 :=
    begin
      cases h 2 with x hx,
      use x,
      rw hx,
      norm_num
    end
    -- END

See if you can use these methods to show that
the composition of surjective functions is surjective.

.. code-block:: lean

    import tactic

    open function

    variables {α : Type*} {β : Type*} {γ : Type*}
    variables {g : β → γ} {f : α → β}

    -- BEGIN
    example (surjg : surjective g) (surjf : surjective f) :
      surjective (λ x, g (f x)) :=
    sorry
    -- END

.. _negation:

Negation
--------

The symbol ``¬`` is meant to express negation,
so ``¬ x < y`` says that ``x`` is not less than ``y``,
``¬ x = y`` (or, equivalently, ``x ≠ y``) says that
``x`` is not equal to ``y``,
and ``¬ ∃ z, x < z ∧ z < y`` says that there does not exist a ``z``
strictly between ``x`` and ``y``.
In Lean, the notation ``¬ A`` abbreviates ``A → false``,
which you can think of as saying that ``A`` implies a contradiction.
Practically speaking, this means that you already know something
about how to work with negations:
you can prove ``¬ A`` by introducing a hypothesis ``h : A``
and proving ``false``,
and if you have ``h : ¬ A`` and ``h' : A``,
then applying ``h`` to ``h'`` yields ``false``.

To illustrate, consider the irreflexivity principle ``lt_irrefl``
for a strict order,
which says that we have ``¬ a < a`` for every ``a``.
The asymmetry principle ``lt_asymm`` says that we have
``a < b → ¬ b < a``. Let's show that ``lt_asymm`` follows
from ``lt_irrefl``.

.. code-block:: lean

    import data.real.basic

    variables a b : ℝ

    -- BEGIN
    example (h : a < b) : ¬ b < a :=
    begin
      intro h',
      have : a < a,
        from lt_trans h h',
      apply lt_irrefl a this
    end
    -- END

.. index:: this, have, tactics ; have, from, tactics ; from

This example introduces a couple of new tricks.
First, when you use ``have`` without providing
a label,
Lean uses the name ``this``,
providing a convenient way to refer back to it.
Also, the ``from`` tactic is syntactic sugar for ``exact``,
providing a nice way to justify a ``have`` with an explicit
proof term.
But what you should really be paying attention to in this
proof is the result of the ``intro`` tactic,
which leaves a goal of ``false``,
and the fact that we eventually prove ``false``
by applying ``lt_irrefl`` to a proof of ``a < a``.

Here is another example, which uses the
predicate ``fn_has_ub`` defined in the last section,
which says that a function has an upper bound.

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

    def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

    variable f : ℝ → ℝ

    -- BEGIN
    example (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
    begin
      intros fnub,
      cases fnub with a fnuba,
      cases h a with x hx,
      have : f x ≤ a,
        from fnuba x,
      linarith
    end
    -- END

See if you can prove these in a similar way:

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

    def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
    def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

    variable f : ℝ → ℝ

    -- BEGIN
    example (h : ∀ a, ∃ x, f x < a) : ¬ fn_has_lb f :=
    sorry

    example : ¬ fn_has_ub (λ x, x) :=
    sorry
    -- END

Mathlib offers a number of useful theorems for relating orders
and negations:

.. code-block:: lean

    import data.real.basic

    variables a b : ℝ

    -- BEGIN
    #check (not_le_of_gt : a > b → ¬ a ≤ b)
    #check (not_lt_of_ge : a ≥ b → ¬ a < b)
    #check (lt_of_not_ge : ¬ a ≥ b → a < b)
    #check (le_of_not_gt : ¬ a > b → a ≤ b)
    -- END

Recall the predicate ``monotone f``,
which says that ``f`` is nondecreasing.
Use some of the theorems just enumerated to prove the following:

.. code-block:: lean

    import data.real.basic

    variables (f : ℝ → ℝ) (a b : ℝ)

    -- BEGIN
    example (h : monotone f) (h' : f a < f b) : a < b :=
    sorry

    example (h : a ≤ b) (h' : f b < f a) : ¬ monotone f :=
    sorry
    -- END

Remember that it is often convenient to use ``linarith``
when a goal follows from linear equations and
inequalities that in the context.

We can show that the first example in the last snippet
cannot be proved if we replace ``<`` by ``≤``.
Notice that we can prove the negation of a universally
quantified statement by giving a counterexample.
Complete the proof.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example :
      ¬ ∀ {f : ℝ → ℝ}, monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
    begin
      intro h,
      let f := λ x : ℝ, (0 : ℝ),
      have monof : monotone f,
      { sorry },
      have h' : f 1 ≤ f 0,
        from le_refl _,
      sorry
    end
    -- END

.. index:: let, tactics ; let

This example introduces the ``let`` tactic,
which adds a *local definition* to the context.
If you put the cursor after the ``let`` command,
in the goal window you will see that the definition
``f : ℝ → ℝ := λ (x : ℝ), 0`` has been added to the context.
Lean will unfold the definition of ``f`` when it has to.
In particular, when we prove ``f 1 ≤ f 0`` with ``le_refl``,
Lean reduces ``f 1`` and ``f 0`` to ``0``.

Use ``le_of_not_gt`` to prove the following:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 :=
    sorry
    -- END

Implicit in many of the proofs we have just done
is the fact that if ``P`` is any property,
saying that there is nothing with property ``P``
is the same as saying that everything fails to have
property ``P``,
and saying that not everything has property ``P``
is equivalent to saying that something fails to have property ``P``.
In other words, all four of the following implications
are valid (but one of them cannot be proved with what we explained so
far):

.. code-block:: lean

    variables {α : Type*} (P : α → Prop)

    example (h : ¬ ∃ x, P x) : ∀ x, ¬ P x :=
    sorry

    example (h : ∀ x, ¬ P x) : ¬ ∃ x, P x :=
    sorry

    example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
    sorry

    example (h : ∃ x, ¬ P x) : ¬ ∀ x, P x :=
    sorry

The first, second, and fourth are straightforward to
prove using the methods you have already seen.
We encourage you to try it.
The third is more difficult, however,
because it concludes that an object exists
from the fact that its nonexistence is contradictory.
This is an instance of *classical* mathematical reasoning,
and, in general, you have to declare your intention
of using such reasoning by adding the command
``open_locale classical`` to your file.
With that command, we can use proof by contradiction
to prove the third implication as follows.

.. code-block:: lean

    import tactic

    variables {α : Type*} (P : α → Prop)

    open_locale classical

    example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
    begin
      by_contradiction h',
      apply h,
      intro x,
      show P x,
      by_contradiction h'',
      exact h' ⟨x, h''⟩
    end

.. index:: by_contradiction, by_contra, tactics ; by_contra and by_contradiction,

Make sure you understand how this works.
The ``by_contradiction`` tactic (also abbreviated to ``by_contra``)
allows us to prove a goal ``Q`` by assuming ``¬ Q``
and deriving a contradiction.
In fact, it is equivalent to using the
equivalence ``not_not : ¬ ¬ Q ↔ Q``.
Confirm that you can prove the forward direction
of this equivalence using ``by_contradiction``,
while the reverse direction follows from the
ordinary rules for negation.

.. code-block:: lean

    import tactic

    open_locale classical

    variable (Q : Prop)

    -- BEGIN
    example (h : ¬ ¬ Q) : Q :=
    sorry

    example (h : Q) : ¬ ¬ Q :=
    sorry
    -- END

Use proof by contradiction to establish the following,
which is the converse of one of the implications we proved above.
(Hint: use ``intro`` first.)

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

    open_locale classical

    variable (f : ℝ → ℝ)

    -- BEGIN
    example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
    sorry
    -- END

.. index:: push_neg, tactics ; push_neg

It is often tedious to work with compound statements with
a negation in front,
and it is a common mathematical pattern to replace such
statements with equivalent forms in which the negation
has been pushed inward.
To facilitate this, mathlib offers a ``push_neg`` tactic,
which restates the goal in this way.
The command ``push_neg at h`` restates the hypothesis ``h``.

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

    open_locale classical

    variable (f : ℝ → ℝ)

    -- BEGIN
    example (h : ¬ ∀ a, ∃ x, f x > a) : fn_has_ub f :=
    begin
      push_neg at h,
      exact h
    end

    example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
    begin
      simp only [fn_has_ub, fn_ub] at h,
      push_neg at h,
      exact h
    end
    -- END

In the second example, we use Lean's simplifier to
expand the definitions of ``fn_has_ub`` and ``fn_ub``.
(We need to use ``simp`` rather than ``rw``
to expand ``fn_ub``,
because it appears in the scope of a quantifier.)
You can verify that in the examples above
with ``¬ ∃ x, P x`` and ``¬ ∀ x, P x``,
the ``push_neg`` tactic does the expected thing.
Without even knowing how to use the conjunction
symbol,
you should be able to use ``push_neg``
to prove the following:

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

    open_locale classical

    variable (f : ℝ → ℝ)

    -- BEGIN
    example (h : ¬ monotone f) : ∃ x y, x ≤ y ∧ f y < f x :=
    sorry
    -- END

.. index:: contrapose, tactics ; contrapose

Mathlib also has a tactic, ``contrapose``,
which transforms a goal ``A → B`` to ``¬ B → ¬ A``.
Similarly, given a goal of proving ``B`` from
hypothesis ``h : A``,
``contrapose h`` leaves you with a goal of proving
``¬ A`` from hypothesis ``¬ B``.
Using ``contrapose!`` instead of ``contrapose``
applies ``push_neg`` to the goal and the relevant
hypothesis as well.

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

    open_locale classical

    variable (f : ℝ → ℝ)

    -- BEGIN
    example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
    begin
      contrapose! h,
      exact h
    end

    example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 :=
    begin
      contrapose! h,
      use x / 2,
      split; linarith
    end
    -- END

We have not yet explained the ``split`` command
or the use of the semicolon after it,
but we will do that in the next section.

.. TODO: make sure we explain split and the semicolon
   in the next section

We close this section with
the principle of *ex falso*,
which says that anything follows from a contradiction.
In Lean, this is represented by ``false.elim``,
which establishes ``false → P`` for any proposition ``P``.
This may seem like a strange principle,
but it comes up fairly often.
We often prove a theorem by splitting on cases,
and sometimes we can show that one of
the cases is contradictory.
In that case, we need to assert that the contradiction
establishes the goal so we can move on to the next one.
(We will see instances of reasoning by cases in
:numref:`disjunction`.)

.. index:: exfalso, contradiction, absurd, tactics ; exfalso, tactics ; contradiction

Lean provides a number of ways of closing
a goal once a contradiction has been reached.

.. code-block:: lean

    variable a : ℕ

    -- BEGIN
    example (h : 0 < 0) : a > 37 :=
    begin
      exfalso,
      apply lt_irrefl 0 h
    end

    example (h : 0 < 0) : a > 37 :=
    absurd h (lt_irrefl 0)

    example (h : 0 < 0) : a > 37 :=
    begin
      have h' : ¬ 0 < 0,
        from lt_irrefl 0,
      contradiction
    end
    -- END

The ``exfalso`` tactic replaces the current goal with
the goal of proving ``false``.
Given ``h : P`` and ``h' : ¬ P``,
the term ``absurd h h'`` establishes any proposition.
Finally, the ``contradiction`` tactic tries to close a goal
by finding a contradiction in the hypotheses,
such as a pair of the form ``h : P`` and ``h' : ¬ P``.
Of course, in this example, ``linarith`` also works.


.. _conjunction_and_biimplication:

Conjunction and Bi-implication
------------------------------

.. index:: split, tactics ; split

You have already seen that the conjunction symbol, ``∧``,
is used to express "and."
The ``split`` tactic allows you to prove a statement of
the form ``A ∧ B``
by proving ``A`` and then proving ``B``.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
    begin
      split,
      { assumption },
      intro h,
      apply h₁,
      rw h
    end
    -- END

.. index:: assumption, tactics ; assumption

In this example, the ``assumption`` tactic
tells Lean to find an assumption that will solve the goal.
Notice that the final ``rw`` finishes the goal by
applying the reflexivity of ``≤``.
The following are alternative ways of carrying out
the previous examples using the anonymous constructor
angle brackets.
The first is a slick proof-term version of the
previous proof,
which drops into tactic mode at the keyword ``by``.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
    ⟨h₀, λ h, h₁ (by rw h)⟩

    example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
    begin
      have h : x ≠ y,
      { contrapose! h₁,
        rw h₁ },
      exact ⟨h₀, h⟩
    end
    -- END

*Using* a conjunction instead of proving one involves unpacking the proofs of the
two parts.
You can uses the ``cases`` tactic for that,
as well as ``rcases``, ``rintros``, or a pattern-matching lambda,
all in a manner similar to the way they are used with
the existential quantifier.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
    begin
      cases h with h₀ h₁,
      contrapose! h₁,
      exact le_antisymm h₀ h₁
    end

    example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
    begin
      rintros ⟨h₀, h₁⟩ h',
      exact h₁ (le_antisymm h₀ h')
    end

    example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
    λ ⟨h₀, h₁⟩ h', h₁ (le_antisymm h₀ h')
    -- END

In contrast to using an existential quantifier,
you can also extract proofs of the two components
of a hypothesis ``h : A ∧ B``
by writing ``h.left`` and ``h.right``,
or, equivalently, ``h.1`` and ``h.2``.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
    begin
      intro h',
      apply h.right,
      exact le_antisymm h.left h'
    end

    example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
    λ h', h.right (le_antisymm h.left h')
    -- END

Try using these techniques to come up with various ways of proving of the following:

.. code-block:: lean

    import data.nat.gcd

    open nat

    -- BEGIN
    example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) :
      m ∣ n ∧ ¬ n ∣ m :=
    sorry
    -- END

You can nest uses of ``∃`` and ``∧``
with anonymous constructors, ``rintros``, and ``rcases``.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
    ⟨5/2, by norm_num, by norm_num⟩

    example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
    begin
      rintros ⟨z, xltz, zlty⟩,
      exact lt_trans xltz zlty
    end

    example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
    λ ⟨z, xltz, zlty⟩, lt_trans xltz zlty
    -- END

You can also use the ``use`` tactic:

.. code-block:: lean

    import data.real.basic
    import data.nat.gcd

    open nat

    -- BEGIN
    example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
    begin
      use 5 / 2,
      split; norm_num
    end

    example : ∃ m n : ℕ,
      4 < m ∧ m < n ∧ n < 10 ∧ prime m ∧ prime n :=
    begin
      use [5, 7],
      norm_num
    end

    example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
    begin
      rintros ⟨h₀, h₁⟩,
      use [h₀, λ h', h₁ (le_antisymm h₀ h')]
    end
    -- END

In the first example, the semicolon after the ``split`` command tells Lean to use the
``norm_num`` tactic on both of the goals that result.

In Lean, ``A ↔ B`` is *not* defined to be ``(A → B) ∧ (B → A)``,
but it could have been,
and it behaves roughly the same way.
You have already seen that you can write ``h.mp`` and ``h.mpr``
or ``h.1`` and ``h.2`` for the two directions of ``h : A ↔ B``.
You can also use ``cases`` and friends.
To prove an if-and-only-if statement,
you can uses ``split`` or angle brackets,
just as you would if you were proving a conjunction.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
    begin
      split,
      { contrapose!,
        rintro rfl,
        reflexivity },
      contrapose!,
      exact le_antisymm h
    end

    example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
    ⟨λ h₀ h₁, h₀ (by rw h₁), λ h₀ h₁, h₀ (le_antisymm h h₁)⟩
    -- END

The last proof term is inscrutable. Remember that you can
use underscores while writing an expression like that to
see what Lean expects.

Try out the various techniques and gadgets you have just seen
in order to prove the following:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example {x y : ℝ} : x ≤ y ∧ ¬ y ≤ x ↔ x ≤ y ∧ x ≠ y :=
    sorry
    -- END

For a more interesting exercise, show that for any
two real numbers ``x`` and ``y``,
``x^2 + y^2 = 0`` if and only if ``x = 0`` and ``y = 0``.
We suggest proving an auxiliary lemma using
``linarith``, ``pow_two_nonneg``, and ``pow_eq_zero``.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    theorem aux {x y : ℝ} (h : x^2 + y^2 = 0) : x = 0 :=
    begin
      have h' : x^2 = 0,
      { sorry },
      exact pow_eq_zero h'
    end

    example (x y : ℝ) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
    sorry
    -- END

In Lean, bi-implication leads a double-life.
You can treat it like a conjunction and use its two
parts separately.
But Lean also knows that it is a reflexive, symmetric,
and transitive relation between propositions,
and you can also use it with ``calc`` and ``rw``.
It is often convenient to rewrite a statement to
an equivalent one.
In the next example, we use ``abs_lt`` to
replace an expression of the form ``abs x < y``
by the equivalent expression ``- y < x ∧ x < y``,
and in the one after that we use ``dvd_gcd_iff``
to replace an expression of the form ``m ∣ gcd n k`` by the equivalent expression ``m ∣ n ∧ m ∣ k``.

.. code-block:: lean

    import data.real.basic
    import data.nat.gcd

    open nat

    -- BEGIN
    example (x y : ℝ) : abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
    begin
      rw abs_lt,
      intro h,
      split; linarith
    end

    example : 3 ∣ gcd 6 15 :=
    begin
      rw dvd_gcd_iff,
      split; norm_num
    end
    -- END

See if you can use ``rw`` with the theorem below
to provide a short proof that negation is not a
nondecreasing function. (Note that ``push_neg`` won't
unfold definitions for you, so the ``rw monotone`` in
the proof of the theorem is needed.)

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    theorem not_monotone_iff {f : ℝ → ℝ}:
      ¬ monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
    by { rw monotone, push_neg }

    example : ¬ monotone (λ x : ℝ, -x) :=
    sorry
    -- END

The remaining exercises in this section are designed
to give you some more practice with conjunction and
bi-implication. Remember that a *partial order* is a
binary relation that is transitive, reflexive, and
antisymmetric.
An even weaker notion sometimes arises:
a *preorder* is just a reflexive, transitive relation.
For any pre-order ``≤``,
Lean axiomatizes the associated strict pre-order by
``a < b ↔ a ≤ b ∧ ¬ b ≤ a``.
Show that if ``≤`` is a partial order,
then ``a < b`` is equivalent to ``a ≤ b ∧ a ≠ b``:

.. code-block:: lean

    import tactic

    -- BEGIN
    variables {α : Type*} [partial_order α]
    variables a b : α

    example : a < b ↔ a ≤ b ∧ a ≠ b :=
    begin
      rw lt_iff_le_not_le,
      sorry
    end
    -- END

.. index:: simp, tactics ; simp

Beyond logical operations, you should not need
anything more than ``le_refl`` and ``le_antisymm``.
Then show that even in the case where ``≤``
is only assumed to be a preorder,
we can prove that the strict order is irreflexive
and transitive.
You do not need anything more than ``le_refl`` and ``le_trans``.
In the second example,
for convenience, we use the simplifier rather than ``rw``
to express ``<`` in terms of ``≤`` and ``¬``.
We will come back to the simplifier later,
but here we are only relying on the fact that it will
use the indicated lemma repeatedly, even if it needs
to be instantiated to different values.

.. code-block:: lean

    import tactic

    -- BEGIN
    variables {α : Type*} [preorder α]
    variables a b c : α

    example : ¬ a < a :=
    begin
      rw lt_iff_le_not_le,
      sorry
    end

    example : a < b → b < c → a < c :=
    begin
      simp only [lt_iff_le_not_le],
      sorry
    end
    -- END


.. _disjunction:

Disjunction
-----------

.. index:: left, right, tactics ; left, tactics ; right

The canonical way to prove a disjunction ``A ∨ B`` is to prove
``A`` or to prove ``B``.
The ``left`` tactic chooses ``A``,
and the ``right`` tactic chooses ``B``.

.. code-block:: lean

    import data.real.basic

    variables {x y : ℝ}

    -- BEGIN
    example (h : y > x^2) : y > 0 ∨ y < -1 :=
    by { left, linarith [pow_two_nonneg x] }

    example (h : -y > x^2 + 1) : y > 0 ∨ y < -1 :=
    by { right, linarith [pow_two_nonneg x] }
    -- END

We cannot use an anonymous constructor to construct a proof
of an "or" because Lean would have to guess
which disjunct we are trying to prove.
When we write proof terms we can use
``or.inl`` and ``or.inr`` instead
to make the choice explicitly.
Here, ``inl`` is short for "introduction left" and
``inr`` is short for "introduction right."

.. code-block:: lean

    import data.real.basic

    variable {y : ℝ}

    -- BEGIN
    example (h : y > 0) : y > 0 ∨ y < -1 :=
    or.inl h

    example (h : y < -1) : y > 0 ∨ y < -1 :=
    or.inr h
    -- END

It may seem strange to prove a disjunction by proving one side
or the other.
In practice, which case holds usually depends a case distinction
that is implicit or explicit in the assumptions and the data.
The ``cases`` tactic allows us to make use of a hypothesis
of the form ``A ∨ B``.
In contrast to the use of ``cases`` with conjunction or an
existential quantifier,
here the ``cases`` tactic produces *two* goals.
Both have the same conclusion, but in the first case,
``A`` is assumed to be true,
and in the second case,
``B`` is assumed to be true.
In other words, as the name suggests,
the ``cases`` tactic carries out a proof by cases.
As usual, we can tell Lean what names to use for the hypotheses.
In the next example, we tell Lean
to use the name ``h`` on each branch.

.. code-block:: lean

    import data.real.basic

    variables {x y : ℝ}

    -- BEGIN
    example : x < abs y → x < y ∨ x < -y :=
    begin
      cases le_or_gt 0 y with h h,
      { rw abs_of_nonneg h,
        intro h, left, exact h },
      rw abs_of_neg h,
      intro h, right, exact h
    end
    -- END

The absolute value function is defined in such a way
that we can immediately prove that
``x ≥ 0`` implies ``abs x = x``
(this is the theorem ``abs_of_nonneg``)
and ``x < 0`` implies ``abs x = -x`` (this is ``abs_of_neg``).
The expression ``le_or_gt 0 x`` establishes ``0 ≤ x ∨ x < 0``,
allowing us to split on those two cases.
Try proving the triangle inequality using the two
first two theorems in the next snippet.
They are given the same names they have in mathlib.

.. code-block:: lean

    import data.real.basic

    variables {x y : ℝ}

    namespace my_abs

    -- BEGIN
    theorem le_abs_self : x ≤ abs x :=
    sorry

    theorem neg_le_abs_self : -x ≤ abs x :=
    sorry

    theorem abs_add : abs (x + y) ≤ abs x + abs y :=
    sorry
    -- END

    end my_abs

In case you enjoyed these (pun intended) and
you want more practice with disjunction,
try these.

.. code-block:: lean

    import data.real.basic

    variables {x y : ℝ}

    namespace my_abs

    -- BEGIN
    theorem lt_abs : x < abs y ↔ x < y ∨ x < -y :=
    sorry

    theorem abs_lt : abs x < y ↔ - y < x ∧ x < y :=
    sorry
    -- END

    end my_abs

You can also use ``rcases`` and ``rintros`` with disjunctions.
When these result in a genuine case split with multiple goals,
the patterns for each new goal are separated by a vertical bar.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 :=
    begin
      rcases lt_trichotomy x 0 with xlt | xeq | xgt,
      { left, exact xlt },
      { contradiction },
      right, exact xgt
    end
    -- END

You can still nest patterns and use the ``rfl`` keyword
to substitute equations:

.. code-block:: lean

    import tactic

    -- BEGIN
    example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k :=
    begin
      rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩,
      { rw [mul_assoc],
        apply dvd_mul_right },
      rw [mul_comm, mul_assoc],
      apply dvd_mul_right
    end
    -- END

See if you can prove the following with a single (long) line.
Use ``rcases`` to unpack the hypotheses and split on cases,
and use a semicolon and ``linarith`` to solve each branch.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example {z : ℝ} (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) :
      z ≥ 0 :=
    sorry
    -- END

On the real numbers, an equation ``x * y = 0``
tells us that ``x = 0`` or ``y = 0``.
In mathlib, this fact is known as ``eq_zero_or_eq_zero_of_mul_eq_zero``,
and it is another nice example of how a disjunction can arise.
See if you can use it to prove the following:

.. code-block:: lean

    import data.real.basic

    variables (x y : ℝ)

    -- BEGIN
    example (h : x^2 = 1) : x = 1 ∨ x = -1 :=
    sorry

    example (h : x^2 = y^2) : x = y ∨ x = -y :=
    sorry
    -- END

Remember that you can use the ``ring`` tactic to help
with calculations.

In an arbitrary ring :math:`R`, an element :math:`x` such
that :math:`x y = 0` for some nonzero :math:`y` is called
a *left zero divisor*,
an element :math:`x` such
that :math:`y x = 0` for some nonzero :math:`y` is called
a *right zero divisor*,
and an element that is either a left or right zero divisor
is called simply a *zero divisor*.
The theorem ``eq_zero_or_eq_zero_of_mul_eq_zero``
says that the real numbers have no nontrivial zero divisors.
A commutative ring with this property is called an *integral domain*.
Your proofs of the two theorems above should work equally well
in any integral domain:

.. code-block:: lean

    import algebra.group_power tactic

    variables {R : Type*} [integral_domain R]

    variables (x y : R)

    example (h : x^2 = 1) : x = 1 ∨ x = -1 :=
    sorry

    example (h : x^2 = y^2) : x = y ∨ x = -y :=
    sorry

In fact, if you are careful, you can prove the first
theorem without using commutativity of multiplication.
In that case, it suffices to assume that ``R`` is
a ``domain`` instead of an ``integral_domain``.

.. index:: excluded middle

Sometimes in a proof we want to split on cases
depending on whether some statement is true or not.
For any proposition ``P``, we can use
``classical.em P : P ∨ ¬ P``.
The name ``em`` is short for "excluded middle."

.. code-block:: lean

    example (P : Prop) : ¬ ¬ P → P :=
    begin
      intro h,
      cases classical.em P,
      { assumption },
      contradiction
    end

.. index:: by_cases, tactics ; by_cases

You can shorten ``classical.em`` to ``em``
by opening the ``classical`` namespace with the command
``open classical``.
Alternatively, you can use the ``by_cases`` tactic.
The ``open_locale classical`` command guarantees that Lean can
make implicit use of the law of the excluded middle.

.. code-block:: lean

    import tactic

    open_locale classical

    example (P : Prop) : ¬ ¬ P → P :=
    begin
      intro h,
      by_cases h' : P,
      { assumption },
      contradiction
    end

Notice that the ``by_cases`` tactic lets you
specify a label for the hypothesis that is
introduced in each branch,
in this case, ``h' : P`` in one and ``h' : ¬ P``
in the other.
If you leave out the label,
Lean uses ``h`` by default.
Try proving the following equivalence,
using ``by_cases`` to establish one direction.

.. code-block:: lean

    import tactic

    open_locale classical

    -- BEGIN
    example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
    sorry
    -- END


.. _sequences_and_convergence:

Sequences and Convergence
-------------------------

We now have enough skills at our disposal to do some real mathematics.
In Lean, we can represent a sequence :math:`s_0, s_1, s_2, \ldots` of
real numbers as a function ``s : ℕ → ℝ``.
Such a sequence is said to *converge* to a number :math:`a` if for every
:math:`\varepsilon > 0` there is a point beyond which the sequence
remains within :math:`\varepsilon` of :math:`a`,
that is, there is a number :math:`N` such that for every
:math:`n \ge N`, :math:`| s_n - a | < \varepsilon`.
In Lean, we can render this as follows:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    def converges_to (s : ℕ → ℝ) (a : ℝ) :=
    ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε
    -- END

The notation ``∀ ε > 0, ...`` is a convenient abbreviation
for ``∀ ε, ε > 0 → ...``, and, similarly,
``∀ n ≥ N, ...`` abbreviates ``∀ n, n ≥ N →  ...``.
And remember that ``ε > 0``, in turn, is defined as ``0 < ε``,
and ``n ≥ N`` is defined as ``N ≤ n``.

.. index:: extentionality, ext, tactics ; ext

In this section, we'll establish some properties of convergence.
But first, we will discuss three tactics for working with equality
that will prove useful.
The first, the ``ext`` tactic,
gives us a way of proving that two functions are equal.
Let :math:`f(x) = x + 1` and :math:`g(x) = 1 + x`
be functions from reals to reals.
Then, of course, :math:`f = g`, because they return the same
value for every :math:`x`.
The ``ext`` tactic enables us to prove an equation between functions
by proving that their values are the same
at all the values of their arguments.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example : (λ x y : ℝ, (x + y)^2) = (λ x y : ℝ, x^2 + 2*x*y + y^2) :=
    by { ext, ring }
    -- END

.. index:: congr, tactics ; congr

We'll see later that ``ext`` is actually more general, and also one can
specify the name of the variables that appear.
For instance you can try to replace ``ext`` with ``ext u v`` in the
above proof.
The second tactic, the ``congr`` tactic,
allows us to prove an equation between two expressions
by reconciling the parts that are different:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (a b : ℝ) : abs a = abs (a - b + b) :=
    by  { congr, ring }
    -- END

Here the ``congr`` tactic peels off the ``abs`` on each side,
leaving us to prove ``a = a - b + b``.

.. index:: convert, tactics ; convert

Finally, the ``convert`` tactic is used to apply a theorem
to a goal when the conclusion of the theorem doesn't quite match.
For example, suppose we want to prove ``a < a * a`` from ``1 < a``.
A theorem in the library, ``mul_lt_mul_right``,
will let us prove ``1 * a < a * a``.
One possibility is to work backwards and rewrite the goal
so that it has that form.
Instead, the ``convert`` tactic lets us apply the theorem
as it is,
and leaves us with the task of proving the equations that
are needed to make the goal match.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example {a : ℝ} (h : 1 < a) : a < a * a :=
    begin
      convert (mul_lt_mul_right _).2 h,
      { rw [one_mul] },
      exact lt_trans zero_lt_one h
    end
    -- END

This example illustrates another useful trick: when we apply an
expression with an underscore
and Lean can't fill it in for us automatically,
it simply leaves it for us as another goal.

The following shows that any constant sequence :math:`a, a, a, \ldots`
converges.

.. code-block:: lean

    import data.real.basic

    def converges_to (s : ℕ → ℝ) (a : ℝ) :=
    ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

    variable (a : ℝ)

    -- BEGIN
    theorem converges_to_const : converges_to (λ x : ℕ, a) a :=
    begin
      intros ε εpos,
      use 0,
      intros n nge, dsimp,
      rw [sub_self, abs_zero],
      apply εpos
    end
    -- END

.. TODO: reference to the simplifier

Lean has a tactic, ``simp``, which can often save you the
trouble of carrying out steps like ``rw [sub_self, abs_zero]``
by hand.
We will tell you more about it soon.

For a more interesting theorem, let's show that if ``s``
converges to ``a`` and ``t`` converges to ``b``, then
``λ n, s n + t n`` converges to ``a + b``.
It is helpful to have a clear pen-and-paper
proof in mind before you start writing a formal one.
Given ``ε`` greater than ``0``,
the idea is to use the hypotheses to obtain an ``Ns``
such that beyond that point, ``s`` is within ``ε / 2``
of ``a``,
and an ``Nt`` such that beyond that point, ``t`` is within
``ε / 2`` of ``b``.
Then, whenever ``n`` is greater than or equal to the
maximum of ``Ns`` and ``Nt``,
the sequence ``λ n, s n + t n`` should be within ``ε``
of ``a + b``.
The following example begins to implement this strategy.
See if you can finish it off.

.. code-block:: lean

    import data.real.basic

    def converges_to (s : ℕ → ℝ) (a : ℝ) :=
    ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

    -- BEGIN
    variables {s t : ℕ → ℝ} {a b : ℝ}

    theorem converges_to_add
      (cs : converges_to s a) (ct : converges_to t b):
    converges_to (λ n, s n + t n) (a + b) :=
    begin
      intros ε εpos, dsimp,
      have ε2pos : 0 < ε / 2,
      { linarith },
      cases cs (ε / 2) ε2pos with Ns hs,
      cases ct (ε / 2) ε2pos with Nt ht,
      use max Ns Nt,
      sorry
    end
    -- END

As hints, you can use ``le_of_max_le_left`` and ``le_of_max_le_right``,
and ``norm_num`` can prove ``ε / 2 + ε / 2 = ε``.
Also, it is helpful to use the ``congr`` tactic to
show that ``abs (s n + t n - (a + b))`` is equal to
``abs ((s n - a) + (t n - b)),``
since then you can use the triangle inequality.
Notice that we marked all the variables ``s``, ``t``, ``a``, and ``b``
implicit because they can be inferred from the hypotheses.

Proving the same theorem with multiplication in place
of addition is tricky.
We will get there by proving some auxiliary statements first.
See if you can also finish off the next proof,
which shows that if ``s`` converges to ``a``,
then ``λ n, c * s n`` converges to ``c * a``.
It is helpful to split into cases depending on whether ``c``
is equal to zero or not.
We have taken care of the zero case,
and we have left you to prove the result with
the extra assumption that ``c`` is nonzero.

.. code-block:: lean

    import data.real.basic

    def converges_to (s : ℕ → ℝ) (a : ℝ) :=
    ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

    theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
    sorry

    variables {s : ℕ → ℝ} {a : ℝ}

    -- BEGIN
    theorem converges_to_mul_const
        {c : ℝ} (cs : converges_to s a) :
      converges_to (λ n, c * s n) (c * a) :=
    begin
      by_cases h : c = 0,
      { convert converges_to_const 0,
        { ext, rw [h, zero_mul] },
        rw [h, zero_mul] },
      have acpos : 0 < abs c,
        from abs_pos_of_ne_zero h,
      sorry
    end
    -- END

The next theorem is also independently interesting:
it shows that a convergent sequence is eventually bounded
in absolute value.
We have started you off; see if you can finish it.

.. code-block:: lean

    import data.real.basic

    def converges_to (s : ℕ → ℝ) (a : ℝ) :=
    ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

    variables {s : ℕ → ℝ} {a : ℝ}

    -- BEGIN
    theorem exists_abs_le_of_converges_to (cs : converges_to s a) :
      ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
    begin
      cases cs 1 zero_lt_one with N h,
      use [N, abs a + 1],
      sorry
    end
    -- END

In fact, the theorem could be strengthened to assert
that there is a bound ``b`` that holds for all values of ``n``.
But this version is strong enough for our purposes,
and we will see at the end of this section that it
holds more generally.

The next lemma is auxiliary: we prove that if
``s`` converges to ``a`` and ``t`` converges to ``0``,
then ``λ n, s n * t n`` converges to ``0``.
To do so, we use the previous theorem to find a ``B``
that bounds ``s`` beyond some point ``N₀``.
See if you can understand the strategy we have outlined
and finish the proof.

.. code-block:: lean

    import data.real.basic

    def converges_to (s : ℕ → ℝ) (a : ℝ) :=
    ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

    variables {s t : ℕ → ℝ} {a : ℝ}

    theorem exists_abs_le_of_converges_to (cs : converges_to s a) :
      ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
    sorry

    -- BEGIN
    lemma aux (cs : converges_to s a) (ct : converges_to t 0) :
      converges_to (λ n, s n * t n) 0 :=
    begin
      intros ε εpos, dsimp,
      rcases exists_abs_le_of_converges_to cs with ⟨N₀, B, h₀⟩,
      have Bpos : 0 < B,
        from lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _)),
      have pos₀ : ε / B > 0,
        from div_pos εpos Bpos,
      cases ct _ pos₀ with N₁ h₁,
      sorry
    end
    -- END

If you have made it this far, congratulations!
We are now within striking distance of our theorem.
The following proof finishes it off.

.. code-block:: lean

    import data.real.basic

    def converges_to (s : ℕ → ℝ) (a : ℝ) :=
    ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

    theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
    sorry

    variables {s t : ℕ → ℝ} {a b : ℝ}

    theorem converges_to_add
        (cs : converges_to s a) (ct : converges_to t b):
      converges_to (λ n, s n + t n) (a + b) :=
    sorry

    theorem converges_to_mul_const
        (c : ℝ) (cs : converges_to s a) :
      converges_to (λ n, c * s n) (c * a) :=
    sorry

    lemma aux (cs : converges_to s a) (ct : converges_to t 0) :
      converges_to (λ n, s n * t n) 0 :=
    sorry

    -- BEGIN
    theorem converges_to_mul
        (cs : converges_to s a) (ct : converges_to t b):
      converges_to (λ n, s n * t n) (a * b) :=
    begin
      have h₁ : converges_to (λ n, s n * (t n - b)) 0,
      { apply aux cs,
        convert converges_to_add ct (converges_to_const (-b)),
        ring },
      convert (converges_to_add h₁ (converges_to_mul_const b cs)),
      { ext, ring },
      ring
    end
    -- END

For another challenging exercise,
try filling out the following sketch of a proof that limits
are unique.
(If you are feeling bold,
you can delete the proof sketch and try proving it from scratch.)

.. code-block:: lean

    import data.real.basic

    def converges_to (s : ℕ → ℝ) (a : ℝ) :=
    ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

    open_locale classical

    -- BEGIN
    theorem converges_to_unique {s : ℕ → ℝ} {a b : ℝ}
        (sa : converges_to s a) (sb : converges_to s b) :
      a = b :=
    begin
      by_contradiction abne,
      have : abs (a - b) > 0,
      { sorry },
      let ε := abs (a - b) / 2,
      have εpos : ε > 0,
      { change abs (a - b) / 2 > 0, linarith },
      cases sa ε εpos with Na hNa,
      cases sb ε εpos with Nb hNb,
      let N := max Na Nb,
      have absa : abs (s N - a) < ε,
      { sorry },
      have absb : abs (s N - b) < ε,
      { sorry },
      have : abs (a - b) < abs (a - b),
      { sorry },
      exact lt_irrefl _ this
    end
    -- END

.. solution:
    theorem converges_to_unique {s : ℕ → ℝ} {a b : ℝ}
        (sa : converges_to s a) (sb : converges_to s b) :
      a = b :=
    begin
      by_contradiction abne,
      have : abs (a - b) > 0,
      { apply lt_of_le_of_ne,
        { apply abs_nonneg },
          intro h'',
          apply abne,
          apply eq_of_abs_sub_eq_zero h''.symm, },
      let ε := abs (a - b) / 2,
      have εpos : ε > 0,
      { change abs (a - b) / 2 > 0, linarith },
      cases sa ε εpos with Na hNa,
      cases sb ε εpos with Nb hNb,
      let N := max Na Nb,
      have absa : abs (s N - a) < ε,
      { apply hNa, apply le_max_left },
      have absb : abs (s N - b) < ε,
      { apply hNb, apply le_max_right },
      have : abs (a - b) < abs (a - b),
        calc
          abs (a - b) = abs (- (s N - a) + (s N - b)) :
            by { congr, ring }
          ... ≤ abs (- (s N - a)) + abs (s N - b) :
            abs_add _ _
          ... = abs (s N - a) + abs (s N - b) :
            by rw [abs_neg]
          ... < ε + ε : add_lt_add absa absb
          ... = abs (a - b) : by norm_num,
      exact lt_irrefl _ this
    end


We close the section with the observation that our proofs can be generalized.
For example, the only properties that we have used of the
natural numbers is that their structure carries a partial order
with ``min`` and ``max``.
You can check that everything still works if you replace ``ℕ``
everywhere by any linear order ``α``:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    variables {α : Type*} [linear_order α]

    def converges_to (s : α → ℝ) (a : ℝ) :=
    ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε
    -- END

.. TODO: reference to later chapter

In a later chapter, we will see that mathlib has mechanisms
for dealing with convergence in vastly more general terms,
not only abstracting away particular features of the domain
and codomain,
but also abstracting over different types of convergence.
