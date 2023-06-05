.. _structures:

Structures
==========

Modern mathematics makes essential use of algebraic
structures,
which encapsulate patterns that can be instantiated in
multiple settings.
The subject provides various ways of defining such structures and
constructing particular instances.

Lean therefore provides corresponding ways of
defining structures formally and working with them.
You have already seen examples of algebraic structures in Lean,
such as rings and lattices, which were discussed in
:numref:`Chapter %s <basics>`.
This chapter will explain the mysterious square bracket annotations
that you saw there,
``[Ring α]`` and ``[Lattice α]``.
It will also show you how to define and use
algebraic structures on your own.

For more technical detail, you can consult `Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean/>`_,
and a paper by Anne Baanen, `Use and abuse of instance parameters in the Lean mathematical library <https://arxiv.org/abs/2202.01629>`_.

.. include:: C06_Structures/S01_Structures.inc
.. include:: C06_Structures/S02_Algebraic_Structures.inc
.. include:: C06_Structures/S03_Building_the_Gaussian_Integers.inc
