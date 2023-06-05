.. _hierarchies:

Hierarchies
===========

We have seen in :numref:`Chapter %s <structures>` how to define the class
of groups and build instances of this class, and then how to build an instance
of the commutative ring class. But of course there is a hierarchy here: a
commutative ring is in particular an additive group. In this chapter we
will study how to build such hierarchies. They appear in all branches
of mathematics but in this chapter the emphasis will be on algebraic examples.

It may seem premature to discuss how to build hierarchies before more discussions
about using existing hierarchies. But some understanding of the technology underlying
hierarchies is required to use them. So you should probably still read this chapter,
but without trying too hard to remember everything on your first read, then read
the following chapters and come back here for a second reading.

In this chapter, we will redefine (simpler versions of) many things that appear in Mathlib
so we will used indices to distinguish our version. For instance we will have ``Ring₁``
as our version of ``Ring``. Since we will gradually explain more powerful ways of formalizing
structures, those indices will sometimes grow beyond one.

.. include:: C07_Hierarchies/S01_Basics.inc
.. include:: C07_Hierarchies/S02_Morphisms.inc
.. include:: C07_Hierarchies/S03_Subobjects.inc
