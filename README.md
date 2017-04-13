GHC Core Small-Step semantics
=============================

This module contains an executable, type ignoring small-step semantics for Haskell Core with lazyness.

It has a heap, a current expression and a stack, and closely follows Sestoft’s semantics.

Naming is handled the same way as in GHC: When we enter a binder (which we do when applying a lambda, when moving let-bound things onto the heap and in a case expression), we freshen the names as required.

This semantics ignores types. This means that intermediate configurations will not be well-typed.

The semantics ignores the IdInfo of GHC variables. It remains to be seen if some of the convenience functions (e.g. exprIsHNF and exprIsTrivial) use them, and if that causes problems.

The semantics handles closed terms. There is no support for a module structure (although that would not be hard to add).

Relatedly, primitive operations (which are manifest simply as free global variables) are not supported. It might be possible to parametrize over their execution.
