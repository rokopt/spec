module Geb.Geb

import Library.FunctionsAndRelations
import Library.Decidability

%default total

-- | A "Language" (short in this case for "programming language") is a category
-- | which is capable of performing computation and can be defined solely by
-- | computation.  It can be viewed as having morphisms which represent
-- | computable functions with computably-representable effects.
-- |
-- | By "capable of performing computation", we mean that Gödel's
-- | incompleteness theorems apply to the category.  In other words, it can
-- | express metalogic; we could also say that it can reflect itself, in that
-- | it can define functions on its own expressions.  (So perhaps we might
-- | say something like "computable metacategory" rather than "programming
-- | language".)
-- |
-- | A language is unsuitable as a metalogic if it is inconsistent -- if its
-- | operational semantics allow non-termination, or if it has any partial
-- | functions.  Of course, one consequence of Gödel's incompleteness theorems
-- | is that we can never be sure that there _are_ any languages that are
-- | suitable as metalogics in that sense!
-- |
-- | So there is a minimal programming language, with this definition:  just
-- | what is required for Gödel's incompleteness theorems to apply.  There is
-- | also a maximal programming language:  the universal Turing machine,
-- | with non-terminating and partial functions.
public export
data Language : Type where
  -- | The minimal programming language required for Gödel's incompleteness
  -- | theorems to apply.  We treat this abstractly, as a category with
  -- | an initial object, a terminal object, finite products and coproducts,
  -- | an object which we interpret as the type of representations of the
  -- | language's objects and morphisms, and a decidable equality on those
  -- | representations.  The combination of products, coproducts, and decidable
  -- | equality gives us the ability to perform substitution, which in turn
  -- | allows us to represent function application -- the fundamental
  -- | computation in any programming language.
  Minimal : Language
