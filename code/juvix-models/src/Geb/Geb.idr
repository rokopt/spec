module Geb.Geb

import Library.FunctionsAndRelations
import RefinedSExp.SExp
import Library.Decidability
import RefinedSExp.SExp

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

--------------------------------------------
---- S-expression representation of Geb ----
--------------------------------------------

-- | Having a representation of all Geb expressions as S-expressions allows
-- | us to define, check, and interpret them in uniform ways, without having
-- | to use custom ADTs in different metalanguages (where in this case
-- | "metalanguages" refers to programming languages in which we might interpret
-- | Geb expressions, such as Haskell, Rust, or Juvix).
public export
data GebAtom : Type where
  -- | The notion of a language itself.
  GALanguage : GebAtom

  -- | The minimal programming language.
  GAMinimal : GebAtom

public export
gaEncode : GebAtom -> Nat
gaEncode GALanguage = 0
gaEncode GAMinimal = 1

public export
gaDecode : Nat -> Maybe GebAtom
gaDecode 0 = Just GALanguage
gaDecode 1 = Just GAMinimal
gaDecode _ = Nothing

export
gaDecodeEncodeIsJust : (a : GebAtom) -> gaDecode (gaEncode a) = Just a
gaDecodeEncodeIsJust GALanguage = Refl
gaDecodeEncodeIsJust GAMinimal = Refl

public export
gebAtomToString : GebAtom -> String
gebAtomToString GALanguage = "Language"
gebAtomToString GAMinimal = "Minimal"

public export
Show GebAtom where
  show a = ":" ++ gebAtomToString a

public export
gaEq : GebAtom -> GebAtom -> Bool
gaEq a a' = gaEncode a == gaEncode a'

public export
Eq GebAtom where
  (==) = gaEq

public export
Ord GebAtom where
  a < a' = gaEncode a < gaEncode a'

export
gaDecEq : (a, a' : GebAtom) -> Dec (a = a')
gaDecEq a a' with (decEq (gaEncode a) (gaEncode a'))
  gaDecEq a a' | Yes eq = Yes $
    justInjective $
      trans
        (sym (gaDecodeEncodeIsJust a))
        (trans (cong gaDecode eq) (gaDecodeEncodeIsJust a'))
  gaDecEq a a' | No neq = No $ \aeq => neq $ cong gaEncode aeq

public export
DecEq GebAtom where
  decEq = gaDecEq

public export
GebSExp : Type
GebSExp = SExp GebAtom

public export
GebSList : Type
GebSList = SList GebAtom

public export
Show GebSExp where
  show = fst (sexpShows show)

public export
Show GebSList where
  show l = "(" ++ snd (sexpShows show) l ++ ")"

public export
gsDecEq : DecEqPred GebSExp
gsDecEq = sexpDecEq gaDecEq

public export
gslDecEq : DecEqPred GebSList
gslDecEq = slistDecEq gaDecEq

public export
DecEq GebSExp where
  decEq = gsDecEq

public export
DecEq GebSList where
  decEq = gslDecEq

public export
Eq GebSExp using decEqToEq where
  (==) = (==)

public export
Ord GebSExp where
  (<) = sexpLessThan (<)

public export
Ord GebSList where
  (<) = slistLessThan (<)

public export
data GebExpressionClass : Type where
  LanguageClass : GebExpressionClass

public export
gebClassToExp : GebExpressionClass -> GebSExp
gebClassToExp LanguageClass = $^ GALanguage

public export
gebExpToClass : GebSExp -> Maybe GebExpressionClass
gebExpToClass (GALanguage $* []) = Just LanguageClass
gebExpToClass _ = Nothing

export
gebExpressionClassRepresentationComplete :
  (c : GebExpressionClass) -> gebExpToClass (gebClassToExp c) = Just c
gebExpressionClassRepresentationComplete LanguageClass = Refl

public export
gebLanguageToExp : Language -> GebSExp
gebLanguageToExp Minimal = $^ GAMinimal

public export
gebExpToLanguage : GebSExp -> Maybe Language
gebExpToLanguage (GAMinimal $* []) = Just Minimal
gebExpToLanguage _ = Nothing

export
gebLanguageRepresentationComplete :
  (l : Language) -> gebExpToLanguage (gebLanguageToExp l) = Just l
gebLanguageRepresentationComplete Minimal = Refl
