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
data LanguageRep : Type where
  MinimalRep : LanguageRep

public export
data Language : LanguageRep -> Type where
  -- | The minimal programming language required for Gödel's incompleteness
  -- | theorems to apply.  We treat this abstractly, as a category with
  -- | an initial object, a terminal object, finite products and coproducts,
  -- | an object which we interpret as the type of representations of the
  -- | language's objects and morphisms, and a decidable equality on those
  -- | representations.  The combination of products, coproducts, and decidable
  -- | equality gives us the ability to perform substitution, which in turn
  -- | allows us to represent function application -- the fundamental
  -- | computation in any programming language.
  Minimal : Language MinimalRep

public export
language : (r : LanguageRep) -> Language r
language MinimalRep = Minimal

-------------------------
---- Minimal objects ----
-------------------------

-- | Every programming language (using the Geb definition) has an initial
-- | object, a terminal object, finite products and coproducts, an object
-- | which we interpret as the type of representations of the language's
-- | objects and morphisms, and a decidable equality on those
-- | representations.  This is enough to perform substitution on
-- | representations.
-- |
-- | Note that we are _not_ assuming exponential objects yet -- for example,
-- | the minimal language does not have any first-class functions, and
-- | primitive recursion has only first-order functions.

-- | Well-typed representations of common objects.
public export
data MinimalObjectRep : Type where
  InitialRep : MinimalObjectRep
  TerminalRep : MinimalObjectRep
  ProductRep : MinimalObjectRep -> MinimalObjectRep -> MinimalObjectRep
  CoproductRep : MinimalObjectRep -> MinimalObjectRep -> MinimalObjectRep
  ExpressionRep : MinimalObjectRep

-- | Minimal objects, indexed by their representations.
public export
data MinimalObject : MinimalObjectRep -> Type where
  Initial : MinimalObject InitialRep
  Terminal : MinimalObject TerminalRep
  Product : {r, r' : MinimalObjectRep} ->
    MinimalObject r -> MinimalObject r' -> MinimalObject (ProductRep r r')
  Coproduct : {r, r' : MinimalObjectRep} ->
    MinimalObject r -> MinimalObject r' -> MinimalObject (CoproductRep r r')
  Expression : MinimalObject ExpressionRep

-- | Translate a representation to a minimal object.
public export
minimalObject : (r : MinimalObjectRep) -> MinimalObject r
minimalObject InitialRep = Initial
minimalObject TerminalRep = Terminal
minimalObject (ProductRep o o') =
  Product (minimalObject o) (minimalObject o')
minimalObject (CoproductRep o o') =
  Coproduct (minimalObject o) (minimalObject o')
minimalObject ExpressionRep = Expression

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

  -- | The notion of an object of any programming language.
  GAObject : GebAtom

  -- | Objects common to all programming languages.
  GAInitial : GebAtom
  GATerminal : GebAtom
  GAProduct : GebAtom
  GACoproduct : GebAtom
  GAExpression : GebAtom

public export
gaEncode : GebAtom -> Nat
gaEncode GALanguage = 0
gaEncode GAMinimal = 1
gaEncode GAObject = 2
gaEncode GAInitial = 3
gaEncode GATerminal = 4
gaEncode GAProduct = 5
gaEncode GACoproduct = 6
gaEncode GAExpression = 7

public export
gaDecode : Nat -> Maybe GebAtom
gaDecode 0 = Just GALanguage
gaDecode 1 = Just GAMinimal
gaDecode 2 = Just GAObject
gaDecode 3 = Just GAInitial
gaDecode 4 = Just GATerminal
gaDecode 5 = Just GAProduct
gaDecode 6 = Just GACoproduct
gaDecode 7 = Just GAExpression
gaDecode _ = Nothing

export
gaDecodeEncodeIsJust : (a : GebAtom) -> gaDecode (gaEncode a) = Just a
gaDecodeEncodeIsJust GALanguage = Refl
gaDecodeEncodeIsJust GAMinimal = Refl
gaDecodeEncodeIsJust GAObject = Refl
gaDecodeEncodeIsJust GAInitial = Refl
gaDecodeEncodeIsJust GATerminal = Refl
gaDecodeEncodeIsJust GAProduct = Refl
gaDecodeEncodeIsJust GACoproduct = Refl
gaDecodeEncodeIsJust GAExpression = Refl

public export
gebAtomToString : GebAtom -> String
gebAtomToString GALanguage = "Language"
gebAtomToString GAMinimal = "Minimal"
gebAtomToString GAObject = "Object"
gebAtomToString GAInitial = "Initial"
gebAtomToString GATerminal = "Terminal"
gebAtomToString GAProduct = "Product"
gebAtomToString GACoproduct = "Coproduct"
gebAtomToString GAExpression = "Expression"

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

----------------------------------------------------------------------------
---- Translation between (well-typed) Geb expressions and S-expressions ----
----------------------------------------------------------------------------

public export
data GebExpressionClass : Type where
  LanguageClass : GebExpressionClass
  ObjectClass : GebExpressionClass

public export
gebClassToExp : GebExpressionClass -> GebSExp
gebClassToExp LanguageClass = $^ GALanguage
gebClassToExp ObjectClass = $^ GAObject

public export
gebExpToClass : GebSExp -> Maybe GebExpressionClass
gebExpToClass (GALanguage $* []) = Just LanguageClass
gebExpToClass (GAObject $* []) = Just ObjectClass
gebExpToClass _ = Nothing

export
gebExpressionClassRepresentationComplete :
  (c : GebExpressionClass) -> gebExpToClass (gebClassToExp c) = Just c
gebExpressionClassRepresentationComplete LanguageClass = Refl
gebExpressionClassRepresentationComplete ObjectClass = Refl

public export
gebLanguageRepToExp : LanguageRep -> GebSExp
gebLanguageRepToExp _ = ?gebLanguageRepToExp_hole

public export
gebExpToLanguageRep : GebSExp -> Maybe LanguageRep
gebExpToLanguageRep _ = ?gebExpToLanguageRep_hole

public export
gebLanguageRepRepresentationComplete : (r : LanguageRep) ->
  gebExpToLanguageRep (gebLanguageRepToExp r) = Just r
gebLanguageRepRepresentationComplete _ =
  ?gebLanguageRepRepresentationComplete_hole

public export
gebExpToLanguage : GebSExp -> Maybe (r : LanguageRep ** Language r)
gebExpToLanguage x = case gebExpToLanguageRep x of
  Just r => Just (r ** language r)
  Nothing => Nothing

public export
gebLanguageRepresentationComplete : {r : LanguageRep} -> (l : Language r) ->
  gebExpToLanguage (gebLanguageRepToExp r) = Just (r ** l)
gebLanguageRepresentationComplete {r} l =
  ?gebLanguageRepresentationComplete_hole

public export
gebMinimalObjectRepToExp : MinimalObjectRep -> GebSExp
gebMinimalObjectRepToExp _ = ?gebMinimalObjectToExp_hole

public export
gebExpToMinimalObjectRep : GebSExp -> Maybe MinimalObjectRep
gebExpToMinimalObjectRep _ = ?gebExpToMinimalObjectRep_hole

public export
gebMinimalObjectRepRepresentationComplete : (r : MinimalObjectRep) ->
  gebExpToMinimalObjectRep (gebMinimalObjectRepToExp r) = Just r
gebMinimalObjectRepRepresentationComplete _ =
  ?gebMinimalObjectRepRepresentationComplete_hole

public export
gebExpToMinimalObject :
  GebSExp -> Maybe (r : MinimalObjectRep ** MinimalObject r)
gebExpToMinimalObject x = case gebExpToMinimalObjectRep x of
  Just r => Just (r ** minimalObject r)
  Nothing => Nothing

public export
gebMinimalObjectRepresentationComplete :
  {r : MinimalObjectRep} -> (o : MinimalObject r) ->
  gebExpToMinimalObject (gebMinimalObjectRepToExp r) = Just (r ** o)
gebMinimalObjectRepresentationComplete {r} o =
  ?gebMinimalObjectRepresentationComplete_hole
