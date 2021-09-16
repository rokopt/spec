module ReflectiveLanguages.Substitutive

import Library.FunctionsAndRelations
import Library.Decidability
import RefinedSExp.List
import public Datatypes.DependentAlgebraicTypes
import public Data.Nat

%default total

prefix 11 *^
prefix 11 *|
infixl 7 *~

mutual
  -- | An S-expression whose only atoms are de Bruijn indices.
  -- | The "C" prefix is for "Context"; de Bruijn indices are references
  -- | to variables in a context.
  -- |
  -- | An S-expression may be either an atom or a list of S-expressions.
  public export
  data CSExp : (contextSize : Nat) -> Type where
    -- | An atom, which is a de Bruijn index.
    (*^) : {contextSize : Nat} -> (index : Nat) ->
      {auto indexValid : index `LT` contextSize} -> CSExp contextSize
    -- | A list of S-expressions.
    (*|) : {contextSize : Nat} -> CSList contextSize -> CSExp contextSize

  -- | The list form of S-expressions whose only atoms are de Bruijn indices.
  public export
  data CSList : (contextSize : Nat) -> Type where
    -- | The empty list, which may be formed in any context.
    (*-) : {contextSize : Nat} -> CSList contextSize
    -- | A non-empty list whose tail's context includes the head.
    -- | This is a dependent list, also known as a telescope.
    (*~) : {contextSize : Nat} ->
      CSExp contextSize -> CSList (S contextSize) -> CSList contextSize

mutual
  public export
  -- | Introduce an unused variable into the context of an S-expression.
  csIntroOne : {origContextSize : Nat} -> CSExp origContextSize ->
    CSExp (S origContextSize)
  csIntroOne ((*^) index {indexValid}) =
    (*^) index {indexValid=(lteSuccRight indexValid)}
  csIntroOne (*| l) = *| (cslIntroOne l)

  public export
  -- | Introduce an unused variable into the context of an S-list.
  cslIntroOne : {origContextSize : Nat} -> CSList origContextSize ->
    CSList (S origContextSize)
  cslIntroOne (*-) = (*-)
  cslIntroOne (hd *~ tl) = csIntroOne hd *~ cslIntroOne tl

-- | Introduce unused variables into the context of an S-expression.
public export
csIntro : {newVars, origContextSize : Nat} ->
  CSExp origContextSize -> CSExp (newVars + origContextSize)
csIntro {newVars=Z} x = x
csIntro {newVars=(S Z)} x = csIntroOne x
csIntro {newVars=(S (S n))} x = csIntroOne (csIntro {newVars=(S n)} x)

-- | Introduce unused variables into the context of an S-list.
public export
cslIntro : {newVars, origContextSize : Nat} ->
  CSList origContextSize -> CSList (newVars + origContextSize)
cslIntro {newVars=Z} x = x
cslIntro {newVars=(S Z)} x = cslIntroOne x
cslIntro {newVars=(S (S n))} x = cslIntroOne (cslIntro {newVars=(S n)} x)

-- | A non-empty list whose tail's context does not include the head.
-- | This is a non-dependent cons.
infixr 7 *:
public export
(*:) : {contextSize : Nat} ->
  CSExp contextSize -> CSList contextSize -> CSList contextSize
hd *: tl = hd *~ (cslIntro {newVars=1} tl)

-- | A non-dependent list.
public export
csList : {contextSize : Nat} -> List (CSExp contextSize) -> CSList contextSize
csList [] = (*-)
csList (x :: xs) = x *: (csList xs)

-- | Decide whether all members of a list of indices are in bounds.
public export
isValidIndexList : (contextSize : Nat) -> List Nat -> Bool
isValidIndexList contextSize [] = True
isValidIndexList contextSize (index :: indices) =
  index < contextSize && isValidIndexList contextSize indices

-- | A proof that all members of a list of indices are in bounds.
public export
IsValidIndexList : (contextSize : Nat) -> List Nat -> Type
IsValidIndexList contextSize indices =
  IsTrue (isValidIndexList contextSize indices)

public export
CSNPred : Nat -> Type
CSNPred contextSize = CSExp contextSize -> Bool

public export
CSPred : Type
CSPred = (contextSize : Nat) -> CSNPred contextSize

public export
CSLNPred : Nat -> Type
CSLNPred contextSize = CSList contextSize -> Bool

public export
CSLPred : Type
CSLPred = (contextSize : Nat) -> CSLNPred contextSize
