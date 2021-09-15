module ReflectiveLanguages.Test.SubstitutiveTest

import ReflectiveLanguages.Substitutive
import ReflectiveLanguages.Interpretations.SubstitutiveInterpretation
import Library.FunctionsAndRelations
import Library.Test.TestLibrary
import Library.Decidability
import Datatypes.DependentAlgebraicTypes

%default total

public export
noDuplicates : List Nat -> Bool
noDuplicates [] = True
noDuplicates (n :: l) = find (== n) l == Nothing && noDuplicates l

public export
NoDuplicates : List Nat -> Type
NoDuplicates = IsTrue . noDuplicates

public export
noDuplicatesTail : {n : Nat} -> {l : List Nat} ->
  NoDuplicates (n :: l) -> NoDuplicates l
noDuplicatesTail {l=[]} noDups = Refl
noDuplicatesTail {n} {l=(n' :: l')} noDups with (n' == n)
  noDuplicatesTail {n} {l=(n' :: l')} Refl | True impossible
  noDuplicatesTail {n} {l=(n' :: l')} noDups | False =
    snd $ andElimination noDups

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

export
isAtom : (index : Nat) -> CSPred
isAtom givenIndex _ (*^ foundIndex) = givenIndex == foundIndex
isAtom _ _ (*| _) = False

export
isSuccLike : (carrier, succ : Nat) ->
  {auto noDups : NoDuplicates [ carrier, succ ]} -> CSPred
isSuccLike carrier succ _ (*| ( (*^ i) *: (*^ i') *: (*-) ) ) =
  i == succ && i' == carrier
isSuccLike _ _ _ _ = False

export
isNatFLike : (carrier, zero, succ : Nat) ->
  {auto noDups : NoDuplicates [ zero, carrier, succ ]} -> CSLPred
isNatFLike carrier zero succ {noDups} contextSize
  ( zeroClause *: succClause *: (*-) ) =
    isAtom zero contextSize zeroClause &&
    isSuccLike
      carrier succ
        {noDups=(noDuplicatesTail {l=([ carrier, succ ])} noDups)}
        contextSize succClause
isNatFLike _ _ _ _ _ = False

export
isNatLike : (zero, succ : Nat) -> {auto noDups : NoDuplicates [ zero, succ ]} ->
  CSPred
isNatLike zero succ contextSize (*^ i) = zero == i
isNatLike zero succ contextSize (*| ( (*^ i) *: n *: (*-) ) ) =
  succ == i && isNatLike zero succ contextSize n
isNatLike _ _ _ _ = False

export
substitutiveTests : IO ()
substitutiveTests = pure ()
