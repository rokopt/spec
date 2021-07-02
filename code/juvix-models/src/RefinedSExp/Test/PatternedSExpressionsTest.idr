module RefinedSExp.Test.PatternedSExpressionsTest

import RefinedSExp.PatternedSExpressions

%default total

NatOrStringPat : Pattern
NatOrStringPat = (#|) [ NatPat , StringPat ]

PairNatOrStringPat : Pattern
PairNatOrStringPat = (#*) [ NatOrStringPat , NatOrStringPat ]

LocationAnnotation : Pattern
LocationAnnotation = NatPat

PairWithLocation : Pattern
PairWithLocation = (#*) [ PairNatOrStringPat , LocationAnnotation ]

IsNumericAnnotation : Pattern
IsNumericAnnotation = BoolPat

LocationAndIsNumericAnnotation : Pattern
LocationAndIsNumericAnnotation =
  (#*) [ LocationAnnotation , IsNumericAnnotation ]

AnnotatePairNatOrStringPatWithLocation :
  Transformer PairNatOrStringPat PairWithLocation
AnnotatePairNatOrStringPatWithLocation matchedList = case matchedList of
  (_ ** ListPairForAllEmpty)
    impossible
  (_ ** (ListPairForAllCons _ ListPairForAllEmpty))
    impossible
  ([ left, right ] **
   (ListPairForAllCons leftMatches
    (ListPairForAllCons rightMatches ListPairForAllEmpty))) =>
      ?AnnotatePairNatOrStringPatWithLocation_hole
  (_ **(ListPairForAllCons _ (ListPairForAllCons _ (ListPairForAllCons _ _))))
    impossible
