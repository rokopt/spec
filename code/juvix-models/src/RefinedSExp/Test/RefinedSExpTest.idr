module RefinedSExp.Test.RefinedSExpTest

import public RefinedSExp.RefinedSExp

%default total

sexpShows : {atom : Type} -> (showAtom : atom -> String) ->
  (SExp atom -> String, SList atom -> String)
sexpShows showAtom =
  sexpDepContextFreeFolds
    (SExpDepContextFreeFoldArgs {sp=(\_ => String)} {lp=(\_ => String)}
      (\a, l, s => case l of
        [] => "$(" ++ showAtom a ++ ")"
        _ => "$(" ++ showAtom a ++ ":" ++ s ++ ")")
      ("")
      (\_, _, x, l => x ++ l))

Show atom => Show (SExp atom) where
  show x = show' x where
    show' : SExp atom -> String
    show' x = case x of (a $: _) => fst (sexpShows show) x

nilNotationTest : SList Nat
nilNotationTest = ($|)

bigNotationTest : SExp Nat
bigNotationTest =
  0 $:
  (1 $: 2 $:^ 3) $+
  (4 $: 5 $^+ (6 $: 7 $^+ (8 $: 9 $:^ 10) $+^ 11) $+ 12 $:^ 13) $+
  14 $^+
  15 $^+
  (16 $: 17 $:^ 18) $+
  (19 $^^ 20) $+^
  21

export
refinedSExpTests : IO ()
refinedSExpTests = do
  printLn nilNotationTest
  printLn bigNotationTest
