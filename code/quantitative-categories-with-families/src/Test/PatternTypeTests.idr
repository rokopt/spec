module Test.PatternTypeTests

import PatternTypes

%default total

NSExp : Type
NSExp = SExp Nat

NSList : Type
NSList = SList Nat

ns0 : NSExp
ns0 = ($^) 0

nsNil : NSList
nsNil = ($|)

ns1 : NSExp
ns1 = ($^) 1

ns2 : NSExp
ns2 = ($^) 2

ns0_1 : NSExp
ns0_1 = 0 $: ns1 $+ nsNil

ns0_1' : NSExp
ns0_1' = 0 $:| ns1

notationTest : 0 $: ($^) 1 $+ ($|) = 0 $^^ 1
notationTest = Refl
