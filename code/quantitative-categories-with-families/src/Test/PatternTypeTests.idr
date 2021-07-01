module Test.PatternTypeTests

import PatternTypes

%default total

NSExp : Type
NSExp = SExp Nat

NSList : Type
NSList = SList Nat

NSCons : Nat -> NSList -> NSExp
NSCons = SCons

NSNil : NSList
NSNil = SNil

NSLCons : NSExp -> NSList -> NSList
NSLCons = SLCons

NSAtom : Nat -> NSExp
NSAtom = SAtom

ns0 : NSExp
ns0 = ($^) 0

ns1 : NSExp
ns1 = ($^) 1

ns2 : NSExp
ns2 = ($^) 2

ns0_1 : NSExp
ns0_1 = 0 $: ns1 $+ NSNil

ns0_1' : NSExp
ns0_1' = 0 $:| ns1

notationTest : 0 $: ($^) 1 $+ ($|) = 0 $^^ 1
notationTest = Refl

bigNotationTest :
  NSCons 0
  (NSLCons
    (NSCons 1
    (NSLCons (NSAtom 2)
    (NSLCons (NSAtom 3)
    NSNil)))
  (NSLCons
    (NSCons 4
    (NSLCons (NSAtom 5)
    (NSLCons
      (NSCons 6
      (NSLCons (NSAtom 7)
      (NSLCons (NSAtom 8)
      NSNil)))
    (NSLCons (NSAtom 9)
    (NSLCons (NSAtom 10)
    NSNil)))))
  (NSLCons
    (NSCons 11 NSNil)
  (NSLCons (NSAtom 12)
  (NSLCons
    (NSCons 13
    (NSLCons (NSAtom 14) (NSLCons (NSAtom 15) (NSNil))))
  (NSLCons (NSCons 16 (NSLCons (NSAtom 17) NSNil))
  NSNil)))))) =
  0 $:
  (1 $: 2 $:^ 3) $+
  (4 $: 5 $^+ (?hole2c) $+ 9 $:^ 10) $+
  ?hole3 $+
  ($^) 12 $+
  ?hole5 $++
  ?hole6
bigNotationTest = Refl
