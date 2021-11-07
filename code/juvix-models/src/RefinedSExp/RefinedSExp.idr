module RefinedSExp.RefinedSExp

import public Library.Decidability
import public RefinedSExp.SExp

-- “Ah Love! could thou and I with Fate conspire
-- To grasp this sorry Scheme of Things entire,
-- Would not we shatter it to bits -- and then
-- Re-mould it nearer to the Heart's Desire!”
--  - _Rubaiyat of Omar Khayyam_ (tr. Edward FitzGerald)

%default total

public export
PureSExpRefinement : Type -> Type
PureSExpRefinement atom = SExp atom -> Bool

public export
PureSExpIsRefined : {atom : Type} -> PureSExpRefinement atom -> SPred atom
PureSExpIsRefined = (.) IsTrue

public export
SCPred : Type -> Type -> Type
SCPred atom context = (x : SExp atom) -> (c : context) -> Bool

public export
SExpRefinementInContext : Type -> Type -> Type
SExpRefinementInContext atom context = SExp atom -> context -> Bool
