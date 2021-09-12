module RefinedSExp.RefinedSExp

import public Library.Decidability

-- “Ah Love! could thou and I with Fate conspire
-- To grasp this sorry Scheme of Things entire,
-- Would not we shatter it to bits -- and then
-- Re-mould it nearer to the Heart's Desire!”
--  - _Rubaiyat of Omar Khayyam_ (tr. Edward FitzGerald)

%default total

-- | A StructExp/StructList is a form of S-expression for which identity is
-- | determined solely by structure -- there's no notion of a type of atom;
-- | there are simply anonymous "holes" where atoms might be, and any two
-- | holes might be either constrained to be equal or not.
mutual
  prefix 11 $<
  prefix 11 $>
  prefix 11 $|
  public export
  data StructExp : (holesInContext, holesInExpression : Nat) -> Type where
    -- | A reference to a hole in context constrains a hole to be equal to
    -- | the one it refers back to.
    ($<) : Fin holesInContext ->
      StructExp holesInContext 0
    -- | A new hole might not be equal to any that comes before it in an
    -- | expression.
    ($>) :
      StructExp holesInContext 1
    -- | A list may be viewed as an expression with the same context and
    -- | number of new holes.
    ($|) : StructList holesInContext holesInList ->
      StructExp holesInContext holesInList

  prefix 7 $-
  infix 7 $:
  public export
  data StructList : (holesInContext, holesInList : Nat) -> Type where
    -- | An empty list contains no holes, and can be formed in any context.
    ($-) : StructList holesInContext 0
    -- | A non-empty list's head introduces its new holes into the context
    -- | of the tail.  Thus it might be viewed as a form of telescope.
    ($:) : StructExp holesInContext holesInHead ->
      StructList (holesInHead + holesInContext) holesInTail ->
      StructList holesInContext (holesInHead + holesInTail)
