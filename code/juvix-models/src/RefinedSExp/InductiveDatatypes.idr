module RefinedSExp.InductiveDatatypes

import Library.FunctionsAndRelations
import public RefinedSExp.AlgebraicTypes
import public RefinedSExp.Datatypes

%default total

public export
data ParameterizedDatatype : (penv : PrimitiveEnv) -> Type where
  ConstDatatype :
    Datatype penv -> ParameterizedDatatype penv
  VariableDatatype :
    (Datatype penv -> Datatype penv) -> ParameterizedDatatype penv
