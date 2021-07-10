module RefinedSExp.DepList

import public RefinedSExp.List

%default total

infixr 7 :::
public export
data ListForAll :
  {atom : Type} -> (depType : atom -> type) -> List atom -> Type where
    (|:|) : {atom : Type} -> {depType : atom -> Type} ->
            ListForAll depType []
    (:::) : {atom : Type} -> {depType : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            depType a -> ListForAll depType l ->
            ListForAll depType (a :: l)

public export
data ListExists :
  {atom : Type} -> (depType : atom -> type) -> List atom -> Type where
    (<::) : {atom : Type} -> {depType : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            depType a ->
            ListExists depType (a :: l)
    (>::) : {atom : Type} -> {depType : atom -> Type} ->
            {a : atom} -> {l : List atom} ->
            ListExists depType l ->
            ListExists depType (a :: l)
