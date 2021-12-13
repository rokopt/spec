# Fixing Agda formalisation of "An Internalist Approach to Correct-by-Construction Compilers"

**Authors**

- Alberto Pardo , Emmanuel Gunther , Miguel Pagano , Marcos Viera

*Unfortunately, the original sources
do not type-check. As a result, I have postulated every single lemma that present any kind of problem. The main issue is import to an old Agda standard library, which has been changing quite a lot since then.*

- [ ] Postulate anything that seems to not type-check
- [ ] Fix compilation with Agda V.2.6.2
- [ ] Support the lastest standard library
- [ ] Remove postulates
- [ ] Add an index relating lemmas to the paper.
- [ ] Add Makefile

## Abstract

In this paper we present a methodology to organize the construction of a correct compiler, taking advantage of the power of full dependently type systems. The basic idea consists in decorating the abstract syntax of languages with their semantics, allowing to express the correctness of the compiler at type level. We show our methodology in a first small example and then explore how it can be promoted to more realistic languages, realizing that our internalistic approach is feasible for defining a correct-by-construction compiler from an imperative language with conditional iteration to a stack based intermediate language. We also show how this methodology can be combined with the externalist approach, compiling from the intermediate language to an assembly-like low level code and separately proving its correctness.

```agda
{-# OPTIONS --allow-unsolved-metas #-}
open import Assm
open import Loop
open import While

open import CompLoopAssm
open import CompWhileLoop

-- library
open import Common
open import ListProperties
```
