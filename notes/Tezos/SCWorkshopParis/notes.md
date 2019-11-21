Session 1

Introduction to Michelson - nothing new. They should write an untyped interpreter or compile the Michelson, it might be faster. Possible upgrade.

Albert Intermediate Language

Intermediate language target
- Abstract stack with variables
- Linear type system for resource tracking
- More misc goodies

What do we want?
standard closures - ask this?

Questions
stack efficiency, do you gain from linear types, is anything nontrivial with respect to ordering, do you use the optimal stack rearranger
  - answer: it's alphabetical
is there a parser, will it be maintained
  - answer: yes, but has conflicts

conclusion:
could be nice, we can target the linear type system
not convinced this is production ready

Introduction to Ligo

a lot of focus on type inference
type theory is something like System Fw
one goal is a smart contract language as a DSL designed in LIGO
much type theory such wow
features like scheme?

Introduction to SmartPy

python library for writing dapps on tezos
generates michelson + tests, there are tools for deployment & interaction
smartml - intermediate representation
there are michelson to michelson optimisations, we should steal them or share a library
dig/dug usage, nice macros
will also work with the json specifications

Specifying contract interfaces with JSON ==> moved

contract orchestration for ocaml

will start in appx. 1 month
contracts were invoked in the wrong state, oops
a library for interleaving contract interactions
staged execution (early stage / late stage)
Possibly more than 2 stages

general thoughts on session 1: for features, need more analysis of *why*

Session 2

Specifying contract interfaces with JSON

there's a spec
let's use it
even if draft
we don't want to have opinions on these sorts of problems
specs are gucci
many things can be documented, apparently, not just interfaces
there is a draft spec, we should read it
it's a json schema
where are the tzips, find them

feedback on juvix presentation
look up hs to coq
look up graded modal types (but already rejected)
what is type safety? question re semantics - type preservation, progress, correctness of usage annotations

archetype - edukera

domain specific language, transcodes to others
for simple asset manipulation, properties thereof

mi cho coq

embedding of michelson in coq
syntax, typesystem, interpreter
weakest-precondition calculus
seems useful
has gas?
used for manager contract iirc

questions:
can we generate the proofs, I wonder
this seems generally well done
