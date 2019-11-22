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

session 3

refx

in collaboration with dailambda
guarantee more functional properties of contract
refinement types, semi-automatic static verifier
refx static verifier, smt solver
mini-Michelson

k-michelson

it's michelson in k

michelson in why3
ligo michelson certified certifying compiler
specification language embedded in sc

static analyses & verification of michelson programs
verifiable certificates for something
what is the certificate certifying?

session 4

universal cubes mcmt

model checker - cubicle ocaml
universite paris sud
reasoning about processes
backward reachability - reason about universal cubes
~ weakest-precondition calculus
cubicle to whyml

scaml - nice, simple ocaml - michelson compiler, uses ocaml compiler-libs
written in 5 days
ocaml tools for free
read the ocaml to lambda calculus part
has closures

blockchains as fancy distributed spreadsheets
spreadsheet transformed into smart contract
somewhat limited, but cool idea

smart types for smart contracts
graphical automata for program reasoning
check automata, alter code if necessary
pre/post conditions

ConCert - smart contract certification framework in Coq
concordium foundation - research center at Aarhus University
lambda-cert - system f w/inductive types & recursion
metacoq - metaprogramming facilities to Coq, Coq as its own tactic language
pcuic - polymorphic cumulative calculus of inductive constructions
basis for verified compiler - certicoq - and verified extraction
maybe other languages could be translated like lambda-smart

general thoughts
academic work tends to be very disjoint, e.g. no type theorists / zkp authors talk to each other
doing research as a company can give us advantages here if we recognize these factors
deployment / maintenance is tricky
w.r.t. tezos - let's interoperate where we can, avoid having opinions on non-essential topics
look for synergies in protocol development & tooling work (e.g. new michelson instructions, backends)
find a way to publish papers occaisionally, it will help w/academic review
