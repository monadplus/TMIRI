# Effect Handlers in Scope

## Structure

- First part: provide background on the effect handlers approach:
  - Section 2: Handling backtracking computations
  - Section 3: Prepare the ground for more modular syntax by using datatypes a la carte.
  - Section 4: Show how state can be added to nondeterministic computation.
  - Section 5: Show how handlers can span different syntax signatures
- Second part: scoped effects
  - Section 6:  builds grammars to parse input, and shows how using handlers to create local scopes imposes undesired semantics.
  - Section 7: fix the problem by using syntax to delimit the scope.
  - Section 8: demonstrate expection handling as another example that requires scoped effects
  - Section 9: resolves section 8 
  - Section 10: improve solution proposed on section 9. High-order syntax is introduced.
  - Section 11: example where our first-order approach fails, but that can be solved with higher-order syntax.
  - Section 12: related work
  - Section 13: conclusion
  
## Paper

Paper notes by section
  
### 1. Introduction

Two approaches to capture scoped constructs in syntax and achieve different semantics:

- Express scopes using the existing algebraic handlers frameworks.
- high-order syntax

Effect handlers: lightweight and compositional means of describing effectful computations.

Using handlers for scoping has an important limitation. The semantics of handlers is orthogonal i.e. depends on the order of application (e.g. state and non-determinism).

Paper shifts the responsibility of creating scopes from handlers to syntax. This allow safely reorder handlers to control the interaction semantics while scoping is unaffected.

### 2. Backtracking Computation

The effect handlers approach:

1. Syntax to represent the actions of interest.
2. Handlers are written that interpret syntax trees into a semantic domain.

See `Backtr.hs`

### 3. Syntax Signatures

See `Prog.hs`
