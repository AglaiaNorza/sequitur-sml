very simple tool to check if arithmetic implications are valid, built for use with hoare logic. 

uses fourier-motzkin elimination to see if the negation of the formula is unsatisfiable.

----
basics:
- converts nested math expressions into a flat list of variables and a constant (variables ≤ const)
- formulae are normalized into disjunctive normal form (a list of "scenarios")
  - constraints are rounded down with gcd tightening to exclude Real solutions
- the naive solver partitions constraints based on variable coefficients and resolves them until it finds a contradiction (e.g. 0 ≤ −5) or runs out of variables

---
could do:
- [ ] counterexample generation
- [ ] simple heuristic to start with variable that generates the fewest new constraints
