simple tool to check if (linear) arithmetic implications are valid, built for use with hoare logic. 

uses fourier-motzkin elimination to see if the negation of the formula is unsatisfiable.

----
basics:
- converts nested math expressions into a flat list of variables and a constant (variables ≤ const)
- formulae are normalized into disjunctive normal form (a list of "scenarios")
  - constraints are rounded down with gcd tightening to exclude Real solutions
- the naive solver partitions constraints based on variable coefficients and resolves them until it finds a contradiction (e.g. 0 ≤ −5) or runs out of variables

----
There are two ways to use the solver depending on whether you need a simple "yes/no" or a concrete counterexample for failure.

#### "simple" mode (`verify`)
standard verification mode: checks every scenario in the negated formula to see if all are unsatisfiable

* **function**: `verify f`
* returns `"VALID implication!!"` if its negation is unsatisfiable, or `"INVALID implication. srry."` if a scenario might be satisfiable

#### witness mode (`verify_with_counterexample`)
uses a backtracking solver to generate a concrete counterexample (a "model") when an implication is not found to be valid

* **function**: `verify_with_counterexample f`
* if a scenario is satisfiable, the solver works backward through the eliminated variables using `find_valid_int` to pick an integer that satisfies the original constraints based on each partial model
* returns `"VALID implication!!"` or a formatted string containing the specific variable assignments that break the implication (e.g., `"INVALID implication. Counterexample: { x=5, y=2 }"`)

---
could do:
- [ ] simple heuristic to start with variable that generates the fewest new constraints
- [ ] write simple DPLL/CDCL
