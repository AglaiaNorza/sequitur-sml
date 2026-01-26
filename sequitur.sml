datatype term = Const of int | Var of string | Plus of (term * term) | Minus of (term * term) | Times of (term * term) 

datatype formula = True | False 
                | Lt of (term * term) | Lte of (term * term)  
                | Gt of (term * term) | Gte of (term * term)  
                | Eq of (term * term) 
                | Not of formula | And of (formula * formula) | Or of (formula * formula)
                | Implies of (formula * formula)

(* variable * coefficient, and then the constant on the right *)
(* eg 2x + 3y <= 5 --> [(x, 2), (y, 3)], 5  *)
type linear_ineq = (string * int) list * int

(* simple sums *)
(* like 2x+ 3y + 2 + 5 --> [(x,2), (y,3)], 7 *)
type flat_term = (string * int) list * int

fun addAndCollapse ([]) = []
    | addAndCollapse ((var, coeff)::rest) =
        let
            (* splits into two lists: one with the tuples w/keys matching var, and one with the others *)
            val (matches, others) = List.partition (fn (v, _) => v = var) rest
            (* foldl "accumulates" over (var, coeff), summing up values *)
            val newMe = List.foldl (fn ((_, v), (x, current_sum)) => (x, current_sum + v)) (var, coeff) matches 
        in
            newMe::addAndCollapse(others)
        end

(* sums "polynomial" terms maintaining flat term structure *)
fun sumTerms ((vars1, c1), (vars2, c2)): flat_term = (addAndCollapse(vars1 @ vars2), c1+c2)
    
(* 3*(2x + 3y) *)
fun multiplyTerms (c, (vars, const)): flat_term =
    (* multiplying each variable's coefficient + the constant coefficient *)
    ((List.map(fn (var, k) => (var, k*c)) vars), const*c)

(* 2x + 3y + 2 + 5 --> [(x,2), (y,3)], 7 *)
fun flattenTerms (t: term): flat_term =
    case t of
        Plus(t1, t2) => sumTerms(flattenTerms t1, flattenTerms t2)
        | Minus(t1, t2) => sumTerms(flattenTerms t1, (multiplyTerms (~1, flattenTerms t2)))
        | Times (t1, t2) => 
            (case (t1, t2) of
                (Const t1, t2) => multiplyTerms(t1, flattenTerms t2)
                | (t1, Const t2) => multiplyTerms(t2, flattenTerms t1)
                | _ => raise Fail "nop" (* must be linear *))
        | Const c => ([],  c)
        | Var x => ([(x, 1)], 0)
        
(* x + b <= y - c --> x - y + (b + c) --> x - y <= -(b+c) *)
fun normaliseTerms ((t1: term), (t2: term)): linear_ineq =
    let 
        val (vars, c) = sumTerms (flattenTerms t1, multiplyTerms(~1, flattenTerms t2))
    in
        (vars, ~c)
    end

(* NOTs should be pushed down to the leaves *)
fun negateFormula (f: formula): formula =
    case f of
        True => False
        | False => True
        | Lt(t1, t2) => Gte(t1, t2)
        | Lte(a, b) => Gt(a, b)
        | Gte(a, b) => Le(a, b)
        | Gte(a, b) => Lt(a, b)
        | Eq(a, b) => Or(Lt(a, b), Gt(a, b)) 
        | Not(f2) => f2
        | And(p, q) => Or(negate p, negate q)
        | Or(p, q) => And(negate p, negate q)
        | Implies(p, q) => And(p, negate q)

(* distributive property *)
fun distributeAnd (f1, f2) = 
    (* cross product + flattening *)
    List.concat(List.map(fn left => List.map(fn right => left @ right)f1) f2))

(* DNF *)
(* (outer list is OR, inner lists are AND) *)
fun normaliseFormula (f: formula): linear_ineq list list =
    case f of
        Lte(a, b) => [[normaliseTerms(a, b)]]

        (* a < b -> a <= b-1 -> a-b => -1 *)
        | Lt(a, b) => 
            let val (vars, k) = normaliseTerms(a, b) 
                in [[ (vars, k - 1) ]] end

        (* a >= b -> b <= a *)
        | Gte(a, b) => [[normaliseTerms(b, a)]]

        (* a > b  -> b < a -> b <= a - 1 *)
        | Gt(a, b) => 
            let val (vars, k) = normaliseTerms(b, a)
                in [[ (vars, k-1) ]] end

        (* a = b  -> a <= b AND b <= a *)
        | Eq(a,b) => [ [ normaliseTerms(a, b), normaliseTerms(b, a) ] ]

        | Not(f1) => normaliseFormula
     (negate f1)

        (* (A v B) ^ (C v D) -> (A ^ C) v (A ^ D) v (B ^ C) v (B ^ D) *)
        | And(f1, f2) => distributeAnd (normaliseFormula
     f1, normaliseFormula
     f2)

        | Or(f1, f2) => (normaliseFormula
     p) @ (normaliseFormula
     q)
        
        (* P->Q = !P v Q *)
        | Implies(f1, f2) => 
            (normaliseFormula
         (negate p)) @ (normaliseFormula
         q)

(* todo: validity check............ *)