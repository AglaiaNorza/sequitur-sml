use "data.sml";

(* constraints: [ ([(x,2), (y, 5)], 7), ([(x,-10), (z, 32)], 8) ] *)
(* splits list  of linear equations into three based on coefficient of given string *)
fun partition((constraints: linear_ineq list), x:string) =
    let
        val (pos_list, rest) = List.partition (fn (l, _) => 
            List.exists (fn (var, coeff) => var = x andalso coeff > 0) l) 
            constraints;

        val (neg_list, none_list) = List.partition (fn (l, _) => 
            List.exists (fn (var, coeff) => var = x andalso coeff < 0) l) 
            rest
    in 
        (pos_list, neg_list, none_list)
    end

(* 
    we have
    -2x + y <= 5
    3x -z <= 10

    by doing
    3 (-2x + y <= 5) = -6x + 3y <= 15 +
    2 (3x -z <= 10) = +6x -2z <= 20 =

    we get 3y -2z <= 35
    (no x !!)
*)
fun resolve((lower_const: linear_ineq), (upper_const: linear_ineq), x: string): linear_ineq =
    let
        val (lcl, _) = lower_const
        val (ucl, _) = upper_const
        val SOME(_, c1) = List.find((fn (v, _) => v = x)) lcl
        val SOME(_, c2) = List.find((fn (v, _) => v = x)) ucl
    in
        sumTerms(multiplyTerms(c2, lower_const), multiplyTerms((~c1), upper_const))
    end 

(* given a list of positive constraints and one of negative, we "resolve" every pair *)
fun crossProduct((posList: linear_ineq list), (negList: linear_ineq list), x: string) =
(* i am having so much fun i feel like i'm back using streams in java *)
    List.concat (
        List.map (fn negConst => 
            List.map (fn posConst => 
                resolve(negConst, posConst, x)
            ) posList
        ) negList
    )

(* 
    format is (vars) <= const, so one is contradictory if
    there are no vars (so, it's 0 on the left side)
    and the right side is not >= 0
    ( 0 <= -5 is contraddictory )
  *)
fun isContradictory(constraints: linear_ineq list) = 
    List.exists(fn(vars, const)=> const < 0 andalso List.all (fn (_, coeff) => coeff = 0) vars) constraints

fun solve((constraints: linear_ineq list), variables: string list) = 
    if isContradictory(constraints) then UNSAT
    else
        case variables of
            [] => SAT 

            | (x::rest) => 
                let
                    val (pos, neg, noX) = partition (constraints, x)
                in
                    if length pos = 0 orelse length neg = 0 then
                        solve(noX, rest)
                    else
                        let
                            val newConstraints = crossProduct(pos, neg, x)
                        in
                            solve(newConstraints @ noX, rest)
                        end
                end

fun check_scenario(constraints) = 
        let
            val vars = getVariables(constraints)
        in
            solve(constraints, vars)
        end

fun verify(f: formula) = 
    let
        val negated_f = negateFormula f
        (* we need to prove that ~f is UNSAT *)
        
        (* list of lists of constraints, in DNF *)
        val scenarios = normaliseFormula negated_f
    in
        if List.all (fn s => check_scenario(s) = UNSAT) scenarios 
        then "VALID implication!!"
        else "INVALID implication. srry."
    end
