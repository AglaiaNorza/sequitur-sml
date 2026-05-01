use "data.sml";

(* --------------------- utils ------------------------ *)
(* 
* substitutes to move all 'known' variables to the constant side of the inequality 
* starting with the original constant 'k', it subtracts (coefficient * assigned_value) 
* for every term whose variable is already in the model
* (transforms a multi-variable inequality (eg cx*x + c1*v1 + ... <= k) 
* into a simplified bound (cx*x <= k_new) for the variable currently being solved
*)
fun evaluate_rest(vars, model) k =
    List.foldl (fn ((v, c), acc) =>
        case List.find (fn (m_var, _) => m_var = v) model of
            SOME(_, value) => acc - (c * value)
          | NONE => acc
    ) k vars

(* finds an int that satisfies all constraints for variable 'x' given a partial model *)
fun find_valid_int(x, constraints, model) =
    let
        fun get_limit((vars, k)) =
            let
                val SOME(_, coeff) = List.find (fn (v, _) => v = x) vars
                val remaining_k = evaluate_rest(List.filter (fn (v, _) => v <> x) vars, model) k
            in
                (coeff, remaining_k)
            end

        val limits = List.map get_limit constraints
        
        val upper_bounds = List.filter (fn (c, _) => c > 0) limits
        val lower_bounds = List.filter (fn (c, _) => c < 0) limits

        val max_v_opt = case upper_bounds of
            [] => NONE
          | (c,k)::rest => SOME (List.foldl (fn ((c, k), cur) => Int.min(cur, k div c)) (k div c) rest)
        
        val min_v_opt = case lower_bounds of
            [] => NONE
          | (c,k)::rest => SOME (List.foldl (fn ((c, k), cur) => Int.max(cur, ~( (~k) div c ))) (~( (~k) div c )) rest)
    in
        case (min_v_opt, max_v_opt) of
            (SOME min_val, _) => min_val   (* pick the tightest lower bound if it exists *)
          | (NONE, SOME max_val) => max_val  (* if only upper bounded, pick the upper bound *)
          | (NONE, NONE) => 0  (* if completely unbounded, pick a clean 0 *)
    end

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

(* --------------------- core ------------------------ *)

(* returns SOME () if SAT, NONE if UNSAT *)
fun solve(constraints, []) = if isContradictory(constraints) then NONE else SOME ()
  | solve(constraints, x::rest) =
    if isContradictory(constraints) then NONE
    else
        let val (pos, neg, noX) = partition (constraints, x)
        in solve(crossProduct(pos, neg, x) @ noX, rest) end

(* alternative solve function that returns SOME model or NONE *)
fun solve_with_model(constraints, []) = if isContradictory(constraints) then NONE else SOME []
  | solve_with_model(constraints, x::rest) =
    if isContradictory(constraints) then NONE
    else
        let
            val (pos, neg, noX) = partition (constraints, x)
            val projected = crossProduct(pos, neg, x) @ noX
        in
            case solve_with_model(projected, rest) of
                NONE => NONE
                (* we look back at the constraints involving 'x' and calculate its 
                * valid range based on the values already in the model *)
              | SOME model => SOME ((x, find_valid_int(x, pos @ neg, model)) :: model)
        end

fun check_scenario(constraints) = 
        let
            val vars = getVariables(constraints)
        in
            solve(constraints, vars)
        end


(* --------------------- main runners ------------------------ *)

(* handler that takes a solver function and a result-formatter *)
fun generic_verify solver formatter (f: formula) =
    let
        val negated_f = negateFormula f
        val scenarios = normaliseFormula negated_f
        
        fun loop [] = NONE
          | loop (s::ss) =
            case solver(s, getVariables s) of
                 SOME x => SOME x
               | NONE   => loop ss
    in
        case loop scenarios of
            NONE => "VALID implication!!"
          | SOME result => formatter result
    end


(* "simple" version: we don't need a countermodel *)
fun verify f = 
    generic_verify solve (fn _ => "INVALID implication. srry.") f

(* witness version: uses backtracking solver *)
fun verify_with_counterexample f =
    let
        fun model_format model =
            let val str = String.concatWith ", " 
                (List.map (fn (v, i) => v ^ "=" ^ Int.toString i) model)
            in "INVALID implication. Counterexample: { " ^ str ^ " }" end
    in
        generic_verify solve_with_model model_format f
    end
