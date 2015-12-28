(*========================== DATA STRUCTURE  =======================================*)



type  term = Var of string 
| Integer of int 
| Bool of bool 
| Unit of unit 
|Plus of term * term 
| Mul of term * term 
|Minus of term *term
|Div of term *term 
|And of term * term 
|Or of term * term
|Not of term
|Tuple of term * term
|ProjectionX of term
|ProjectionY of term 
|Equal of term * term 
|IfThenElse of term * term * term  
|Abstract of string * term 
|App of term * (term ) ;;


type opCode = 
Ret
|Call 
|Op_plus 
| Op_mul
|Op_and 
|Op_minus
|Op_div
|Op_or
|Op_not
|Op_equal 
|Op_If_then_else 
|Op_tuple
|Op_projeX
|Op_projeY
| Lookup of string  
|CLOS of ( string  ) * (opCode list ) 
|Const of term ;;

type table = Table of string * term ;;

type closure  = (string ) * (opCode list  ) *  table list ;;

type contentStack =  T of term | C of closure ;;

type stack = (contentStack list);;


type dump = stack * table * (opCode list  ) ;;
(*===================================== END DATASTRUCTURE ======================================================*)


(*produce compile code *)
let rec compileCode listeOfTerm = match listeOfTerm with
 [] -> []
 |hd::tl -> (match hd  with
 	| Var(a) -> Lookup(a):: (compileCode tl )
 	| Integer(i) -> Const( Integer(i) ):: (compileCode tl )
 	|Bool(b) ->  Const(Bool(b)):: ( compileCode tl )
 	|Unit(b) ->  Const(Unit(b)):: ( compileCode tl ) 
 	|Plus(t1,t2) ->  (compileCode [t1]) @ (compileCode [t2]) @ [ Op_plus ] @(compileCode tl )
 	|Mul(t1,t2) ->  (compileCode [t1]) @ (compileCode [t2]) @ [ Op_mul ] @(compileCode tl )
 	|Minus(t1,t2) ->  (compileCode [t1]) @ (compileCode [t2]) @ [ Op_minus ] @(compileCode tl )
 	|Div(t1,t2) ->  (compileCode [t1]) @ (compileCode [t2]) @ [ Op_div ] @(compileCode tl )
 	|And(t1,t2) ->  (compileCode [t1]) @ (compileCode [t2]) @ [ Op_and ] @(compileCode tl )
	|Or(t1,t2) ->  (compileCode [t1]) @ (compileCode [t2]) @ [ Op_or ] @(compileCode tl )
	|Not(t1) ->  (compileCode [t1]) @  [ Op_not ] @(compileCode tl )
	|Equal(t1,t2) ->  (compileCode [t1]) @ (compileCode [t2]) @ [ Op_equal ] @(compileCode tl )
	|Abstract ( var,termListe )   ->  [CLOS( var, compileCode [termListe] @ [Ret]  )] @ (compileCode tl ) 
	|App ( u , t1 )  -> (compileCode [u] ) @ (compileCode [t1]) @ [Call] @ (compileCode tl)
	|Tuple (a,b) ->  (compileCode [a]) @ (compileCode [b]) @ [ Op_tuple ] @(compileCode tl )
	|ProjectionX(Tuple(a,b)) ->  (compileCode [a]) @ (compileCode [b]) @ [ Op_projeX ] @(compileCode tl )
	|ProjectionY(Tuple(a,b)) ->  (compileCode [a]) @ (compileCode [b]) @ [ Op_projeY ] @(compileCode tl )
	|IfThenElse(condition,expr1 ,expr2) -> ( compileCode [expr1] ) @ (compileCode [expr2] ) @ ( compileCode [condition] )@ [Op_If_then_else] @ (compileCode tl) ) ;;


exception ArgumentOrfunctionMissing;;
exception SecondElementOfStackNotAClosure;;



(*======================CALL CONTEXT===================================================*)
(*create mapping var x with value closure ! usefull for call function*)
let createMappingTable stck env = 

	let secndArg l =  match l with
	 t::r -> List.hd r in 
	
	 let getTerm p = match p with
	  T(term1) -> term1 in 

	if (List.length stck < 2) then raise  ArgumentOrfunctionMissing 
	else ( match (secndArg stck) with
		C(x,compCodeDashDash,tableDash) -> 	Table(x,(getTerm (List.hd stck) ))::env 
		| _ ->  raise SecondElementOfStackNotAClosure);;


let getCompileCodeFromClosure stck = 

	let secondArg l =  match l with
	 t::r -> List.hd r in 
	
	if (List.length stck < 2) then raise  ArgumentOrfunctionMissing 
	else (match (secondArg stck ) with 
		C(x,compCodeDashDash,tableDash) -> compCodeDashDash
		| _ ->raise SecondElementOfStackNotAClosure );;


(*=========================================RETURN CONTEXT===========================*)
let getFirstElementTriple t = match t with
 (a,b,c) -> a ;;

 let getSecondElementTriple t = match t with
 (a,b,c) -> b ;;

 let getThirdElementTriple t = match t with
 (a,b,c) -> c ;;



(*=====================================MAIN OPERATION (PLUS , MUL, ETC ...)=====================================================*)

let getFirstElementStack stck  = List.hd stck;;

let getSecondElementStack stck =  List.hd (List.tl stck) ;;
let getThirdElementStack stck =  List.hd (List.tl (List.tl stck)) ;;

let stackAfterPop2Element stck = List.tl (List.tl stck) ;;

let rec searchValueInEnv var env = match env with
 [] -> T(Var(var)) 
| t::r  -> (match t with
		 Table(a,b) -> if a = var then T(b) else searchValueInEnv var r );;
	
(*=====================================================================================================================*)



let rec evaluateCompileCode stck env compCode dmp = match compCode with
  []-> (stck,env,compCode,dmp)
 | t::r -> (match t with
 	| Lookup(x) -> ( evaluateCompileCode ( (searchValueInEnv x env )::stck) env r dmp )
 	
 	|Const(c)-> ( evaluateCompileCode (T(c)::stck) env r dmp )
 	
 	|CLOS(a,body) -> ( evaluateCompileCode (  C(a,body,env)::stck) env r dmp )
 	
 	|Call -> (evaluateCompileCode []  (createMappingTable stck env)  (getCompileCodeFromClosure stck)  (((stackAfterPop2Element stck),env,r)::dmp ) ) 
 	
 	|Ret -> (evaluateCompileCode((List.hd stck)::(getFirstElementTriple  (List.hd dmp)) ) (getSecondElementTriple (List.hd dmp) ) (getThirdElementTriple (List.hd dmp) ) (List.tl dmp) )
 	
 	|Op_plus -> (match (getFirstElementStack stck),( getSecondElementStack stck ) with
 		 T(Integer(a)),T(Integer(b)) ->   evaluateCompileCode  (T(Integer(a+b))::(stackAfterPop2Element stck)) env r dmp )
 	
 	|Op_mul -> (match (getFirstElementStack stck),( getSecondElementStack stck ) with
 		 T(Integer(a)),T(Integer(b)) ->   evaluateCompileCode  (T(Integer(a*b))::(stackAfterPop2Element stck)) env r dmp )
 	
 	|Op_minus -> (match (getFirstElementStack stck),( getSecondElementStack stck ) with
 		 T(Integer(a)),T(Integer(b)) ->   evaluateCompileCode  (T(Integer(b-a))::(stackAfterPop2Element stck)) env r dmp )
 	
 	|Op_div -> (match (getFirstElementStack stck),( getSecondElementStack stck ) with
 		 T(Integer(a)),T(Integer(b)) ->   evaluateCompileCode  (T(Integer(b/a))::(stackAfterPop2Element stck)) env r dmp )
 	
 	|Op_and -> (match (getFirstElementStack stck),( getSecondElementStack stck ) with
 		 T(Bool(a)),T(Bool(b)) ->   evaluateCompileCode  (T(Bool(a && b))::(stackAfterPop2Element stck)) env r dmp )
 	
 	|Op_or -> (match (getFirstElementStack stck),( getSecondElementStack stck ) with
 		 T(Bool(a)),T(Bool(b)) ->   evaluateCompileCode  (T(Bool(a || b))::(stackAfterPop2Element stck)) env r dmp )
 	
 	|Op_not -> (match (getFirstElementStack stck) with
 		 T(Bool(a)) ->   evaluateCompileCode  (T(Bool(not a))::( List.tl stck)) env r dmp )

 	|Op_equal -> (match (getFirstElementStack stck),( getSecondElementStack stck ) with
 		 T(Bool(a)),T(Bool(b)) ->   evaluateCompileCode  (T(Bool(a = b))::(stackAfterPop2Element stck)) env r dmp 
 		|T(Integer(a)),T(Integer(b)) ->   evaluateCompileCode  (T(Bool(a=b))::(stackAfterPop2Element stck)) env r dmp )

 	|Op_tuple ->  (match (getFirstElementStack stck),( getSecondElementStack stck ) with
 		 T(Bool(a)),T(Bool(b)) ->   evaluateCompileCode (T(Tuple(Bool(b),Bool(a)))::(stackAfterPop2Element stck)) env r dmp 
 		|T(Integer(a)),T(Integer(b)) ->  evaluateCompileCode (T(Tuple(Integer(b),Integer(a)))::(stackAfterPop2Element stck))  env r dmp 
 		|T(Integer(a)),T(Bool(b)) -> evaluateCompileCode (T(Tuple(Bool(b),Integer(a)))::(stackAfterPop2Element stck))  env r dmp
 		|T(Bool(a)),T(Integer(b))-> evaluateCompileCode (T(Tuple(Integer(b),Bool(a)))::(stackAfterPop2Element stck))  env r dmp  ) 

 	|Op_projeX ->( match  ( getSecondElementStack stck )with
 	  	T(Bool(a)) -> evaluateCompileCode ( T(Bool(a))::(stackAfterPop2Element stck)) env r dmp 
 		|T(Integer(a)) -> evaluateCompileCode ( T(Integer(a))::(stackAfterPop2Element stck)) env r dmp )

 	|Op_projeY ->( match  (getFirstElementStack stck) with
 	  	T(Bool(a)) -> evaluateCompileCode ( T(Bool(a))::(stackAfterPop2Element stck)) env r dmp 
 		|T(Integer(a)) -> evaluateCompileCode ( T(Integer(a))::(stackAfterPop2Element stck)) env r dmp )

	|Op_If_then_else -> (match (getFirstElementStack stck) with
 		 T(Bool(a)) ->   if (a = true) then (evaluateCompileCode [(getThirdElementStack stck)] env r dmp ) else (evaluateCompileCode [ (getSecondElementStack stck) ] env r dmp )));; 


(*check with app working well *)

let main term1 = match (evaluateCompileCode [] [] (compileCode term1) [] )with
(a,b,c,d) -> a;;
