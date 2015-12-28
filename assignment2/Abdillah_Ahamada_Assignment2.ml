(*Abdillah Ahamada  -  exchange program *)


(*This file contains some functions to manipulates abstract propositions *)


(*data structure *)
type prop = Atom of string 
		| T 
		| F
    | Not of prop 
		| And of prop * prop
    | Or of prop * prop 
		| Imply of prop * prop
    | Iff of prop * prop ;;

(*------------------------------------------------------------------------------*)
(* ht: prop -> int, which returns the height of a proposition (syntax tree) *)

let rec ht p = match p with 
							|Atom s -> 0 
							|T-> 0
							|F-> 0
							|Not p1-> 1+ (ht p1 )
							|And(p1,p2)-> 1+ (max (ht p1) (ht p2))
							|Or(p1,p2)-> 1+ (max (ht p1) (ht p2))
							|Iff(p1,p2)-> 1+ (max (ht p1) (ht p2))
							|Imply(p1,p2)-> 1+ (max (ht p1) (ht p2));;	

(*------------------------------------------------------------------------------*) 

(*size: prop ->, which returns the number of nodes in a proposition (syntax tree)*)	

let rec size p = match p with 
							|Atom s -> 1 
							|T-> 1
							|F-> 1
							|Not p1-> 1+ (size p1 )
							|And(p1,p2)-> 1 + (size p1) + (size p2)
							|Or(p1,p2)-> 1 + (size p1) + (size p2)
							|Iff(p1,p2)-> 1 + (size p1) + (size p2)
							|Imply(p1,p2)-> 1 +(size p1) + (size p2)	;;

(*-----------------------------------------------------------------------------------------*) 

(*atoms: prop -> string set, which returns the set of propositional variables that appear in a proposition*)

let rec  member x s = match s with 
	[]-> false 
	|t::r -> if (x=t) then true else (member x r) ;;

let rec union s1 s2 = match (s1,s2) with
	([],[]) -> []
	|([],sprime) -> sprime
	|(sprime,[]) -> sprime
	|(t::r,sb) -> if((member t sb)=false) then t::union r sb else union r sb ;;


let rec atoms p = match p with 
							|Atom s ->[s]
							|T-> []
							|F-> []
							|Not p1-> atoms p1
							|And(p1,p2)-> union (atoms p1)  (atoms p2)
							|Or(p1,p2)-> union (atoms p1)  (atoms p2)
							|Iff(p1,p2)-> union (atoms p1)  (atoms p2)
							|Imply(p1,p2)-> union (atoms p1)  (atoms p2);;

(*-----------------------------------------------------------------------------------------*) 
(*truth: prop -> (string -> bool) -> bool, which evaluates a proposition with respect to a given truth assignment to atoms*)

let rec truth p alpha = match p with 
								Atom s -> alpha s 
								|T-> true
								|F-> false
								|Not p1-> not (truth p1 alpha)
								|And(p1,p2)->  (truth p1 alpha) && (truth p2 alpha)
								|Or(p1,p2)->  (truth p1 alpha) || (truth p2 alpha)
								|Imply(p1,p2)->  (not (truth p1 alpha)) ||  (truth p2 alpha)
								|Iff(p1,p2)->  (truth (Imply(p1,p2)) alpha ) && (truth (Imply(p2,p1)) alpha );;

(*-----------------------------------------------------------------------------------------*) 
(*nnf: prop -> prop, which converts a proposition into negation normal form. *) 

let rec nnf p = match p with
		|Atom s->p
		|T->T
		|F->F
		|And(p1,p2)->And(nnf p1,nnf p2)
		|Or(p1,p2)->Or(nnf p1,nnf p2)
		|Imply(p1,p2)->Or(nnf (Not p1),nnf p2)
		|Iff(p1,p2)->Or(And(nnf (Not p1),nnf (Not p2)),And(nnf p1,nnf p2))
		|Not p1->match p1 with
			|Atom s->p
			|T->F
			|F->T
			|Not p11->nnf p11
			|And(p11,p12)->Or(nnf(Not p11),nnf(Not p12))
			|Or(p11,p12)->And(nnf(Not p11),nnf(Not p12))
			|Imply(p11,p12)->And(nnf p11,nnf(Not p12))
			|Iff(p11,p12)->And(Or(nnf p11,nnf p12),Or(nnf(Not p11),nnf(Not p12)))
;;
(*-----------------------------------------------------------------------------------------*) 
(*cnf: prop -> prop set set, which converts a proposition into conjunctive normal form (POS) as a set of clauses, each of which is a set of literals (a special subset of prop).. *)


(*allow to distribute the or operator *)
let rec  distribute_or p = match p with 
	And (p1a,p1b) -> And (distribute_or p1a , distribute_or p1b)
	|Or(p1,p2) -> (match (p1,p2) with 
							(And(p11,p12),p21) -> distribute_or( And( Or(p11,p21), Or(p12,p21) ))
							|(p11,And(p21,p22)) -> distribute_or (And( Or(p11,p21) ,Or(p11,p22) ))
							|(p11,p21)->  if ( ((distribute_or p11) = p11) && ((distribute_or p21) = p21) ) then p else distribute_or( Or(distribute_or p11,distribute_or p21) ) )

|Atom s -> p 
|T -> p
|F -> p
|Not(pneg) -> Not (distribute_or pneg);;



 

let rec cnf p =match (nnf p) with 
		Atom s -> p 
		|T -> p 
		|F -> p
		|Not (p1) ->  nnf (Not(p1))
		|And(p1,p2) -> And( (cnf p1) , ( cnf p2 ))
		|Or(p1,p2) ->   distribute_or (Or( p1, p2))
		|Imply(p1,p2) ->  Or( cnf (Not p1) , cnf p2)
		|Iff(p1,p2) -> And ( cnf(Imply(p1,p2))  ,cnf(Imply(p2,p1))   );;

(*-----------------------------------------------------------------------------------------*) 

(*dnf: prop -> prop set set,  which converts a proposition into disjunctive normal form (SOP) as a set of terms, each of which is a set of literals (a special subset of prop)..*)

(*allow to distribute the and operator *)
let rec  distribute_and p = match p with 
	Or (p1a,p1b) -> Or (distribute_and p1a , distribute_and p1b)
	|And(p1,p2) -> (match (p1,p2) with 
							(Or(p11,p12),p21) -> distribute_and( Or( And(p11,p21), And(p12,p21) ))
							|(p11,Or(p21,p22)) -> distribute_and (Or( And(p11,p21) ,And(p11,p22) ))
							|(p11,p21)->  if ( ((distribute_and p11) = p11) && ((distribute_and p21) = p21) ) then p else distribute_and( And(distribute_and p11,distribute_and p21) ) )

|Atom s -> p 
|T -> p
|F -> p
|Not(pneg) -> Not (distribute_and pneg);;


let rec dnf p =match (nnf p) with 
		Atom s -> p 
		|T -> p 
		|F -> p
		|Not (p1) ->  nnf (Not(p1))
		|Or(p1,p2) -> Or( (dnf p1) , ( dnf p2 ))
		|And(p1,p2) ->   distribute_and (And(p1,p2))
		|Imply(p1,p2) ->  Or( dnf (Not p1) , dnf p2)
		|Iff(p1,p2) -> And ( dnf(Imply(p1,p2))  ,dnf(Imply(p2,p1))   );;

(*-----------------------------------------------------------------------------------------*) 


(*isSatisfiable: prop -> bool, which checks if a proposition is satisfiable*)


(*****-------- This section allows to create a function wich maps all atoms with  a boolean  value  ------------ *)
let propEmpty = function x -> false ;;

(*add an over key to the function func2 which is mapping with value v *)
let add func2 (key:string) (v:bool)=function kprime -> if kprime=key then v else func2 key;;



(*create the function which maps each element of liste with with corresponding value in tabBool*)
let rec create_fonction_truth_table liste tabBool = match liste with 
	[] -> propEmpty 
	|_ ->  if ((List.length liste)=1) then (add  (propEmpty )  (List.hd liste) (List.hd tabBool) ) else add (create_fonction_truth_table (List.tl liste) (List.tl tabBool)) (List.hd liste) (List.hd tabBool);;


let rec insert x liste = match liste with 
			|[] ->[]
			|t::r -> (x::t)::insert x r;;

(*create a truth  table of length n *)
let rec create_truth_table n = match n with 
	0 -> [[]]
	|1 -> [[true];[false]]
	|_ -> (insert true (create_truth_table (n-1) ))@ (insert false(create_truth_table (n-1) ));;


(*use create_fonction_truth_table function to create  a list of function for every line of truth table  *)
let rec create_all_function_truth_table liste truth_table = match truth_table with 
	[[]] -> [[]]
	|[] -> [[]]
	|t::r -> [create_fonction_truth_table liste t] :: (create_all_function_truth_table liste r) ;;



let isSatisfiable p = 
	let table = create_all_function_truth_table (atoms p) (create_truth_table  (List.length (atoms p))) in 

	let noeffect s = false in 

	let rec check p1 tab = match tab with 
	[[]] -> (truth p1 noeffect) 
	|[] -> (truth p1 noeffect ) 
	|(t::r) -> if ((truth p1 (List.hd t))=true) then true else ( check p1 r )  in (check p table);;

	(*-----------------------------------------------------------------------------------------*)
(*isTautology :prop -> bool ,which checks if a proposition is a tautology*)

let  isTautology p = 
let table = create_all_function_truth_table (atoms p) (create_truth_table  (List.length (atoms p))) in 

	let noeffect s = false in 

let rec check p1 tab = match tab with 
	[[]] -> (truth p1 noeffect) 
	|[] -> (truth p1 noeffect ) 
	|(t::r) ->  (truth p1 (List.hd t))&& ( check p1 r )  in (check p table);;

	(*-----------------------------------------------------------------------------------------*)

	(*isEquivalent: prop->prop->bool which cheks if two propositions are logically equivalent*) (*verifier que les deux liste d'atom sont equivalent ?*)

let isEquivalent pa pb = 

let table = create_all_function_truth_table ( union (atoms pa) (atoms pb)) (create_truth_table  (List.length (union (atoms pa) (atoms pb)))) in 

let noeffect s = false in 


let rec check p1 p2 tab = match tab with 
	[[]] -> (truth p1 noeffect) = (truth p2 noeffect)
	|[] -> (truth p1 noeffect ) =(truth p2 noeffect) 
	|(t::r) -> ( ( (truth p1 (List.hd t)) =  (truth p2 (List.hd t))  ) ) && ( check p1 p2 r )  in (check pa pb table);;

	(*-----------------------------------------------------------------------------------------*)

	(*entails :prop -> prop -> bool which checks if second proposition is a logical consequence of the first proposition *)

	let entails pa pb = 

let table = create_all_function_truth_table ( union (atoms pa) (atoms pb)) (create_truth_table  (List.length (union (atoms pa) (atoms pb)))) in 

let noeffect s = false in 


let rec check p1 p2 tab = match tab with 
	[[]] -> (truth p1 noeffect) = (truth p2 noeffect)
	|[] -> (truth p1 noeffect ) =(truth p2 noeffect) 
	|(t::r) -> ( ( (not (truth p1 (List.hd t))) ||  (truth p2 (List.hd t))  ) ) && ( check p1 p2 r )  in (check pa pb table);;
 
	
