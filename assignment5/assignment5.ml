
(*data structure*)
type term = V of string | Node of string * (term list);;
type formula = Predicate of string *(term list);;
type fact = Head of formula;;
type rule = formula *( formula list );;
type clause = F of fact | R of rule ;;
type programme  = Clause of (clause list ) ;;


(**********************************************************BEGIN MGU FROM ASSIGNMENT 3*************************************************************************************)


let rec  member x s = match s with 
	[]-> false 
	|t::r -> if (x=t) then true else (member x r) ;;


let rec union s1 s2 = match (s1,s2) with
	([],[]) -> []
	|([],sprime) -> sprime
	|(sprime,[]) -> sprime
	|(t::r,sb) -> if((member t sb)=false) then t::union r sb else union r sb ;;

let first couple = match couple with
(a,b) -> a ;;

let second couple = match couple with
 (a,b) -> b ;;


let rec var preterm =  (match preterm with
 V(s) -> [s]
| Node(s,l) -> (vars_liste l)  ) and (*mutuellement dépendantes*)

 vars_liste liste_of_pretem = match liste_of_pretem with
 [] -> []
| (t :: r ) ->  match  t  with 
				V(s) -> union ([s]) ((vars_liste r)) 
				|Node(s,l) -> union (var  t)  (vars_liste r) ;; 


let create_vars a = V(a);;

let vars preterm = List.map  create_vars (var preterm );;	

let rec subssof x xs= match xs with
			[]->x
			|(i,j)::ps->if i=x then j else subssof x ps;;
let rec subst s t=match t with 
		V v ->subssof t s 
		|Node (u,ls)-> Node (u,List.map (subst s) ls);;
exception NOT_UNIFIABLE;;
let mgu t1 t2 =let rec check arr (t11,t22)=
					let rec process arr liss=match liss with 
								[]->arr
								|xxx::xss-> process (check arr xxx) xss in  
					if(t11=t22) then arr else(
						match (t11,t22) with
						(Node (a,l1),Node (b,l2))->if(a=b) then 
						process arr (List.combine l1 l2)
						else
						raise NOT_UNIFIABLE
						|(V a,V b)->if a=b then arr else if (subssof t11 arr)=t11 && (subssof t22 arr)=t22 then 
									arr@[(t11,t22)]
									else if(subssof t11 arr)=t11 && (subssof t22 arr)!=t22 then(
								if(member t11 (vars (subssof t22 arr))) then raise NOT_UNIFIABLE 
								else arr@[(t11,(subssof t11 arr))]
								)
								else if(subssof t22 arr)=t22 && (subssof t11 arr)!=t11 then(
								if(member t22 (vars (subssof t11 arr))) then raise NOT_UNIFIABLE 
								else arr@[(t22,(subssof t22 arr))]
								)
								else(
									if((subssof t11 arr)=(subssof t22 arr)) then 
									arr else 
									raise NOT_UNIFIABLE
								)
						|(V a,Node (b,l2))->( if((subssof t11 arr)=t22) then arr else if  (member t11 (vars (t22)))
									then 	raise NOT_UNIFIABLE
									else 
										arr@[(t11,t22)]
									)
						|(Node (b,l2),V a)->( if((subssof t22 arr)=t11) then arr else if  (member t22 (vars (t11)))
									then 	raise NOT_UNIFIABLE
									else 
										arr@[(t22,t11)]
									)
						)
						
					in
					check [] (t1,t2);;



(**********************************************************END MGU FROM ASSIGNMENT 3*************************************************************************************)

exception Fact_OR_RULE_DONT_BELONG_TO_PROGRAM of string ;;
exception PREDICATE_SYMBOL_DONT_BELONG_TO_PROGRAM of string ;;


(*treatment of querry which match with a fact, see again the case if node(a)=node(b) *)
let rec  mguliste listeVarFact listeArgQuerry = match (listeVarFact,listeArgQuerry) with
 ([],[])-> []
| (t1::r1,t2::r2) -> (match (t1,t2) with
					 (Node(a,[]),Node(b,[])) -> if(Node(a,[])=Node(b,[])) then [(Node(a,[]),Node(b,[]))]:: (mguliste r1 r2) else (mgu t1 t2)::(mguliste r1 r2)
					 |(_,_) -> (mgu t1 t2)::(mguliste r1 r2));;


(*husband(X,Y):-male(X) : for this example , this function takes [x,y] and [x] as parameters and indicates at which positon is x(here : 0)*)
let rec varBelongTO listeVarHead varelementbody = if ( (List.mem varelementbody listeVarHead )=false ) then -1 else
( match listeVarHead with
	| (t1::r1) -> if (t1=varelementbody) then 0 else 1 + (varBelongTO r1 varelementbody));;

(*return element which is at pos pos in the list*)
let rec returnElementAtPOs liste pos= match liste with
(t1::r1) -> if (pos=0) then t1 else returnElementAtPOs r1 (pos-1);;



(* rule : husband(X,Y):-male(X),married(x,y). Querry : husband("p",D) , 
This function takes as argument [x,y] , [x] and return ["p"] in case of male(x) And takes [X,Y] && [x,y] in case of marrried(x,y) and  return ["p",D] in case of *)
let rec buildListeGoodArdument listeVariable listeBodyOfRule listeArgumentQuerry = match listeBodyOfRule with
 [] -> []
| (t1::r1) -> if ( (varBelongTO  listeVariable t1 ) <> -1 ) then (returnElementAtPOs listeArgumentQuerry  (varBelongTO  listeVariable t1 )) ::
	(buildListeGoodArdument listeVariable r1 listeArgumentQuerry) else t1::(buildListeGoodArdument listeVariable r1 listeArgumentQuerry);;



(*indicate if a fact or a rule belong to the program *)
	let rec factOrRuleBelongToProgram factOrRule program = match program with
	 [] -> false
	| (t1::r1)  -> ( match (t1,factOrRule) with
		 (F( Head( Predicate(p1,l1) ) ), Predicate(p2,l2) )  ->  if ( (p1=p2) && (List.length l1 = List.length l2 ) )then true else (factOrRuleBelongToProgram factOrRule r1)
		|  (  R(Predicate(sympolePredicate,listeVarHeadOfRule),listeBodyOfRule), Predicate(p3,l3) ) ->  if ( (sympolePredicate=p3)  && (List.length listeVarHeadOfRule= List.length l3) ) then true else (factOrRuleBelongToProgram factOrRule r1) );;

(*return true  if  factOrrule  is a rule , otherwise false *)
let rec  isRule  factOrRule  program = match program with
 [] -> false 
| (t1::r1) -> ( match (t1,factOrRule) with
(F( Head( Predicate(p1,l1) ) ), Predicate(p2,l2) )  ->  if ( (p1=p2) && (List.length l1 = List.length l2 ) )then false else (isRule factOrRule r1)
|( R(Predicate(sympolePredicate,listeVarHeadOfRule),listeBodyOfRule), Predicate(p3,l3)) ->  if ( (sympolePredicate=p3) && (List.length listeVarHeadOfRule= List.length l3)) then true
				else (isRule factOrRule r1) );;


(*return string which represente symbol of a predicate p *)
let returnSymbolPredicate p = match p with
 Predicate(p1,l1) -> p1;;

(*return liste which represente liste of var or constante of anny predicate *)
 let returnVarOfPredicate p = match p with
  Predicate(p1,l1) -> l1;;


(*let rec substituteVaroableWithGoodElement lvar larg= match (lvar,larg) with
([],[])->[]
| (V(a)::r1,V(b)::r2) -> V(a)::(substituteVaroableWithGoodElement r1  r2)
| (Node(a1,l1)::r3, V(b1)::r4)-> Node(a1,l1)::(substituteVaroableWithGoodElement r3 r4)
| (V(b2)::r5,Node(a2,l2)::r6)-> Node(a2,l2)::(substituteVaroableWithGoodElement r5 r6)
|(Node(a3,l3)::r7,Node(a4,l4)::r8) -> Node(a3,l3)::(substituteVaroableWithGoodElement r7 r8);;*)


(*THis function return liste of all finding result*)
let rec  evaluate program programbis querry = ( match programbis with
 [] -> []
| (head1::tail1) -> (match (head1,querry) with
	 (  F (Head( Predicate(p1,l1) )) ,  Predicate(p2,l2) ) -> if ( (p1=p2) && (List.length l1 = List.length l2 ) ) then 
	 																				(try (mguliste l1 l2)::(evaluate program tail1 querry ) with 
	 																					NOT_UNIFIABLE -> (evaluate program tail1 querry )
	 																					|_ -> (mguliste l1 l2)::(evaluate program tail1 querry ))
	 																					else (evaluate program tail1 querry ) 
	
	| (  R(Predicate(sympolePredicate,listeVarHeadOfRule),listeBodyOfRule), Predicate(p3,l3)  )-> if ( (sympolePredicate=p3) && (List.length listeVarHeadOfRule = List.length l3) ) then 
																		(try  (mguRuleListe  program tail1 listeVarHeadOfRule listeBodyOfRule l3)@(evaluate program tail1 querry ) with
																		NOT_UNIFIABLE -> (evaluate program tail1 querry )
																		| _  ->  (mguRuleListe  program tail1 listeVarHeadOfRule listeBodyOfRule l3)@(evaluate program tail1 querry ) )
																								else (evaluate program tail1 querry)) ) and 


 mguRuleListe  program programbis listeVariable listeBodyOfRule listeArgumentQuerry = match listeBodyOfRule with
 []-> []
|(t1::r1) -> if ( (factOrRuleBelongToProgram t1 program )=true) then if ( (isRule t1 program )=true) then 
(evaluate program program (Predicate( (returnSymbolPredicate t1) , (buildListeGoodArdument listeVariable  (returnVarOfPredicate t1) listeArgumentQuerry ))))@
(mguRuleListe program program listeVariable r1 listeArgumentQuerry)
else (evaluate program program (Predicate( (returnSymbolPredicate t1) , (buildListeGoodArdument listeVariable  (returnVarOfPredicate t1) listeArgumentQuerry ))))@
(mguRuleListe program program listeVariable r1 listeArgumentQuerry) 
						else  raise  (Fact_OR_RULE_DONT_BELONG_TO_PROGRAM (returnSymbolPredicate t1) ) ;;


(*=======================================presentation of result final=====================================================================================*)						

(*indicate if pattern [Node("patteer",[]),Node("patteer",[])] belong to liste of result *)
let rec  containPattern liste pattern = ( match liste with
 [] -> false 
| (t1::r1) -> containPatternListeOne r1  t1 pattern ) and  

 containPatternListeOne tailOfInitialListe l p  = match l  with
	 [] -> (containPattern tailOfInitialListe p)
	| (hd::tl) -> if hd =  (Node(p,[]),(Node(p,[])) ) then true else ( containPatternListeOne tailOfInitialListe tl p ) ;;


let rec containsJustFreeVariable l = match l with
 [] -> true
| hd ::tl -> ( match hd with
	 V(a)-> containsJustFreeVariable tl 
	| _ -> false );; 



(*this function return a list of all good result(without ducplication) *)
let createResultForFreevariable program querry = 

let nbElementQuerry querr = match querr with
	Predicate(p,l) -> List.length l  in 

let rec takeGoodresult l  = match l with
[] -> []
| t1::r1 ->   if ( (List.length t1) = (nbElementQuerry querry) ) then (union [t1] (takeGoodresult r1) ) else (takeGoodresult r1) in 



let rec returnOccurenceOne t1 var =( match t1 with
	 [] -> []
	| (hd::tl) -> if  ( (first hd)= var ) then union [t1] (returnOccurenceOne tl var) else ( returnOccurenceOne tl var ) ) in 

let rec returnOccurenceVartwo l1 var = match l1 with
 [] -> []
| t1::r1 -> (returnOccurenceOne t1 var) @(returnOccurenceVartwo r1 var)   in 

let rec returnOccurenceVar l5 var = match l5 with
[] -> []
| j::k -> (returnOccurenceVartwo j var )@(returnOccurenceVar k var) in 


let rec rfinal  pr querr qu  = match qu with
[]  -> []
| (t2::r2) -> ( returnOccurenceVar (takeGoodresult (evaluate pr pr querr)) (t2) )@ (rfinal pr querr r2)

in ( rfinal program querry (returnVarOfPredicate querry) );;




let evaluateFinal program querry = if ( ( factOrRuleBelongToProgram querry program ) =true ) then 

if (  (containsJustFreeVariable (returnVarOfPredicate querry ))=true) then (createResultForFreevariable program querry)
															else []

else 
	raise (PREDICATE_SYMBOL_DONT_BELONG_TO_PROGRAM (returnSymbolPredicate querry)) ;;


(*write unification function between all list which are from evaluate*)
