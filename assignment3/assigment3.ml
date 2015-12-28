(*Abdillah Ahamada -exchange program *)


(*data structure, a term can be a free variable , or a string (which actually the tree  node) followed by a list of terms  *)
type term = V of string | Node of string * (term list);;

(*------------------------------------------------------------------------------------------------------------------------------------------*)

(*1) Given a signature consisting of symbols and their arities (>= 0) in any suitable form -- either as a list of (symbol, arity) pairs,
 or as a function from symbols to arities,
 write a function check_sig that checks whether the signature is a valid signature (no repeated symbols, arities are non-negative etc.)*)

let first couple = match couple with
(a,b) -> a ;;

let second couple = match couple with
 (a,b) -> b ;;


let rec  member x s = match s with 
	[]-> false 
	|t::r -> if (x=t) then true else (member x r) ;;

let rec  belong_two_times x s = match s with 
	[]-> false 
	|t::r -> if (x=t) && member x (List.tl s)  then true else (belong_two_times x r) ;; 

let rec liste_of_symbol l = match l with
| []-> []
| t ::r -> (first t ):: liste_of_symbol r ;;

(*let rec  liste_of_arity l = match l with
| []-> []
| t ::r -> (second t ):: liste_of_arity r ;;*)

let rec check_sig signature = match signature with
| [] -> true
|  t::r -> if ( ((  belong_two_times  (first t)  (liste_of_symbol signature) ) =true  )  ||  ( (second t) < 0 ) )  then false else 
					true && (check_sig r ) ;;			


(*------------------------------------------------------------------------------------------------------------------------------------------*)
(*2) Given a valid signature (checked using check_sig), 
define a function wfterm that checks that a given preterm is well-formed according to the signature.*)

(*exception Element_not_present;;*)

let rec return_couple symbol signature = match signature with 
[] -> ("", -1) (*maybe use exception ? *)
|(t::r) -> if ( (first t) =symbol ) then t else return_couple symbol r ;;


 let  isVariable s = match s with
 	V(i) -> true 
 	|_ -> false;;
 

let rec wfterm preterm signature = 
 ( if (check_sig signature = false) then false 
else 

	match preterm with
 	V(s)-> true
 	|Node(s,liste ) -> if (  (second (return_couple s signature )) <> (List.length liste) ) then false else wfterm_liste liste signature ) and (*mutuellement dépendantes*) 

 wfterm_liste liste_of_pretem signature =  match liste_of_pretem with
 					[]-> true
 					| (t::r) -> if( (isVariable t ) =true) then true && (wfterm_liste r signature ) else (wfterm t signature ) ;;


(*------------------------------------------------------------------------------------------------------------------------------------------*)
 (*Define functions ht, size and vars that given a well-formed term, return its height, 
 its size and the set of variables appearing in it respectively.  
 Use map, foldl and other such functions as far as possible wherever you use lists.  *)					

let max a b = if (a >= b ) then a else b ;;

let rec contains_just_var l = match l with
 []-> true 
| t::r -> match t with
		Node(s,l) -> false 
		|V(s) -> ( true ) && (contains_just_var r) ;;

let rec ht preterm  = (match preterm with
 V(s) -> 0 
| Node(s,l) ->  1 +  (ht_liste l) ) and (*mutuellement dépendantes*)

  ht_liste liste_of_pretem = match liste_of_pretem with
 [] -> 0 
| (t :: r ) ->  match  t  with 
				V(s) -> max (0) (ht_liste r)  
				|Node(s,l) -> if ( (contains_just_var l) =true ) then (max (1) (ht_liste r) )    else (ht t) ;; 



(*-------------------------------------------------*)

(*À finir de debuguer *)
let rec size preterm =  (match preterm with
 V(s) -> 1
| Node(s,l) -> 1 + (size_liste l) )  and (*mutuellement dépendantes*)

 size_liste liste_of_pretem = match liste_of_pretem with
 [] -> 0 
| (t :: r ) ->  match  t  with 
				V(s) -> (1 + (size_liste r))  
				|Node(s,l) ->  ( (size t) +(size_liste r ) );;

(*-------------------------------------------------*)

let rec union s1 s2 = match (s1,s2) with
	([],[]) -> []
	|([],sprime) -> sprime
	|(sprime,[]) -> sprime
	|(t::r,sb) -> if((member t sb)=false) then t::union r sb else union r sb ;;


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


(*let vars preterm = union( (var preterm) (var preterm) ;;*)

(*------------------------------------------------------------------------------------------------------------------------------------------*)
	(*define the function subst that given a termt and a substitution s ,applies the (Unique homomorphic extension of ) s to t 
	Ensure that subst is efficiently implemented*)


let rec  treatment_node  subst_fonction el = (match el with
 V(var)-> ( subst_fonction (V(var)) )
| Node(a, liste ) -> match liste with
			 [] -> Node(a,[])
			| _ -> Node(a,(treatmentListe (liste) (subst_fonction)  )))  and 

 treatmentListe l s   =match l with
[] -> []
| (t::r) -> match t with
		 V(var) -> s (V(var)):: (treatmentListe (r) (s)  ) 
		| Node(b,l2) -> (treatment_node s (Node(b,l2))) ::(treatmentListe r s ) ;;

				 

let rec subst preterm s =

let map_function = treatment_node s in 
	
	 match preterm with
 V(a) -> (s (V(a)) )
| Node(a, l ) -> Node (a,List.map map_function l);;

(*------------------------------------------------------------------------------------------------------------------------------------------*)
exception Not_UNIFIABLE ;;

let rec return_subsitituion el liste= match liste with
 [] -> el
 |(t::r) -> if( (first t) = el) then (second t ) else return_subsitituion el r ;;

 let create_function a b = (a,b);;

  let create_function_from_couple a = function el -> if ((first a) =el) then (second a ) else el ;;


 let rec equals e f =( match (e,f) with
 (V(a),(V(b))) -> if(V(a)=V(b)) then true else false
 | (V(g),Node(h,l)) -> false 
 |(Node(i,l),V(p)) -> false 
 |(Node(a1,l1),Node(a2,l2)) -> if (a1 <> a2 ) then false else (equals_liste l1 l2 ) ) and 

 equals_liste l3 l4 = match (l3,l4) with
 ([],[]) -> true
 |([],la) -> false 
 |(la,[]) -> false
 |((t1::r1),(t2::r2) ) -> (equals t1 t2 ) && (equals_liste r1 r2 );; 

 (*let return_liste_of_node n = match n with
  Node(a,l) -> l ;;

  let return_operation n = match n with
  | Node(a,l) -> a *)
  


 let rec subst_inside_Node n liste_of_subs = match liste_of_subs with
	[] -> n
 |(t1::r1) -> subst_inside_Node  (subst n (create_function_from_couple  t1)) r1 ;;

let mgu preterm1 preterm2 = 

let rec mgu_prime p1 p2 liste = match (p1,p2) with
			 (V(a),V(b)) -> (match (((return_subsitituion (V(a)) liste )  ) , ((return_subsitituion (V(b)) liste )  ) )  with
							 (V(c),V(d)) -> (create_function (V(c)) (V(d)) ) :: liste 
			 				| (V(c),Node(a,l)) -> if(  ( member (V(c)) (vars (subst_inside_Node  (Node(a,l)) liste ) )) =true ) then raise  Not_UNIFIABLE 
			 									else (create_function (V(c)) (Node(a,l))  ) ::liste 

			 				| (Node(a,l),V(c)) -> if(  ( member (V(c)) (vars (subst_inside_Node  (Node(a,l)) liste ) )) =true ) then raise  Not_UNIFIABLE 
			 									else (create_function (V(c)) (Node(a,l))  ) ::liste 
			 				
			 				|(Node(a1,l1),Node(a2,l2)) -> if ((equals (Node(a1,l1)) (Node(a2,l2))) =false) then  raise  Not_UNIFIABLE 
			 																					else mgu_prime (Node(a1,l1)) (Node(a2,l2))  liste )

			 |(V(q),Node(a3,l3)) -> if(  ( member (V(q)) (vars (Node(a3,l3))) ) =true ) then raise  Not_UNIFIABLE 
			 									else (create_function (V(q)) (Node(a3,l3))  ) ::liste 
			
			 |(Node(a3,l3),V(q)) -> if(  ( member (V(q)) (vars (Node(a3,l3))) ) =true ) then raise  Not_UNIFIABLE 
			 									else (create_function (V(q)) (Node(a3,l3))  ) ::liste 

			|(Node(a4,l5),Node(a6,l7) )-> if (a4<> a6) then raise Not_UNIFIABLE  else (mgu_liste l5 l7 liste ) and 

mgu_liste li1 li2 result  = match (li1,li2) with
([],[])-> []
| (t1::r1,t2::r2) -> (mgu_prime t1 t2 result ) @ ( mgu_liste r1 r2 [] ) in (mgu_prime preterm1 preterm2 [] );;  
