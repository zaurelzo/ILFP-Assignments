let alpha = [("or",2);("plus",2);("moins",2);("not",1)];;
let beta = [("or",2);("plus",2);("moins",-2);("not",1)];;
let gama = [("or",2);("plus",0);("moins",4);("not",1)];;
let omega = [("or",2);("plus",2);("moins",4);("or",1)];;



(**=========================1 )test check_sig=====================================*) 

check_sig  alpha ;;(*true*) 
check_sig  beta ;;(*false,negative arity*) 
check_sig  gama ;;(*true*)
check_sig  omega ;;(*false,repeated symbol *) 

(*============================ 2)test wfterm =================================================*)



let signature1 = [("or",2);("plus",2);("moins",2);("not",1);("null",0)];; 
let signature2 = [("or",2);("plus",3);("moins",2);("not",2);("null",0)];; 

let t1 = V ("var1");;
let t2 = Node ("or",[V ("a");V("b")]) ;;
let t3 = Node ("plus" , [V("a"); Node("not",[V("b")])]) ;;
let t4 = Node ("plus" , [  Node("or",[V("k");V("l")])   ; Node("not",[V("b")])] ) ;; 
let t5 = Node ("or" , [  Node("plus",[V("a");V("b");V("c")])  ; Node( "plus" , [V("a") ; Node("not",[V("a");V("b")])] )  ]) ;;
let t6 = Node ("or" , [  Node("plus",[V("a");V("b")])  ; Node( "plus" , [V("a") ; Node("not",[V("a")])] )  ]) ;;
let t7 = Node ("or" , [  Node("plus",[V("a");V("b")])  ; Node( "plus" , [ V("a") ; Node( "moins",[V("a");Node( "not"  ,[V("a")] ) ])] )  ]) ;;
let t8 = Node ("or",[V ("a");V("b");V("c")]) ;;

wfterm t1 signature1 ;;(*true,because juste variable*)
wfterm t2 signature1 ;;(*true,because we have two variable*) 
wfterm t3 signature1 ;;(*true,because "plus" has arity 2 and "not" has arity 1*)
wfterm t4 signature1 ;;(*true,plus arity 2 ,or arity 2 ,not arity 1*)  
wfterm t5 signature1 ;;(*false,because plus has 3 argument and should have 2 *) 
wfterm t5 signature2 ;;(*true*) 


(*============================ 3)Test ht ,size ,var =============================================*)

ht t1;;(*0*)
size t1;;(*1*)
vars t1;;(*var1*)

ht t2;;(*1*)
size t2;;(*3*)
vars t2 ;;

ht t3;;(*2*)
size t3;;(*4*)
vars t3;;

ht t4;;(*2*)
size t4;;(*6*)
vars t4 ;; 

ht t6;;(*3*)
size t6;;(*8*)
vars t6;;

ht t7;;(*4*)
size t7;;(*10*)
vars t7;;


(*=========================== 4 ) subst ==================================================*)


(*substitute one varible *)
let myfun el = if (el= V("a")) then Node("+" , [V("alpha"); V("beta")])  else el ;;

subst (V("a")) myfun ;;
subst (Node("NULL",[])) myfun;;
subst t1 myfun ;; 
subst t2 myfun ;;
subst t3 myfun ;;  
subst t4 myfun ;;  
subst t5 myfun ;; 

(* a) composition of substitutions*)
let myfun2 el  = match el with
V("x") -> Node ("+", [Node ("1", []); Node ("0", [])])
| V("y") -> Node ("-", [Node ("0", []); Node ("1", [])])
| _ -> el ;;

subst (Node ("+", [Node ("-", [V "x"; Node ("1", [])]); Node ("+", [V "y"; Node ("0", [])])])) myfun2 ;;

(*======================================== 5) mgu ===========================================================*)

mgu (V "x") (V "y");;
mgu (V "x") (Node ("1", []));;
mgu (Node ("1", [])) (Node ("0", []));;
mgu (Node ("1", [])) (Node ("1", []));;

mgu (Node ("+", [V "x"; Node ("+", [V "y"; Node ("0", [])])])) (Node ("+", [Node ("-", [Node ("1", []); V "z"]); Node ("+", [V "w"; Node ("0", [])])]));;(*a*)

mgu (Node ("+", [V "x"; Node ("+", [V "y"; Node ("0", [])])])) (Node ("+", [Node ("-", [Node ("1", []); V "z"]); Node ("+", [Node ("0", []); V "w"])]));;

mgu (Node ("+", [V "x"; Node ("+", [V "y"; Node ("0", [])])])) (Node ("+", [Node ("-", [Node ("1", []); V "z"]); Node ("+", [V "w"; Node ("1", [])])]));;(*c *)


mgu (Node ("+", [V "x"; Node ("+", [V "y"; Node ("0", [])])])) (Node ("+", [Node ("-", [Node ("1", []); V "z"]); Node ("+", [V "x"; Node ("1", [])])]));;(*d*)


mgu (Node ("+", [V "v"; Node ("+", [V "y"; Node ("0", [])])])) (Node ("+", [Node ("-", [Node ("1", []); V "z"]); Node ("+", [V "x"; Node ("0", [])])]));;
mgu (Node ("+", [Node ("-", [Node ("1", []); V "z"]); Node ("+", [V "x"; Node ("0", [])])])) (Node ("+", [V "v"; Node ("+", [V "y"; Node ("0", [])])]));;


let test1= Node ("+", [V("b");V("c")]);;
let test2= Node ("+",  [V("b");  Node("*",[V("a");V("c")])  ]  );;

mgu test1 test2;;