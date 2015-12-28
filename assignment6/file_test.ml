(**test compile code *)


(*basic examples*)
let inst1 = Var("x");; 
let inst2 = Integer(2);;
let inst3 = Bool(true)
let inst4 = Unit(print_newline());;
let inst5 = Plus (inst1,inst2);;
let inst51 = Minus(Integer(3),Integer(6));;
let inst6 = And(Bool(true),Equal(Integer(1),Integer(2)) );;

(*more complex examples *)
let inst8 = App(Abstract ("x",Div(Var("x"),Integer(2))), Integer(12));; 
let inst9 = App(Abstract ("x",Mul(Div(Var("x"),Integer(2)),Plus(Var("x"),Integer(1)))), Integer(6));;
let inst10=IfThenElse(inst6,inst9,inst8);;
let inst13 = Tuple(inst8, inst9);;
let inst14 =Tuple(Integer 14, Bool true  );;
let inst15 = ProjectionY(inst13);;

(* to run your example*)
main [inst15];;


