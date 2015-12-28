(**test compile code *)

let inst1 = Var("x");; 
let inst2 = Integer(2);;
let inst3 = Bool(true)
let inst4 = Unit(print_newline());;
let inst5 = Plus (inst1,inst2);;
let inst51 = Minus(Integer(3),Integer(6));;
let inst6 = And(Bool(true),Equal(Integer(1),Integer(2)) );;

let inst8 = App(Abstract ("x",Div(Var("x"),Integer(2))), Integer(12));;
let inst9 = App(Abstract ("x",Mul(Div(Var("x"),Integer(2)),Plus(Var("x"),Integer(1)))), Integer(6));;


let cl1 = ("x" , [Op_plus] ,  table ;;
let ex1 =Plus(Integer(3),Integer(4));;
let ex2 = Mul(Plus(Integer(1),Integer(1)),Plus(Integer(2),Integer(1)));;
let ex3 = And(Bool(true), Bool(false));;
let ex4 = Not(And(Bool(true),Bool(true)));; 
let ex5 = Not(Bool(true));;
let ex6 = Equal(ex2,Integer(2));;
let programme = [inst1; inst2 ; inst3 ; inst4; inst6 ;inst5];;
let inst10=IfThenElse(inst6,inst9,inst8);;
let inst11 = App(App(Abstract("x", Abstract("y", Plus(Var "x" , Var "y"))), Integer 2), Integer 3);;
let inst12 = App(Abstract("x", App(Var "x", Integer 2)), Abstract("y", Plus( Var "y", Integer 3)));;
let inst13 = Tuple(inst8, inst9);;
let inst14 =Tuple(Integer 14, Bool true  );;
let inst15 = ProjectionY(inst13);;


compileCode programme;;
compileCode [inst8];;
compileCode [ex11];;


main [inst15];;


