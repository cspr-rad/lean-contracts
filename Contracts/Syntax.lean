inductive Asset : Type :=
| asset : String -> Asset
inductive Party : Type :=
| party : String -> Party

inductive Var : Type :=
| V1
| VS (v : Var)

inductive ObsLabel : Type :=
| LabelReal (o : String)
| LabelBool (o : String)

inductive Op : Type :=
| Add
| Sub
| Mult
| Div
| And
| Or
| Less
| Leq
| Eq
| Not
| Neg
| BLiteral (b : Bool)
| RLiteral (r : Int)
| Cond

inductive Exp : Type :=
| OpE (op: Op) (args : List Exp) : Exp
| Obs (l : ObsLabel) (i : Int) : Exp
| VarE (v : Var) : Exp
| Acc (f : Exp) (d : Nat) (e : Exp) : Exp

inductive Contract {A P : Type} : Type :=
| Zero : Contract
| Let : Exp -> Contract -> Contract
| Transfer : P -> P -> A -> Contract
| Scale : Exp -> Contract -> Contract
| Translate : Nat -> Contract -> Contract
| Both : Contract -> Contract -> Contract
| If : Exp -> Nat -> Contract -> Contract -> Contract
