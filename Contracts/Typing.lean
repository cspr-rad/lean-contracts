import Contracts.Syntax

inductive Ty : Type :=
  | REAL
  | BOOL

inductive TypeOp : Op -> List Ty -> Ty -> Prop :=
  | type_blit b : TypeOp (Op.BLiteral b) [] BOOL
  | type_rlit r : TypeOp (Op.RLiteral r) [] REAL
  | type_neg : TypeOp Op.Neg [REAL] REAL
  | type_not : TypeOp Op.Not [BOOL] BOOL
  | type_cond t : TypeOp Op.Cond [BOOL,t,t] t
  | type_add : TypeOp Op.Add [REAL,REAL] REAL
  | type_sub : TypeOp Op.Sub [REAL,REAL] REAL
  | type_mult : TypeOp Op.Mult [REAL,REAL] REAL
  | type_div : TypeOp Op.Div [REAL,REAL] REAL
  | type_and : TypeOp Op.And [BOOL,BOOL] BOOL
  | type_or : TypeOp Op.Or [BOOL,BOOL] BOOL
  | type_less : TypeOp Op.Less [REAL,REAL] BOOL
  | type_leq : TypeOp Op.Leq [REAL,REAL] BOOL
  | type_eq : TypeOp Op.Eq [REAL,REAL] BOOL
notation "|-Op" e ":" t "=>" r => TypeOp e t r

inductive TypeObs : ObsLabel -> Ty -> Prop :=
  | type_obs_bool b : TypeObs (ObsLabel.LabelBool b) BOOL
  | type_obs_real r : TypeObs (ObsLabel.LabelReal r) REAL
notation "|-O" e ":" t => TypeObs e t

def TyEnv := List Ty

inductive TypeVar : TyEnv -> Var -> Ty -> Prop :=
  | type_var_1 t g : TypeVar (t::g) Var.V1 t
  | type_var_S g v t t' : TypeVar g v t -> TypeVar (t'::g) (Var.VS v) t
notation g "|-X" v ":" t => TypeVar g v t

def List.all2 {A B} (P : A -> B -> Prop) : List A -> List B -> Prop
  | [], [] => True
  | a::as, b::bs => P a b /\ List.all2 P as bs
  | _, _ => False

inductive TypeExp : TyEnv -> Exp -> Ty -> Prop :=
  | type_op g op es ts (t : Ty) : (|-Op op : ts => t) -> (∀ p, p ∈ List.zip es ts -> TypeExp g p.1 p.2) -> TypeExp g (Exp.OpE op es) t
  | type_obs (t : Ty) g o z : (|-O o : t) -> TypeExp g (Exp.Obs o z) t
  | type_var t g v : (g |-X v : t) -> TypeExp g (Exp.VarE v) t
  | type_acc n t g e1 e2 : ((t::g) |-X Var.V1 : t) -> TypeExp g e1 t -> TypeExp g e2 t -> TypeExp g (Exp.Acc e1 n e2) t
notation g "|-E" e ":" t => TypeExp g e t

inductive TypeContract {A P : Type} : TyEnv -> @Contract A P -> Prop :=
  | type_zero g : TypeContract g Contract.Zero
  | type_let g e c t : (g |-E e : t) -> TypeContract (t::g) c -> TypeContract g (Contract.Let e c)
  | type_transfer p1 p2 c g : TypeContract g (Contract.Transfer p1 p2 c)
  | type_scale e c g : (g |-E e : REAL) -> TypeContract g c -> TypeContract g (Contract.Scale e c)
  | type_translate d c g : TypeContract g c -> TypeContract g (Contract.Translate d c)
  | type_both c1 c2 g : TypeContract g c1 -> TypeContract g c2 -> TypeContract g (Contract.Both c1 c2)
  | type_if e (d : Nat) c1 c2 g : (g |-E e : BOOL) -> TypeContract g c1 -> TypeContract g c2 -> TypeContract g (Contract.If e d c1 c2)
notation g "|-C" c => TypeContract g c
