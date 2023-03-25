(*Kathleen Hoff, Maria Toneto e Matheus Stein*)

(*T ::= int | bool | T1 → T2 | T list | T1 ∗ T2 | maybe T*)
type tipo = 
    TyInt
  | TyBool
  | TyFn    of tipo * tipo
  | TyPair  of tipo * tipo 
  | TyList  of tipo
  | TyMaybe of tipo
      
  
(*op ∈ {+, −, ∗, div, <, ≤, >, ≥, =, and, or}*)
type op = Sum | Sub | Mul | Div | Ls | LsE | Gt | GtE | Eq | OpAnd | OpOr
  
type ident = string 
  
type typeEnv = (ident * tipo) list 
(*n | b | e1 op e2 | if e1 then e2 else e3
| x | e1 e2 | fn x : T ⇒ e | let x : T = e1 in e2
| let rec f : T1 → T2 = fn x : T1 ⇒ e1 in e2
                                            | (e1, e2) | fst e | snd e
                                            | nil : T | e1::e2 | hd e | tl e
                                            | match e1 with nil ⇒ e2 | x::xs ⇒ e3
                                                          | just e | nothing : T
| match e1 with nothing ⇒ e2 | just x ⇒ e3*)
type expr = 
    Num     of int 
  | Bool    of bool
  | OpBi    of op    * expr * expr
  | If      of expr  * expr * expr
  | Var     of ident
  | App     of expr  * expr
  | Fn      of ident * tipo  * expr
  | Let     of ident * tipo  * expr  * expr 
  | LetRec  of ident * tipo  * expr * expr 
  | Pair    of expr  * expr
  | Fst     of expr
  | Snd     of expr 
  | Nil     of tipo
  | Cons    of expr * expr
  | Hd      of expr 
  | Tl      of expr 
  | MatchL  of expr  * expr * expr * ident * ident
  | Just    of expr
  | Nothing of tipo
  | MatchJ  of expr * expr * expr * ident 

                 (*Matheus*) 
type valor =
    VN of int
  | VB of bool
  | VPair of valor * valor 
  | VClos  of ident * expr * renv
  | VRclos of ident * ident * expr * renv 
  | VList of valor list
  | VOption of valor option

and 
  renv = (ident * valor) list 
  
type context = valor 
               
                 (*Matheus*)

exception TypeError
  
exception NImpError of string
  
let rec lookup a k = 
  match a with
    [] -> None
  | (y,i) :: tl -> if (y = k) then Some i else lookup tl k 
          
let update a k i =
  (k,i) :: a
  
let rec typeinfer (a: typeEnv) (e: expr): tipo = 
  match e with 
    Num n -> TyInt
  | Bool b -> TyBool
  | OpBi (op,e2, e3) ->
      let t2 = typeinfer a e2 in 
      let t3 = typeinfer a e3 in
      (match op with
         Sum
       | Sub
       | Mul
       | Div ->
           if t2 = TyInt && t3 = TyInt then
             TyInt
           else raise TypeError
       | OpAnd
       | OpOr -> 
           if t2 = TyBool && t3 = TyBool then
             TyBool
           else raise TypeError
       | _ -> 
           if t2 = TyInt && t3 = TyInt then
             TyBool
           else raise TypeError
      )
             
  | If (e1, e2, e3) ->
      let t1 = typeinfer a e1 in
      (match t1 with
         TyBool ->
           let t2 = typeinfer a e2 in
           let t3 = typeinfer a e3 in
           if t2 = t3 then t2
           else raise TypeError
       | _ -> raise TypeError 
      ) 
        
  | Var x -> 
      (match lookup a x with
         Some t -> t
       | None -> raise TypeError)
      
  | Pair(e1,e2) -> 
      let t1 = typeinfer a e1 in 
      let t2 = typeinfer a e2 in
      TyPair(t1,t2)
          
  | Fn (x, t, e2) -> 
      let up = update a x t in
      TyFn(t, typeinfer up e2)
      
  | App (e1, e2) ->  
      let t1 = typeinfer a e1 in
      let t2 = typeinfer a e2 in
      (match t1 with 
         TyFn(t_in, t_out) ->
           if t2 = t_in then 
             t_out
           else raise TypeError
       | _ -> raise TypeError
      )
      
  | Fst (e1) ->
      let t1 = typeinfer a e1 in
      (match t1 with
         TyPair(t1, _) -> t1
       | _ -> raise TypeError)
      
  | Snd (e1) ->
      let t1 = typeinfer a e1 in 
      (match t1 with
         TyPair(_, t2) -> t2
       | _ -> raise TypeError
      )
      
  | Let (x, t, e1, e2) ->
      if (typeinfer a e1) = t then typeinfer (update a x t) e2
      else raise TypeError
  
  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) -> 
      let taF = update a f tf in
      let taFX = update taF x tx in
      let te1 = typeinfer taFX e1 in 
      let te2 = typeinfer taF e2 in
      if t1 = tx && t2 = te1 then 
        te2
      else raise TypeError
          
  | LetRec _ -> raise (NImpError "bug parser")
                 
  | Nil (t)-> TyList(t)
  | Cons (e1, e2) ->
      let t1 = typeinfer a e1 in
      let t2 = typeinfer a e2 in 
      if t2 = TyList(t1) then 
        TyList(t1)
      else raise TypeError 
          
  |Hd(e1)->
      let t1 = typeinfer  a e1 in 
      (match t1 with 
         TyList(t) -> t 
       | _ -> raise TypeError)
       
      
  
  | Tl(e1) ->
      let t1 = typeinfer  a e1 in 
      (match t1 with 
         TyList(t) -> t 
       | _ -> raise TypeError)
        
  | MatchL(e1, e2, e3, xh, xt) -> 
      let t1 = typeinfer a e1 in
      let t2 = typeinfer a e2 in 
      (match t1 with
         TyList(t) -> (
           let up2 = update a xh t in
           let up1 = update up2 xt t1 in
           let t3 = typeinfer up1 e3 in
           if t2 = t3 then 
             t2 
           else raise TypeError )
       |_ -> raise TypeError
      )
  
  | Just(e1)->
      let t1 = typeinfer a e1 in
      TyMaybe(t1)
        
  | Nothing (t) ->
      TyMaybe(t)
        
  | MatchJ (e1, e2, e3, x) ->
      let t1 = typeinfer a e1 in
      let t2 = typeinfer a e2 in 
      (match t1 with 
         TyMaybe(t) -> (
           let t3 = typeinfer (update a x t1) e3 in
           if t2 = t3 then 
             t2
           else raise TypeError)
       | _ -> raise TypeError 
      ) 
          
      
let type_to_str (t :tipo): string  = 
  (match t with
     TyInt -> "int"
   | TyBool -> "bool"
   | TyFn(t1,t2) -> "T1 -> T2"
   | TyPair(t1,t2) -> "T1*T2" 
   | TyList(t1)    -> "T list"
   | TyMaybe(t1)   -> "Maybe T"
  )
  
let interpretador (a: typeEnv) (e: expr) = 
  try 
    let t = typeinfer a e in 
    print_endline (type_to_str  t)
  with TypeError -> print_endline "Erro de Tipo" 
  
                      
                      (* AVALIADOR *)

let rec compute (oper: op) (v1: valor) (v2: valor) : valor =
  match (oper, v1, v2) with 
    (Sum,  VN n1, VN n2) -> VN (n1 + n2)
  | (Sub,  VN n1, VN n2) -> VN (n1 - n2)
  | (Mul, VN n1, VN n2) -> VN (n1 * n2) 
  | (Div, VN n1, VN n2) -> VN( n1 / n2) 
  | (Ls, VN n1, VN n2) -> VB( n1 < n2)
  | (LsE,VN n1, VN n2) -> VB( n1 <= n2) 
  | (Gt, VN n1, VN n2) -> VB( n1 > n2) 
  | (GtE,VN n1, VN n2) -> VB( n1 >= n2)
  | (Eq, VN n1, VN n2) -> VB( n1 = n2)
  | (OpAnd, VB b1, VB b2) -> VB(b1 && b2)
  | (OpOr, VB b1, VB b2) -> VB( b1 || b2)
  | _ -> raise TypeError 
           
let rec eval (a:renv) (e:expr) : context =
  match e with
    Num n -> (VN n)
               
  | Bool b -> (VB b)
              
  | OpBi(oper,e1,e2) ->
      let (v1) = eval a e1 in
      let (v2) = eval a e2
      in (compute oper v1 v2)

  | If(e1,e2,e3) ->
      (match eval a e1 with
         (VB true)  -> eval a e2
       | (VB false) -> eval a e3
       | _ -> raise TypeError )

  | Var x ->
      (match lookup a x with
         Some v -> (v)
       | None -> raise TypeError)

  | App(e1,e2) ->
      let (v1)  = eval a e1 in
      let (v2) = eval a e2 in
      (match v1 with
         VClos(x,ebdy,a') ->
           let a'' = update a' x v2
           in eval a'' ebdy 

       | VRclos(f,x,ebdy,a') ->
           let a''  = update a' x v2 in
           let a''' = update a'' f v1
           in eval a''' ebdy 
       | _ -> raise TypeError)
        
  | Fn (x,_,e1) ->  
      (VClos(x,e1,a))
      
  | Let (x,_,e1,e2) ->
      let (v1) = eval a e1 
      in eval (update a x v1) e2 
        
  | LetRec (f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let a' = update a f (VRclos(f,x,e1,a))
      in eval a' e2
        
  | LetRec _ -> raise (NImpError "bug parser")
        
  | Pair (e1,e2) ->
      let (v1) = eval a e1 in
      let (v2) = eval a e2
      in (VPair(v1,v2))
         
  | Fst e ->
      (match eval a e with
       | (VPair(v1,_)) -> (v1)
       | _ -> raise TypeError)
      
  | Snd e ->
      (match eval a e with
       | (VPair(_,v2)) -> (v2)
       | _ -> raise TypeError)
                
  | Nil e -> VList []
        
  | Cons (e1, e2) ->
      let (v1) = eval a e1 in
      let (v2) = eval a e2 in
      VList (v1 :: v2 :: [])
        
  | Hd e ->
      (match eval a e with
       | VList [] -> VList []
       | VList (h :: _) -> h
       | _ -> raise (NImpError "bug parser"))
        
  | Tl e ->
      (match eval a e with
       | VList [] -> VList []
       | VList (_ :: t) -> VList t
       | _ -> raise (NImpError "bug parser"))
        
  | MatchL (e1, e2, e3, w, u) ->
      (match eval a e1 with
       | VList [] -> eval a e2
       | VList (x :: xs) -> eval a e3 
       | _ -> raise (NImpError "bug parser"))
        
  | Just e -> eval a e
        
  | Nothing e -> VOption None
        
  | MatchJ (e1, e2, e3, z)  ->
      (match eval a e1 with
       | VOption None -> eval a e2
       | VOption Some x -> eval a e3
       | _ -> raise (NImpError "bug parser"))
  

(* função que converte tipo para string *)

let rec typeToString (t:tipo) : string =
  match t with
    TyInt  -> "int"
  | TyBool -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (typeToString t1) ^ " --> " ^ (typeToString t2) ^ ")"
  | TyPair(t1,t2) ->  "("  ^ (typeToString t1) ^ " * "   ^ (typeToString t2) ^ ")"
  | TyList t1 -> "FazerTylist"
  | TyMaybe t1 -> "FazerTyMaybe"


(* função que converte valor para string *)
let rec valueToString (v: valor) : string =
  match v with
    VN n -> string_of_int n
  | VB b -> string_of_bool b 
  | VPair(v1, v2) -> "(" ^ valueToString v1 ^ "," ^ valueToString v1 ^ ")"
  | VClos _ ->  "fn"
  | VRclos _ -> "fn"
  | VList [] -> "[]" 
  | VList (x :: xs) -> "[" ^ valueToString x ^ "]" 
  | VOption None -> "none"
  | VOption Some x -> valueToString x


(* interpretador *)
(*fazer intepretador*)
