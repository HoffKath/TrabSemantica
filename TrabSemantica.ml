(* This is an OCaml editor.
   Enter your program here and send it to the toplevel using the "Eval code"
   button or [Ctrl-e]. *)
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

and 
  renv = (ident * valor) list 

type omega = valor list
    
let newAddress memory =
  List.length memory 
    
let appendValue memory value =
  List.append memory [value]

let replace l pos a =
  List.mapi (fun i x -> if i = pos then a else x) l   

type context = valor * omega 
               
                 (*Matheus*)

exception BugTypeInfer  

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
      if t1 = t3 && t2 = te1 then 
        te2
      else raise TypeError
                 
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
  
let inter (a: typeEnv) (e: expr) = 
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
  | _ -> raise BugTypeInfer 
           
let rec eval (a:renv) (e:expr) (omega:omega) : context =
  match e with
    Num n -> (VN n, omega)
               
  | Bool b -> (VB b, omega)
              
  | OpBi(oper,e1,e2) ->
      let (v1, omega') = eval a e1 omega in
      let (v2, omega'') = eval a e2 omega'
      in (compute oper v1 v2, omega'')

  | If(e1,e2,e3) ->
      (match eval a e1 omega with
         (VB true, omega')  -> eval a e2 omega'
       | (VB false, omega') -> eval a e3 omega'
       | _ -> raise BugTypeInfer )

  | Var x ->
      (match lookup a x with
         Some v -> (v, omega)
       | None -> raise BugTypeInfer)

  | App(e1,e2) ->
      let (v1, omega')  = eval a e1 omega in
      let (v2, omega'') = eval a e2 omega' in
      (match v1 with
         VClos(x,ebdy,a') ->
           let a'' = update a' x v2
           in eval a'' ebdy omega''

       | VRclos(f,x,ebdy,a') ->
           let a''  = update a' x v2 in
           let a''' = update a'' f v1
           in eval a''' ebdy omega''
       | _ -> raise BugTypeInfer)
        
  | Fn (x,_,e1) ->  
      (VClos(x,e1,a), omega)
      
  | Let (x,_,e1,e2) ->
      let (v1, omega') = eval a e1 omega
      in eval (update a x v1) e2 omega' 
        
  | LetRec  (f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let a' = update a f (VRclos(f,x,e1,a))
      in eval a' e2 omega
        
  | Pair (e1,e2) ->
      let (v1, omega') = eval a e1 omega in
      let (v2, omega'') = eval a e2 omega'
      in (VPair(v1,v2), omega'')
         
  | Fst e ->
      (match eval a e omega with
       | (VPair(v1,_), omega') -> (v1, omega')
       | _ -> raise BugTypeInfer)
      
  | Snd e ->
      (match eval a e omega with
       | (VPair(_,v2), omega') -> (v2, omega')
       | _ -> raise BugTypeInfer)
                
  | Nil x ->
      raise (NImpError "Ainda não implementado")
        
  | Cons (x, y) ->
      raise (NImpError "Ainda não implementado")
        
  | Hd x ->
      raise (NImpError "Ainda não implementado") 
        
  | Tl x ->
      raise (NImpError "Ainda não implementado")
        
  | MatchL (x, y, z, w, u) ->
      raise (NImpError "Ainda não implementado")
        
  | Just x ->
      raise (NImpError "Ainda não implementado")
        
  | Nothing x ->
      raise (NImpError "Ainda não implementado")
        
  | MatchJ (w,x, y, z)  ->
      raise (NImpError "Ainda não implementado")
  

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


(* interpretador *)

let interpretador (e:expr) : unit =
  try
    let t = typeinfer [] e in
    let (v, omega) = eval [] e []
    in  print_string ((valueToString v) ^ " : " ^ (typeToString t)
                      ^ ", mem: {"
                      ^ (String.concat ", " (List.map (fun x -> valueToString x) omega))
                      ^ "}")
  with
    NImpError msg ->  print_string ("erro de tipo - " ^ msg)
