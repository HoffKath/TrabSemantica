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
type op = Sum 
        | Sub
        | Mul 
        | Div
        | Ls
        | LsE
        | Gt
        | GtE
        | Eq
        | OpAnd
        | OpOr
  
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
  | MatchL  of tipo * expr  * expr * expr * expr * expr
  | Just    of expr
  | Nothing of tipo
  | MatchJ  of tipo * expr * expr * expr * expr 
  
exception TypeError
  
let rec lookup a k: tipo option = 
  match a with
    [] -> None
  | (y,i) :: tl -> if (y = k) then Some i else lookup tl k 
          
let update (a: typeEnv) (k: ident) (i: tipo) : typeEnv =
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
         TyFn (t_in, t_out) ->
           if t2 = t_in then 
             t_out
           else raise TypeError
       | _ -> raise TypeError
      )
      
  | Fst (e1) ->
      let t1 = typeinfer a e1 in
      (match t1 with
         TyPair (t1, _) -> t1
       | _ -> raise TypeError)
      
  | Snd (e1) ->
      let t1 = typeinfer a e1 in 
      (match t1 with
         TyPair (_, t2) -> t2
       | _ -> raise TypeError
      )
      
  | Let (x, t, e1, e2) -> 
      if (typeinfer a e1) = t then typeinfer (update a x t) e2
      else raise TypeError
  
  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) -> 
      let taF = update a f tf in
      let taFX = update taF x tx in
      let tup = typeinfer taFX e1 in 
      if tup = t1 then
        typeinfer taF e2
      else raise TypeError
                 
  | Nil (t)-> TyList (t)
  | Cons (e1, e2) ->
      let t1 = typeinfer a e1 in
      let t2 = typeinfer a e2 in 
      if t2 = TyList (t1) then 
        TyList (t1)
  
  | Hd (e1) ->
      let t1 = typeinfer a e1 in
      (match t1 with
         TyList (t1, _) -> t1
       | _ -> raise TypeError)
        
  | Tl (e1) ->
      let t1 = typeinfer a e1 in
      (match t1 with
         TyList (_, t1) -> t1
       | _ -> raise TypeError)
        
  | MatchL(t, e1, e2, e3, xh, xt) ->
      let t1 = typeinfer a e1 in
      let t2 = typeinfer a e2 in 
      let txh = typeinfer a xh in
      let txt = typeinfer a xt in
      let upxh = update a txh e3 in
      let upxs = update a upxh e3 in 
      let t3 = typeinfer upxs e3 in
      
      if t1 = TyList(t) then 
        (match e1 with 
         | Nil (t) -> t2
         | Cons (xh, xt) -> t3
         | _ -> raise TypeError
        )
      else raise TypeError
            
  | Just(e1)->
      let t1 = typeInfer a e1 in
      TyMaybe(t1)
        
  | Nothing (t) ->
      TyMaybe(t)
        
  | MatchJ (t, e1, e2, e3, x) ->
      let t1 = typeInfer a e1 in
      let t2 = typeInfer a e2 in 
      let upx = update a x e3 in
      let t3 = typeInfer upx e3 in 
      
      if t1 = TyMaybe(t) then 
        (match e1 with 
         | Nothing (t)  -> t2
         | Just (x) -> t3
         | _ -> raise TypeError )
      else raise TypeError
          
  
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
    let t = typeInfer a e in 
    print_endline (type_to_str  t)
  with TypeError -> print_endline "Erro de Tipo" 