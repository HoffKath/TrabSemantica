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
type op = sum 
        | sub
        | mul 
        | div
        | ls
        | lsE
        | gt
        | gtE
        | eq
        | opAnd
        | opOr
  
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
  | LetRec  of expr  * ident * tipo  * expr * expr 
  | Pair    of expr  * expr
  | Fst     of expr
  | Snd     of expr 
  | Nil     of tipo
  | Cons    of expr  * expr
  | Hd      of expr  * expr
  | Tl      of expr  * expr
  | MatchL  of tipo * expr  * expr * expr * expr * expr
  | Just    of expr
  | Nothing of tipo
  | MatchJ  of tipo * expr * expr * expr * expr 
  
               
  
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
         sum
       | sub
       | mult
       | div ->
           if t2 = TyInt && t3 = TyInt then
             TyInt
           else raise 
       | opAnd
       | opOr -> 
           if t2 = TyBool && t3 = TyBool then
             TyBool
           else raise
       | _ -> 
           if eqType(e2) && eqType(e3) then
             TyBool
           else raise )
             
  | If (e1, e2, e3) ->
      let t1 = typerinfer a e1 in
      (match t1 with
         TyBool ->
           let t2 = typeinfer a e2 in
           let t3 = typeinfer a e3 in
           if t2 = t3 then t2
           else raise
       | _ -> raise )
      
  | Var (e1) -> 
      lookup a x
      
  | Pair (e1, e2) ->
      let t1 = typeInfer a e1 in 
      let t2 = typeInfer a e2 in 
      if t1 = t2 then 
        TyPair (t1, t2)
          
  | Fn (x, t, e2) -> 
      let up = update a x t in
      TyFn(t, typeInfer up e2)
      
  | App (e1, e2) ->  
      let t1 = typeInfer a e1 in
      let t2 = typeInfer a e2 in
      (match t1 with 
         TyFn (t_in, t_out) ->
           if t2 = t_in then 
             t_out
           else raise
       | _ -> raise)
      
  | Fst (e1) ->
      let t1 = typeInfer a e1 in
      (match t1 with
         TyPair (t1, _) -> t1
       | _ -> raise)
      
  | Snd (e1) ->
      let t1 = typeInfer a e1 in 
      (match t1 with
         TyPair (t1, _) -> t2
       | _ -> raise)
      
  | Let (x, t, e1, e2) -> 
      let tx = typeInfer a x in
      let up = update a x tx in
      let t1 = typeInfer a e1 in
      if t = t1 then 
        typeInfer up e2
      else raise
  
  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) -> 
      let taF = update a f tf in
      let taFX = update taF x tx in
      let tup = typeInfer taFX e1 in 
      if tup = t2 then
        typeInfer taF e2
      else raise 
                 
  | Nil (t)-> TyList (t)
  | Cons (e1, e2) ->
      let t1 = typeInfer a e1 in
      let t2 = typeInfer a e2 in 
      if t2 = TyList (t1) then 
        TyList (t1)
  
  | Hd (e1,e2) ->
      let t1 = typeInfer a e1 in 
      t1
        
  | Tl (e1,e2) ->
      let t2 = typeInfer a e2 in
      t2
        
  | MatchL(t, e1, e2, e3, xh, xt) ->
      let t1 = typeInfer a e1 in
      let t2 = typeInfer a e2 in
      let t3 = typeInfer a e3 in
      let txh = typeInfer a xh in
      let txt = typeInfer a xt in
      if t1 = TyList(t) &&  txh = t && txt = TyList(t) then 
        (match e1 with 
         | Nil (t) -> t2
         | Cons (xh, xt) -> t3
         | _ -> raise
        )
      else raise 
            
  | Just(e1)->
      let t1 = typeInfer a e1 in
      TyMaybe(t1)
        
  | Nothing (t) ->
      TyMaybe(t)
        
  | MatchJ (t, e1, e2, e3, x) ->
      let t1 = typeInfer a e1 in
      let t2 = typeInfer a e2 in
      let t3 = typeInfer a e3 in 
      let tx = typeInfer a x in 
      if t1 = TyMaybe(t) && tx = t then 
        (match e1 with 
         | Nothing (t)  -> t2
         | Just (x) -> t3
         | _ -> raise )
      else raise
  
         (*fazer eqTYPE*)