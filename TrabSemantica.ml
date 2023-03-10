(* This is an OCaml editor.
   Enter your program here and send it to the toplevel using the "Eval code"
   button or [Ctrl-e]. *)
(*Kathleen Hoff, Maria Toneto e Matheus Stein*)

(*T ::= int | bool | T1 → T2 | T list | T1 ∗ T2 | maybe T*)
type tipo = 
    TyInt
  | TyBool
  | TyFn    of tipo * tipo
  | TyPair   of tipo * tipo 
  | TyList  of tipo 
  | TyVar   of int 
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
  | True
  | False 
  | OpBi    of op
  | If      of expr  * expr * expr
  | Var     of ident
  | App     of expr  * expr
  | Fn      of ident * expr
  | Let     of ident * expr  * expr 
  | LetRec  of ident * ident * expr * expr
  | Pair    of expr  * expr
  | Fst     of expr
  | Snd     of expr 
  | Nil
  | List    of expr  * expr
  | Hd      of expr
  | Tl      of expr 
  | MatchL  of expr  * expr * expr
  | Just    of expr
  | Nothing
  | MatchJ  of expr  * expr * expr
  | raise
  
               
  
let rec lookup a k: tipo option = 
  match a with
    [] -> None
  | (y,i) :: tl -> if (y = k) then Some i else lookup tl k 
          
let update (a: typeEnv) (k: ident) (i: tipo) : typeEnv =
  (k,i) :: a
  
let rec typeinfer (g: typeEnv) (e: expr): tipo = 
  match e with 
    Num n -> TyInt
  | True  -> TyBool
  | False -> TyBool
  | OpBi (e1,e2, e3) ->
      if e1 = sum then TyInt
      else if e1 = sub then TyInt
      else if e1 = mult then TyInt 
      else if e1 = div then TyInt
      else TyBool
  | If (e1, e2, e3) ->
      let t1 = typerinfer g e1 in
      (match t1 with
         TyBool ->
           let t2 = typeinfer g e2 in
           let t3 = typeinfer g e3 in
           if t2 = t3 then t2
           else raise
  