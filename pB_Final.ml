(* ----------------------------- opal.ml START ------------------------------ *)
(* lazy stream -------------------------------------------------------------- *)

module Opal = struct
  module LazyStream = struct
    type 'a t = Cons of 'a * 'a t Lazy.t | Nil

    let of_stream stream =
      let rec next stream =
        try Cons (Stream.next stream, lazy (next stream))
        with Stream.Failure -> Nil
      in
      next stream
    let of_function f =
      let rec next f =
        match f () with Some x -> Cons (x, lazy (next f)) | None -> Nil
      in
      next f

    let of_string str = str |> Stream.of_string |> of_stream
    let of_channel ic = ic |> Stream.of_channel |> of_stream
  end

  (* utilities ---------------------------------------------------------------- *)

  let implode l = String.concat "" (List.map (String.make 1) l)

  let explode s =
    let l = ref [] in
    String.iter (fun c -> l := c :: !l) s;
    List.rev !l

  let ( % ) f g x = g (f x)

  let parse parser input =
    match parser input with Some (res, _) -> Some res | None -> None

  (* primitives --------------------------------------------------------------- *)

  type 'token input = 'token LazyStream.t
  type ('token, 'result) monad = ('result * 'token input) option

  type ('token, 'result) parser =
    'token input -> ('result * 'token input) option

  let return x input = Some (x, input)

  let ( >>= ) x f input =
    match x input with
    | Some (result', input') -> f result' input'
    | None -> None

  let ( let* ) = ( >>= )

  let ( <|> ) x y input =
    match x input with Some _ as ret -> ret | None -> y input

  let rec scan x input =
    match x input with
    | Some (result', input') -> LazyStream.Cons (result', lazy (scan x input'))
    | None -> LazyStream.Nil

  let mzero _ = None

  let any = function
    | LazyStream.Cons (token, input') -> Some (token, Lazy.force input')
    | LazyStream.Nil -> None

  let satisfy test = any >>= fun res -> if test res then return res else mzero
  let eof x = function LazyStream.Nil -> Some (x, LazyStream.Nil) | _ -> None

  (* derived combinators ------------------------------------------------------ *)

  let ( => ) x f = x >>= fun r -> return (f r)
  let ( >> ) x y = x >>= fun _ -> y

  let ( << ) x y =
    x >>= fun r ->
    y >>= fun _ -> return r

  let ( <~> ) x xs =
    x >>= fun r ->
    xs >>= fun rs -> return (r :: rs)

  let rec choice = function [] -> mzero | h :: t -> h <|> choice t
  let rec count n x = if n > 0 then x <~> count (n - 1) x else return []
  let between op ed x = op >> x << ed
  let option default x = x <|> return default
  let optional x = option () (x >> return ())
  let rec skip_many x = option () (x >>= fun _ -> skip_many x)
  let skip_many1 x = x >> skip_many x

  let rec many x =
    option []
      ( x >>= fun r ->
        many x >>= fun rs -> return (r :: rs) )

  let many1 x = x <~> many x
  let sep_by1 x sep = x <~> many (sep >> x)
  let sep_by x sep = sep_by1 x sep <|> return []
  let end_by1 x sep = sep_by1 x sep << sep
  let end_by x sep = end_by1 x sep <|> return []

  let chainl1 x op =
    let rec loop a =
      op >>= (fun f -> x >>= fun b -> loop (f a b)) <|> return a
    in
    x >>= loop

  let chainl x op default = chainl1 x op <|> return default

  let rec chainr1 x op =
    x >>= fun a -> op >>= (fun f -> chainr1 x op => f a) <|> return a

  let chainr x op default = chainr1 x op <|> return default

  (* singletons --------------------------------------------------------------- *)

  let exactly x = satisfy (( = ) x)
  let one_of l = satisfy (fun x -> List.mem x l)
  let none_of l = satisfy (fun x -> not (List.mem x l))
  let range l r = satisfy (fun x -> l <= x && x <= r)

  (* char parsers ------------------------------------------------------------- *)

  let space = one_of [ ' '; '\t'; '\r'; '\n' ]
  let spaces = skip_many space
  let newline = exactly '\n'
  let tab = exactly '\t'
  let upper = range 'A' 'Z'
  let lower = range 'a' 'z'
  let digit = range '0' '9'
  let letter = lower <|> upper
  let alpha_num = letter <|> digit
  let hex_digit = range 'a' 'f' <|> range 'A' 'F' <|> digit
  let oct_digit = range '0' '7'

  (* lex helper --------------------------------------------------------------- *)

  let lexeme x = spaces >> x

  let token s =
    let rec loop s i =
      if i >= String.length s then return s else exactly s.[i] >> loop s (i + 1)
    in
    lexeme (loop s 0)
end
(* ------------------------------ opal.ml END ------------------------------- *)

type formula =
  | Prop of int
  | Const of bool
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula

module Parser = struct
  open Opal

  exception Syntax_error
  exception Runtime_error

  (* parser *)

  let integer = spaces >> many1 digit => implode % int_of_string
  let negop = token "!" >> return (fun x -> Not x)
  let orop = token "|" >> return (fun x y -> Or (x, y))
  let andop = token "&" >> return (fun x y -> And (x, y))
  let implop = token "->" >> return (fun x y -> Imp (x, y))
  let binop = andop <|> orop <|> implop
  let atom = integer => fun n -> Prop n

  let rec formula input = (atomic_formula <|> complex_formula) input
  and atomic_formula input = atom input
  and complex_formula input = (neg_formula <|> binop_formula) input

  and binop_formula input =
    (let* _ = token "(" in
     let* l = formula in
     let* op = binop in
     let* r = formula in
     let* _ = token ")" in
     return (op l r))
      input

  and neg_formula input =
    (let* op = negop in
     let* _ = token "(" in
     let* f = formula in
     let* _ = token ")" in
     return (op f))
      input

  let parse_formula input = parse (formula << (spaces << eof ())) input
end

let parse_formula s =
  Parser.parse_formula (Opal.LazyStream.of_string s) |> Option.get

(* SOLUÇÂO APARTIR DAQUI *)

(*Lê o numero de variaveis*)
let numVariables = read_int()

(*Lê a string*)
let string = read_line ()

(*Tipo da árvore Node com Leaf Left, inteiro, Leaf right*)
type 'a tree =
  | Leaf of bool
  | Node of 'a tree * 'a * 'a tree;;    

(*Tira as implicações dá formula*)
let rec impfree form = 
  match form with
  | Imp(c_1, c_2) -> Or(Not (impfree(c_1)), impfree(c_2))
  | Prop c -> Prop c
  | Const c -> Const c
  | Not x -> Not (impfree (x))
  | And (a, b) -> And(impfree (a), impfree(b))
  | Or (a, b) -> Or(impfree (a), impfree(b))

(*Tira as negações dá formula ficando antes das proposições ou das constantes*)
let rec negFree formula = 
  match formula with
  |Not (Or((x), (z))) -> And(negFree(Not x), negFree(Not z))
  |Not(And((x), (z))) -> Or(negFree(Not x), negFree(Not z))
  | Not (Prop c) -> Not(negFree(Prop c))
  | Not (Const c) -> Not(negFree(Const c))
  | Not (Not x) -> negFree (x) 
  | And (a, b) -> And(negFree (a), negFree(b))
  | Or (a, b) -> Or(negFree (a), negFree(b))
  | Prop c -> Prop c
  | Const c -> Const c
  | _ -> failwith "Impossible"
                 
(*Muda o valor da Prop x na form para Const bool*)      
let rec changeValue form x bool =
  match form with 
  | Prop y -> if x = y then Const bool else Prop y
  | Const y -> Const y
  | Not(Prop y) -> if x=y then (if bool then Const false else Const true ) else Not(Prop y) 
  | Or(a, b) ->  Or(changeValue a x bool, changeValue b x bool)
  | And(a, b) -> And(changeValue a x bool, changeValue b x bool)
  | _ -> failwith "Impossible"   
           
(*Verifica se a form é verdadeira ou se é falsa se não for nem uma nem outra devolve a formúla*)
let rec check form =
  match form with 
  | Const x -> Const x 
  | Prop x -> Prop x 
  | Not x -> Not x
  |Or (a, b) ->
      let c = check a in
      let d = check b in
      if c = Const true && d = Const true then Const true else if
        c = Const true && d != Const true then Const true else if
        d = Const true && c != Const true then Const true else if
        c = Const false && d = Const false then Const false else (Or(c, d))                                   
  |And (a, b) ->
      let c = check a in
      let d = check b in
      if c = Const true && d = Const true then Const true else if
        c = Const true && d != Const true then Const false else if
        d = Const true && c != Const true then Const false else if
        c = Const false && d = Const false then Const false else (And(c, d)) 
  | _ -> failwith "Impossible"

(*Verifica se a formula já com constantes pode verificar já verdadeiro*)
let truefalse nform = 
  if  (check (nform) = Const true)then true else false

(*Constroi a árvore com o niveis = numvariaveis sendo o ultimo nivel so Leaf
 este vai incrementando e verificando se a Leaf é true ou false pois se for false 
 tem de continuar para baixo para testar com o valor booleano das outras variaveis *)
let rec buildTree form t var = 
  if var != numVariables then 
    let nformT = changeValue form var true in 
    let nformF = changeValue form var false in
    let right = truefalse nformT in
    let left = truefalse nformF in 
    match t with 
    | Leaf c -> Node(buildTree nformF (Leaf (left)) (var+1), var,  buildTree nformT (Leaf (right)) (var+1) )
    | Node (Leaf x,v, Leaf y) -> if x = true && y = true then Leaf true else if
          x = true && y = false then Node (Leaf x,var, buildTree nformT (Leaf y) (var+1) ) else if
          y= true && x = false then Node (buildTree nformF (Leaf x) (var+1),var, Leaf y) else
          Node ( buildTree nformF (Leaf x) (var+1) ,(var), buildTree nformT (Leaf y) (var+1) )
    | Node (x, y, z) -> Node (buildTree nformF x (var+1), var, buildTree nformT z (var+1))
  else t 


(*Conta o número de folhas*)
let rec countLeafs t =
  match t with 
  | Leaf _-> 1
  | Node( l,v ,r) ->
      countLeafs l + countLeafs r ;;

(*Conta o número de folhas com o valor true*)
let rec countTrues t =
  match t with 
  | Leaf true -> 1
  | Leaf false -> 0
  | Node(left, x, right) -> countTrues  left + countTrues right


(*Remover os duplicados por exemplo quando uma arvore tem dois falses basta ter um *)
let rec dontDuplicate t =
  match t with 
  | Leaf _ -> t
  | Node (left, x, right) ->
      let left_T = dontDuplicate left in
      let right_T = dontDuplicate right in
      match left_T with 
      | Leaf _ -> (if left_T = right_T then left_T else Node (left_T, x, right_T))
      | _ -> Node (left_T, x,right_T)

(*Percorre primeiro para a esquerda se encontrar um Leaf true devolve logo um array e a flag com o valor 1 se nao encontrar procura para a direita
e se tambem nao encontrar a direita devolve um array e uma flag com o valor 0*)      
let rec depth_first_s t array index = 
  match t with
  | Leaf true -> (1, array)
  | Leaf false -> (0, array)
  | Node(l, x,r) -> (
      let left = depth_first_s l (array.(index) <- 0; array) (index + 1) in 
      match left with
      | (1, a) -> (1, a)
      | (0, a) -> (
          let right = depth_first_s r (array.(index) <- 1; array) (index + 1) in
          match right with
          | (1 , a) -> (1, a)
          | _ -> (0, a)
        ) 
      | _ -> failwith "ERRO"
    )

(* Formula inicial sem implicações e os not já estão antes da variavel*)
let form = negFree (impfree (parse_formula string))

(*árvore construida*)
let tree = buildTree form (Leaf false) 0

(*árvore reduzida -> Binary Decision Diagram*)
let robdd = dontDuplicate tree

(*Aqui aplica o algoritmo DFS, Busca em profundidade, o que vai fazer é tentar andar mais para o lado esquerdo e se não encontrar true vai indo para o direito
  Devolve 1 se encontrou Leaf true, devolve 0 se não encontrou Leaf true e o array com as modificações do caminho/valores das variaveis*)
let (flag, array) = depth_first_s robdd (Array.make numVariables 0) 0 

(*OUTPUT*)
let output = 
  if flag = 0 then Printf.printf "NONE" else Array.iter (Printf.printf "%d") array;
  Printf.printf "\n%d\n" (countTrues tree);
  Printf.printf "%d\n" (countLeafs (robdd));

(* Exemplo 
-> INPUT:
3
((0 -> 1) & 2)
-> formula - Pois já foi aplicado o impfree e o negFree
And (Or (Not (Prop 0), Prop 1), Prop 2)
-> arvore
  Node
   (Node (Node (Leaf false, 2, Leaf true), 1,
    Node (Leaf false, 2, Leaf true)),
   0,
   Node (Node (Leaf false, 2, Leaf false), 1,
  Node (Leaf false, 2, Leaf true)))
-> bdd
  Node
   (Node (Node (Leaf false, 2, Leaf true), 1, Node (Leaf false, 2, Leaf true)),
   0, 
   Node (Leaf false, 1, Node (Leaf false, 2, Leaf true)))
-> output
001
3
7
  *)
