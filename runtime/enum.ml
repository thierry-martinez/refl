open Desc

open Tools

type ('a, 'arity, 'b) typed_attribute_kind +=
  | Attribute_value : ('a, 'arity, int) typed_attribute_kind

let constructor_value :
  type types structure .
  int ->
  (types, structure, 'arity, 'rec_arity, 'kinds, 'positive,
    'negative, 'direct, 'gadt) constructor ->
  int =
fun default_value constructor ->
  match constructor with
  | Constructor constructor ->
      begin match constructor.attributes.typed Attribute_value with
      | Some value -> value
      | _ -> default_value
      end
  | Exists _ -> default_value

let rec constructor_fold :
  type cases structures .
  (int -> int -> int) -> int -> int ->
  (cases, structures, 'arity, 'rec_arity, 'kinds, 'positive,
    'negative, 'direct, 'gadt) constructors ->
  int =
fun op value default_value constructors ->
  match constructors with
  | CNil -> value
  | CCons { head; tail } ->
      let head_value = constructor_value default_value head in
      constructor_fold op (op value head_value) (succ head_value) tail

let fold :
  type a .
  (int -> int -> int) ->
  (a, [`RecArity of [`Constr of 'structures] * _],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  int =
fun op constructors ->
  match constructors with
  | RecArity { desc = Constr { constructors = CCons { head; tail }; _ }; _} ->
      let head_value = constructor_value 0 head in
      constructor_fold op head_value (succ head_value) tail

let min :
  type a .
  (a, [`RecArity of [`Constr of 'structures] * _],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  int =
fun constructors ->
  fold min constructors

let max :
  type a .
  (a, [`RecArity of [`Constr of 'structures] * _],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  int =
fun constructors ->
  fold max constructors

let rec value_of_choice :
  type cases structures .
  int ->
  (cases, structures, 'arity, 'rec_arity, 'kinds, 'positive,
    'negative, 'direct, 'gadt) constructors ->
  cases choice -> int =
fun default_value constructors choice ->
  match constructors, choice with
  | CCons { head; _ }, CFirst _ ->
      constructor_value default_value head
  | CCons { head; tail }, CNext choice ->
      let head_value = constructor_value default_value head in
      value_of_choice (succ head_value) tail choice
  | _ -> .

let to_int :
  type a .
  (a, [`RecArity of [`Constr of 'structures] * _],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  a -> int =
fun desc value ->
  match desc with
  | RecArity { desc = Constr { constructors; destruct; _ }; _ } ->
      value_of_choice 0 constructors (destruct value)

let rec of_int_aux :
  type cases structures .
  int ->
  (cases, structures, 'arity, 'rec_arity, 'kinds, 'positive,
    'negative, 'direct, 'gadt) constructors ->
  int -> cases choice option =
fun default_value constructors value ->
  match constructors with
  | CCons { head; tail } ->
      let head_value = constructor_value default_value head in
      begin if value = head_value then
        match head with
        | Constructor { kind = CTuple TNil; eqs = ENil; _ } ->
            Some (CFirst ((), ()))
        | _ -> None
      else
        match of_int_aux (succ head_value) tail value with
        | Some choice -> Some (CNext choice)
        | None -> None
      end
  | _ -> None

let of_int_opt :
  type a .
  (a, [`RecArity of [`Constr of 'structures] * _],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  int -> a option =
fun desc value ->
  match desc with
  | RecArity { desc = Constr { construct; constructors; _ }; _ } ->
      match of_int_aux 0 constructors value with
      | None -> None
      | Some choice -> Some (construct choice)

let to_string :
  type a .
  (a, [`RecArity of [`Constr of 'structures] * _],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  a -> string =
fun desc value ->
  match desc with
  | RecArity { desc = Constr { constructors; destruct; _ }; _ } ->
      let Destruct destruct =
        Constructor.destruct constructors (destruct value) in
      destruct.name

let rec of_string_aux :
  type cases structures .
  (cases, structures, 'arity, 'rec_arity, 'kinds, 'positive,
    'negative, 'direct, 'gadt) constructors ->
  string ->
  cases choice option =
fun constructors value ->
  match constructors with
  | CCons { head; tail } ->
      begin match head with
      | Constructor c when c.name = value ->
          begin match c.kind, c.eqs with
          | CTuple TNil, ENil ->
              Some (CFirst ((), ()))
          | _ -> None
          end
      | _ ->
          match of_string_aux tail value with
          | Some choice -> Some (CNext choice)
          | None -> None
      end
  | _ -> None

let of_string_opt :
  type a .
  (a, [`RecArity of [`Constr of 'structures] * _],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  string -> a option =
fun desc value ->
  match desc with
  | RecArity { desc = Constr { construct; constructors; _ }; _ } ->
      match of_string_aux constructors value with
      | None -> None
      | Some choice -> Some (construct choice)
