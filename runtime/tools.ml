open Desc

let cast : type a b . (a, b) eq -> a -> b = fun Eq x -> x

let eq_symmetric : type a b . (a, b) eq -> (b, a) eq = fun Eq -> Eq

let sub_gadt_functional sub sub' =
  sub.sub_gadt_functional sub.sub_gadt_ext sub'.sub_gadt_ext

type 'types selection_of_choice =
  | SelectionOfChoice : {
      index : ([`Succ of 'index], 'types, 'a, _) selection;
      item : 'a;
    } -> 'types selection_of_choice

let selection_of_choice : type types .
  types choice -> types selection_of_choice =
fun choice ->
  let rec aux : type index types item tail .
    (index, types, item, tail) selection ->
    tail choice ->
    types selection_of_choice =
  fun index choice ->
    match choice with
    | CFirst item ->
        SelectionOfChoice { index = Next index; item }
    | CNext choice ->
        aux (Next index) choice in
  aux Start choice

let rec variable_functional :
  type index arity a b positive_a direct_a positive_b direct_b .
  (index, arity, a, positive_a, direct_a) variable ->
  (index, arity, b, positive_b, direct_b) variable ->
  (a, b) eq =
fun index_a index_b ->
  match index_a, index_b with
  | VFirst, VFirst -> Eq
  | VNext index_a, VNext index_b ->
      let Eq = variable_functional index_a index_b in
      Eq

type ('index, 'index') compare =
  | LessThan
  | Equal of ('index, 'index') eq
  | GreaterThan

let rec compare_length :
  type count_a types_a count_b types_b .
  (count_a, types_a) length ->
  (count_b, types_b) length ->
  (count_a, count_b) compare =
fun length_a length_b ->
  match length_a, length_b with
  | Zero, Zero -> Equal Eq
  | Succ length_a, Succ length_b ->
      begin match compare_length length_a length_b with
      | LessThan -> LessThan
      | GreaterThan -> GreaterThan
      | Equal Eq -> Equal Eq
      end
  | Zero, Succ _ -> LessThan
  | Succ _, Zero -> GreaterThan

let rec compare_selection :
  type index index' sequence sequence' head tail head' tail' .
  (index, sequence, head, tail) selection ->
  (index', sequence', head', tail') selection ->
  (index, index') compare =
fun selection selection' ->
  match selection, selection' with
  | Start, Start -> Equal Eq
  | Start, Next _ -> LessThan
  | Next _, Start -> GreaterThan
  | Next selection, Next selection' ->
      match compare_selection selection selection' with
      | LessThan -> LessThan
      | Equal Eq -> Equal Eq
      | GreaterThan -> GreaterThan

let rec selection_functional_tail :
    type index sequence head tail head' tail' .
    (index, sequence, head, tail) selection ->
    (index, sequence, head', tail') selection ->
    (tail, tail') eq =
fun selection selection' ->
  match selection, selection' with
  | Start, Start -> Eq
  | Next selection, Next selection' ->
      let Eq = selection_functional_tail selection selection' in
      Eq

let selection_functional_head :
    type index sequence head head' tail tail'.
    ([`Succ of index], sequence, head, tail) selection ->
    ([`Succ of index], sequence, head', tail') selection ->
    (head, head') eq =
fun selection selection' ->
  match selection, selection' with
  | Next selection, Next selection' ->
      let Eq = selection_functional_tail selection selection' in
      Eq

let rec equal_variable : type index_a index_b arity_a arity_b a b positive_a
    positive_b direct_a direct_b .
  (index_a, arity_a, a, positive_a, direct_a) variable ->
  (index_b, arity_b, b, positive_b, direct_b) variable ->
  ((index_a, index_b) eq, unit) result =
fun index_a index_b ->
  match index_a, index_b with
  | VFirst, VFirst -> Ok Eq
  | VNext index_a, VNext index_b ->
      begin match equal_variable index_a index_b with
      | Ok Eq -> Ok Eq
      | Error () -> Error ()
      end
  | _ -> Error ()

let attributes_empty = {
  typed = (fun _ -> None);
}

module type Type = sig
  type t
end

module Vector (T : UnaryType) = struct
  type ('a, 'occurrence) item =
    | None : (_, [`Absent]) item
    | Some : 'a T.t -> ('a, _) item

  type ('sequence, 'occurrences) t =
    | [] : (unit, unit) t
    | (::) : ('head, 'occurrence) item * ('tail, 'occurrences) t ->
        ('head * 'tail, 'occurrence * 'occurrences) t

  let rec get :
    type index sequence value positive occurrences .
    (index, sequence, value, positive, occurrences) variable ->
      (sequence, occurrences) t -> value T.t =
  fun index vector ->
    match index, vector with
    | VFirst, (Some head) :: _ -> head
    | VNext index, _ :: tail -> get index tail

  let rec make_transfer :
    type source sub arg sequence .
    (source, sub, arg) transfer_arguments -> (sequence, source) t ->
    ((sequence, arg) t, (sub, [`Absent]) eq) result =
  fun transfer items ->
    match transfer, items with
    | VTANil, [] -> Ok []
    | VTACons { head = Transfer; _ }, None :: _items ->
        Error Eq
    | VTACons { head = Transfer; tail }, Some item :: items ->
        begin match make_transfer tail items with
        | Ok tail -> Ok (Some item :: tail)
        | Error result -> Error result
        end
    | VTACons { head = Skip; tail = tail }, _item :: items ->
        begin match make_transfer tail items with
        | Ok tail -> Ok (None :: tail)
        | Error result -> Error result
        end

  type ('arity, 'rec_arity, 'kinds) make = {
      f : 'a 'structure 'ap 'an 'ad 'gadt .
        ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'ap, 'an, 'ad, 'gadt)
          desc -> ('arity, 'ad) t -> 'a T.t;
    }

  let rec make :
    type types structures subpositive subnegative subdirect arguments gadt .
    ('arity, 'rec_arity, 'kinds) make ->
    (types, structures, 'arity, 'rec_arity, 'kinds, arguments, gadt) vector ->
    ('positive, 'negative, 'direct, subpositive, subnegative, subdirect,
      arguments) transfer ->
    ('arity, 'direct) t ->
    (types, subdirect) t =
  fun f vector transfer items ->
    match vector, transfer with
    | VNil, VTNil -> []
    | VCons { head; tail },
      VTCons { head = (_, direct); tail = transfer_tail } ->
        begin match make_transfer direct items with
        | Ok arg_items ->
            Some (f.f head arg_items) :: make f tail transfer_tail items
        | Error Eq ->
            None :: make f tail transfer_tail items
        end

  type 'presence any =
    | None : [`Absent] any
    | Some : {
          item : 'a . 'a T.t;
        } -> _ any

  let rec append :
    type count types arity subarity directs direct subdirect presence .
    presence any ->
    (presence, directs) presences ->
    (count, directs) length ->
    (directs, direct, subdirect) append ->
    (count, types) length ->
    (types, arity, subarity) append  ->
    (arity, direct) t ->
    (subarity, subdirect) t =
  fun any presences count_directs direct count arity items ->
    match presences, count_directs, direct, count, arity with
    | Presences, Zero, Nil, Zero, Nil -> items
    | AddPresent presences, Succ count_directs, Add direct, Succ count,
      Add arity ->
        let items =
          append any presences count_directs direct count arity items in
        begin match any with
        | Some { item } -> Some item :: items
        end
    | AddAbsent presences, Succ count_directs, Add direct, Succ count,
      Add arity ->
        let items =
          append any presences count_directs direct count arity items in
        None :: items
    | _ -> .

  let rec to_sequence :
    type sequence occurrences .
    [`Present] any -> (sequence, occurrences) t -> sequence Sequence(T).t =
  fun any v ->
    match v with
    | [] -> []
    | head :: tail ->
        let head =
          match head with
          | None ->
              let Some { item } = any in
              item
          | Some head -> head in
        head :: to_sequence any tail
end

module type BinaryType = sig
  type ('a, 'b) t
end

module BinaryVector (T : BinaryType) = struct
  type ('a, 'b, 'occurrence) item =
    | None : (_, _, [`Absent]) item
    | Some : ('a, 'b) T.t -> ('a, 'b, _) item

  type ('a, 'b, 'occurrences) t =
    | [] : (unit, unit, unit) t
    | (::) : ('head_a, 'head_b, 'occurrence) item *
        ('tail_a, 'tail_b, 'occurrences) t ->
        ('head_a * 'tail_a, 'head_b * 'tail_b, 'occurrence * 'occurrences) t

  let rec get :
    type index a b value_a value_b positive occurrences .
    (index, a, value_a, positive, occurrences) variable ->
    (index, b, value_b, positive, occurrences) variable ->
      (a, b, occurrences) t -> (value_a, value_b) T.t =
  fun index_a index_b vector ->
    match index_a, index_b, vector with
    | VFirst, VFirst, (Some head) :: _ -> head
    | VNext index_a, VNext index_b, _ :: tail -> get index_a index_b tail

  let rec make_transfer :
    type source sub arg a b .
    (source, sub, arg) transfer_arguments -> (a, b, source) t ->
    ((a, b, arg) t, (sub, [`Absent]) eq) result =
  fun transfer items ->
    match transfer, items with
    | VTANil, [] -> Ok []
    | VTACons { head = Transfer; _ }, None :: _items ->
        Error Eq
    | VTACons { head = Transfer; tail }, Some item :: items ->
        begin match make_transfer tail items with
        | Ok tail -> Ok (Some item :: tail)
        | Error result -> Error result
        end
    | VTACons { head = Skip; tail = tail }, _item :: items ->
        begin match make_transfer tail items with
        | Ok tail -> Ok (None :: tail)
        | Error result -> Error result
        end

  type ('arity_a, 'arity_b, 'rec_arity, 'kinds, 'gadt_a, 'gadt_b) make = {
      f : 'a 'b 'structure 'ap 'an 'ad .
        ('a, 'structure, 'arity_a, 'rec_arity, 'kinds, 'ap, 'an, 'ad, 'gadt_a)
          desc ->
        ('b, 'structure, 'arity_b, 'rec_arity, 'kinds, 'ap, 'an, 'ad, 'gadt_b)
          desc -> ('arity_a, 'arity_b, 'ad) t -> ('a, 'b) T.t;
    }

  let rec make :
    type types_a types_b structures subpositive subnegative subdirect arguments
      gadt_a gadt_b .
    ('arity_a, 'arity_b, 'rec_arity, 'kinds, gadt_a, gadt_b) make ->
    (types_a, structures, 'arity_a, 'rec_arity, 'kinds, arguments, gadt_a)
      vector ->
    (types_b, structures, 'arity_b, 'rec_arity, 'kinds, arguments, gadt_b)
      vector ->
    ('positive, 'negative, 'direct, subpositive, subnegative, subdirect,
      arguments) transfer ->
    ('arity_a, 'arity_b, 'direct) t ->
    (types_a, types_b, subdirect) t =
  fun f vector_a vector_b transfer items ->
    match vector_a, vector_b, transfer with
    | VNil, VNil, VTNil -> []
    | VCons a, VCons b,
      VTCons { head = (_, direct); tail = transfer_tail } ->
        begin match make_transfer direct items with
        | Ok arg_items ->
            Some (f.f a.head b.head arg_items) ::
              make f a.tail b.tail transfer_tail items
        | Error Eq ->
            None :: make f a.tail b.tail transfer_tail items
        end

  type 'presence any =
    | None : [`Absent] any
    | Some : {
          item : 'a 'b . ('a, 'b) T.t;
        } -> _ any

  let rec append :
    type count directs types_a types_b a b sub_a sub_b direct subdirect
      presence .
    presence any ->
    (presence, directs) presences ->
    (count, directs) length ->
    (directs, direct, subdirect) append ->
    (count, types_a) length ->
    (types_a, a, sub_a) append  ->
    (count, types_b) length ->
    (types_b, b, sub_b) append  ->
    (a, b, direct) t ->
    (sub_a, sub_b, subdirect) t =
  fun any presences count_directs direct count_a a count_b b items ->
    match presences, count_directs, direct, count_a, a, count_b, b with
    | Presences, Zero, Nil, Zero, Nil, Zero, Nil -> items
    | AddPresent presences, Succ count_directs, Add direct, Succ count_a, Add a,
      Succ count_b, Add b ->
        let items =
          append any presences count_directs direct count_a a count_b b items in
        begin match any with
        | Some { item } -> Some item :: items
        end
    | AddAbsent presences, Succ count_directs, Add direct, Succ count_a, Add a,
      Succ count_b, Add b ->
        let items =
          append any presences count_directs direct count_a a count_b b items in
        None :: items
end

module ParameterizedVector (T : BinaryType) = struct
  type ('a, 'b, 'occurrence) item =
    | None : (_, _, [`Absent]) item
    | Some : ('a, 'b) T.t -> ('a, 'b, _) item

  type ('sequence, 'b, 'occurrences) t =
    | [] : (unit, _, unit) t
    | (::) : ('head, 'b, 'occurrence) item * ('tail, 'b, 'occurrences) t ->
        ('head * 'tail, 'b, 'occurrence * 'occurrences) t

  module Unary (U : Type) = struct
    module Item = struct
      type 'a t = ('a, U.t) T.t
    end

    module Unary = Vector (Item)

    let rec to_unary :
      type sequence occurrences .
      (sequence, U.t, occurrences) t ->
      (sequence, occurrences) Unary.t =
    fun vector ->
      match vector with
      | [] -> []
      | Some head :: tail -> Some head :: to_unary tail
      | None :: tail -> None :: to_unary tail

    include Unary
  end
end

module SignedVector (T : BinaryType) = struct
  type ('a, 'b, 'positive, 'negative) item =
    | None :  ('a, 'b, [`Absent], [`Absent]) item
    | P : ('a, 'b) T.t -> ('a, 'b, _, [`Absent]) item
    | N : ('b, 'a) T.t-> ('a, 'b, [`Absent], _) item
    | PN : (('a, 'b) T.t * ('b, 'a) T.t) -> ('a, 'b, _, _) item

  type ('a, 'b, 'positive, 'negative) t =
    | [] : (unit, unit, unit, unit) t
    | (::) : ('a, 'b, 'positive, 'negative) item *
        ('aa, 'bb, 'positive_tail, 'negative_tail) t
        -> ('a * 'aa, 'b * 'bb, 'positive * 'positive_tail,
          'negative * 'negative_tail) t

  let reverse_item :
    type positive negative .
    ('a, 'b, positive, negative) item ->
    ('b, 'a, negative, positive) item = function
    | None -> None
    | P p -> N p
    | N n -> P n
    | PN (p, n) -> PN (n, p)

  let pos : type negative .
        ('a, 'b, [`Present], negative) item -> ('a, 'b) T.t = function
    | P p | PN (p, _) -> p

  let rec get :
    type index a b a_value b_value positive negative direct .
    (index, a, a_value, positive, direct) variable ->
    (index, b, b_value, positive, direct) variable ->
      (a, b, positive, negative) t -> (a_value, b_value) T.t =
  fun a_index b_index vector ->
    match a_index, b_index, vector with
    | VFirst, VFirst, head :: _ -> pos head
    | VNext a_index, VNext b_index, _ :: tail -> get a_index b_index tail

  let rec reverse :
    type a b positive negative .
    (a, b, positive, negative) t ->
    (b, a, negative, positive) t =
  function
    | [] -> []
    | hd :: tl -> reverse_item hd :: reverse tl

  type ('a, 'b, 'positive, 'negative) symmetric_item =
    | SNone :  ('a, 'b, [`Absent], [`Absent]) symmetric_item
    | SPN : (('a, 'b) T.t * ('b, 'a) T.t) -> ('a, 'b, _, _) symmetric_item

  type ('a, 'b, 'positive, 'negative) symmetric =
    | [] : (unit, unit, unit, unit) symmetric
    | (::) : ('a, 'b, 'positive, 'negative) symmetric_item *
        ('aa, 'bb, 'positive_tail, 'negative_tail) symmetric
        -> ('a * 'aa, 'b * 'bb, 'positive * 'positive_tail,
          'negative * 'negative_tail) symmetric

  type ('a, 'b, 'sp, 'sn, 'ap, 'an) make_transfer =
    | TNone : ('a, 'b, [`Absent], [`Absent], 'ap, 'an) make_transfer
    | TP :
        ('a, 'b, 'ap, 'an) t -> ('a, 'b, _, [`Absent], 'ap, 'an) make_transfer
    | TN :
        ('a, 'b, 'an, 'ap) t -> ('a, 'b, [`Absent], _, 'ap, 'an) make_transfer
    | TPN :
        ('a, 'b, 'an, 'ap) symmetric -> ('a, 'b, _, _, 'an, 'ap)
          make_transfer

  let rec reverse_of_symmetric :
    type a b positive negative .
    (a, b, positive, negative) symmetric ->
    (a, b, negative, positive) symmetric =
  function
    | [] -> []
    | SPN (f, g) :: tl -> SPN (f, g) :: reverse_of_symmetric tl
    | SNone :: tl -> SNone :: reverse_of_symmetric tl

  let rec p_of_symmetric :
    type a b ap an .
    (a, b, ap, an) symmetric -> (a, b, ap, an) t =
  function full ->
    match full with
    | [] -> []
    | SPN (f, g) :: tail -> PN (f, g) :: p_of_symmetric tail
    | SNone :: tail -> None :: p_of_symmetric tail

  let rec n_of_symmetric :
    type a b ap an .
    (a, b, ap, an) symmetric -> (a, b, an, ap) t =
  function full ->
    match full with
    | [] -> []
    | SPN (f, g) :: tail -> PN (f, g) :: n_of_symmetric tail
    | SNone :: tail -> None :: n_of_symmetric tail

  let rec make_transfer :
    type p n sp sn ap an a b .
    (p, n, sp, sn, ap, an) transfer_matrix -> (a, b, p, n) t ->
    (a, b, sp, sn, ap, an) make_transfer =
  fun transfer items ->
    match transfer, items with
    | { pp = VTANil; pn = VTANil; np = VTANil; nn = VTANil }, [] -> TPN []
    | { pp = VTACons { head = pp_head; tail = pp };
        pn = VTACons { head = pn_head; tail = pn };
        np = VTACons { head = np_head; tail = np };
        nn = VTACons { head = nn_head; tail = nn }}, head :: tail ->
          match make_transfer { pp; pn; np; nn } tail with
          | TNone -> TNone
          | TP tail ->
              begin match pp_head, pn_head, np_head, nn_head, head with
              | _, _, _, _, PN item -> TP (PN item :: tail)
              | _, _, Transfer, _, P _ -> TNone
              | _, _, Skip, _, P item -> TP (P item :: tail)
              | Transfer, _, _, _, N _ -> TNone
              | Skip, _, _, _, N item -> TP (N item :: tail)
              | Transfer, _, _, _, None -> TNone
              | Skip, _, Transfer, _, None -> TNone
              | Skip, _, Skip, _, None -> TP (None :: tail)
              end
          | TN tail ->
              begin match pp_head, pn_head, np_head, nn_head, head with
              | _, _, _, _, PN item -> TN (PN item :: tail)
              | _, _, _, Transfer, P _ -> TNone
              | _, _, _, Skip, P item -> TN (P item :: tail)
              | _, Transfer, _, _, N _ -> TNone
              | _, Skip, _, _, N item -> TN (N item :: tail)
              | _, _, _, Transfer, None -> TNone
              | _, Transfer, _, Skip, None -> TNone
              | _, Skip, _, Skip, None -> TN (None :: tail)
              end
          | TPN tail ->
              begin match pp_head, pn_head, np_head, nn_head, head with
              | _, _, _, _, PN item -> TPN (SPN item :: tail)
              | _, Skip, _, Transfer, P item ->
                  TP (P item :: p_of_symmetric tail)
              | Transfer, Transfer, _, Transfer, P _item -> TNone
              | Skip, Transfer, Transfer, Skip, P item ->
                  TN (P item :: n_of_symmetric tail)
              | Transfer, Skip, _, _, N item ->
                  TN (N item :: n_of_symmetric tail)
              | Transfer, _, Transfer, Transfer, N _item -> TNone
              | Skip, Transfer, Transfer, Skip, N item ->
                  TP (N item :: p_of_symmetric tail)
              | Transfer, Transfer, Transfer, Transfer, None -> TNone
              | Skip, Transfer, Transfer, Skip, None -> TNone
              | Transfer, Skip, Skip, Transfer, None -> TNone
              | Skip, Skip, _, _, _ -> TPN (SNone :: tail)
              end

  type ('rec_arity, 'a_kinds, 'b_kinds) make = {
      f : 'a 'b 'structure 'a_arity 'b_arity 'ap 'an 'ad 'gadt .
        ('a, 'structure, 'a_arity, 'rec_arity, 'a_kinds, 'ap, 'an, 'ad,
          'gadt) desc ->
        ('b, 'structure, 'b_arity, 'rec_arity, 'b_kinds, 'ap, 'an, 'ad,
          'gadt) desc ->
          ('a_arity, 'b_arity, 'ap, 'an) t -> ('a, 'b) T.t;
    }

  let rec make :
    type a_types b_types structures arguments subpositive subnegative
          subdirect a_arity b_arity rec_arity gadt .
    (rec_arity, 'a_kinds, 'b_kinds) make ->
    (a_types, structures, a_arity, rec_arity, 'a_kinds, arguments, gadt)
      vector ->
    (b_types, structures, b_arity, rec_arity, 'b_kinds, arguments, gadt)
      vector ->
    ('positive, 'negative, 'direct, subpositive, subnegative, subdirect,
      arguments) transfer ->
    (a_arity, b_arity, 'positive, 'negative) t ->
    (a_types, b_types, subpositive, subnegative) t =
    fun f a_arguments b_arguments transfer items ->
      match a_arguments, b_arguments, transfer with
      | VNil, VNil, VTNil -> []
      | VCons { head = a_head; tail = a_tail },
        VCons { head = b_head; tail = b_tail },
        VTCons { head = (matrix, _); tail = transfer_tail } ->
          begin match make_transfer matrix items with
          | TPN args ->
              PN (
                f.f a_head b_head (p_of_symmetric args),
                f.f b_head a_head
                  (reverse (p_of_symmetric (reverse_of_symmetric args)))) ::
              make f a_tail b_tail transfer_tail items
          | TP args ->
              P (f.f a_head b_head args) ::
              make f a_tail b_tail transfer_tail items
          | TN args ->
              N (f.f b_head a_head (reverse args)) ::
              make f a_tail b_tail transfer_tail items
          | TNone ->
              None :: make f a_tail b_tail transfer_tail items
          end
end

module type Desc_type = sig
  type ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
    'direct, 'gadt) t
end

module Desc_vector (T : Desc_type) = struct
  type ('sequence, 'structure, 'arities, 'rec_arity, 'kinds, 'positive,
         'negative, 'direct, 'gadts) t =
    | [] :
        (unit, 'structure, unit, 'rec_arity, 'kinds, 'positive, 'negative,
          'direct, 'gadts) t
    | (::) :
        ('head, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, 'gadt) T.t *
        ('tail, 'structure, 'arities, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, 'gadts) t ->
          ('head * 'tail, 'structure, 'arity * 'arities, 'rec_arity,
            'kinds, 'positive, 'negative, 'direct, 'gadt * 'gadts) t
end

module Section = struct
  type ('index, 'sequences, 'sequence, 'subsequences) t =
    | [] : (_, unit, unit, unit) t
    | (::) :
        ('index, 'head, 'item, 'first) selection
        * ('index, 'tail, 'items, 'others) t ->
          ('index, 'head * 'tail, 'item * 'items, 'first * 'others) t

  type ('index, 'sequences, 'subsequences) some =
    | Some :
        ('index, 'sequences, 'sequence, 'subsequences) t ->
          ('index, 'sequences, 'subsequences) some
end

type ('a_arity, 'b_arity, 'rec_arity, 'kinds_a, 'kinds_b, 'positive, 'negative,
       'direct, 'gadt) map = {
    f : 'a 'b 'structure .
      ('a, 'structure, 'a_arity, 'rec_arity, 'kinds_a, 'positive, 'negative,
        'direct, 'gadt) desc ->
      ('b, 'structure, 'b_arity, 'rec_arity, 'kinds_b, 'positive, 'negative,
        'direct, 'gadt) desc -> 'a -> 'b
  }

module type Mapper = sig
  type positive

  type negative

  type rec_arity

  type gadt

  type a_arity

  type b_arity

  type ('a_arity, 'b_arity, 'positive, 'negative) t

  val initial : (a_arity, b_arity, positive, negative) t

  val grow :
      ('a_arity, 'b_arity, 'positive, 'negative) t ->
        ('a * 'a_arity, 'a * 'b_arity, _ * 'positive,
          _ * 'negative) t

  val map :
      ('a_arity, 'b_arity, 'positive, 'negative) t ->
      ('a, 'structure, 'a_arity, rec_arity, 'kinds, 'positive, 'negative,
        'direct, gadt) desc ->
      ('b, 'structure, 'b_arity, rec_arity, 'kinds, 'positive, 'negative,
        'direct, gadt) desc -> 'a -> 'b
end

type 'count map_length =
  | MapLength : {
      length : ('count, _) length;
    } ->
      'count map_length

type ('types, 'tail) make_append =
  | MakeAppend : ('types, 'tail, 'append) append ->
      ('types, 'tail) make_append

let rec make_append :
  type count types .
  (count, types) length ->
  (types, 'tail) make_append =
  fun length ->
    match length with
    | Zero -> MakeAppend Nil
    | Succ length ->
        let MakeAppend result = make_append length in
        MakeAppend (Add result)

module MapperTools (M : Mapper) = struct
  type ('types, 'arity_a, 'arity_b, 'subpositive, 'subnegative) make_variables =
    | MakeVariables : {
        subarity_a : ('types, 'arity_a, 'subarity_a) append;
        subarity_b : ('types, 'arity_b, 'subarity_b) append;
        mapper :
          ('subarity_a, 'subarity_b, 'subpositive, 'subnegative) M.t;
      } ->
        ('types, 'arity_a, 'arity_b, 'subpositive, 'subnegative) make_variables

  let rec make_variables_aux :
    type count types arity_a arity_b positive negative positives negatives
      subpositive subnegative .
    (count, types) length ->
    (count, positives) length ->
    (positives, positive, subpositive) append ->
    (count, negatives) length ->
    (negatives, negative, subnegative) append ->
    (arity_a, arity_b, positive, negative) M.t ->
    (types, arity_a, arity_b, subpositive, subnegative) make_variables =
  fun count positive_count positive negative_count negative mapper ->
    match count, positive_count, positive, negative_count, negative
    with
    | Zero, Zero, Nil, Zero, Nil ->
        MakeVariables { subarity_a = Nil; subarity_b = Nil; mapper }
    | Succ count, Succ positive_count, Add positive, Succ negative_count,
      Add negative->
        let MakeVariables { subarity_a; subarity_b; mapper } =
          make_variables_aux count positive_count positive negative_count
            negative mapper in
        MakeVariables {
            subarity_a = Add subarity_a;
            subarity_b = Add subarity_b;
            mapper = M.grow mapper;
          }

  let make_variables length variables mapper =
    let { positive_count; positive; negative_count; negative; _ } =
      variables in
    make_variables_aux length positive_count positive negative_count negative
      mapper
end

let rec append_functional :
  type prefix suffix result1 result2 .
  (prefix, suffix, result1) append ->
  (prefix, suffix, result2) append ->
  (result1, result2) eq =
fun append1 append2 ->
  match append1, append2 with
  | Nil, Nil -> Eq
  | Add append1, Add append2 ->
      let Eq = append_functional append1 append2 in
      Eq

module Tuple = struct
  module Tuple = struct
    type ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) structure =
    | [] :
        (unit, unit, 'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct,
          'gadt) structure
    | (::) :
        ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
          'direct, 'gadt) desc *
        ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) structure ->
        ('a * 'types, 'structure * 'structures, 'arity, 'rec_arity,
          'kinds, 'positive, 'negative, 'direct, 'gadt) structure

    let rec of_desc :
      type types structures .
      (types, structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
        'direct, 'gadt) tuple_structure ->
      (types, structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
        'direct, 'gadt) structure =
    fun tuple ->
      match tuple with
      | TNil -> []
      | TCons { head; tail } -> head :: of_desc tail

    type ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
           'direct, 'gadt) t = {
        structure :
          ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) structure;
        values : 'types;
      }
  end

  include Tuple

  module Item = struct
    type ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) t = {
        desc :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
            'direct, 'gadt) desc;
        value : 'a;
      }
  end

  let rec map :
    type a_types b_types structures gadt .
    ('a_arity, 'b_arity, 'rec_arity, 'kinds_a, 'kinds_b, 'positive, 'negative,
      'direct, gadt) map ->
    (a_types, structures, 'a_arity, 'rec_arity, 'kinds_a, 'positive, 'negative,
      'direct, gadt) tuple_structure ->
    (b_types, structures, 'b_arity, 'rec_arity, 'kinds_b, 'positive, 'negative,
      'direct, gadt) tuple_structure ->
    a_types -> b_types =
  fun f a_tuple b_tuple a_types ->
    match a_tuple, b_tuple, a_types with
    | TNil, TNil, () -> ()
    | TCons { head = a_head; tail = a_tail },
      TCons { head = b_head; tail = b_tail },
      (head, tail) ->
        (f.f a_head b_head head, map f a_tail b_tail tail)
    | _ -> .

  type ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
         'direct, 'gadt) fold =
    | Fold : {
          index : ([`Succ of 'index], 'types, 'a, _) selection;
          index_structure :
            ([`Succ of 'index], 'structures, 'structure, _) selection;
          desc :
            ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
              'direct, 'gadt) desc;
          value : 'a;
        } ->
          ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) fold

  let fold
      (f :
        ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
          'direct, 'gadt) fold -> 'acc -> 'acc)
      (tuple :
        ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
          'direct, 'gadt) t) acc =
    let rec aux :
      type index head head_structure subtypes substructures .
      (index, 'types, head, subtypes) selection ->
      (index, 'structures, head_structure, substructures) selection ->
      (subtypes, substructures, 'arity, 'rec_arity, 'kinds, 'positive,
        'negative, 'direct, 'gadt) structure ->
      subtypes -> 'a -> 'a =
    fun index index_structure structure values acc ->
      match structure, values with
      | [], () -> acc
      | desc :: s_tail, (value, v_tail) ->
          let index = Next index in
          let index_structure = Next index_structure in
          let acc = f (Fold { index; index_structure; desc; value }) acc in
          aux index index_structure s_tail v_tail acc in
    aux Start Start tuple.structure tuple.values acc

  module Items = Desc_vector (Item)

  module Tuples = Desc_vector (Tuple)

  type ('index, 'structure, 'structures, 'arities, 'tuples,
        'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadts)
          structure_find =
    | Structure_find : {
          section : ([`Succ of 'index], 'tuples, 'section, 'others) Section.t;
          items :
            ('section, 'structure, 'arities, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadts) Items.t;
          others :
            ('others, 'structures, 'arities, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadts) Tuples.t
        } ->
          ('index, 'structure, 'structures, 'arities, 'tuples,
            'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadts)
            structure_find

  type ('tuples, 'structures, 'arities, 'rec_arity, 'kinds, 'positive,
        'negative, 'direct, 'gadts) find =
    | Find : {
          index :
            ([`Succ of 'index], 'structures, 'structure, _) selection;
          section : ([`Succ of 'index], 'tuples, 'section, _) Section.t;
          items :
            ('section, 'structure, 'arities, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadts) Items.t;
    } ->
        ('tuples, 'structures, 'arities, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, 'gadts) find

  let find :
    type arities gadts .
        ('tuple * 'tuples, 'structures, arities, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, gadts) Tuples.t ->
        (('tuple * 'tuples, 'structures, arities, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, gadts) find -> 'a option) ->
        'a option =
  fun tuples f ->
    let rec make_section :
        type index current other_structures base_structures
          tail tail_section current_section structure
          tail_structures arities gadts .
        ([`Succ of index], base_structures, current, tail_structures)
          selection ->
        (index, tail_section, current_section, tail) Section.t ->
        (tail, structure * other_structures, arities, 'rec_arity,
          'kinds, 'positive, 'negative, 'direct, gadts) Tuples.t ->
        (index, structure, other_structures, arities, tail_section,
          'rec_arity, 'kinds, 'positive, 'negative, 'direct, gadts)
            structure_find =
    fun index section tuples ->
      match section, tuples with
      | [], [] ->
          Structure_find { section = []; items = []; others = [] }
      | head_section :: tail_section, head :: tail ->
          let Structure_find tail =
            make_section index tail_section tail in
          let desc :: structure = head.structure in
          let (value, values) = head.values in
          Structure_find {
            section = Next head_section :: tail.section;
            items = { desc; value } :: tail.items;
            others = { structure; values } :: tail.others
          } in
    let rec aux :
        type index subtuple subtuples substructures structure section .
        (index, 'structures, structure, substructures) selection ->
        (index, 'tuple * 'tuples, section, subtuple * subtuples) Section.t ->
        (subtuple * subtuples, substructures, arities, 'rec_arity, 'kinds,
          'positive, 'negative, 'direct, gadts) Tuples.t ->
        'a option =
    fun index section tuples ->
      let first :: tail = tuples in
      let head_section :: tail_section = section in
      match first with
      | { structure = []; values = () } -> None
      | { structure = desc :: structure;
          values = (value, values)} ->
          let index = Next index in
          let Structure_find { section; items; others } =
            make_section index tail_section tail in
          let section : (_, _, _, _) Section.t = Next head_section :: section in
          begin match
            f ((Find { index; section;
              items = { desc; value } :: items } :
                ('tuple * 'tuples, 'structures, arities, 'rec_arity, 'kinds,
                  'positive, 'negative, 'direct, gadts) find ))
          with
          | None -> aux index section ({ structure; values } :: others)
          | result -> result
          end
      in
    let rec start_section :
        type subtuples arities gadts .
        (subtuples, 'structures, arities, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, gadts) Tuples.t ->
        ([`Zero], subtuples, subtuples) Section.some =
    fun tuples ->
      match tuples with
      | [] -> Some []
      | _head :: tail ->
          let Some tail = start_section tail in
          Some (Start :: tail) in
    let Some section = start_section tuples in
    aux Start section tuples
end

module Record = struct
  module Record = struct
    type ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
           'direct, 'gadt) t = {
        structure :
          ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) record_structure;
        values : 'types;
      }
  end

  module Field = struct
    type ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) t = {
        field :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
            'direct, 'gadt) record_field;
        value : 'a;
      }
  end

  include Record

  let rec map :
    type a_types b_types structures gadt .
    ('a_arity, 'b_arity, 'rec_arity, [> `Poly of unit] as 'kinds_a, 'kinds_b,
      'positive, 'negative, 'direct, gadt) map ->
    (a_types, structures, 'a_arity, 'rec_arity, 'kinds_a, 'positive, 'negative,
      'direct, gadt) record_structure ->
    (b_types, structures, 'b_arity, 'rec_arity, 'kinds_b, 'positive, 'negative,
      'direct, gadt) record_structure ->
    a_types -> b_types =
  fun f a_record b_record a_types ->
    match a_record, b_record, a_types with
    | RNil, RNil, () -> ()
    | RCons { head = Mono a_head; tail = a_tail },
      RCons { head = Mono b_head; tail = b_tail },
      (head, tail) ->
        (f.f a_head.desc b_head.desc head, map f a_tail b_tail tail)
    | _ -> .

  module Map (M : Mapper) = struct
    module Tools = MapperTools (M)

    let map_poly :
      ('arity_a, 'arity_b, 'positive, 'negative) M.t ->
      ('count, [`Absent], 'positive, 'negative, 'direct, 'positives,
        'negatives, 'directs, 'subpositive, 'subnegative, 'subdirect)
        subvariables ->
      ('a, 'structure, 'arity_a, 'rec_arity, 'kinds, 'subpositive,
        'subnegative, 'subdirect, M.gadt, 'count) forall_destruct ->
      (('b, 'structure, 'arity_b, 'rec_arity, 'kinds, 'subpositive,
        'subnegative, 'subdirect, M.gadt, 'count) forall_construct -> 'b) ->
      'a -> 'b =
    fun mapper variables_a destruct_a construct_b value ->
      let forall_construct :
        type forall b subarity .
        (_, forall) length ->
        (forall, 'arity_b, subarity) append ->
        (b, _, subarity, M.rec_arity, 'kinds, 'subpositive,
          'subnegative, 'subdirect, 'gadt) desc ->
        b =
      fun count arity_b desc_b ->
        let MakeAppend arity_a = make_append count in
        let ForallDestruct { desc = desc_a; destruct } =
          destruct_a.forall_destruct count arity_a in
        let MakeVariables { mapper; subarity_a; subarity_b } =
          Tools.make_variables count variables_a mapper in
        let Eq = append_functional arity_a subarity_a in
        let Eq = append_functional arity_b subarity_b in
        M.map mapper desc_a desc_b (destruct value) in
      construct_b { forall_construct }

    let rec map_with :
      type types_a types_b arity_a arity_b structure kinds .
      (arity_a, arity_b, 'positive, 'negative) M.t ->
      (types_a, structure, arity_a, M.rec_arity, kinds, 'positive,
        'negative, 'direct, M.gadt) record_structure ->
      (types_b, structure, arity_b, M.rec_arity, kinds, 'positive,
        'negative, 'direct, M.gadt) record_structure ->
      types_a -> types_b =
    fun mapper record_a record_b types_a ->
      match record_a, record_b, types_a with
      | RNil, RNil, () -> ()
      | RCons a, RCons b, (head, tail) ->
          let head =
            match a.head, b.head with
            | Mono a, Mono b ->
                M.map mapper a.desc b.desc head
            | Poly a, Poly b ->
                let Eq =
                  append_functional a.variables.positive b.variables.positive in
                let Eq =
                  append_functional a.variables.negative b.variables.negative in
                let Eq =
                  append_functional a.variables.direct b.variables.direct in
                map_poly mapper a.variables a.destruct b.construct head in
          head, map_with mapper a.tail b.tail tail
      | _ -> .

    let map record_a record_b types_a =
      map_with M.initial record_a record_b types_a
  end

  type ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
         'direct, 'gadt) fold =
    | Fold : {
          index : ([`Succ of 'index], 'types, 'a, _) selection;
          index_structure :
            ([`Succ of 'index], 'structures, 'structure, _) selection;
          field :
            ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
              'direct, 'gadt) record_field;
          value : 'a;
        } ->
          ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) fold

  let fold
      (f :
        ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
          'direct, 'gadt) fold -> 'acc -> 'acc)
      (record :
        ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
          'direct, 'gadt) t) acc =
    let rec aux :
      type index head head_structure subtypes substructures .
      (index, 'types, head, subtypes) selection ->
      (index, 'structures, head_structure, substructures) selection ->
      (subtypes, substructures, 'arity, 'rec_arity, 'kinds, 'positive,
        'negative, 'direct, 'gadt) record_structure ->
      subtypes -> 'a -> 'a =
    fun index index_structure structure values acc ->
      match structure, values with
      | RNil, () -> acc
      | RCons { head = field; tail = s_tail }, (value, v_tail) ->
          let index = Next index in
          let index_structure = Next index_structure in
          let acc = f (Fold { index; index_structure; field; value }) acc in
          aux index index_structure s_tail v_tail acc in
    aux Start Start record.structure record.values acc

  module Fields = Desc_vector (Field)

  module Records = Desc_vector (Record)

  type ('index, 'structure, 'structures, 'arities, 'records,
        'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadts)
          structure_find =
    | Structure_find : {
          section : ([`Succ of 'index], 'records, 'section, 'others) Section.t;
          items :
            ('section, 'structure, 'arities, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadts) Fields.t;
          others :
            ('others, 'structures, 'arities, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadts) Records.t
        } ->
          ('index, 'structure, 'structures, 'arities, 'records,
            'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadts)
            structure_find

  type ('records, 'structures, 'arities, 'rec_arity, 'kinds, 'positive,
        'negative, 'direct, 'gadts) find =
    | Find : {
          index :
            ([`Succ of 'index], 'structures, 'structure, _) selection;
          section : ([`Succ of 'index], 'records, 'section, _) Section.t;
          items :
            ('section, 'structure, 'arities, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadts) Fields.t;
    } ->
        ('records, 'structures, 'arities, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, 'gadts) find

  let find :
    type arities gadts .
        ('record * 'records, 'structures, arities, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, gadts) Records.t ->
        (('record * 'records, 'structures, arities, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, gadts) find -> 'a option) ->
        'a option =
  fun records f ->
    let rec make_section :
        type index current other_structures base_structures
          tail tail_section current_section structure
          tail_structures arities gadts .
        ([`Succ of index], base_structures, current, tail_structures)
          selection ->
        (index, tail_section, current_section, tail) Section.t ->
        (tail, structure * other_structures, arities, 'rec_arity,
          'kinds, 'positive, 'negative, 'direct, gadts) Records.t ->
        (index, structure, other_structures, arities, tail_section,
          'rec_arity, 'kinds, 'positive, 'negative, 'direct, gadts)
            structure_find =
    fun index section records ->
      match section, records with
      | [], [] ->
          Structure_find { section = []; items = []; others = [] }
      | head_section :: tail_section, head :: tail ->
          let Structure_find tail =
            make_section index tail_section tail in
          let RCons { head = field; tail = structure } = head.structure in
          let (value, values) = head.values in
          Structure_find {
            section = Next head_section :: tail.section;
            items = { field; value } :: tail.items;
            others = { structure; values } :: tail.others
          } in
    let rec aux :
        type index subrecord subrecords substructures structure section .
        (index, 'structures, structure, substructures) selection ->
        (index, 'record * 'records, section, subrecord * subrecords) Section.t ->
        (subrecord * subrecords, substructures, arities, 'rec_arity, 'kinds,
          'positive, 'negative, 'direct, gadts) Records.t ->
        'a option =
    fun index section records ->
      let first :: tail = records in
      let head_section :: tail_section = section in
      match first with
      | { structure = RNil; values = () } -> None
      | { structure = RCons { head = field; tail = structure };
          values = (value, values)} ->
          let index = Next index in
          let Structure_find { section; items; others } =
            make_section index tail_section tail in
          let section : (_, _, _, _) Section.t = Next head_section :: section in
          begin match
            f ((Find { index; section;
              items = { field; value } :: items } :
                ('record * 'records, 'structures, arities, 'rec_arity, 'kinds,
                  'positive, 'negative, 'direct, gadts) find ))
          with
          | None -> aux index section ({ structure; values } :: others)
          | result -> result
          end
      in
    let rec start_section :
        type subrecords arities gadts .
        (subrecords, 'structures, arities, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, gadts) Records.t ->
        ([`Zero], subrecords, subrecords) Section.some =
    fun records ->
      match records with
      | [] -> Some []
      | _head :: tail ->
          let Some tail = start_section tail in
          Some (Start :: tail) in
    let Some section = start_section records in
    aux Start section records
end

module Constructor = struct
  let rec map_eqs :
    type a_eqs structure_eqs b_eqs kinds_a kinds_b .
    (a_eqs, structure_eqs, kinds_a, 'gadt) constructor_eqs ->
    (b_eqs, structure_eqs, kinds_b, 'gadt) constructor_eqs ->
    a_eqs -> b_eqs =
  fun a_eqs b_eqs eqs ->
    match a_eqs, b_eqs, eqs with
    | ENil, ENil, () -> ()
    | ECons { head = head_a; tail = tail_a },
      ECons { head = head_b; tail = tail_b },
      (eq, eq_tail) ->
        let Eq = selection_functional_head head_a head_b in
        (eq, map_eqs tail_a tail_b eq_tail)

  let rec map_choice :
    type a_arity b_arity rec_arity a_cases b_cases structures positive
      negative direct gadt .
    (a_arity, b_arity, rec_arity,
     [> `Exists of unit] as 'kinds_a, 'kinds_b, positive,
      negative, direct, gadt) map ->
    (a_cases, structures, a_arity, rec_arity, 'kinds_a, positive, negative,
      direct, gadt) constructors ->
    (b_cases, structures, b_arity, rec_arity, 'kinds_b, positive, negative,
      direct, gadt) constructors ->
    a_cases choice -> b_cases choice =
  fun f a_constructors b_constructors a_choice ->
    match a_constructors, b_constructors, a_choice with
    | CCons { tail = a_constructors; _ },
      CCons { tail = b_constructors; _ },
      CNext a_choice ->
        CNext (map_choice f a_constructors b_constructors a_choice)
    | CCons { head = Constructor { kind = a_constructor; eqs = a_eqs; _ }; _ },
      CCons { head = Constructor { kind = b_constructor; eqs = b_eqs; _ }; _ },
      CFirst (a_types, eqs) ->
        let eqs = map_eqs a_eqs b_eqs eqs in
        CFirst begin match a_constructor, b_constructor with
        | CTuple a_tuple, CTuple b_tuple ->
            (Tuple.map f a_tuple b_tuple a_types, eqs)
        | CRecord a_record, CRecord b_record ->
            (Record.map f a_record b_record a_types, eqs)
        | _ -> .
        end
    | _ -> .

  module Map (M : Mapper) = struct
    module Tools = MapperTools (M)

    module RecordMap = Record.Map (M)

    let map_kind :
      type structure kinds .
      ('a_arity, 'b_arity, 'subpositive, 'subnegative) M.t ->
      ('types_a, structure, 'a_arity, M.rec_arity, kinds, 'subpositive,
        'subnegative, 'subdirect, M.gadt) constructor_kind ->
      ('types_b, structure, 'b_arity, M.rec_arity, kinds, 'subpositive,
        'subnegative, 'subdirect, M.gadt) constructor_kind ->
      'types_a -> 'types_b =
    fun mapper a b values ->
      match a, b with
      | CTuple a_tuple, CTuple b_tuple ->
          Tuple.map { f = fun x -> M.map mapper x } a_tuple b_tuple values
      | CRecord a_record, CRecord b_record ->
          RecordMap.map_with mapper a_record b_record values

    let rec map_choice :
      type a_cases b_cases structures kinds .
      (a_cases, structures, M.a_arity, M.rec_arity, kinds, M.positive,
        M.negative, 'direct, M.gadt) constructors ->
      (b_cases, structures, M.b_arity, M.rec_arity, kinds, M.positive,
        M.negative, 'direct, M.gadt) constructors ->
      a_cases choice -> b_cases choice =
    fun a_constructors b_constructors a_choice ->
      match a_constructors, b_constructors, a_choice with
      | CCons { tail = a_constructors; _ },
        CCons { tail = b_constructors; _ },
        CNext a_choice ->
          CNext (map_choice a_constructors b_constructors a_choice)
      | CCons { head = Constructor a; _ },
        CCons { head = Constructor b; _ },
        CFirst (values, eqs) ->
          let eqs = map_eqs a.eqs b.eqs eqs in
          CFirst (map_kind M.initial a.kind b.kind values, eqs)
      | CCons { head = Exists a; _ },
        CCons { head = Exists b; _ },
        CFirst values ->
          let Eq = selection_functional_head a.selection b.selection in
          let ExistsDestruct a' = a.destruct values in
          let MakeVariables { mapper; subarity_a; subarity_b } =
            Tools.make_variables a'.exists_count a.variables M.initial in
          let Eq =
            append_functional a'.exists subarity_a in
          let Eq =
            append_functional a.variables.positive b.variables.positive in
          let Eq =
            append_functional a.variables.negative b.variables.negative in
          let Eq =
            append_functional a.variables.direct b.variables.direct in
          let ExistsConstruct b' =
            b.construct a'.exists_count a'.constraints subarity_b in
          let values =
            b'.construct (map_kind mapper a'.kind b'.kind a'.values) in
          CFirst values
      | _ -> .
  end

  type ('types, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
        'direct, 'gadt) kind =
    | Tuple :
        ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
          'direct, 'gadt) Tuple.t ->
          ('types, [`Tuple of 'structures], 'arity, 'rec_arity, 'kinds,
            'positive, 'negative, 'direct, 'gadt) kind
    | Record :
        ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
          'direct, 'gadt) Record.t ->
          ('types, [`Record of 'structures], 'arity, 'rec_arity, 'kinds,
            'positive, 'negative, 'direct, 'gadt) kind

  type ('value, 'constructor, 'arity, 'positive, 'negative, 'direct, 'values,
         'structure, 'subarity, 'subpositive, 'subnegative, 'subdirect, 'kinds)
         link =
    | Constructor :
        ('values * 'eqs, [`Constructor of 'structure * 'structure_eq], 'arity,
          'positive, 'negative, 'direct, 'values, 'structure, 'arity,
          'positive, 'negative, 'direct, 'kinds) link
    | Exists : {
          presence : ('kinds, 'local) presence;
          exists_count : ('count, 'exists) length;
          variables : ('count, 'local, 'positive, 'negative, 'direct,
            'positives, 'negatives, 'directs, 'subpositive, 'subnegative,
            'subdirect) subvariables;
          constraints : ('constraints, 'exists) gadt_constraints;
          exists : ('exists, 'arity, 'subarity) append;
        } ->
          (_,
            [`Exists of 'index * 'count * 'structure * 'local * 'positives
              * 'negatives * 'directs],
            'arity, 'positive,
            'negative, 'direct, _, 'structure, 'subarity,
            'subpositive, 'subnegative, 'subdirect,
            [> `Exists] as 'kinds) link

  type ('cases, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
        'direct, 'gadt) destruct =
    | Destruct : {
          constructors :
            ('cases, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadt) constructors;
          index : ([`Succ of 'index], 'cases, 'value, _) selection;
          index_desc :
            ([`Succ of 'index], 'structures, 'constructor, _)
              selection;
          constructor :
            ('value, 'constructor, 'arity, 'rec_arity,
              'kinds, 'positive, 'negative, 'direct, 'gadt) constructor;
          link :
            ('value, 'constructor, 'arity, 'positive, 'negative, 'direct,
              'values, 'structure, 'subarity, 'subpositive, 'subnegative,
              'subdirect, 'kinds) link;
          values : 'values;
          name : string;
          kind :
            ('values, 'structure, 'subarity, 'rec_arity, 'kinds, 'subpositive,
              'subnegative, 'subdirect, 'gadt) kind;
        } ->
            ('cases, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadt) destruct

  let rec destruct_choice :
    type index types structure tail_cases tail_structures arity rec_arity
      kinds positive negative direct gadt .
    ('cases, 'structures, arity, rec_arity, kinds, positive, negative,
      direct, gadt) constructors ->
    (index, 'cases, types, tail_cases) selection ->
    (index, 'structures, structure, tail_structures) selection ->
    (tail_cases, tail_structures, arity, rec_arity, kinds, positive,
      negative, direct, gadt) constructors ->
    tail_cases choice -> ('cases, 'structures, arity, rec_arity, kinds,
      positive, negative, direct, gadt) destruct =
  fun constructors index index_desc subconstructors choice ->
    match subconstructors, choice with
    | CCons { tail; _ }, CNext choice ->
        destruct_choice constructors (Next index) (Next index_desc) tail choice
    | CCons { head; _ }, CFirst arguments ->
        let make name values kind link =
          Destruct {
            constructors; index = Next index; index_desc = Next index_desc;
            constructor = head; values; name; kind; link } in
        begin match head, arguments with
        | Constructor cstr, (values, _eqs) ->
            begin match cstr.kind with
            | CTuple structure ->
                let structure = Tuple.of_desc structure in
                make cstr.name values (Tuple { structure; values }) Constructor
            | CRecord structure ->
                make cstr.name values (Record { structure; values }) Constructor
            end
        | Exists { presence; variables; destruct; name; _ }, values ->
            let ExistsDestruct
              { exists_count; exists; constraints; values; kind } =
              destruct values in
            let link =
              Exists { presence; exists_count; constraints; exists;
                variables } in
            begin match kind with
            | CTuple structure ->
                let structure = Tuple.of_desc structure in
                make name values (Tuple { structure; values }) link
            | CRecord structure ->
                make name values (Record { structure; values }) link
            end
        end
    | _ -> .

  let destruct constructors x =
    destruct_choice constructors Start Start constructors x
end

module Variant = struct
  type ('types, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
        'direct, 'gadt) argument =
    | None :
        (unit, unit, 'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct,
          'gadt)
          argument
    | Some : {
          desc :
            ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
              'direct, 'gadt) desc;
          value : 'a;
        } ->
          ('a * unit, 'structure * unit, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) argument

  let rec map_choice :
    type a_cases b_cases structures .
      ('a_arity, 'b_arity, 'rec_arity, 'kinds_a, 'kinds_b, 'positive, 'negative,
        'direct, 'gadt) map ->
    (a_cases, structures, 'a_arity, 'rec_arity, 'kinds_a, 'positive, 'negative,
      'direct, 'gadt) variant_constructors ->
    (b_cases, structures, 'b_arity, 'rec_arity, 'kinds_b, 'positive, 'negative,
      'direct, 'gadt) variant_constructors ->
    a_cases choice -> b_cases choice =
  fun f a_constructors b_constructors a_choice ->
    match a_constructors, b_constructors, a_choice with
    | VCCons { tail = a_constructors; _ },
      VCCons { tail = b_constructors; _ },
      CNext a_choice ->
        CNext (map_choice f a_constructors b_constructors a_choice)
    | VCCons { head = VConstructor { argument = a_argument; _ }; _ },
      VCCons { head = VConstructor { argument = b_argument; _ }; _ },
      CFirst arguments ->
        begin match a_argument, b_argument, arguments with
        | VNone, VNone, () -> CFirst ()
        | VSome a_struct, VSome b_struct, (head, ()) ->
            CFirst (f.f a_struct b_struct head, ())
        end
    | VCCons { head = VInherit a_argument; _ },
      VCCons { head = VInherit b_argument; _ },
      CFirst argument ->
        CFirst (f.f a_argument b_argument argument)
    | _ -> .

  type ('types, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
        'direct, 'gadt) kind =
    | Constructor : {
          name : string;
          argument :
            ('types, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadt) argument;
        } ->
          ('types, [`Constr of 'structure], 'arity, 'rec_arity, 'kinds,
            'positive, 'negative, 'direct, 'gadt) kind
    | Inherit : {
          desc :
            ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
              'direct, 'gadt) desc;
          value : 'a;
        } ->
          ('a, [`Inherit of 'structure], 'arity, 'rec_arity, 'kinds,
            'positive, 'negative, 'direct, 'gadt) kind

  type ('cases, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
        'direct, 'gadt) destruct =
    | Destruct : {
          constructors :
            ('cases, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadt) variant_constructors;
          index : ([`Succ of 'index], 'cases, 'types, _) selection;
          index_desc :
            ([`Succ of 'index], 'structures, 'structure, _) selection;
          constructor :
            ('types, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadt) variant_constructor;
          kind :
            ('types, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadt) kind;
        } ->
            ('cases, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadt) destruct

  let rec destruct_choice :
    type index types structure tail_cases tail_structures .
    ('cases, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) variant_constructors ->
    (index, 'cases, types, tail_cases) selection ->
    (index, 'structures, structure, tail_structures) selection ->
    (tail_cases, tail_structures, 'arity, 'rec_arity, 'kinds, 'positive,
      'negative, 'direct, 'gadt) variant_constructors ->
    tail_cases choice -> ('cases, 'structures, 'arity, 'rec_arity, 'kinds,
      'positive, 'negative, 'direct, 'gadt) destruct =
  fun constructors index index_desc subconstructors choice ->
    match subconstructors, choice with
    | VCCons { tail; _ }, CNext choice ->
        destruct_choice constructors (Next index) (Next index_desc) tail choice
    | VCCons { head; _ }, CFirst values ->
        begin match head, values with
          | VConstructor { name; argument = VNone; _ },
            () ->
              Destruct {
                constructors; index = Next index; index_desc = Next index_desc;
                constructor = head;
                kind = Constructor { name; argument = None }}
          | VConstructor { name; argument = VSome desc; _ }, (value, ()) ->
              Destruct {
                constructors; index = Next index; index_desc = Next index_desc;
                constructor = head;
                kind = Constructor {
                  name = name; argument = Some { desc; value }}}
          | VInherit desc, value ->
              Destruct {
                constructors; index = Next index; index_desc = Next index_desc;
                constructor = head; kind = Inherit { desc; value }}
        end
    | _ -> .

  let destruct constructors x =
    destruct_choice constructors Start Start constructors x
end

module Object = struct
  module Object = struct
    type ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
           'direct, 'gadt) t = {
        structure :
          ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) object_methods;
        methods : 'types Delays.t;
      }
  end

  include Object

  let rec map :
    type methods_a methods_b structures .
      ('a_arity, 'b_arity, 'rec_arity, 'kinds_a, 'kinds_b, 'positive, 'negative,
        'direct, 'gadt) map ->
    (methods_a, structures, 'a_arity, 'rec_arity, 'kinds_a, 'positive,
      'negative, 'direct, 'gadt) object_methods ->
    (methods_b, structures, 'b_arity, 'rec_arity, 'kinds_b, 'positive,
      'negative, 'direct, 'gadt) object_methods ->
    methods_a Delays.t -> methods_b Delays.t =
  fun f methods_a methods_b a ->
    match methods_a, methods_b, a with
    | ONil, ONil, [] -> []
    | OCons { head = OMethod head_a; tail = tail_a },
      OCons { head = OMethod head_b; tail = tail_b }, head :: tail ->
        (fun () -> f.f head_a.desc head_b.desc (head ())) ::
        map f tail_a tail_b tail
    | _ -> .

  type ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
         'direct, 'gadt) fold =
    | Fold : {
          index : ([`Succ of 'index], 'types, 'a, _) selection;
          index_structure :
            ([`Succ of 'index], 'structures, [`Method of 'structure], _)
              selection;
          name : string;
          desc :
            ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
              'direct, 'gadt) desc;
          method_ : unit -> 'a;
        } ->
          ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) fold

  let fold
      (f :
        ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
          'direct, 'gadt) fold -> 'acc -> 'acc)
      (obj :
        ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
          'direct, 'gadt) t) acc =
    let rec aux :
      type index head head_structure subtypes substructures .
      (index, 'types, head, subtypes) selection ->
      (index, 'structures, head_structure, substructures) selection ->
      (subtypes, substructures, 'arity, 'rec_arity, 'kinds, 'positive,
        'negative, 'direct, 'gadt) object_methods ->
      subtypes Delays.t -> 'a -> 'a =
    fun index index_structure structure values acc ->
      match structure, values with
      | ONil, [] -> acc
      | OCons { head = OMethod s_head; tail = s_tail }, head :: tail ->
          let index = Next index in
          let index_structure = Next index_structure in
          let acc = f (Fold { index; index_structure; name = s_head.name;
            desc = s_head.desc; method_ = head }) acc in
          aux index index_structure s_tail tail acc in
    aux Start Start obj.structure obj.methods acc

  module Method = struct
    type ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) t = {
        structure :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
            'direct, 'gadt) object_method;
        value : unit -> 'a;
      }
  end

  module Methods = Desc_vector (Method)

  module Objects = Desc_vector (Object)

  type ('index, 'structure, 'structures, 'arities, 'tuples,
        'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadts)
          structure_find =
    | Structure_find : {
          section : ([`Succ of 'index], 'tuples, 'section, 'others) Section.t;
          methods :
            ('section, 'structure, 'arities, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadts) Methods.t;
          others :
            ('others, 'structures, 'arities, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadts) Objects.t
        } ->
          ('index, 'structure, 'structures, 'arities, 'tuples,
            'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadts)
            structure_find

  type ('tuples, 'structures, 'arities, 'rec_arity, 'kinds, 'positive,
        'negative, 'direct, 'gadts) find =
    | Find : {
          index :
            ([`Succ of 'index], 'structures, 'structure, _) selection;
          section : ([`Succ of 'index], 'tuples, 'section, _) Section.t;
          methods :
            ('section, 'structure, 'arities, 'rec_arity, 'kinds, 'positive,
              'negative, 'direct, 'gadts) Methods.t;
    } ->
        ('tuples, 'structures, 'arities, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, 'gadts) find

  let find :
    type arities gadts .
        ('tuple * 'tuples, 'structures, arities, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, gadts) Objects.t ->
        (('tuple * 'tuples, 'structures, arities, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, gadts) find -> 'a option) ->
        'a option =
  fun tuples f ->
    let rec make_section :
        type index current other_structures base_structures
          tail tail_section current_section structure
          tail_structures arities gadts .
        ([`Succ of index], base_structures, current, tail_structures)
          selection ->
        (index, tail_section, current_section, tail) Section.t ->
        (tail, structure * other_structures, arities, 'rec_arity,
          'kinds, 'positive, 'negative, 'direct, gadts) Objects.t ->
        (index, structure, other_structures, arities, tail_section,
          'rec_arity, 'kinds, 'positive, 'negative, 'direct, gadts)
            structure_find =
    fun index section tuples ->
      match section, tuples with
      | [], [] ->
          Structure_find { section = []; methods = []; others = [] }
      | head_section :: tail_section, head :: tail ->
          let Structure_find tail =
            make_section index tail_section tail in
          let OCons { head = method_; tail = structure } = head.structure in
          let value :: methods = head.methods in
          Structure_find {
            section = Next head_section :: tail.section;
            methods = { structure = method_; value } :: tail.methods;
            others = { structure; methods } :: tail.others
          } in
    let rec aux :
        type index subtuple subtuples substructures structure section .
        (index, 'structures, structure, substructures) selection ->
        (index, 'tuple * 'tuples, section, subtuple * subtuples) Section.t ->
        (subtuple * subtuples, substructures, arities, 'rec_arity, 'kinds,
          'positive, 'negative, 'direct, gadts) Objects.t ->
        'a option =
    fun index section objects ->
      let first :: tail = objects in
      let head_section :: tail_section = section in
      match first with
      | { structure = ONil; methods = [] } -> None
      | { structure = OCons { head = structure; tail = structure_tail };
          methods = value :: methods_tail } ->
          let index = Next index in
          let Structure_find { section; methods; others } =
            make_section index tail_section tail in
          let section : (_, _, _, _) Section.t = Next head_section :: section in
          begin match
            f ((Find { index; section;
              methods = { structure; value } :: methods } :
                ('tuple * 'tuples, 'structures, arities, 'rec_arity, 'kinds,
                  'positive, 'negative, 'direct, gadts) find ))
          with
          | None ->
              aux index section
                ({ structure = structure_tail;
                  methods = methods_tail } :: others)
          | result -> result
          end
      in
    let rec start_section :
        type subtuples arities gadts .
        (subtuples, 'structures, arities, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, gadts) Objects.t ->
        ([`Zero], subtuples, subtuples) Section.some =
    fun tuples ->
      match tuples with
      | [] -> Some []
      | _head :: tail ->
          let Some tail = start_section tail in
          Some (Start :: tail) in
    let Some section = start_section tuples in
    aux Start section tuples
end
