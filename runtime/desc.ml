type ('a, 'b) eq =
  | Eq : ('a, 'a) eq

type ('a, 'b, 'c) builtin_desc =
  | Bool : (bool, [`Bool], [> `Bool]) builtin_desc
  | Bytes : (bytes, [`Bytes], [> `Bytes]) builtin_desc
  | Char : (char, [`Char], [> `Char]) builtin_desc
  | Float : (float, [`Float], [> `Float]) builtin_desc
  | Int : (int, [`Int], [> `Int]) builtin_desc
  | Int32 : (int32, [`Int32], [> `Int32]) builtin_desc
  | Int64 : (int64, [`Int64], [> `Int64]) builtin_desc
  | Nativeint : (nativeint, [`Nativeint], [> `Nativeint]) builtin_desc
  | String : (string, [`String], [> `String]) builtin_desc

type ('index, 'items, 'value, 'tail) selection =
  | Start :
      ([`Zero], 'sequence, _, 'sequence) selection
  | Next :
      ('index, 'sequence, _, 'head * 'tail) selection ->
        ([`Succ of 'index], 'sequence, 'head, 'tail) selection

type ('index, 'items, 'value, 'tail) binary_selection =
  | BinaryStart :
      ([`Start], 'sequence, _, 'sequence) binary_selection
  | Zero :
      ('index, 'sequence, _, 'zero * 'one) binary_selection ->
        ([`Zero of 'index], 'sequence, _, 'zero) binary_selection
  | One :
      ('index, 'sequence, _, 'zero * 'one) binary_selection ->
        ([`One of 'index], 'sequence, _, 'one) binary_selection
  | Select :
      ('index, 'sequence, _, 'contents ref) binary_selection ->
        ([`Select of 'index], 'sequence, 'contents, unit) binary_selection

type 'cases choice =
  | CFirst : 'types -> ('types * _) choice
  | CNext : 'cases choice -> (_ * 'cases) choice

type 'cases binary_choice =
  | CEnd : 'types -> 'types ref binary_choice
  | CZero : 'cases binary_choice -> ('cases * _) binary_choice
  | COne : 'cases binary_choice -> (_ * 'cases) binary_choice

module type UnaryType = sig
  type 'a t
end

module Sequence (T : UnaryType) = struct
  type _ t =
    | [] : unit t
    | (::) : 'head T.t * 'tail t -> ('head * 'tail) t
end

module Delay = struct
  type 'a t = unit -> 'a
end

module Delays = Sequence (Delay)

module Comparer = struct
  type 'a t = 'a -> 'a -> int
end

module Comparers = Sequence (Comparer)

type ('index, 'arity, 'a, 'positive, 'direct) variable =
  | VFirst :
      ([`Zero], 'value * _, 'value, [`Present] * _, [`Present] * _) variable
  | VNext :
      ('index, 'sequence, 'value, 'positive, 'direct) variable ->
      ([`Succ of 'index], _ * 'sequence, 'value, _ * 'positive, _ * 'direct)
        variable

type ('count, 'types) length =
  | Zero : ([`Zero], unit) length
  | Succ : ('length, 'types) length -> ([`Succ of 'length], _ * 'types) length

type ('a, 'b, 'c) append =
  | Nil : (unit, 'a, 'a) append
  | Add :
      ('a, 'b, 'c) append ->
        ('head * 'a, 'b, 'head * 'c) append

type ('global, 'local) presence =
  | Present : ([> `Present], [`Present]) presence
  | Absent : (_, [`Absent]) presence

type ('presence, 'directs) presences =
  | Presences : (_, unit) presences
  | AddPresent :
      ('presence, 'directs) presences ->
      ([> `Present] as 'presence, [`Present] * 'directs) presences
  | AddAbsent :
      ('presence, 'directs) presences ->
      ('presence, [`Absent] * 'directs) presences

type ('constraints, 'exists) gadt_constraints = ..

type ('constraints, 'exists) gadt_constraints +=
  | NoConstraints

type ('gadt, 'sub_gadt) sub_gadt_ext = ..

type ('gadt, 'sub_gadt) sub_gadt = {
    sub_gadt_ext : ('gadt, 'sub_gadt) sub_gadt_ext;
    sub_gadt_functional : 'gadt 'sub_gadt0 'sub_gadt1 .
      ('gadt, 'sub_gadt0) sub_gadt_ext -> ('gadt, 'sub_gadt1) sub_gadt_ext ->
      ('sub_gadt0, 'sub_gadt1) eq;
  }

type ('count, 'local, 'positive, 'negative, 'direct, 'positives, 'negatives,
       'directs, 'subpositive, 'subnegative, 'subdirect) subvariables = {
    presences : ('local, 'directs) presences;
    positive_count : ('count, 'positives) length;
    positive : ('positives, 'positive, 'subpositive) append;
    negative_count : ('count, 'negatives) length;
    negative : ('negatives, 'negative, 'subnegative) append;
    direct_count : ('count, 'directs) length;
    direct : ('directs, 'direct, 'subdirect) append;
  }

module Kinds = struct
  type builtin =
      [`Bool | `Bytes | `Char | `Float | `Int | `Int32 | `Int64 | `Nativeint |
        `String | `Unit]

  type structural =
      [`Array | `Constr | `Object | `Tuple | `Record | `Variant]

  type comparable =
      [builtin | structural | `Variable | `Lazy | `Opaque | `GADT | `Exists
    | `Absent | `Attributes | `MapOpaque ]

  type arrow = [`Arrow | `Labelled_arrow]

  type all = [comparable | `Present | arrow ]
end

type ('a, 'arity, 'attribute) typed_attribute_kind = ..

type
  ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct,
    'gadt) desc =
  | Variable :
      ('index, 'arity, 'a, 'positive, 'direct) variable ->
      ('a, [`Variable of 'index], 'arity, 'rec_arity, [> `Variable],
        'positive, _, 'direct, _) desc
  | Builtin :
      ('a, 'structure, 'kinds) builtin_desc ->
      ('a, [`Builtin of 'structure], 'arity, 'rec_arity, 'kinds, _, _, _, _)
        desc
  | Array :
      ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'negative, 'positive,
        'negative, 'gadt) desc ->
      ('a array, [`Array of 'structure], 'arity, 'rec_arity,
        [> `Array] as 'kinds, 'negative, 'positive, 'negative, 'gadt) desc
  | Arrow : {
        parameter :
          ('a, 'a_structure, 'arity, 'rec_arity, 'kinds, 'negative, 'positive,
            'negative, 'gadt) desc;
        result :
          ('b, 'b_structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
            'positive, 'gadt) desc;
      } ->
        ('a -> 'b, [`Arrow of 'a_structure -> 'b_structure], 'arity,
          'rec_arity, [> `Arrow] as 'kinds, 'positive, 'negative, _, 'gadt)
          desc
  | LabelledArrow : {
        label : string;
        optional : bool;
        parameter :
          ('a, 'a_structure, 'arity, 'rec_arity, 'kinds, 'negative, 'positive,
            'negative, 'gadt) desc;
        result :
          ('b, 'b_structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
            'positive, 'gadt) desc;
        wrap : (('a -> 'b) -> 'arrow);
        unwrap : ('arrow -> ('a -> 'b));
      } ->
        ('arrow, [`LabelledArrow of 'a_structure -> 'b_structure], 'arity,
          'rec_arity, [> `Arrow] as 'kinds, 'positive, 'negative, _, 'gadt)
          desc
  | Constr : {
        constructors :
          ('cases, 'structures, 'arity, 'rec_arity, 'kinds,
            'positive, 'negative, 'direct, 'gadt) constructors;
        construct : 'cases binary_choice -> 'a;
        destruct : 'a -> 'cases binary_choice;
      } ->
        ('a, [`Constr of 'structures], 'arity, 'rec_arity,
          [> `Constr] as 'kinds, 'positive, 'negative, 'direct, 'gadt) desc
  | Variant : {
        constructors :
          ((_ * _) as 'cases, 'structures, 'arity, 'rec_arity, 'kinds,
            'positive, 'negative, 'direct, 'gadt) variant_constructors;
        construct : 'cases choice -> 'a;
        destruct : 'a -> 'cases choice;
      } ->
        ('a, [`Variant of 'structures], 'arity, 'rec_arity,
          [> `Variant] as 'kinds, 'positive, 'negative, 'direct, 'gadt) desc
  | Tuple : {
        structure :
          ((_ * (_ * _)) as 'types, 'structures, 'arity, 'rec_arity, 'kinds,
            'positive, 'negative, 'direct, 'gadt) tuple_structure;
        construct : 'types -> 'a;
        destruct : 'a -> 'types;
      } ->
        ('a, [`Tuple of 'structures], 'arity, 'rec_arity,
          [> `Tuple] as 'kinds, 'positive, 'negative, 'direct, 'gadt) desc
  | Record : {
        structure :
          ((_ * _) as 'types, 'structures, 'arity, 'rec_arity, 'kinds,
            'positive, 'negative, 'direct, 'gadt) record_structure;
        construct : 'types -> 'a;
        destruct : 'a -> 'types;
      } ->
        ('a, [`Record of 'structures], 'arity, 'rec_arity,
          [> `Record] as 'kinds, 'positive, 'negative, 'direct, 'gadt) desc
  | Object : {
        methods :
          ('methods, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) object_methods;
        construct : 'methods Delays.t -> 'a;
        destruct : 'a -> 'methods Delays.t;
      } ->
        (< .. > as 'a, [`Object of 'structures], 'arity, 'rec_arity,
          [> `Object] as 'kinds, 'positive, 'negative, 'direct, 'gadt) desc
  | Lazy :
      ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
        'direct, 'gadt) desc ->
        ('a Lazy.t, [`Lazy of 'structure], 'arity, 'rec_arity,
          [> `Lazy] as 'kinds, 'positive, 'negative, 'direct, 'gadt) desc
  | Apply : {
        arguments :
          ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'variables,
            'gadt) vector;
        desc :
          ('a, 'structure, 'types, 'rec_arity, 'kinds, 'subpositive,
            'subnegative, 'subdirect, 'gadt) desc;
        transfer :
          ('positive, 'negative, 'direct, 'subpositive, 'subnegative,
            'subdirect, 'variables) transfer;
      } ->
        ('a,
          [`Apply of 'structure * 'structures * 'subpositive * 'subnegative *
            'subdirect * 'variables],
          'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt)
          desc
  | Opaque : {
        desc :
          ('a, 'structure, 'arity, 'rec_arity, Kinds.all, 'positive,
            'negative, 'direct, 'gadt) desc;
      } ->
        ('a, [`Opaque of 'structure * 'direct], 'arity,
          'rec_arity, [> `Opaque], 'positive, 'negative, _, 'gadt) desc
  | MapOpaque :
        ('a, [`MapOpaque of 'a], 'arity,
          'rec_arity, [> `MapOpaque], 'positive, 'negative, _, 'gadt) desc
  | Rec : {
        index :
          ([`Succ of 'index], 'rec_arity, 'length * 'structure, _) selection;
        desc :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) desc;
      } ->
        ('a, [`Rec of 'index], 'arity, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, 'gadt) desc
  | RecArity : {
        desc :
          ('a, 'structure, 'arity, 'new_rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) desc;
(*
        rec_arity : ('new_rec_arity, 'new_rec_arity) rec_arity;
*)
      } ->
          ('a, [`RecArity of 'structure * 'new_rec_arity], 'arity,
            'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc
  | SelectGADT : {
        index : ([`Succ of 'index], 'gadt, 'sub_gadt, _) selection;
        desc :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'sub_gadt) desc;
      } ->
        ('a, [`SelectGADT of 'structure * 'index], 'arity, 'rec_arity,
          [> `GADT] as 'kinds, 'positive, 'negative, 'direct, 'gadt) desc
  | SubGADT : {
        sub_gadt : ('gadt, 'sub_gadt) sub_gadt;
        desc :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'sub_gadt) desc;
      } ->
        ('a, [`SubGADT of 'structure], 'arity, 'rec_arity,
          [> `GADT] as 'kinds, 'positive, 'negative, 'direct, 'gadt) desc
  | Attributes : {
        attributes :
          ('a, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) attributes;
        desc :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) desc;
      } ->
        ('a, [`Attributes of 'structure], 'arity, 'rec_arity,
          [> `Attributes] as 'kinds, 'positive, 'negative, 'direct, 'gadt) desc

and ('cases, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) constructors =
  | CLeaf :
      ('types_and_eqs, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
         'negative, 'direct, 'gadt) constructor ->
      ('types_and_eqs ref, 'structure ref, 'arity, 'rec_arity, 'kinds,
         'positive, 'negative, 'direct, 'gadt) constructors
  | CNode : {
        zero :
          ('cases0, 'structures0, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) constructors;
        one :
          ('cases1, 'structures1, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) constructors;
      } ->
        ('cases0 * 'cases1, 'structures0 * 'structures1, 'arity, 'rec_arity,
          'kinds, 'positive, 'negative, 'direct, 'gadt) constructors

and ('types_and_eqs, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
      'negative, 'direct, 'gadt) constructor =
  | Constructor : {
        name : string;
        kind :
          ('types, 'structure_types, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) constructor_kind;
        eqs : ('eqs, 'structure_eqs, 'kinds, 'gadt) constructor_eqs;
        attributes :
          ('types, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) attributes;
      } ->
        ('types * 'eqs, [`Constructor of 'structure_types * 'structure_eqs],
          'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt)
          constructor
  | Exists : {
        name : string;
        selection : ([`Succ of 'index], 'gadt, 'constraints, _) selection;
        presence : ('kinds, 'local) presence;
        variables :
          ('count, 'local, 'positive, 'negative, 'direct, 'positives,
            'negatives, 'directs, 'subpositive, 'subnegative,
            'subdirect) subvariables;
        construct :
          'exists 'subarity .
          ('count, 'exists) length ->
          ('constraints, 'exists) gadt_constraints ->
          ('exists, 'arity, 'subarity) append ->
          ('value, 'structure, 'subarity, 'rec_arity,
            'kinds, 'subpositive, 'subnegative, 'subdirect, 'gadt)
              exists_construct;
        destruct :
          'value ->
          ('count, 'constraints, 'value, 'structure, 'arity, 'rec_arity, 'kinds,
            'subpositive, 'subnegative, 'subdirect, 'gadt) exists_destruct;
    } ->
      ('value,
        [`Exists of 'index * 'count * 'structure * 'local * 'positives *
          'negatives * 'directs],
        'arity, 'rec_arity, ([> `Exists] as 'kinds), 'positive,
        'negative, 'direct, 'gadt) constructor

and ('value, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
      'negative, 'direct, 'gadt) exists_construct =
  | ExistsConstruct : {
        kind : ('types, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, 'gadt) constructor_kind;
        construct : 'types -> 'value;
      } ->
        ('value, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, 'gadt) exists_construct

and ('count, 'constraints, 'value, 'structure, 'arity, 'rec_arity, 'kinds,
      'positive, 'negative, 'direct, 'gadt) exists_destruct =
  | ExistsDestruct : {
        exists_count : ('count, 'exists) length;
        exists : ('exists, 'arity, 'subarity) append;
        constraints : ('constraints, 'exists) gadt_constraints;
        kind : ('types, 'structure, 'subarity, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, 'gadt) constructor_kind;
        values : 'types;
      } ->
        ('count, 'constraints, 'value, 'structure, 'arity, 'rec_arity, 'kinds,
          'positive, 'negative, 'direct, 'gadt) exists_destruct

and ('types, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) constructor_kind =
  | CTuple :
      ('types, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
        'direct, 'gadt)
        tuple_structure ->
      ('types, [`Tuple of 'structure], 'arity, 'rec_arity, 'kinds, 'positive,
        'negative, 'direct, 'gadt)
        constructor_kind
  | CRecord :
      ('types, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
        'direct, 'gadt)
        record_structure ->
      ('types, [`Record of 'structure], 'arity, 'rec_arity, 'kinds, 'positive,
        'negative, 'direct, 'gadt)
        constructor_kind

and ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt)
      tuple_structure =
  | TNil :
      (unit, unit, 'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct,
        'gadt) tuple_structure
  | TCons : {
        head :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
           'direct, 'gadt) desc;
        tail :
          ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) tuple_structure;
      } ->
        ('a * 'types, 'structure * 'structures, 'arity, 'rec_arity,
          'kinds, 'positive, 'negative, 'direct, 'gadt) tuple_structure

and ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt)
      record_structure =
  | RNil :
      (unit, unit, 'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct,
        'gadt) record_structure
  | RCons : {
        head :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
            'direct, 'gadt) record_field;
        tail :
          ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) record_structure;
      } ->
        ('a * 'types, 'structure * 'structures, 'arity, 'rec_arity,
          'kinds, 'positive, 'negative, 'direct, 'gadt) record_structure

and ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) record_field =
  | Mono : {
        label : string;
        desc :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
           'direct, 'gadt) desc;
        attributes :
          ('a, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
            'direct, 'gadt) attributes;
      } ->
        ('a, [`Mono of 'structure], 'arity, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, 'gadt) record_field
  | Poly : {
        label : string;
        variables :
          ('count, [`Absent], 'positive, 'negative, 'direct, 'positives,
            'negatives, 'directs, 'subpositive, 'subnegative,
            'subdirect) subvariables;
        destruct :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'subpositive,
            'subnegative, 'subdirect, 'gadt, 'count) forall_destruct;
        construct :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'subpositive,
            'subnegative, 'subdirect, 'gadt, 'count) forall_construct ->
          'a
      } ->
        ('a,
          [`Poly of 'structure * 'count * 'positives * 'negatives * 'directs],
          'arity, 'rec_arity, [> `Poly] as 'kinds, 'positive, 'negative,
          'direct, 'gadt) record_field

and ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt, 'count) forall_construct = {
        forall_construct :
          'forall 'b 'subarity .
          ('count, 'forall) length ->
          ('forall, 'arity, 'subarity) append ->
          ('b, 'structure, 'subarity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) desc ->
          'b;
      }

and ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'subpositive,
      'subnegative, 'subdirect, 'gadt, 'count) forall_destruct = {
        forall_destruct :
          'forall 'subarity .
          ('count, 'forall) length ->
          ('forall, 'arity, 'subarity) append ->
          ('a, 'structure, 'subarity, 'rec_arity, 'kinds, 'subpositive,
            'subnegative, 'subdirect, 'gadt) forall_destruct_result;
      }

and ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) forall_destruct_result =
  | ForallDestruct : {
        desc : ('b, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, 'gadt) desc;
        destruct : 'a -> 'b;
      } ->
        ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
          'direct, 'gadt) forall_destruct_result

and ('cases, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) variant_constructors =
  | VCNil :
      (unit, unit, 'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct,
        'gadt) variant_constructors
  | VCCons : {
        head :
          ('types, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) variant_constructor;
        tail :
          ('cases, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) variant_constructors;
      } ->
        ('types * 'cases, 'structure * 'structures, 'arity, 'rec_arity,
          'kinds, 'positive, 'negative, 'direct, 'gadt) variant_constructors

and ('types, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) variant_constructor =
  | VConstructor : {
        name : string;
        argument :
          ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) variant_argument;
      } ->
        ('types, [`Constr of 'structures], 'arity, 'rec_arity, 'kinds,
          'positive, 'negative, 'direct, 'gadt) variant_constructor
  | VInherit :
      ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
        'direct, 'gadt) desc ->
        ('a, [`Inherit of 'structure], 'arity, 'rec_arity, 'kinds,
          'positive, 'negative, 'direct, 'gadt) variant_constructor

and ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) variant_argument =
  | VNone :
      (unit, unit, 'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct,
        'gadt) variant_argument
  | VSome :
      ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
        'direct, 'gadt) desc ->
        ('a * unit, 'structure * unit, 'arity, 'rec_arity, 'kinds, 'positive,
          'negative, 'direct, 'gadt) variant_argument

and ('methods, 'structures, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) object_methods =
  | ONil :
      (unit, unit, 'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct,
        'gadt) object_methods
  | OCons : {
        head :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) object_method;
        tail :
          ('methods, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) object_methods;
      } ->
        ('a * 'methods, 'structure * 'structures, 'arity, 'rec_arity,
          'kinds, 'positive, 'negative, 'direct, 'gadt) object_methods

and ('types, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
      'direct, 'gadt) object_method =
  | OMethod : {
        name : string;
        desc :
          ('a, 'structures, 'arity, 'rec_arity, 'kinds, 'positive,
            'negative, 'direct, 'gadt) desc;
      } ->
        ('a, [`Method of 'structures], 'arity, 'rec_arity, 'kinds,
          'positive, 'negative, 'direct, 'gadt) object_method
(*
  | OInherit :
      ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
        'direct, 'gadt) desc ->
        ('a, [`Inherit of 'structure], 'arity, 'rec_arity, 'kinds,
          'positive, 'negative, 'direct, 'gadt) object_method
*)

and ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'variables, 'gadt)
      vector =
  | VNil : (unit, unit, 'arity, 'rec_arity, 'kinds, unit, 'gadt) vector
  | VCons : {
        head :
          ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
            'direct, 'gadt) desc;
        tail :
          ('types, 'structures, 'arity, 'rec_arity, 'kinds, 'variables,
            'gadt) vector;
      } ->
        ('a * 'types, 'structure * 'structures, 'arity, 'rec_arity,
          'kinds, ('positive * 'negative * 'direct) * 'variables, 'gadt)
          vector

and ('positive, 'negative, 'direct, 'subpositive, 'subnegative, 'subdirect,
      'variables) transfer =
  | VTNil : (_, _, _, unit, unit, unit, unit) transfer
  | VTCons :
      { head :
          ('p, 'n, 'sp, 'sn, 'ap, 'an) transfer_matrix *
          ('d, 'sd, 'ad) transfer_arguments;
        tail :
          ('p, 'n, 'd, 'sps, 'sns, 'sds, 'variables) transfer } ->
      ('p, 'n, 'd, 'sp * 'sps, 'sn * 'sns, 'sd * 'sds,
        ('ap * 'an * 'ad) * 'variables) transfer

and ('p, 'n, 'sp, 'sn, 'ap, 'an) transfer_matrix = {
    pp : ('p, 'sp, 'ap) transfer_arguments;
    pn : ('p, 'sn, 'an) transfer_arguments;
    np : ('n, 'sp, 'an) transfer_arguments;
    nn : ('n, 'sn, 'ap) transfer_arguments;
  }

and ('source, 'sub, 'arg) transfer_arguments =
  | VTANil : (unit, _, unit) transfer_arguments
  | VTACons :
      { head : ('source, 'sub, 'arg) transfer_argument;
        tail : ('sources, 'sub, 'args) transfer_arguments } ->
        ('source * 'sources, 'sub, 'arg * 'args) transfer_arguments

and ('source, 'sub, 'arg) transfer_argument =
  | Transfer : ('a, 'a, [`Present]) transfer_argument
  | Skip : (_, _, [`Absent]) transfer_argument

and ('eqs, 'structure_eqs, 'kinds, 'gadt) constructor_eqs =
  | ENil :
      (unit, unit, 'kinds, 'gadt) constructor_eqs
  | ECons : {
        head : ([`Succ of 'index], 'gadt, 'eq, _) selection;
        tail : ('eqs, 'structure_eqs, 'kinds, 'gadt) constructor_eqs;
      } ->
          ('eq * 'eqs, 'index * 'structure_eqs, [> `GADT] as 'kinds, 'gadt)
            constructor_eqs

and ('a, 'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt)
      attributes = {
    typed :
      'attribute .
      ('a, 'arity, 'attribute) typed_attribute_kind -> 'attribute option;
  }

(*
and ('types, 'rec_arity) rec_arity =
  | ANil : (unit, 'rec_arity) rec_arity
  | ACons : {
        head : ('count, 'arity) length *
          (_, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
            'direct, 'gadt) desc;
        tail : ('types, 'rec_arity) rec_arity;
      } ->
        (('count * 'structure) * 'types, 'rec_arity) rec_arity
*)
