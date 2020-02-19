module Refl = Desc

type unit__structure =
  [`Name of [`Constr of ([`Constructor of ([`Tuple of unit] * unit)] ref)]]

type unit__arity = [`Zero]

type unit__rec_arity = (unit__arity * unit__structure) * unit

type _ Refl.type_name += Name_unit : unit Refl.type_name

let unit_refl :
    (unit, unit__structure, 'arity, unit__rec_arity, [> `Constr | `Name],
      unit, unit, unit, unit) Refl.desc =
  Name {
    name = Name_unit;
    desc = Constr {
    constructors = CLeaf (
        Constructor {
          name = "()";
          kind = CTuple TNil;
          eqs = ENil;
          attributes = Tools.attributes_empty; });
    construct = (fun (CEnd ((), ())) -> ());
    destruct = (fun () -> CEnd ((), ()));
  }}

type 'a list = 'a List.t =
  | []
  | (::) of 'a * 'a list
        [@@deriving refl]

type ('a, 'b) result = ('a, 'b) Stdlib.result =
  | Ok of 'a
  | Error of 'b
        [@@deriving refl]

type 'a option = 'a Option.t =
  | None
  | Some of 'a
        [@@deriving refl]

type 'a ref = 'a Stdlib.ref =
  { mutable contents : 'a }
        [@@deriving refl]
