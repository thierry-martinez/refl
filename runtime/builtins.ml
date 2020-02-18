module Refl = Desc

type unit__structure =
  [`Constr of ([`Constructor of ([`Tuple of unit] * unit)] ref)]

type unit__arity = [`Zero]

type unit__rec_arity = (unit__arity * unit__structure) * unit

let unit_refl :
    (unit, unit__structure, 'arity, unit__rec_arity, [> `Constr],
      unit, unit, unit, unit) Refl.desc =
  Constr {
    constructors = CLeaf (
        Constructor {
          name = "()";
          kind = CTuple TNil;
          eqs = ENil;
          attributes = Tools.attributes_empty; });
    construct = (fun (CEnd ((), ())) -> ());
    destruct = (fun () -> CEnd ((), ()));
  }

type 'a list = 'a List.t =
  | []
  | (::) of 'a * 'a list
        [@@deriving refl]

type ('a, 'b) result = ('a, 'b) Result.t =
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
