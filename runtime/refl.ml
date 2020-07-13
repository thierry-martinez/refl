include Desc

module Builtins = Builtins

module Tools = Tools

include Convert

include Map

include Show

module Compare = Compare

module Comparer = Compare.Comparer

module Comparers = Compare.Comparers

let compare_gen = Compare.compare_gen

let compare_poly = Compare.compare_poly

let compare = Compare.compare

module Eq = Eq

module Equaler = Eq.Equaler

module Equalers = Eq.Equalers

let equal_poly = Eq.equal_poly

let equal = Eq.equal

module Hash = Hash

let hash = Hash.hash

include Enum

include Iter

include Fold

include Make

module Lift = Lift

module Visit = Visit

module Ocaml_attributes = struct
  type ('a, 'arity, 'b) typed_attribute_kind +=
    | Attribute_doc : ('a, 'arity, string) typed_attribute_kind
end
