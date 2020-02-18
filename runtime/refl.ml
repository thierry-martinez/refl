include Desc

module Builtins = Builtins

module Tools = Tools

include Convert

include Map

include Show

include Compare

include Eq

include Enum

include Iter

include Fold

include Make

module Ocaml_attributes = struct
  type ('a, 'arity, 'b) typed_attribute_kind +=
    | Attribute_doc : ('a, 'arity, string) typed_attribute_kind
end
