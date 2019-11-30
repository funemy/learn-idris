StringOrNat : (isStr : Bool) -> Type
StringOrNat False = Nat
StringOrNat True = String

lengthOrDouble : (isStr : Bool) -> StringOrNat isStr -> Nat
lengthOrDouble False x = x + x
lengthOrDouble True x = length x
