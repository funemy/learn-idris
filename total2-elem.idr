data Elem : a -> List a -> Type where
  Here : Elem x (x :: xs)
  There : Elem x ys -> Elem x (y :: ys)

Beatles : List String
Beatles = ["John", "Paul", "George", "Ringo"]

georgeInBeatles : Elem "George" Beatles
georgeInBeatles = There (There Here)

HasNoElem : Elem "Pete" ["John", "Paul", "George", "Ringo"] -> Void
HasNoElem (There (There (There (There Here)))) impossible
HasNoElem (There (There (There (There (There _))))) impossible


peteNotInBeatles : Not (Elem "Pete" Beatles)
peteNotInBeatles = HasNoElem

isElem : (x : a) -> (xs : List a) -> Maybe (Elem x xs)
isElem x [] = Nothing
isElem x (y :: xs) = case isElem x xs of
                          Nothing => Nothing
                          (Just k) => Just (There k)


