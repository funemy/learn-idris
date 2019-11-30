import Data.Vect

%default total

data EqNat : Nat -> Nat -> Type where
     SameNat : (num : Nat) -> EqNat num num

smallProofEq : EqNat (2 + 2) 4
smallProofEq = SameNat 4

-- smallProofNotEq : EqNat (2 + 2) 5
-- smallProofNotEq = smallProofNotEq

successorEq : EqNat x y -> EqNat (S x) (S y)
successorEq (SameNat x) = SameNat (S x)

smallProof : 2 + 2 = 4
-- Refl has an implicit argument x
-- The following line also type check
-- smallProof = Refl {x=4}
smallProof = Refl

notTrue : 2 + 2 = 5 -> Void
notTrue Refl impossible

checkEqNat : (n : Nat) -> (m : Nat) -> Maybe (n = m)
checkEqNat Z Z = Just Refl
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              -- (Just (Refl {x=k})) => Just (Refl {x=(S k)})
                              (Just Refl) => Just Refl

tryZip : Vect n a -> Vect m b -> Maybe (Vect n (a, b))
tryZip {n} {m} xs ys = case checkEqNat n m of
                            Nothing => Nothing
                            (Just Refl) => Just (zip xs ys)

zeroNotSucc : (0 = S k) -> Void
zeroNotSucc Refl impossible

sucNotZero : (S k = 0) -> Void
sucNotZero Refl impossible

successorFail : (contra : (k = j) -> Void) -> (S k = S j) -> Void
successorFail contra Refl = contra Refl

checkEqNat2 : (n : Nat) -> (m : Nat) -> Dec (n = m)
checkEqNat2 Z Z = Yes Refl
checkEqNat2 Z (S k) = No zeroNotSucc
checkEqNat2 (S k) Z = No sucNotZero
checkEqNat2 (S k) (S j) = case checkEqNat2 k j of
                              (Yes Refl) => Yes Refl
                              (No contra) => No (successorFail contra)

tryZip2 : Vect n a -> Vect m b -> Maybe (Vect n (a, b))
tryZip2 {n} {m} xs ys = case checkEqNat2 n m of
                             (Yes Refl) => Just (zip xs ys)
                             (No contra) => Nothing


