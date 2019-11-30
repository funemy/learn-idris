-- Here we are giving  the type of a type constructor
data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  -- here a and k are implicitly bond with types
  -- {a : Type} -> {k : Nat} ->
  (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs, ys, zs

append : Vect n a -> Vect m a -> Vect (n+m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys


zip : Vect n a -> Vect n b -> Vect n (a, b)
zip [] [] = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys


empties : Vect m (Vect 0 e)
-- implictly bring m to scope
empties {m = Z} = []
empties {m = S k} = [] :: empties {m = k}

transpostHelper : (x : Vect m e) -> (xs_trans : Vect m (Vect k e)) -> Vect m (Vect (S k) e)
transpostHelper [] [] = []
transpostHelper (x :: xs) (y :: ys) = (x :: y) :: transpostHelper xs ys

transpose_mat : Vect n (Vect m e) -> Vect m (Vect n e)
transpose_mat [] = empties
transpose_mat (x :: xs) =
  let xs_trans = transpose_mat xs in
    transpostHelper x xs_trans
