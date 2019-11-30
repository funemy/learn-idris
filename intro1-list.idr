-- How a list is defined
-- data List a = Nil | (::) a (List a)

my_append : List a -> List a -> List a
my_append [] ys = ys
my_append (x :: xs) ys = x :: my_append xs ys
