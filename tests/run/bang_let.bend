# a ! let binds a closed value reusable: a list under ! is read at every
# use, a closure under ! runs at every use, and a ! variable passes to a
# ! binder as the recipe it holds.
import Base

def sum(xs: List<U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      (h + sum(t) : U32)

def twice(!f: U32 -> U32, x: U32) -> U32:
  f(f(x))

def main() -> U32:
  !xs : List<U32> = [1, 2, 3]
  !add : U32 -> U32 = x => (x + 1 : U32)
  (sum(xs) + sum(xs) + add(add(1)) + twice(add, 1) : U32)

#|18
