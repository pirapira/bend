# a ! variable passes to a ! binder as the recipe it holds: iter carries
# its function through the recursion and runs it at every step.
import Base

def iter(!f: U32 -> U32, n: Nat, x: U32) -> U32:
  match n:
    case 0n:
      x
    case 1n+p:
      iter(f, p, f(x))

def double(x: U32) -> U32:
  (x * 2 : U32)

def main() -> U32:
  iter(double, 4n, 1)

#|16
