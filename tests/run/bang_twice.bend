# a ! binder is reusable at any kind: twice runs its function argument
# twice, though a function is Type. the call pays: inc is closed.
import Base

def twice(!f: U32 -> U32, x: U32) -> U32:
  f(f(x))

def inc(x: U32) -> U32:
  (x + 1 : U32)

def main() -> U32:
  twice(inc, 5)

#|7
