# a ! argument is closed: a live variable of the caller cannot enter it,
# or the callee would copy what the caller may use once.
import Base

def twice(!f: U32 -> U32, x: U32) -> U32:
  f(f(x))

def add(n: U32, x: U32) -> U32:
  twice(y => (y + n : U32), x)

#|Error:
#|- message  : a closed argument for a ! binder (n is a live variable here: a ! argument names defs and erased variables only, or is a ! variable itself, so it can be run any number of times)
#|Context:
#|- n : U32
#|- x : U32
#|Location: add
#| 8 | def add(n: U32, x: U32) -> U32:
#| 9>|   twice(y => (y + n : U32), x)
#|10 |
#|exit 1
