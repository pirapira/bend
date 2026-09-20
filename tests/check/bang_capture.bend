# a ! argument captures nothing, not even a ! variable: a recipe is a
# closure, and one that captures nothing is a static value the runtime
# shares for free. a ! variable passes on as itself instead.
import Base

def twice(!f: U32 -> U32, x: U32) -> U32:
  f(f(x))

def four(!f: U32 -> U32, x: U32) -> U32:
  twice(y => f(f(y)), x)

#|Error:
#|- message  : a closed argument for a ! binder (f is a live variable here: a ! argument names defs and erased variables only, or is a ! variable itself, so it can be run any number of times)
#|Context:
#|- f : @_:U32 -> U32
#|- x : U32
#|Location: four
#| 9 | def four(!f: U32 -> U32, x: U32) -> U32:
#|10>|   twice(y => f(f(y)), x)
#|11 |
#|exit 1
