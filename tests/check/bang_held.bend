# a def with a ! parameter is called, never held: its type is no
# function type a binder can name.
import Base

def twice(!f: U32 -> U32, x: U32) -> U32:
  f(f(x))

def apply(g: (U32 -> U32) -> U32 -> U32, x: U32) -> U32:
  g(x => x, x)

def main() -> U32:
  apply(twice, 3)

#|Error:
#|- expected : @_:(@_:U32 -> U32) -> @_:U32 -> U32
#|- observed : @!f:(@_:U32 -> U32) -> @x:U32 -> U32
#|Location: main
#|11 | def main() -> U32:
#|12>|   apply(twice, 3)
#|13 |
#|exit 1
