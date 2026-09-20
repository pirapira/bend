# a def with a ! parameter is called, never held: a let cannot bind it,
# since its type is no type a binder may name.
import Base

def twice(!f: U32 -> U32, x: U32) -> U32:
  f(f(x))

def main() -> U32:
  t = twice
  t(x => x, 3)

#|Error:
#|- expected : a - or plain binder (! marks a def's parameter or a let, never a type)
#|- observed : @!f:(@_:U32 -> U32) -> @x:U32 -> U32
#|Location: main
#|4 |
#|5>| def twice(!f: U32 -> U32, x: U32) -> U32:
#|6 |   f(f(x))
#|exit 1
