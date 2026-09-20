# ! marks a def's parameter or a let, never a type: a def with a ! binder
# is called, never held, so no datatype carries a recipe.
import Base

def apply(g: @!f:(U32 -> U32) -> U32, x: U32) -> U32:
  g(x)

#|Error:
#|- expected : a - or plain binder (! marks a def's parameter or a let, never a type)
#|- observed : 'f'
#|Location:
#|4 |
#|5>| def apply(g: @!f:(U32 -> U32) -> U32, x: U32) -> U32:
#|6 |   g(x)
#|exit 1
