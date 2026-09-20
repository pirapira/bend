# a ! field is refused: a datatype never carries a recipe, or one rebuilt
# from its own field would be omega.
import Base

type R is Type:
  In{!f: R -> Empty}

#|Error:
#|- expected : a - or plain binder (! marks a def's parameter or a let, never a field or a datatype parameter)
#|- observed : 'f'
#|Location:
#|5 | type R is Type:
#|6>|   In{!f: R -> Empty}
#|7 |
#|exit 1
