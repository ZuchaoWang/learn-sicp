# scheme resolver
# see 4.1.6
# TODO: add resolver

# it supports set_at and lookup_at, which will be used in resolver
# ref: https://craftinginterpreters.com/resolving-and-binding.html
#
# def set_at(self, distance: int, name: str, sv: SchemeVal):
#     env = self._ancestor(distance)
#     env._bindings[name] = sv

# def lookup_at(self, distance: int, name: str):
#     env = self._ancestor(distance)
#     return env._bindings[name]

# def _ancestor(self, distance: int):
#     env = self
#     while distance > 0:
#         if env._enclosing is None:
#             self._error('no ancestor at distance %d' % distance)
#         else:
#             env = env._enclosing
#             distance -= 1
#     return env