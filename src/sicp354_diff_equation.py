# the goal is to calculate function f such that dy/dt = f(y)
# here y is represented as a stream (y(0), y(dt), y(2*dt), ...)
# and we have the boundary condition of y(0) = y0
#
# to calulate y, we rely on two equations
# dy = f(y), y(n*dt) = y(0) + cumsum(dy) * dt
# above we use dy to abbreviate dy/dt in the following text
#
# the difficulty in stream processing is that dy and y depend on each other
# in our solution, in y's definition, we explicitly put dy inside lambda, so that it is lazily evaulated
# this is quite similar to sin/cos power series example
# if we use y = integral(dy, y0, dt), then both defnition of y and dy will depend on each other, which is illegal

import math
from typing import Callable
import sicp352_prime_number

Stream = sicp352_prime_number.Stream


def solve(f: Callable[[float], float], y0: float, dt: float):
    y = Stream(y0, lambda: Stream.add(y, dy.scale(dt)))
    dy = Stream.map(f, y)
    return y


def test():
    def f(y): return y
    precision = 1e-4
    y = solve(f, 1, precision)
    e1 = y.nth_value(int(1/precision))
    print('e precise:  %.14f' % math.e)
    print('e estimate: %.14f' % e1)
    assert abs(math.e-e1) < 1e-3


if __name__ == '__main__':
    test()
