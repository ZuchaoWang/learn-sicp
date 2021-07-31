# exercise 3.59-62

from typing import Callable, Tuple
from .sicp352_prime_number import Stream


class PowerSeries(Stream):
    def ps_stringify(self, n: int) -> str:
        if n < 2:
            n = 2
        # get topn coefficients
        coeffs = self.topn_values(n)
        # calculate coeff_strs, e.g. 1, 2*x, -4*x^2
        coeff_strs = []
        if coeffs[0] != 0:
            coeff_strs.append(str(coeffs[0]))
        if coeffs[1] != 0:
            coeff_strs.append('%f*x' % coeffs[1])
        for i in range(2, n):
            if coeffs[i] != 0:
                coeff_strs.append('%f*x^%d' % (coeffs[i], i))
        # if all zeros
        if len(coeff_strs) == 0:
            return '0'
        else:  # has at least one none-zero term
            res = coeff_strs[0]
            for cs in coeff_strs[1:]:
                if cs[0] != '-':
                    cs = '+' + cs
                res += cs
            return res

    def ps_reciprocal(self) -> "PowerSeries":
        head = self.value()
        assert head != 0
        self_normalized = self.scale(1/head)
        rp = Stream(1, lambda: self_normalized.next().scale(-1).ps_mult(rp))
        return rp.scale(1/head)

    def ps_square(self) -> "PowerSeries":
        return PowerSeries.ps_mult(self, self)

    @staticmethod
    def ps_mult(p1: "PowerSeries", p2: "PowerSeries") -> "PowerSeries":
        def calc_mult(n: int) -> "PowerSeries":
            coeffs1 = p1.topn_values(n+1)
            coeffs2 = p2.topn_values(n+1)
            sum = 0
            for i in range(n+1):
                sum += coeffs1[i] * coeffs2[n+1-i]
            return PowerSeries(sum, lambda: calc_mult(n+1))

        return calc_mult(0)

    @staticmethod
    def ps_div(p1: "PowerSeries", p2: "PowerSeries") -> "PowerSeries":
        return PowerSeries.ps_mult(p1, p2.ps_reciprocal())


def make_sin_cos() -> Tuple[PowerSeries, PowerSeries]:
    integers_rp = Stream.make_integers().next().reciprocal()
    sin = PowerSeries(0, lambda: Stream.mult(cos, integers_rp))
    cos = PowerSeries(1, lambda: Stream.mult(sin, integers_rp).scale(-1))
    return sin, cos


def make_factorial() -> Stream:
    integers_from_one = Stream.make_integers().next()
    # pattern: when (k+1)-th item only depends on k-th value
    factorial = Stream(1, lambda: Stream.mult(factorial, integers_from_one))
    return factorial


def make_exponential(a: int) -> Stream:
    twos = Stream.make_ones().scale(a)
    exponential = Stream(1, lambda: Stream.mult(exponential, twos))
    return exponential


def make_bernoulli() -> Stream:
    factorial = make_factorial()

    def combination(n: int, k: int) -> int:
        return factorial.nth_value(n)//(factorial.nth_value(k) * factorial.nth_value(n-k))

    # pattern: when (k+1)-th item only depends on all 1-st ~ k-th value
    bernoulli = Stream(1, lambda: calc_bernoulli(1))

    def calc_bernoulli(n: int):
        '''bernoulli number recursive definition:
        https://proofwiki.org/wiki/Definition:Bernoulli_Numbers'''
        sum = 0
        for k in range(n):
            sum += combination(n, k) * bernoulli.nth_value(k) / (n+1-k)
        sum = -sum
        return Stream(sum, lambda: calc_bernoulli(n+1))

    return bernoulli


def coeff_sin(i: int, factorial: Stream) -> float:
    if i % 2:
        return 0
    else:
        c = 1/factorial.nth_value(i)
        if i % 4 == 1:
            return c
        else:
            return -c


def coeff_cos(i: int, factorial: Stream) -> float:
    if i % 2:
        c = 1/factorial.nth_value(i)
        if i % 4 == 0:
            return c
        else:
            return -c
    else:
        return 0


def coeff_one(i: int) -> float:
    if i == 0:
        return 1
    else:
        return 0


def coeff_tan(i: int, factorial: Stream, bernoulli: Stream, exponential2: Stream) -> float:
    '''tanganet formula:
    https://proofwiki.org/wiki/Power_Series_Expansion_for_Tangent_Function'''
    if i == 0:
        return 0
    else:
        e2 = exponential2.nth_value(i+1)
        b = bernoulli.nth_value(i+1)
        f = factorial.nth_value(i+1)
        c = e2*(e2-1)*b/f
        if i % 4 == 1:
            return c
        else:
            return -c


def test_one(name: str, p: PowerSeries, n_coeff: int, coeff_func: Callable[[int], float]):
    p_str = p.ps_stringify(n_coeff)
    print('%s(x) = %s' % (name, p_str))
    for i in range(n_coeff):
        pn = p.nth_value(i)
        cn = coeff_func(i)
        assert abs(pn - cn) <= 1e-4 * (abs(pn) + abs(cn))


def test():
    # calculate
    ps_sin, ps_cos = make_sin_cos()
    ps_one = PowerSeries.add(PowerSeries.square(
        ps_sin), PowerSeries.ps_square(ps_cos))
    ps_tan = PowerSeries.ps_div(ps_sin, ps_cos)
    # test prepare
    factorial = make_factorial()
    bernoulli = make_bernoulli()
    exponential2 = make_exponential(2)
    n_coeff = 10
    # test
    test_one("sin", ps_sin, n_coeff, lambda i: coeff_sin(i, factorial))
    test_one("cos", ps_cos, n_coeff, lambda i: coeff_cos(i, factorial))
    test_one("one", ps_one, n_coeff, lambda i: coeff_one(i))
    test_one("tan", ps_tan, n_coeff, lambda i: coeff_tan(
        i, factorial, bernoulli, exponential2))
