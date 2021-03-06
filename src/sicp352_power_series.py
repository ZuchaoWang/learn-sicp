# exercise 3.59-62
# we represent power series as infinite stream
# and define operations on power series

from typing import Callable, Tuple
from sicp352_prime_number import InfStream


def almost_equal(x: float, y: float):
    eps = 1e-6
    ok1 = abs(x-y) < eps
    ok2 = (abs(x-y) < eps * (abs(x) + abs(y)))
    return ok1 or ok2


def ps_stringify(s: InfStream, n: int) -> str:
    if n < 2:
        n = 2
    # get topn coefficients
    coeffs = s.topn_values(n)
    # calculate coeff_strs, e.g. 1, 2*x, -4*x^2
    coeff_strs = []
    if not almost_equal(coeffs[0], 0):
        if not almost_equal(coeffs[0], 1):
            coeff_strs.append(str(coeffs[0]))
        else:
            coeff_strs.append('1')
    if not almost_equal(coeffs[1], 0):
        if not almost_equal(coeffs[1], 1):
            coeff_strs.append('%f*x' % coeffs[1])
        else:
            coeff_strs.append('x')
    for i in range(2, n):
        if not almost_equal(coeffs[i], 0):
            if not almost_equal(coeffs[i], 1):
                coeff_strs.append('%f*x^%d' % (coeffs[i], i))
            else:
                coeff_strs.append('x^%d' % (i))
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


def ps_mult(s1: InfStream, s2: InfStream) -> InfStream:
    # pattern: (k+1)-th item does not depend on previous items
    def calc_mult(n: int) -> InfStream:
        coeffs1 = s1.topn_values(n+1)
        coeffs2 = s2.topn_values(n+1)
        sum = 0
        for i in range(n+1):
            sum += coeffs1[i] * coeffs2[n-i]
        return InfStream(sum, lambda: calc_mult(n+1))

    return calc_mult(0)


def ps_reciprocal(s: InfStream) -> InfStream:
    head = s.value()
    assert head != 0
    self_normalized = s.scale(1/head)
    rp = InfStream(1, lambda: ps_mult(self_normalized.next().scale(-1), rp))
    return rp.scale(1/head)


def ps_square(s: InfStream) -> InfStream:
    return ps_mult(s, s)


def ps_div(s1: InfStream, s2: InfStream) -> InfStream:
    return ps_mult(s1, ps_reciprocal(s2))


def make_sin_cos() -> Tuple[InfStream, InfStream]:
    integers_rp = InfStream.make_integers().next().reciprocal()
    sin = InfStream(0, lambda: InfStream.mult(cos, integers_rp))
    cos = InfStream(1, lambda: InfStream.mult(sin, integers_rp).scale(-1))
    return sin, cos


def make_factorial() -> InfStream:
    integers_from_one = InfStream.make_integers().next()
    # pattern: when (k+1)-th item only depends on k-th value
    factorial = InfStream(1, lambda: InfStream.mult(factorial, integers_from_one))
    return factorial


def make_exponential(a: int) -> InfStream:
    twos = InfStream.make_ones().scale(a)
    exponential = InfStream(1, lambda: InfStream.mult(exponential, twos))
    return exponential


def make_bernoulli() -> InfStream:
    factorial = make_factorial()

    def combination(n: int, k: int) -> int:
        return factorial.nth_value(n)//(factorial.nth_value(k) * factorial.nth_value(n-k))

    # pattern: when (k+1)-th item only depends on all 1-st ~ k-th value
    bernoulli = InfStream(1, lambda: calc_bernoulli(1))

    def calc_bernoulli(n: int):
        '''bernoulli number recursive definition:
        https://proofwiki.org/wiki/Definition:Bernoulli_Numbers'''
        sum = 0
        for k in range(n):
            sum += combination(n, k) * bernoulli.nth_value(k) / (n+1-k)
        sum = -sum
        return InfStream(sum, lambda: calc_bernoulli(n+1))

    return bernoulli


def coeff_sin(i: int, factorial: InfStream) -> float:
    if i % 2 == 0:
        return 0
    else:
        c = 1/factorial.nth_value(i)
        if i % 4 == 1:
            return c
        else:
            return -c


def coeff_cos(i: int, factorial: InfStream) -> float:
    if i % 2 == 0:
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


def coeff_tan(i: int, factorial: InfStream, bernoulli: InfStream, exponential2: InfStream) -> float:
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


def test_one(name: str, s: InfStream, n_coeff: int, coeff_func: Callable[[int], float]):
    p_str = ps_stringify(s, n_coeff)
    print('%s(x) = %s' % (name, p_str))
    for i in range(n_coeff):
        pn = s.nth_value(i)
        cn = coeff_func(i)
        ok = almost_equal(pn, cn)
        if not ok:
            print(name, i, pn, cn)
            assert False


def test():
    # calculate
    ps_sin, ps_cos = make_sin_cos()
    ps_one = InfStream.add(ps_square(ps_sin), ps_square(ps_cos))
    ps_tan = ps_div(ps_sin, ps_cos)
    # test prepare
    fact = make_factorial()
    bern = make_bernoulli()
    exp2 = make_exponential(2)
    n_coeff = 10
    # test
    test_one("sin", ps_sin, n_coeff, lambda i: coeff_sin(i, fact))
    test_one("cos", ps_cos, n_coeff, lambda i: coeff_cos(i, fact))
    test_one("one", ps_one, n_coeff, lambda i: coeff_one(i))
    test_one("tan", ps_tan, n_coeff, lambda i: coeff_tan(i, fact, bern, exp2))


if __name__ == '__main__':
    test()
