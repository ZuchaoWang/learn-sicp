# this is pure algorithm
# I will not use lookup table

# interger gcd

def gcd_int(a, b):
    # ensure a >= b
    if a < b:
        (a, b) = (b, a)
    # iterate
    while b > 0:
        (a, b) = (b, a % b)
    return a


def test_one_int(a, b, c_exp):
    c = gcd_int(a, b)
    print('gcd_int(%d, %d) = %d' % (a, b, c))
    assert c == c_exp


# polynomial gcd

# term


def power_term(term):
    return term[0]


def coeff_term(term):
    return term[1]


def make_term(power, coefficient):
    return (power, coefficient)


def stringify_term(term):
    p = power_term(term)
    c = coeff_term(term)
    if p == 0:
        return str(c)
    else:
        pstr = 'x^%d' % p if p > 1 else 'x'
        if c == 1:
            return pstr
        elif c == -1:
            return '-%s' % pstr
        else:
            return '%s*%s' % (str(c), pstr)


# terms


def reduce_terms(terms):
    return [t for t in terms if coeff_term(t)]


def add_terms(terms1, terms2):
    terms_res = []
    i1 = 0
    i2 = 0
    l1 = len(terms1)
    l2 = len(terms2)
    while (i1 < l1 and i2 < l2):
        p1 = power_term(terms1[i1])
        c1 = coeff_term(terms1[i1])
        p2 = power_term(terms2[i2])
        c2 = coeff_term(terms2[i2])
        if p1 == p2:
            t = make_term(p1, c1+c2)
            i1 += 1
            i2 += 1
        elif p1 > p2:
            t = terms1[i1]
            i1 += 1
        else:
            t = terms2[i2]
            i2 += 1
        terms_res.append(t)
    if i1 < l1:
        terms_res.extend(terms1[i1:l1])
    if i2 < l2:
        terms_res.extend(terms2[i2:l2])
    return reduce_terms(terms_res)


def scale_terms(terms, x):
    terms_res = [make_term(power_term(t), coeff_term(t)*x) for t in terms]
    return reduce_terms(terms_res)


def inv_scale_terms(terms, x):
    terms_res = [make_term(power_term(t), coeff_term(t)//x) for t in terms]
    return reduce_terms(terms_res)


def sub_terms(terms1, terms2):
    return add_terms(terms1, scale_terms(terms2, -1))


def mult_terms(terms1, terms2):
    terms_res = []
    l1 = len(terms1)
    l2 = len(terms2)
    for i1 in range(l1):
        p1 = power_term(terms1[i1])
        c1 = coeff_term(terms1[i1])
        terms_sub = []
        for i2 in range(l2):
            p2 = power_term(terms2[i2])
            c2 = coeff_term(terms2[i2])
            t = make_term(p1+p2, c1*c2)
            terms_sub.append(t)
        terms_res = add_terms(terms_res, terms_sub)
    return reduce_terms(terms_res)


def div_terms(terms1, terms2):
    assert len(terms1) and len(terms2)
    terms_rem = terms1
    terms_div = []
    while True:
        if len(terms_rem) == 0:
            break
        p1 = power_term(terms_rem[0])
        p2 = power_term(terms2[0])
        if p1 < p2:
            break
        else:
            c1 = coeff_term(terms_rem[0])
            c2 = coeff_term(terms2[0])
            t = make_term(p1-p2, c1//c2)
            terms_rem = sub_terms(terms_rem, mult_terms([t], terms2))
            terms_div.append(t)
    return terms_div, terms_rem


def pseudo_div_terms(terms1, terms2):
    assert len(terms1) and len(terms2)
    p1 = power_term(terms1[0])
    c1 = coeff_term(terms1[0])
    p2 = power_term(terms2[0])
    c2 = coeff_term(terms2[0])
    if p1 < p2:
        return terms1
    # now assume p1 >= p2
    cgcd = gcd_int(abs(c1), abs(c2))
    factor = int(pow(c2//cgcd, p1-p2+1))
    return div_terms(scale_terms(terms1, factor), terms2)


def prime_terms(terms):
    # make all prime to each other
    if len(terms) == 0:
        return terms
    else:
        factor = 0
        for i in range(0, len(terms)):
            factor = gcd_int(factor, abs(coeff_term(terms[i])))
        assert factor > 0
        if coeff_term(terms[0]) < 0:
            factor = -factor
        return inv_scale_terms(terms, factor)


def gcd_terms(terms1, terms2):
    if len(terms1) == 0:
        return terms2
    if len(terms2) == 0:
        return terms1
    p1 = power_term(terms1[0])
    p2 = power_term(terms2[0])
    if p1 < p2:
        (terms1, terms2) = (terms2, terms1)
    terms1 = prime_terms(terms1)
    terms2 = prime_terms(terms2)
    while len(terms2) > 0:
        _, terms_rem = pseudo_div_terms(terms1, terms2)
        terms_rem = prime_terms(terms_rem)
        (terms1, terms2) = (terms2, terms_rem)
    return terms1


def stringify_terms(terms):
    res_str = ''
    if len(terms):
        tstr = stringify_term(terms[0])
        res_str += tstr
        for i in range(1, len(terms)):
            tstr = stringify_term(terms[i])
            if tstr[0] == '-':
                res_str += tstr
            else:
                res_str += '+'
                res_str += tstr
    return res_str


# polynomial


def make_polynomial_inner(terms):
    return terms


def make_polynomial(*term_tuples):
    # sparse format, decreasing order
    # coefficient can only be integer
    # variable restricted to be x
    # just represent polynomial as tuples
    terms = [make_term(t[0], t[1]) for t in term_tuples]
    terms = reduce_terms(terms)
    return make_polynomial_inner(terms)


def terms_polynomial(y):
    return y


def gcd_polynomial(y1, y2):
    terms1 = terms_polynomial(y1)
    terms2 = terms_polynomial(y2)
    terms_gcd = gcd_terms(terms1, terms2)
    return make_polynomial_inner(terms_gcd)


def stringify_polynomial(y):
    terms = terms_polynomial(y)
    return stringify_terms(terms)


def test_one_polynomial(y1, y2, ygcdstr_exp):
    ygcd = gcd_polynomial(y1, y2)
    y1str = stringify_polynomial(y1)
    y2str = stringify_polynomial(y2)
    ygcdstr = stringify_polynomial(ygcd)
    print('gcd_polynomial(%s, %s) = %s' % (y1str, y2str, ygcdstr))
    assert ygcdstr == ygcdstr_exp

# final test
def test():
    test_one_int(0, 0, 0)
    test_one_int(3, 0, 3)
    test_one_int(0, 3, 3)
    test_one_int(40, 96, 8)
    test_one_int(96, 40, 8)
    test_one_polynomial(make_polynomial((1, 1), (0, 1)),
                        make_polynomial((1, 1), (0, -1)), '1')
    test_one_polynomial(make_polynomial((1, 1), (0, 1)),
                        make_polynomial((1, 1), (0, 1)), 'x+1')
    test_one_polynomial(make_polynomial((2, 1), (0, -1)),
                        make_polynomial((1, 1), (0, 1)), 'x+1')
    test_one_polynomial(make_polynomial((2, 1), (0, 1)),
                        make_polynomial((1, 1), (0, 1)), '1')
    test_one_polynomial(make_polynomial((2, 2), (1, 3), (0, 1)),
                        make_polynomial((3, 3), (2, 3), (1, 1), (0, 1)), 'x+1')
    test_one_polynomial(make_polynomial((2, -2), (1, -3), (0, -1)),
                        make_polynomial((3, 3), (2, 3), (1, 1), (0, 1)), 'x+1')


if __name__ == '__main__':
    test()
