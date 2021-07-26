op_table = {}
cv_table = {}


def add_type(type, data):
    if type == 'real':
        return data
    else:
        return {'type': type, 'data': data}


def get_type(y):
    if isinstance(y, (int, float)):
        return 'real'
    elif isinstance(y, dict):
        return y['type']
    else:
        assert False


def apply_op(op_name, *args):
    types = [get_type(y) for y in args]
    f = op_table.get((op_name, *types), None)
    if f is not None:
        return f(*args)
    if len(args) == 2:
        t1, t2 = types
        y1, y2 = args
        g1to2 = cv_table.get((t1, t2), None)
        if g1to2 is not None:
            return apply_op(op_name, g1to2(y1, y2), y2)
        g2to1 = cv_table.get((t2, t1), None)
        if g2to1 is not None:
            return apply_op(op_name, y1, g2to1(y2, y1))
    assert False


def make(type, *args):
    f = op_table.get(('make', type), None)
    if f is not None:
        return f(*args)
    assert False


def sum(y1, y2):
    return apply_op('sum', y1, y2)


def product(y1, y2):
    return apply_op('product', y1, y2)


def stringify(y):
    return apply_op('stringify', y)


# we don't need special is_zero, just check ==0 will be enough
# only real can be 0, others if zero must have already been reduced to real 0


def install_real():
    def make_real(y):
        return y

    def sum_real(y1, y2):
        return y1 + y2

    def product_real(y1, y2):
        return y1 * y2

    def stringify_real(y):
        return str(y)

    op_table['sum', 'real', 'real'] = sum_real
    op_table['product', 'real', 'real'] = product_real
    op_table['stringify', 'real'] = stringify_real
    op_table['make', 'real'] = make_real


def install_complex():
    make_real = op_table.get(('make', 'real'), None)
    assert make_real

    def real_complex(y):
        return y['data'][0]

    def imag_complex(y):
        return y['data'][1]

    def force_complex(real, imag):
        return add_type('complex', (real, imag))

    def make_complex(real, imag):
        if imag == 0:  # reduction
            return make_real(real)
        else:
            return force_complex(real, imag)

    def sum_complex(y1, y2):
        a1 = real_complex(y1)
        b1 = imag_complex(y1)
        a2 = real_complex(y2)
        b2 = imag_complex(y2)
        a = a1 + a2
        b = b1 + b2
        return make_complex(a, b)

    def product_complex(y1, y2):
        a1 = real_complex(y1)
        b1 = imag_complex(y1)
        a2 = real_complex(y2)
        b2 = imag_complex(y2)
        a = a1 * a2 - b1 * b2
        b = a1 * b2 + a2 * b1
        return make_complex(a, b)

    def stringify_complex(y):
        a = real_complex(y)
        b = imag_complex(y)
        if a == 0:
            return '%s*i' % (str(b))
        elif b > 0:
            return '%s+%s*i' % (str(a), str(b))
        else:
            return '%s-%s*i' % (str(a), str(-b))

    def convert_real_to_complex(yr, _yc):
        return force_complex(yr, 0)

    op_table['sum', 'complex', 'complex'] = sum_complex
    op_table['product', 'complex', 'complex'] = product_complex
    op_table['stringify', 'complex'] = stringify_complex
    op_table['make', 'complex'] = make_complex

    cv_table['real', 'complex'] = convert_real_to_complex


def install_polynomial():
    make_real = op_table.get(('make', 'real'), None)
    make_complex = op_table.get(('make', 'complex'), None)
    assert make_real
    assert make_complex

    def power_term(t):
        return t['power']

    def coeff_term(t):
        return t['coeff']

    def make_term(power, coeff):
        return {'power': power, 'coeff': coeff}

    def reduce_terms(terms):
        # assume in power decreasing order
        rd_terms = []
        prev_p = None
        for t in terms:
            p = power_term(t)
            c = coeff_term(t)
            if c != 0:
                rd_terms.append(t)
            assert prev_p is None or p < prev_p
            prev_p = p
        return rd_terms

    def sum_terms(terms1, terms2):
        final_terms = []
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
                t = make_term(p1, sum(c1, c2))
                i1 += 1
                i2 += 1
            elif p1 > p2:
                t = terms1[i1]
                i1 += 1
            else:
                t = terms2[i2]
                i2 += 1
            final_terms.append(t)
        if i1 < l1:
            final_terms.extend(terms1[i1:l1])
        if i2 < l2:
            final_terms.extend(terms2[i2:l2])
        return final_terms

    def product_terms(terms1, terms2):
        final_terms = []
        l1 = len(terms1)
        l2 = len(terms2)
        for i1 in range(l1):
            p1 = power_term(terms1[i1])
            c1 = coeff_term(terms1[i1])
            sub_terms = []
            for i2 in range(l2):
                p2 = power_term(terms2[i2])
                c2 = coeff_term(terms2[i2])
                t = make_term(p1+p2, product(c1, c2))
                sub_terms.append(t)
            final_terms = sum_terms(final_terms, sub_terms)
        return final_terms

    def variable_polynomial(y):
        return y['data']['variable']

    def terms_polynomial(y):
        return y['data']['terms']

    def force_polynomial(variable, terms):
        return add_type('polynomial', {'variable': variable, 'terms': terms})

    def make_polynomial_inner(variable, terms):
        rd_terms = reduce_terms(terms)
        if len(rd_terms):
            if power_term(rd_terms[0]) > 0:
                return force_polynomial(variable, rd_terms)
            else:
                return coeff_term(rd_terms[0])
        else:
            return make_real(0)

    def make_polynomial(variable, term_tuples):
        terms = [make_term(t[0], t[1]) for t in term_tuples]
        return make_polynomial_inner(variable, terms)

    def sum_polynomial(y1, y2):
        v1 = variable_polynomial(y1)
        terms1 = terms_polynomial(y1)
        v2 = variable_polynomial(y2)
        terms2 = terms_polynomial(y2)
        assert v1 == v2
        return make_polynomial_inner(v1, sum_terms(terms1, terms2))

    def product_polynomial(y1, y2):
        v1 = variable_polynomial(y1)
        terms1 = terms_polynomial(y1)
        v2 = variable_polynomial(y2)
        terms2 = terms_polynomial(y2)
        assert v1 == v2
        return make_polynomial_inner(v1, product_terms(terms1, terms2))

    def stringify_coeff(coeff):
        coeff_str = stringify(coeff)
        if get_type(coeff) == 'real' and coeff > 0:
            return coeff_str
        else:
            return '(%s)' % coeff_str

    def stringify_term(term, variable):
        p = power_term(term)
        c = coeff_term(term)
        power_str = '%s^%d' % (variable, p) if p > 1 else variable
        coeff_str = stringify_coeff(c)
        if p == 0:
            return coeff_str
        elif coeff_str == '1':
            return power_str
        else:
            return '%s*%s' % (coeff_str, power_str)

    def stringify_polynomial(y):
        v = variable_polynomial(y)
        terms = terms_polynomial(y)
        return '+'.join([stringify_term(t, v) for t in terms])

    def convert_real_to_polynomial(yr, yp):
        v = variable_polynomial(yp)
        terms = [make_term(0, yr)] if yr != 0 else []
        return force_polynomial(v, terms)

    def convert_complex_to_polynomial(yc, yp):
        v = variable_polynomial(yp)
        terms = [make_term(0, yc)]
        return force_polynomial(v, terms)

    op_table['sum', 'polynomial', 'polynomial'] = sum_polynomial
    op_table['product', 'polynomial', 'polynomial'] = product_polynomial
    op_table['stringify', 'polynomial'] = stringify_polynomial
    op_table['make', 'polynomial'] = make_polynomial

    cv_table['real', 'polynomial'] = convert_real_to_polynomial
    cv_table['complex', 'polynomial'] = convert_complex_to_polynomial


def test_one(op_name, y1, y2, yresstr_exp):
    yres = sum(y1, y2) if op_name == 'sum' else product(y1, y2)
    y1str = stringify(y1)
    y2str = stringify(y2)
    yresstr = stringify(yres)
    print('%s(%s, %s) = %s' % (op_name, y1str, y2str, yresstr))
    assert yresstr == yresstr_exp


def test():
    # real
    test_one('sum', 2, -10, '-8')
    test_one('product', 2, -10, '-20')
    # complex
    test_one('sum', make('complex', 0, 0), make('complex', -10, 3), '-10+3*i')
    test_one('product', make('complex', 0, 0), make('complex', -10, 3), '0')
    test_one('sum', make('complex', 2, 1), make('complex', -10, 3), '-8+4*i')
    test_one('product', make('complex', 2, 1),
             make('complex', -10, 3), '-23-4*i')
    test_one('product', make('complex', 2, 1), make('complex', -10, 5), '-25')
    test_one('product', make('complex', 2, 1),
             make('complex', -10, -20), '-50*i')
    # complex and real
    test_one('sum', 2, make('complex', -10, 5), '-8+5*i')
    test_one('sum', make('complex', -10, 5), 2, '-8+5*i')
    test_one('product', 2, make('complex', -10, 5), '-20+10*i')
    test_one('product', make('complex', -10, 5), 2, '-20+10*i')
    test_one('product', make('complex', -10, 5), 0, '0')
    # polynomial
    test_one('sum',
             make('polynomial', 'x', []),  #
             make('polynomial', 'x', [(1, 1), (0, 1)]),  # x+1
             'x+1')
    test_one('product',
             make('polynomial', 'x', []),  #
             make('polynomial', 'x', [(1, 1), (0, 1)]),  # x+1
             '0')
    test_one('sum',
             make('polynomial', 'x', [(2, 1), (1, -1), (0, 1)]),  # x^2-x+1
             make('polynomial', 'x', [(1, 1), (0, 1)]),  # x+1
             'x^2+2')
    test_one('product',
             make('polynomial', 'x', [(2, 1), (1, -1), (0, 1)]),  # x^2-x+1
             make('polynomial', 'x', [(1, 1), (0, 1)]),  # x+1
             'x^3+1')
    test_one('sum',
             make('polynomial', 'x', [
                  (3, 3), (1, make('complex', 2, 3)), (0, 7)]),  # 3*x^3+(2+3i)x+7
             make('polynomial', 'x', [(2, make('complex', 5, 2)), (1, -2)]), # (5+2i)*x^2-2x
             '3*x^3+(5+2*i)*x^2+(3*i)*x+7')
    test_one('product',
             make('polynomial', 'x', [
                  (3, 3), (1, make('complex', 2, 3)), (0, 7)]),  # 3*x^3+(2+3i)x+7
             make('polynomial', 'x', [(2, make('complex', 5, 2)), (1, -2)]), # (5+2i)*x^2-2x
             '(15+6*i)*x^5+(-6)*x^4+(4+19*i)*x^3+(31+8*i)*x^2+(-14)*x')
    # polynomial and real
    test_one('sum',
             2,  #
             make('polynomial', 'x', [(1, 1), (0, 1)]),  # x+1
             'x+3')
    test_one('sum',
             make('polynomial', 'x', [(1, 1), (0, 1)]),  # x+1
             2,
             'x+3')
    test_one('product',
             2,  #
             make('polynomial', 'x', [(1, 1), (0, 1)]),  # x+1
             '2*x+2')
    test_one('product',
             make('polynomial', 'x', [(1, 1), (0, 1)]),  # x+1
             2,
             '2*x+2')
    # polynomial and complex
    test_one('sum',
             make('complex', 2, 3),  #
             make('polynomial', 'x', [(1, 1), (0, 1)]),  # x+1
             'x+(3+3*i)')
    test_one('sum',
             make('polynomial', 'x', [(1, 1), (0, 1)]),  # x+1
             make('complex', 2, 3),
             'x+(3+3*i)')
    test_one('product',
             make('complex', 2, 3),  #
             make('polynomial', 'x', [(1, 1), (0, 1)]),  # x+1
             '(2+3*i)*x+(2+3*i)')
    test_one('product',
             make('polynomial', 'x', [(1, 1), (0, 1)]),  # x+1
             make('complex', 2, 3),
             '(2+3*i)*x+(2+3*i)')
    # polynomial of polynomial
    test_one('sum',
             make('polynomial', 'x', [
                  (1, make('polynomial', 'y', [(1, 1), (0, 1)])), (0, 1)]),  # (y+1)x+1
             make('polynomial', 'x', [
                  (1, make('polynomial', 'y', [(1, 3), (0, 4)])), (0, 2)]),  # (3y+4)x+2
             '(4*y+5)*x+3')
    test_one('product',
             make('polynomial', 'x', [
                  (1, make('polynomial', 'y', [(1, 1), (0, 1)])), (0, 1)]),  # (y+1)x+1
             make('polynomial', 'x', [
                  (1, make('polynomial', 'y', [(1, 3), (0, 4)])), (0, 2)]),  # (3y+4)x+2
             '(3*y^2+7*y+4)*x^2+(5*y+6)*x+2')
    test_one('sum',
             make('polynomial', 'x', [
                  (1, make('polynomial', 'y', [(1, 1), (0, 1)])), (0, 1)]),  # (y+1)x+1
             make('polynomial', 'x', [
                  (1, make('polynomial', 'y', [(1, -1), (0, -1)])), (0, 2)]),  # (-y-1)x+2
             '3')
    test_one('sum',
             make('polynomial', 'x', [(1, make('polynomial', 'y', [
                  (1, make('polynomial', 'z', [(1, 2)])), (0, 1)])), (0, 1)]),  # ((2z)y+1)x+1
             make('polynomial', 'x', [(1, make('polynomial', 'y', [(1, make(
                 'polynomial', 'z', [(1, 1), (0, -1)])), (0, 4)])), (0, 2)]),  # ((z-1)y+4)x+2
             '((3*z+(-1))*y+5)*x+3')
    test_one('product',
             make('polynomial', 'x', [(1, make('polynomial', 'y', [
                  (1, make('polynomial', 'z', [(1, 2)])), (0, 1)])), (0, 1)]),  # ((2z)y+1)x+1
             make('polynomial', 'x', [(1, make('polynomial', 'y', [(1, make(
                 'polynomial', 'z', [(1, 1), (0, -1)])), (0, 4)])), (0, 2)]),  # ((z-1)y+4)x+2
             '((2*z^2+(-2)*z)*y^2+(9*z+(-1))*y+4)*x^2+((5*z+(-1))*y+6)*x+2')


if __name__ == '__main__':
    install_real()
    install_complex()
    install_polynomial()
    test()
