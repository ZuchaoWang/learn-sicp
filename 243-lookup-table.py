# basic expr
def is_number(y):
    return isinstance(y, (int, float))


def is_variable(y):
    return isinstance(y, str)


def is_same_variable(y1, y2):
    return y1 == y2


# lookup table
# (sum | product) => (make | diff | stringify_expr) => func
table = {}


def apply(fname, y, *args):
    f = table[y['type']][fname]
    return f(y['data'], *args)


# general interface
# we use this "make" to ensure make_sum/product function only available after dynamically installing them
# it also ensures them to be a dict with type field, no matter how they are internally represented
def make(etype, *args):
    f = table[etype]['make']
    data, shortcut = f(*args)
    return data if shortcut else {'type': etype, 'data': data}


def stringify_expr(y):
    if is_number(y):
        return str(y)
    elif is_variable(y):
        return y
    else:
        return apply('stringify_expr', y)


def diff(y, x):
    assert is_variable(x)
    if is_number(y):
        return 0
    elif is_variable(y):
        return 1 if is_same_variable(y, x) else 0
    else:
        return apply('diff', y, x)


# additional expr

def install_sum():
    # here y is y['data']
    def get_addend1(y):
        return y['y1']

    def get_addend2(y):
        return y['y2']

    def make_sum(y1, y2):
        if is_number(y1) and is_number(y2):
            return y1 + y2, True
        elif y1 == 0:
            return y2, True
        elif y2 == 0:
            return y1, True
        else:
            return {'y1': y1, 'y2': y2}, False

    def stringify_expr_sum(y):
        y1 = get_addend1(y)
        y2 = get_addend2(y)
        return '(%s+%s)' % (stringify_expr(y1), stringify_expr(y2))

    def diff_sum(y, x):
        y1 = get_addend1(y)
        y2 = get_addend2(y)
        return make('sum', diff(y1, x), diff(y2, x))

    table['sum'] = {
        'make': make_sum,
        'stringify_expr': stringify_expr_sum,
        'diff': diff_sum
    }


def install_product():
    assert 'sum' in table

    # here y is y['data']
    def get_multiplicand1(y):
        return y['y1']

    def get_multiplicand2(y):
        return y['y2']

    def make_product(y1, y2):
        if is_number(y1) and is_number(y2):
            return y1 * y2, True
        elif y1 == 0:
            return 0, True
        elif y1 == 1:
            return y2, True
        elif y2 == 0:
            return 0, True
        elif y2 == 1:
            return y1, True
        else:
            return {'y1': y1, 'y2': y2}, False

    def stringify_expr_product(y):
        y1 = get_multiplicand1(y)
        y2 = get_multiplicand2(y)
        return '(%s*%s)' % (stringify_expr(y1), stringify_expr(y2))

    def diff_product(y, x):
        y1 = get_multiplicand1(y)
        y2 = get_multiplicand2(y)
        return make('sum', make('product', diff(y1, x), y2), make('product', y1, diff(y2, x)))

    table['product'] = {
        'make': make_product,
        'stringify_expr': stringify_expr_product,
        'diff': diff_product
    }


def test_one(y, x, dystr_exp):
    dy = diff(y, x)
    ystr = stringify_expr(y)
    xstr = stringify_expr(x)
    dystr = stringify_expr(dy)
    print('diff(%s, %s) = %s' % (ystr, xstr, dystr))
    assert dystr == dystr_exp


def test():
    test_one(make('sum', make('product', 'a', 'x1'),
             make('product', 'b', 'x2')), 'x1', 'a')
    test_one(make('sum', make('product', 'a', 'x1'),
             make('product', 'b', 'x2')), 'x2', 'b')
    test_one(make('product', make('product', 'x1', 'x2'),
             make('sum', 'x1', 3)), 'x1', '((x2*(x1+3))+(x1*x2))')


if __name__ == '__main__':
    install_sum()
    install_product()
    test()
