def is_number(y):
    return isinstance(y, (int, float))


def is_variable(y):
    return isinstance(y, str)


def is_sum(y):
    return isinstance(y, dict) and y['type'] == 'sum'


def is_product(y):
    return isinstance(y, dict) and y['type'] == 'product'


def get_addend1(y):
    return y['y1']


def get_addend2(y):
    return y['y2']


def get_multiplicand1(y):
    return y['y1']


def get_multiplicand2(y):
    return y['y2']


def make_sum(y1, y2):
    if is_number(y1) and is_number(y2):
        return y1 + y2
    elif y1 == 0:
        return y2
    elif y2 == 0:
        return y1
    else:
        return {'type': 'sum', 'y1': y1, 'y2': y2}


def make_product(y1, y2):
    if is_number(y1) and is_number(y2):
        return y1 * y2
    elif y1 == 0:
        return 0
    elif y1 == 1:
        return y2
    elif y2 == 0:
        return 0
    elif y2 == 1:
        return y1
    else:
        return {'type': 'product', 'y1': y1, 'y2': y2}


def is_same_variable(y1, y2):
    return y1 == y2


def stringify_expr(y):
    if is_number(y):
        return str(y)
    elif is_variable(y):
        return y
    elif is_sum(y):
        y1 = get_addend1(y)
        y2 = get_addend2(y)
        return '(%s+%s)' % (stringify_expr(y1), stringify_expr(y2))
    elif is_product(y):
        y1 = get_multiplicand1(y)
        y2 = get_multiplicand2(y)
        return '(%s*%s)' % (stringify_expr(y1), stringify_expr(y2))
    else:
        assert False


def diff(y, x):
    assert is_variable(x)
    if is_number(y):
        return 0
    elif is_variable(y):
        return 1 if is_same_variable(y, x) else 0
    elif is_sum(y):
        y1 = get_addend1(y)
        y2 = get_addend2(y)
        return make_sum(diff(y1, x), diff(y2, x))
    elif is_product(y):
        y1 = get_multiplicand1(y)
        y2 = get_multiplicand2(y)
        return make_sum(make_product(diff(y1, x), y2), make_product(y1, diff(y2, x)))
    else:
        assert False


def test_one(y, x, dystr_exp):
    dy = diff(y, x)
    ystr = stringify_expr(y)
    xstr = stringify_expr(x)
    dystr = stringify_expr(dy)
    print('diff(%s, %s) = %s' % (ystr, xstr, dystr))
    assert dystr == dystr_exp


def test():
    test_one({
        'type': 'sum',
        'y1': {
            'type': 'product',
            'y1': 'a',
            'y2': 'x1'
        },
        'y2': {
            'type': 'product',
            'y1': 'b',
            'y2': 'x2'
        }
    }, 'x1', 'a')
    test_one({
        'type': 'sum',
        'y1': {
            'type': 'product',
            'y1': 'a',
            'y2': 'x1'
        },
        'y2': {
            'type': 'product',
            'y1': 'b',
            'y2': 'x2'
        }
    }, 'x2', 'b')
    test_one({
        'type': 'product',
        'y1': {
            'type': 'product',
            'y1': 'x1',
            'y2': 'x2'
        },
        'y2': {
            'type': 'sum',
            'y1': 'x1',
            'y2': 3
        }
    }, 'x1', '((x2*(x1+3))+(x1*x2))')


if __name__ == '__main__':
    test()
