# basic expr
def is_number(y):
    return isinstance(y, (int, float))


def is_variable(y):
    return isinstance(y, str)


def is_same_variable(y1, y2):
    return y1 == y2


# general interface

def stringify_expr(y):
    if is_number(y):
        return str(y)
    elif is_variable(y):
        return y
    else:
        return y('stringify_expr')


def diff(y, x):
    assert is_variable(x)
    if is_number(y):
        return 0
    elif is_variable(y):
        return 1 if is_same_variable(y, x) else 0
    else:
        return y('diff', x)


# additional expr
# here we don't support dynamic installation, so we use make_sum/product explicitly, without a common make interface

def make_sum(y1, y2):
    def stringify_expr_sum():
        return '(%s+%s)' % (stringify_expr(y1), stringify_expr(y2))

    def diff_sum(x):
        return make_sum(diff(y1, x), diff(y2, x))

    def op_sum(op, *args):
        if op == 'stringify_expr':
            return stringify_expr_sum()
        elif op == 'diff':
            return diff_sum(*args)
        else:
            assert False

    if is_number(y1) and is_number(y2):
        return y1 + y2
    elif y1 == 0:
        return y2
    elif y2 == 0:
        return y1
    else:
        return op_sum


def make_product(y1, y2):
    def stringify_expr_product():
        return '(%s*%s)' % (stringify_expr(y1), stringify_expr(y2))

    def diff_product(x):
        return make_sum(make_product(diff(y1, x), y2), make_product(y1, diff(y2, x)))

    def op_product(op, *args):
        if op == 'stringify_expr':
            return stringify_expr_product()
        elif op == 'diff':
            return diff_product(*args)
        else:
            assert False

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
        return op_product


def test_one(y, x, dystr_exp):
    dy = diff(y, x)
    ystr = stringify_expr(y)
    xstr = stringify_expr(x)
    dystr = stringify_expr(dy)
    print('diff(%s, %s) = %s' % (ystr, xstr, dystr))
    assert dystr == dystr_exp


def test():
    test_one(make_sum(make_product('a', 'x1'),
             make_product('b', 'x2')), 'x1', 'a')
    test_one(make_sum(make_product('a', 'x1'),
             make_product('b', 'x2')), 'x2', 'b')
    test_one(make_product(make_product('x1', 'x2'),
             make_sum('x1', 3)), 'x1', '((x2*(x1+3))+(x1*x2))')


if __name__ == '__main__':
    test()
