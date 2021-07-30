def make_root(x):
    return lambda y: y*y-x


dy = 1e-4
def derivative(f, y):
    df = f(y+dy) - f(y)
    return df/dy


eps = 1e-4
def fixed_point(f, y0):
    y = y0
    while (abs(f(y)) >= eps):
      h = y - f(y)/derivative(f, y)
      y = h
    return y


def sqrt_newton(x):
    '''
    calulcate sqrt of x in R*, using newton method;
    first transform it to finding root problem: f(y) = y^2 - x = 0
    then transform to fixed point problem: h(y) = y - f(y)/f'(y)
    '''
    f = make_root(x)
    y = fixed_point(f, 1)
    return y


def test_one(x):
    y = sqrt_newton(x)
    print("sqrt_newton(%d) = %f" % (x, y))
    assert abs(y*y - x) < eps


def test():
    for x in range(10):
        y = sqrt_newton(x)
        test_one(x)


if __name__ == '__main__':
    test()