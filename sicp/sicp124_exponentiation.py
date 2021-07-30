def exponentiation(a, n):
    '''log(n) time exponentiation'''
    if n == 0:
        return 1
    elif n % 2:  # odd
        return a*exponentiation(a, n-1)
    else:  # even
        return exponentiation(a*a, n/2)


def test_one(a, n, res_exp):
    an = exponentiation(a, n)
    print("exponentiation(%d, %d) = %d" % (a, n, an))
    assert an == res_exp


def test():
    for i in range(10):
        test_one(3, i, pow(3, i))


if __name__ == '__main__':
    test()
