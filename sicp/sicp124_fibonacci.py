# m is a 2x2 matrix, represented in z-order
# e.g. identity is [1, 0, 0, 1]
# v is a 2x1 vector

def mat22multi(m1, m2):
    '''matrix-matrix multiplication'''
    return [
        m1[0]*m2[0]+m1[1]*m2[2],
        m1[0]*m2[1]+m1[1]*m2[3],
        m1[2]*m2[0]+m1[3]*m2[2],
        m1[2]*m2[1]+m1[3]*m2[3],
    ]


def mat22exp(m, n):
    '''matrix exponentiation'''
    if n == 0:
        return [1, 0, 0, 1]  # identity matrix
    elif n % 2:
        return mat22multi(m, mat22exp(m, n-1))
    else:
        return mat22exp(mat22multi(m, m), n/2)


def mat22vec(m, v):
    '''matrix-vector multiplication'''
    return [
        m[0]*v[0]+m[1]*v[1],
        m[2]*v[0]+m[3]*v[1]
    ]


def fibonacci(n):
    '''
    log(n) time fibonacci, using matrix exponentiation
    [f(n+1), f(n)]T = M*[f(n),f(n-1)]T
    where M is 2x2 matrix: [1, 1, 1, 0]
    '''
    mexpn = mat22exp([1, 1, 1, 0], n)  # M^n
    v0 = [1, 0]  # f(1), f(0)
    vn = mat22vec(mexpn, v0)  # f(n+1), f(n)
    return vn[1]  # f(n)


def test_one(i, res_exp):
    fi = fibonacci(i)
    print("fibonacci(%d) = %d" % (i, fi))
    assert fi == res_exp


def test():
    fbs = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144]
    for i in range(len(fbs)):
        test_one(i, fbs[i])


if __name__ == '__main__':
    test()
