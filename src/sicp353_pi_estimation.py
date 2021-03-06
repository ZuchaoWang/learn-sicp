import math
from sicp352_prime_number import InfStream


def make_pi_summands():
    '''generate 1, -1/3, 1/5, -1/7, ...'''
    def make_pi_summands_from(n: int):
        head = 1/(2*n+1)
        if n % 2 == 1:
            head = -head
        return InfStream(head, lambda: make_pi_summands_from(n+1))
    return make_pi_summands_from(0)


def partial_sum(s: InfStream):
    ps = InfStream(s.value(), lambda: InfStream.add(ps, s.next()))
    return ps


def make_pi_raw():
    '''partial sum of 1 - 1/3 + 1/5 - 1/7 + ...
    will be row 0 of table'''
    pi_summands = make_pi_summands()
    return partial_sum(pi_summands).scale(4)


def euler_transform(s: InfStream):
    '''only applicable to alternative series'''
    v0 = s.value()
    v1 = s.next().value()
    v2 = s.next().next().value()
    if v2-v1*2+v0 == 0:
        head = v2
    else:
        head = v2-(v2-v1)*(v2-v1)/(v2-v1*2+v0)
    return InfStream(head, lambda: euler_transform(s.next()))


def make_pi_acc_table(s: InfStream):
    '''each item is itself a stream of estimation'''
    return InfStream(s, lambda: make_pi_acc_table(euler_transform(s)))


def make_pi_acc1(table: InfStream) -> InfStream:
    '''row 1 of table'''
    return table.next().value()


def make_pi_acc2(table: InfStream) -> InfStream:
    '''column 0 of table'''
    return InfStream.map(lambda s: s.value(), table)


def make_pi_acc3(table: InfStream) -> InfStream:
    '''diagonal of table'''
    def make_pi_acc3_from(n: int):
        head = table.nth_value(n).nth_value(n)
        return InfStream(head, lambda: make_pi_acc3_from(n+1))
    return make_pi_acc3_from(0)


def test():
    pi_raw = make_pi_raw()
    pi_table = make_pi_acc_table(pi_raw)
    pi_acc1 = make_pi_acc1(pi_table)
    pi_acc2 = make_pi_acc2(pi_table)
    pi_acc3 = make_pi_acc3(pi_table)
    res = []
    n = 8
    res.append(pi_raw.topn_values(n))
    res.append(pi_acc1.topn_values(n))
    res.append(pi_acc2.topn_values(n))
    res.append(pi_acc3.topn_values(n))
    # print
    print('estimation of pi = %.14f:' % math.pi)
    print(', '.join(['raw0'+' '*12, 'acc1'+' '*12, 'acc2'+' '*12, 'acc3'+' '*12]))
    for i in range(n):
        print(', '.join(['%.14f' % res[j][i] for j in range(len(res))]))
    # test
    for j in range(len(res)-1):
        assert abs(res[j][-1]-math.pi) >= abs(res[j+1][-1]-math.pi)


if __name__ == '__main__':
    test()