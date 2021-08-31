# excercise 3.68, 3.70, 3.71
# the goal is to find integers that have at least two ways to be represented as sum of cubes
# I feel stream is really good at ordering and counting infinite sequence

from typing import Callable, Tuple
from sicp352_prime_number import InfStream


def interleave(s1: InfStream, s2: InfStream, cmp: Callable[..., int]):
    head1 = s1.value()
    head2 = s2.value()
    cmp_res = cmp(head1, head2)
    if cmp_res == 0: 
        # add two items, because they are different item, just with the same weight
        return InfStream(head1, lambda: InfStream(head2, lambda: interleave(s1.next(), s2.next(), cmp)))
    elif cmp_res < 0:
        return InfStream(head1, lambda: interleave(s1.next(), s2, cmp))
    else:
        return InfStream(head2, lambda: interleave(s1, s2.next(), cmp))


def make_ordered_pairs(s1: InfStream, s2: InfStream, cmp: Callable[..., int]) -> InfStream:
    '''genereate non-duplicate pairs of integers p = (s1[i], s2[j]) and i<j and cmp(p, p_next) <= 0'''
    head_pair = (s1.value(), s2.value())
    def make_upper_pairs(): return InfStream.map(lambda x: (s1.value(), x), s2.next())
    def make_bottom_right_pairs(): return make_ordered_pairs(s1.next(), s2.next(), cmp)
    return InfStream(head_pair, lambda: interleave(make_upper_pairs(), make_bottom_right_pairs(), cmp))


def groupby(s: InfStream, cmp: Callable[..., int]) -> InfStream:
    '''each item in the input is a value
    each item in the output stream is a list of values with the same weight
    this requires the input stream to be already ordered by weight'''
    values = [s.value()]
    s = s.next()
    while cmp(s.value(), values[-1]) == 0:
        values.append(s.value())
        s = s.next()
    return InfStream(values, lambda: groupby(s, cmp))


def calc_weight(p: Tuple[int, int]) -> int:
    '''must be increasing w.r.t. to x and y'''
    x, y = p
    return x*x*x + y*y*y


def cmp_weight(p1: Tuple[int, int], p2: Tuple[int, int]) -> int:
    '''==0 for equal, <0 for less than, >0 for greater than'''
    return calc_weight(p1) - calc_weight(p2)


def stringify_pair(p: Tuple[int, int]) -> str:
    x, y = p
    return '%d^3+%d^3' % (x, y)


def test():
    integers_from_one = InfStream.make_integers().next()
    integer_pairs = make_ordered_pairs(
        integers_from_one, integers_from_one, cmp_weight)
    integer_pair_groups = groupby(integer_pairs, cmp_weight)
    ramanujan = integer_pair_groups.filter(lambda x: len(x) > 1)
    # print
    n = 10
    ramanujan_topn = ramanujan.topn_values(n)
    for r in ramanujan_topn:
        res_list = [str(calc_weight(r[0]))]
        res_list.extend([stringify_pair(p) for p in r])
        print(' = '.join(res_list))
    # only test the first two cases
    # ref: https://zh.wikipedia.org/wiki/1729
    assert calc_weight(ramanujan_topn[0][0]) == 1729
    assert calc_weight(ramanujan_topn[1][0]) == 4104


if __name__ == '__main__':
    test()
