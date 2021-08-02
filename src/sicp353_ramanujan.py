# excercise 3.68, 3.70, 3.71
# the goal is to find integers that have at least two ways to be represented as sum of cubes
# I feel stream is really good at ordering and counting infinite sequence

from typing import Callable, Tuple
import sicp352_prime_number

Stream = sicp352_prime_number.Stream


def interleave(s1: Stream, s2: Stream, cmp: Callable[..., int]):
    head1 = s1.value()
    head2 = s2.value()
    cmp_res = cmp(head1, head2)
    if cmp_res == 0: 
        # add two items, because they are different item, just with the same weight
        return Stream(head1, lambda: Stream(head2, lambda: interleave(s1.next(), s2.next(), cmp)))
    elif cmp_res < 0:
        return Stream(head1, lambda: interleave(s1.next(), s2, cmp))
    else:
        return Stream(head2, lambda: interleave(s1, s2.next(), cmp))


def make_ordered_pairs(s1: Stream, s2: Stream, cmp: Callable[..., int]) -> Stream:
    '''genereate non-duplicate pairs of integers p = (s1[i], s2[j]) and i<j and cmp(p, p_next) <= 0'''
    head_pair = (s1.value(), s2.value())
    def make_upper_pairs(): return Stream.map(lambda x: (s1.value(), x), s2.next())
    def make_bottom_right_pairs(): return make_ordered_pairs(s1.next(), s2.next(), cmp)
    return Stream(head_pair, lambda: interleave(make_upper_pairs(), make_bottom_right_pairs(), cmp))


def groupby(s: Stream, cmp: Callable[..., int]) -> Stream:
    '''each item in the input is a value
    each item in the output stream is a list of values with the same weight
    this requires the input stream to be already ordered by weight'''
    values = [s.value()]
    s = s.next()
    while cmp(s.value(), values[-1]) == 0:
        values.append(s.value())
        s = s.next()
    return Stream(values, lambda: groupby(s, cmp))


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
    integers_from_one = Stream.make_integers().next()
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
