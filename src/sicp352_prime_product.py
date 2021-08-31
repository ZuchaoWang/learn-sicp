# return a list of "simple" numbers in increasing order
# such "simple" numbers only have prime factors 2, 3, 5
# this problem is raised in exercise 3.56 in the context of stream
# but it can also be solved using pure iteration
# using the same idea

from typing import List, TypedDict


class PrimeWorker(TypedDict):
    prime: int
    pos: int
    value: int


def prime_product(primes: List[int], n: int) -> List[int]:
    result = [1]
    workers: List[PrimeWorker] = [{'prime': p, 'pos': 0, 'value': p} for p in primes]
    for _ in range(n-1):
        # find min
        min_worker_index: int = 0
        for i in range(1, len(workers)):
            if workers[i]['value'] < workers[min_worker_index]['value']:
                min_worker_index = i
        # generate next_value
        next_value = workers[min_worker_index]['value']
        result.append(next_value)
        # remove next_value in all workers
        for i in range(0, len(workers)):
            w = workers[i]
            if w['value'] == next_value:
                w['pos'] += 1
                w['value'] = result[w['pos']] * w['prime']
    return result


def check_one(primes: List[int], x: int):
    y = x
    for p in primes:
        while y % p == 0:
            y //= p
    return y == 1


def test():
    primes = [2, 3, 5]
    n = 100
    result = prime_product(primes, n)
    primes_str = ', '.join([str(x) for x in primes])
    result_str = ', '.join([str(x) for x in result])
    print('prime_product of %s, first %d numbers:\n%s' % (primes_str, n, result_str))
    # test increasing order
    for i in range(len(result) - 1):
        assert result[i] < result[i+1]
    # test only have factors in primes
    for i in range(len(result)):
        assert check_one(primes, result[i])


if __name__ == '__main__':
    test()
