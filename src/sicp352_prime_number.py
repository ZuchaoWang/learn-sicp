from typing import Callable, Optional, cast


class InfStream:
    '''
    infinite stream
    easier to implement than possibly finite stream, because no need to check if next is None
    '''

    def __init__(self, head, gen_next: Callable[[], "InfStream"]):
        self.head = head
        self.gen_next = gen_next
        # incorporate memoization within stream, will be used in next()
        self.next_cached = False
        self.next_cached_value: Optional["InfStream"] = None

    def value(self):
        return self.head

    def next(self) -> "InfStream":
        if self.next_cached is False:
            self.next_cached = True
            self.next_cached_value = self.gen_next()
        return cast(InfStream, self.next_cached_value)

    def nth_value(self, n: int):
        s = self
        for _ in range(n):
            s = s.next()
        return s.value()

    def topn_values(self, n: int):
        values = []
        s = self
        for _ in range(n):
            values.append(s.value())
            s = s.next()
        return values

    def filter(self, pred: Callable[..., bool]) -> "InfStream":
        s = self
        while True:
            head = s.value()
            rest = s.next()
            if pred(head):
                def gen_next(): return rest.filter(pred)
                return InfStream(head, gen_next)
            s = rest

    def scale(self, scl) -> "InfStream":
        return InfStream.map(lambda v: v*scl, self)

    def reciprocal(self) -> "InfStream":
        return InfStream.map(lambda v: 1/v, self)

    @staticmethod
    def map(proc: Callable, *sList: "InfStream") -> "InfStream":
        head = proc(*[s.value() for s in sList])

        def gen_next():
            return InfStream.map(proc, *[s.next() for s in sList])
        return InfStream(head, gen_next)

    @staticmethod
    def add(s1: "InfStream", s2: "InfStream") -> "InfStream":
        def adder(a, b):
            return a+b
        return InfStream.map(adder, s1, s2)

    @staticmethod
    def mult(s1: "InfStream", s2: "InfStream") -> "InfStream":
        def multiplier(a, b):
            return a*b
        return InfStream.map(multiplier, s1, s2)

    @staticmethod
    def make_ones():
        ones = InfStream(1, lambda: ones)
        return ones

    @staticmethod
    def make_integers():
        ones = InfStream.make_ones()
        integers = InfStream(0, lambda: InfStream.add(integers, ones))
        return integers


def make_primes_sieve():
    integers = InfStream.make_integers()
    integers_from_two = integers.next().next()

    def sieve(s: InfStream):
        head = s.value()
        return InfStream(head, lambda: sieve(s.next().filter(lambda x: x % head != 0)))

    primes = sieve(integers_from_two)
    return primes


def make_primes_check():
    integers = InfStream.make_integers()
    integers_from_three = integers.next().next().next()
    primes = InfStream(2, lambda: integers_from_three.filter(check_prime))

    def check_prime(x):
        s = primes
        while True:
            head = s.value()
            if head * head > x:
                return True
            if x % head == 0:
                return False
            s = s.next()

    return primes


def test_basic():
    # this test basic implementation
    ones = InfStream.make_ones()
    assert ones.nth_value(1) == 1
    assert ones.nth_value(10) == 1
    assert ones.nth_value(100) == 1
    assert ones.nth_value(1000) == 1

    integers = InfStream.make_integers()
    assert integers.nth_value(1) == 1
    assert integers.nth_value(10) == 10
    assert integers.nth_value(100) == 100
    assert integers.nth_value(1000) == 1000


def test_one(ss: InfStream, sc: InfStream, n):
    # this test prime from two methods
    vs = ss.nth_value(n)
    vc = sc.nth_value(n)
    print('prime(%d) = %d' % (n, vs))
    assert vs == vc


def test():
    test_basic()
    ss = make_primes_sieve()
    sc = make_primes_check()
    test_one(ss, sc, 1)
    test_one(ss, sc, 10)
    test_one(ss, sc, 100)
    # test_one(ss, sc, 1000) # this will execeed max recursion depth


if __name__ == '__main__':
    test()
