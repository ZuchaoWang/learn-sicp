import heapq
from typing import Callable, List, Tuple


class Wire:
    def __init__(self):
        self.signal = 0
        self.handlers = []

    def register_handler(self, h):
        self.handlers.append(h)
        h()

    def get(self) -> bool:
        return self.signal

    def set(self, value: bool):
        if self.signal != value:
            self.signal = value
            for h in self.handlers:
                h()


class Agenda:
    '''simulator, controlling time events'''
    t = 0
    seq_num = 0
    queue: List[Tuple[int, int, Callable]] = []

    @classmethod
    def run_later(cls, delay: int, h: Callable):
        assert delay > 0
        next_time = cls.t + delay
        heapq.heappush(cls.queue, (next_time, cls.seq_num, h))
        cls.seq_num += 1

    @classmethod
    def propagate(cls):
        while len(cls.queue):
            task = heapq.heappop(cls.queue)
            cls.t, _, h = task
            h()

    @classmethod
    def tick(cls):
        cls.t += 1


delays = {
    'invert': 2,
    'or': 3,
    'and': 5,
}


class Probe:
    '''record wire value when it changes'''

    def __init__(self):
        self.events = []

    def probe(self, name: str, w: Wire):
        def record_value():
            self.events.append((Agenda.t, name, w.get()))
        w.register_handler(record_value)

    def stringify(self):
        event_strs = []
        for t, name, value in self.events:
            event_strs.append('%d:%s=%d' % (t, name, value))
        return ', '.join(event_strs)

    def clear(self):
        self.events = []


def make_run_later(output: Wire, next_value: bool):
    def run_later():
        if output.get() != next_value:
            output.set(next_value)
    return run_later


def invert_gate(input: Wire, output: Wire):
    def update():
        next_value = (not input.get())
        run_later = make_run_later(output, next_value)
        Agenda.run_later(delays['invert'], run_later)

    input.register_handler(update)


def or_gate(input1: Wire, input2: Wire, output: Wire):
    def update():
        next_value = (input1.get() or input2.get())
        run_later = make_run_later(output, next_value)
        Agenda.run_later(delays['or'], run_later)

    input1.register_handler(update)
    input2.register_handler(update)


def and_gate(input1: Wire, input2: Wire, output: Wire):
    def update():
        next_value = (input1.get() and input2.get())
        run_later = make_run_later(output, next_value)
        Agenda.run_later(delays['and'], run_later)

    input1.register_handler(update)
    input2.register_handler(update)


def test_one(p: Probe, trigger, event_strs_exp: str):
    p.clear()  # clear prev record
    trigger()  # change input value
    Agenda.propagate()  # simulate to end
    Agenda.tick()  # add 1 tick time padding, convenience for next text_one
    event_strs = p.stringify()  # get records as str
    print(event_strs)
    assert event_strs == event_strs_exp


def test():
    # half adder, all wire initialized to 0
    a = Wire()  # input
    b = Wire()  # input
    d = Wire()
    e = Wire()
    s = Wire()  # output
    c = Wire()  # output
    and_gate(a, b, c)
    or_gate(a, b, d)
    invert_gate(c, e)
    and_gate(d, e, s)
    # set probes
    p = Probe()
    p.probe('a', a)
    p.probe('b', b)
    p.probe('s', s)
    p.probe('c', c)
    # run tests on half adder
    # initially a=b=s=c=0
    test_one(p, lambda: a.set(1), '0:a=1, 8:s=1')
    test_one(p, lambda: b.set(1), '9:b=1, 14:c=1, 21:s=0')
    test_one(p, lambda: a.set(0), '22:a=0, 27:c=0, 34:s=1')
    test_one(p, lambda: b.set(0), '35:b=0, 43:s=0')
    # notice in last test case: a record before b record, and s glitches 0->1->0
    test_one(p, lambda: (a.set(1), b.set(1)),
             '44:a=1, 44:b=1, 49:c=1, 52:s=1, 56:s=0')


if __name__ == '__main__':
    test()
