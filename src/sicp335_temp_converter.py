from typing import List


class Constraint:
    def inform_conflict(self):
        pass

    def inform_set_value(self):
        pass

    def inform_forget_value(self):
        pass


class Connector:
    def __init__(self):
        self.value = None
        self.owner = None
        self.constraints: List[Constraint] = []

    def add_constraint(self, constraint: Constraint):
        if constraint not in self.constraints:
            self.constraints.append(constraint)

    def has_value(self):
        return self.owner is not None

    def get_value(self):
        return self.value if self.owner is not None else None

    def set_value(self, value, who: Constraint):
        if self.owner:
            if value != self.value:
                for constraint in self.constraints:
                    if who != constraint:
                        constraint.inform_conflict()
        else:
            self.value = value
            self.owner = who
            for constraint in self.constraints:
                if who != constraint:
                    constraint.inform_set_value()

    def forget_value(self, who: Constraint):
        if self.owner and self.owner == who:
            self.owner = None
            self.value = None
            for constraint in self.constraints:
                if who != constraint:
                    constraint.inform_forget_value()


class User(Constraint):
    pass


class Probe(Constraint):
    events = []

    def __init__(self, name: str, connector: Connector):
        self.name = name
        self.connector = connector

    def inform_conflict(self):
        Probe.events.append((self.name, 'conflict'))

    def inform_set_value(self):
        Probe.events.append((self.name, 'set', self.connector.get_value()))

    def inform_forget_value(self):
        Probe.events.append((self.name, 'forget'))

    @classmethod
    def probe(cls, name: str, connector: Connector):
        p = Probe(name, connector)
        connector.add_constraint(p)

    @classmethod
    def clear_events(cls):
        cls.events.clear()

    @classmethod
    def stringify_events(cls):
        res_list = []
        for event in cls.events:
            name = event[0]
            etype = event[1]
            if etype == 'conflict':
                res_list.append('%s=x' % name)
            elif etype == 'set':
                res_list.append('%s=%d' % (name, event[2]))
            elif etype == 'forget':
                res_list.append('%s=?' % name)
        return ', '.join(res_list)


class Adder(Constraint):
    '''a1 + a2 == sum'''
    def __init__(self, a1: Connector, a2: Connector, sum: Connector):
        self.a1 = a1
        self.a2 = a2
        self.sum = sum
        self.a1.add_constraint(self)
        self.a2.add_constraint(self)
        self.sum.add_constraint(self)
        self.inform_set_value()

    def inform_set_value(self):
        a1_ok = self.a1.has_value()
        a2_ok = self.a2.has_value()
        sum_ok = self.sum.has_value()
        a1_value = self.a1.get_value()
        a2_value = self.a2.get_value()
        sum_value = self.sum.get_value()
        if a1_ok and a2_ok:
            # update sum
            self.sum.set_value(a1_value + a2_value, self)
        elif a1_ok and (not a2_ok) and sum_ok:
            # update a2
            self.a2.set_value(sum_value - a1_value, self)
        elif (not a1_ok) and a2_ok and sum_ok:
            # update a1
            self.a1.set_value(sum_value - a2_value, self)

    def inform_forget_value(self):
        self.a1.forget_value(self)
        self.a2.forget_value(self)
        self.sum.forget_value(self)
        self.inform_set_value()


class Multiplier(Constraint):
    '''m1 * m2 == product'''
    def __init__(self, m1: Connector, m2: Connector, product: Connector):
        self.m1 = m1
        self.m2 = m2
        self.product = product
        self.m1.add_constraint(self)
        self.m2.add_constraint(self)
        self.product.add_constraint(self)
        self.inform_set_value()

    def inform_set_value(self):
        m1_ok = self.m1.has_value()
        m2_ok = self.m2.has_value()
        product_ok = self.product.has_value()
        m1_value = self.m1.get_value()
        m2_value = self.m2.get_value()
        product_value = self.product.get_value()
        if (m1_ok and m1_value == 0) or (m2_ok and m2_value == 0):
            # update product
            self.product.set_value(0, self)
        elif m1_ok and m2_ok:
            # update product
            self.product.set_value(m1_value * m2_value, self)
        elif m1_ok and (not m2_ok) and product_ok:
            # update m2
            self.m2.set_value(product_value / m1_value, self)
        elif (not m1_ok) and m2_ok and product_ok:
            # update m1
            self.m1.set_value(product_value / m2_value, self)

    def inform_forget_value(self):
        self.m1.forget_value(self)
        self.m2.forget_value(self)
        self.product.forget_value(self)
        self.inform_set_value()


class Constant(Constraint):
    def __init__(self, value, connector: Connector):
        self.value = value
        self.connector = connector
        self.connector.set_value(self.value, self)


def make_temp_converter(c: Connector, f: Connector):
    w = Connector()
    u = Connector()
    v = Connector()
    x = Connector()
    y = Connector()
    Multiplier(c, w, u)
    Multiplier(v, x, u)
    Adder(v, y, f)
    Constant(9, w)
    Constant(5, x)
    Constant(32, y)


def test_one(trigger, eventstr_exp):
    Probe.clear_events()
    trigger()
    eventstr = Probe.stringify_events()
    print('probe:', eventstr)
    assert eventstr == eventstr_exp


def test():
    # set up test
    c = Connector()
    f = Connector()
    Probe.probe('c', c)
    Probe.probe('f', f)
    make_temp_converter(c, f)
    user1 = User()
    user2 = User()
    # perform test
    test_one(lambda: c.set_value(25, user1), 'c=25, f=77')
    test_one(lambda: f.set_value(212, user1), 'f=x')
    test_one(lambda: c.forget_value(user2), '')
    test_one(lambda: c.forget_value(user1), 'c=?, f=?')
    test_one(lambda: c.forget_value(user1), '')
    test_one(lambda: f.set_value(212, user1), 'f=212, c=100')


if __name__ == '__main__':
    test()
