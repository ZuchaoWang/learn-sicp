from typing import Generic, List, Optional, TypeVar


T = TypeVar("T")


class LinkedListNode(Generic[T]):
    def __init__(self, data: T, next: "Optional[LinkedListNode[T]]"):
        self.data = data
        self.next = next

    @staticmethod
    def from_list(ls: List[T]):
        cur: "Optional[LinkedListNode[T]]" = None
        for i in range(len(ls)-1, -1, -1):
            cur = LinkedListNode(ls[i], cur)
        return cur

    @staticmethod
    def to_list(ll: "Optional[LinkedListNode[T]]"):
        ls: List[T] = []
        cur = ll
        while cur is not None:
            ls.append(cur.data)
            cur = cur.next
        return ls


def cycle_detect(head: Optional[LinkedListNode[T]]):
    '''
    Floyd's hare and tortoise algorithm for cycle detection
    head is the start of a linked list
    if cyclic, return the start of cycle node
    if acyclic, return None

    the benefit of the algorithm is that it use linear time and constant space
    and most importantly, it's funny!

    why it works?

    assuming the first x nodes are linear, then followed by a cycle with y nodes
    then hare will chase tortoise at round ceil(x/y)*y
    because now both hare and tortoise has entered the cycle
    and their step difference is a multiple of y

    after that, the tortoise just need to move another x steps to find start of cycle
    because ceil(x/y)*y+x is at the position of the start of cycle
    '''
    if not (head and head.next):
        return None
    hare: Optional[LinkedListNode[T]] = head.next.next
    tortoise: Optional[LinkedListNode[T]] = head.next
    # start chasing
    while hare != tortoise:
        if not (hare and hare.next):
            return None
        hare = hare.next.next
        assert tortoise
        tortoise = tortoise.next
    assert hare == tortoise
    # find start of cycle
    hare = head
    while hare != tortoise:
        assert hare
        assert tortoise
        hare = hare.next
        tortoise = tortoise.next
    return hare


def make_linked_list(n: int, k: Optional[int] = None):
    '''
    make a linked list of n nodes
    each node has data and next pointer
    if k is None, then this is a simple linked list
    if k is an integer, then it's cyclic and the final node point to k-th node
    '''
    assert n >= 1
    assert k is None or (k >= 0 and k < n)
    ll = [LinkedListNode(i, None) for i in range(n)]
    for i in range(n-1):
        ll[i].next = ll[i+1]
    ll[n-1].next = None if k is None else ll[k]
    return ll[0]


def stringify_linked_list(n: int, k: Optional[int] = None):
    ll_str = '->'.join([str(i) for i in range(n)])
    if k is not None:
        ll_str += ('->' + str(k))
    return ll_str


def test_one(n: int, k: Optional[int] = None):
    head = make_linked_list(n, k)
    cycle_node = cycle_detect(head)
    # print result
    ll_str = stringify_linked_list(n, k)
    cycle_str = 'acyclic' if cycle_node is None else (
        'cycle starts at %d' % cycle_node.data)
    print('%s: %s' % (ll_str, cycle_str))
    # check result
    if k is None:
        assert cycle_node is None
    else:
        assert cycle_node.data == k


def test():
    n = 7
    test_one(n)
    for i in range(n):
        test_one(n, i)


if __name__ == '__main__':
    test()
