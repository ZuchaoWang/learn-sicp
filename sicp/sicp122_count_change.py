def count_change(coins, amount):
    '''recursion'''
    if len(coins) == 0 or amount < 0:
        return 0
    elif amount == 0:
        return 1
    else:
        return count_change(coins, amount-coins[0]) + count_change(coins[1:], amount)


def test_one(coins, amount, res_exp):
    count = count_change(coins, amount)
    print("count_change(%s, %d) = %d" % (str(coins), amount, count))
    assert count == res_exp


def test():
    test_one([], 100, 0)
    test_one([10, 5], 0, 1)
    test_one([50, 25, 10, 5, 1], 100, 292)


if __name__ == '__main__':
    test()
