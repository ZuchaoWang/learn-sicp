def queens_recur(n, prefix, poss):
    '''
    prefix is the positions of currently positioned queens (may not have positioned all queens);
    poss is a list storing current fully positioned queues;
    we perform a depth-first search of all positions
    '''

    row = len(prefix)
    if row == n: # all n queens positioned
        poss.append(prefix.copy())
    else: # still has some queen not positioned
        for col in range(n):
            # test confict with each prev position
            ok = True
            for (prev_row, prev_col) in enumerate(prefix):
                if (col == prev_col) \
                    or (row+col == prev_row+prev_col) \
                    or (row-col == prev_row-prev_col):
                    ok = False
                    break
            if ok: # pass all conflict tests
                prefix.append(col)
                queens_recur(n, prefix, poss)
                prefix.pop()


def queens(n):
    prefix = []
    poss = []
    queens_recur(n, prefix, poss)
    return poss


def test_one(n, count_exp):
    poss = queens(n)
    print('queens(%d) finds %d positions:' % (n, len(poss)))
    for p in poss:
        print(''.join([str(i+1) for i in p]), end=' ')
    print('')
    assert len(poss) == count_exp

  
def test():
    test_one(8, 92)


if __name__ == '__main__':
    test()
