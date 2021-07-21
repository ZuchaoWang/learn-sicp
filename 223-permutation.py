def perm_recur(masks, prefix, perms):
    '''
    masks is a boolean array marking used symbol;
    prefix is ordered list of symbols already selected for permutation;
    perms is a list storing current result;
    we perform a depth-first search of all permutations
    '''

    if len(prefix) == len(masks): # all n symbols used
        perms.append(prefix.copy())
    else: # still has some symbol
        for i in range(len(masks)):
            if masks[i] == 0: # i is usable
                masks[i] = 1
                prefix.append(i) # use i
                perm_recur(masks, prefix, perms)
                prefix.pop() # unuse i
                masks[i] = 0


def permutate(n):
    masks = [0 for i in range(n)]
    prefix = []
    perms = []
    perm_recur(masks, prefix, perms)
    return perms


def test_one(n):
    perms = permutate(n)
    print('permutate(%d) finds %d permutations:' % (n, len(perms)))
    for p in perms:
        print(''.join([str(i+1) for i in p]), end=' ')
    print('')
    # check count
    count_exp = 1
    for i in range(n):
        count_exp *= i+1
    assert len(perms) == count_exp
    # check uniq count
    uniq_perm_set = set()
    for p in perms:
        uniq_perm_set.add(''.join([str(i+1) for i in p]))
    assert len(uniq_perm_set) == count_exp
    # check each is a permutation
    for p in perms:
        assert len(p) == n
        mask = [0 for i in range(n)]
        for i in p:
            assert mask[i] == 0
            mask[i] = 1


def test():
    test_one(5)


if __name__ == '__main__':
    test()