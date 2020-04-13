from radical_expr import etimes, esumlist, rtimes, expr_to_float, expr_to_latex
from my_math import float_equal, factorize, r
from functools import reduce
from expr_metrics import expr_length

import my_math
my_math.be_quiet = True
#my_math.float_check = True

# Calculates a radical expression for the pth roots of unity, where p is prime
# Currently this script produces an unrefined expression.
# To understand the difference between an unrefined and a refined radical expression, consider this:
#   Under radicals, you often have to compute sums of roots of unity of lower degree. A refined method computes these sums the same way it would compute a single root of unity of the same degree, resulting in expressions that are no longer than those for the roots themselves. However, an unrefined method computes them by simply adding the predetermined radical expressions for single roots, which often results in a much longer (and uglier) expression.

# list manipulating functions
# Lists of integers are the internal way of representing sums of roots of unity. The length of the list determines the degree of the roots and is often passed in as rnum. Each number in the list is a coefficient for one of the roots, which range from 1 to r_{rnum - 1}.

# adds two root sums
def plus(l1, l2, rnum):
    return [l1[i] + l2[i] for i in range(rnum)]

# sums a list of root sums (list of lists of integers)
def sumlist(ll, rnum):
    if len(ll) == 0:
        raise RuntimeError("Cannot sum an empty list")
    if len(ll) == 1:
        return ll[0]
    else:
        return plus(sumlist(ll[:-1], rnum), ll[-1], rnum)

# multiplies two root sums
def times(l1, l2, rnum):
    ans = [0] * rnum
    for i in range(rnum):
        for j in range(rnum):
            ans[(i + j) % rnum] += l1[i] * l2[j]

    return ans

# multiplies root sum by integer
def itimes(a, l1, rnum):
    return [a * l1[i] for i in range(rnum)]

# takes root sum to integer power
def power(l, n, rnum):
    assert type(n) == int and n > 0
    if n == 1:
        return l
    else:
        return times(power(l, n - 1, rnum), l, rnum)

def l_to_sig(l, rnum, degree, g):
    assert (rnum - 1) % degree == 0
    gpoweri = 1
    ans = [0] * degree
    for i in range(degree):
        ans[i] = l[gpoweri] - l[0]
        gpoweri = (gpoweri * g) % rnum
    return ans

def sig_to_l(sig, rnum, g):
    degree = len(sig)
    assert (rnum - 1) % degree == 0
    ans = [0] * rnum
    gpoweri = 1
    for i in range(rnum - 1):
        ans[gpoweri] = sig[i % degree]
        gpoweri = (gpoweri * g) % rnum
    return ans

def m_to_sig(m, rnums, degrees, gs):
    assert all([(rnums[i] - 1) % degrees[i] == 0 for i in range(len(rnums))])
    gpoweri = 1
    ans = new_mat(degrees[0], degrees[1])
    for i in range(degrees[0]):
        ans[i] = l_to_sig(plus(m[gpoweri], itimes(-1, m[0], rnums[1]), rnums[1]), rnums[1], degrees[1], gs[1])
        gpoweri = (gpoweri * gs[0]) % rnums[0]
    return ans

def sig_to_m(sig, rnums, gs):
    degrees = [0, 0]
    degrees[0] = len(sig)
    degrees[1] = len(sig[0])
    assert all([(rnums[i] - 1) % degrees[i] == 0 for i in range(len(rnums))])
    ans = new_mat(rnums[0], rnums[1])
    gpoweri = 1
    for i in range(rnums[0] - 1):
        ans[gpoweri] = sig_to_l(sig[i % degrees[0]], rnums[1], gs[1])
        gpoweri = (gpoweri * gs[0]) % rnums[0]
    return ans

def lcycperm(l, x, degree):
    x = x % degree
    l = l[degree - x:] + l[:degree - x]
    return l

def mcycperm(m, xy, degrees):
    ans = []
    for i in range(degrees[0]):
        ans.append(lcycperm(m[i], xy[1], degrees[1]))
    ans = lcycperm(ans, xy[0], degrees[0])
    return ans

# entries are in the form (signature of m, exponent, signature of m^exponent). includes both sums and multisums.
power_lookup_table = []

def cyc_compare(l1, l2):
    possible_offsets = []
    for i, n in enumerate(l2):
        if l1[0] == n:
            possible_offsets.append(i)
    if len(possible_offsets) == 0:
        return None
    degree = len(l1)
    for i in possible_offsets:
        fail = False
        for j in range(degree):
            if l1[j] != l2[(j + i) % degree]:
                fail = True
                break
        if not fail:
            return i
    return None

def mcyc_compare(m1, m2):
    possible_offsets = []
    for i, l in enumerate(m2):
        result = cyc_compare(m1[0], l)
        if result != None:
            possible_offsets.append((i, result))
    if len(possible_offsets) == 0:
        return None
    degrees = [len(m1), len(m1[0])]
    for (i, result) in possible_offsets:
        exit_to_here = False
        for j in range(len(m1)):
            for k in range(len(m1[0])):
                if m1[j][k] != m2[(j + i) % degrees[0]][(k + result) % degrees[1]]:
                    exit_to_here = True
                    break
            if exit_to_here:
                break
        if not exit_to_here:
            return (i, result)
    return None

# creates a list of roots of unity of specified degree, represented as lists
def make_cycle(num):
    cycle = []
    for i in range(num):
        root = [0] * num
        root[i] = 1
        cycle.append(root)
    return cycle

# matrix manipulating functions
# Matrices of integers, represented as lists of lists, repersent sums of products of roots of unity of two degrees. The first of those degrees, the length of each list within the matrix, is often passed in as rnum.

# creates a matrix of zeros with the specified number of rows and columns
def new_mat(nrow, ncol):
    m = []
    for i in range(nrow):
        m.append([0] * ncol)
    return m

# adds two matrices
def mplus(m1, m2, rnum):
    if len(m1) != len(m2):
        raise RuntimeError("Cannot add matrices with inconsistent dimensions")
    nrow = len(m1)
    return [plus(m1[i], m2[i], rnum) for i in range(nrow)]

# sums a list of matrices
def msumlist(ml, rnum):
    if len(ml) == 0:
        raise RuntimeError("Cannot sum an empty list")
    if len(ml) == 1:
        return ml[0]
    else:
        return mplus(msumlist(ml[:-1], rnum), ml[-1], rnum)

# multiplies two matrices
def mtimes(m1, m2, rnum):
    if len(m1) != len(m2):
        raise RuntimeError("Cannot multiply matrices with inconsistent dimensions")
    nrow = len(m1)
    ans = new_mat(nrow, rnum)
    for i in range(nrow):
        for j in range(nrow):
            k = (i + j) % nrow
            ans[k] = plus(ans[k], times(m1[i], m2[j], rnum), rnum)
    return ans

# takes matrix to integer power
def mpower(m, n, rnum, degrees, gs):
    msig = m_to_sig(m, [len(m), rnum], degrees, gs)
    for entry in power_lookup_table:
        if entry[1] == n:
            result = mcyc_compare(entry[0], msig)
            if result != None:
                print("Lookup match found. Matrix sig is {} and it matches {}.\n".format(msig, entry[0]))
                return sig_to_m(mcycperm(entry[2], result, degrees), [len(m), rnum], gs)
    assert type(n) == int and n > 0
    ans = new_mat(len(m), rnum)
    ans[0][0] = 1
    for i in range(n):
        ans = mtimes(ans, m, rnum)
    power_lookup_table.append((msig, n, m_to_sig(ans, [len(m), rnum], degrees, gs)))
    return ans

# multiplies two sums of roots of unity of different degrees to obtain a matrix
# rnum is the degree of the roots in the second sum and becomes the row length
def xtimes(col, row, rnum):
    assert len(row) == rnum
    ans = new_mat(len(col), rnum)
    for i in range(len(col)):
        for j in range(rnum):
            ans[i][j] = col[i] * row[j]
    return ans

'''def convert(num, rnum):
    return [num] + [0] * rnum'''

# conversion functions
# Sometimes particular sums of roots of unity are already calculated. If there are sufficient symmetries in the terms of the list, it can be expressed as a sum of these sums.

# given a list and a sequence of terms, expresses the list as a sum of those terms
# each term is either 1 or a list representing a sum of roots
# returns list of coefficients appearing on each tech
def deconvert(l, terms, rnum):
    l = l[:]

    if terms == [1]:
        if l[1:] != [l[1]] * (rnum - 1):
            raise RuntimeError("Unable to separate number into coefficients")
        return [l[0] - l[1]]

    nterms = len(terms)
    coeffs = [0] * nterms
    for i in range(nterms):
        if terms[i] == 1:
            coeffs[i] = l[0]
            l[0] = 0
        elif type(terms[i]) == list:
            assert len(terms[i]) == rnum
            coeff = l[[k for k in range(rnum) if terms[i][k] == 1][0]]
            l = plus(l, itimes(-coeff, terms[i], rnum), rnum)
            coeffs[i] = coeff

    if l != [0] * rnum:
        raise RuntimeError("Unable to separate number into coefficients")
    return coeffs

# given a matrix and a sequence of terms, expresses each row of matrix as a sum of those terms
def mdeconvert(m, terms, rnum):
    return [deconvert(l, terms, rnum) for l in m]

# floating point functions
# In order to check that the answer is correct, we need to convert our expressions into complex floating point numbers. This is quite useful for debugging.

# converts a simple list (sum of roots of unity) to a float
def to_float(l, rnum):
    values = [r(rnum, i) for i in range(rnum)]
    return sum([l[i] * values[i] for i in range(rnum)])

# converts a matrix to a float
def mat_to_float(m, rnum):
    nrow = len(m)
    values = [r(rnum, i) for i in range(rnum)]
    return sum([sum([m[i][j] * values[j] for j in range(rnum)]) * r(nrow, i) for i in range(nrow)])

# radical-expression functions
# When a sum of roots of unity is expressed in terms of previously calculated sums, the radical expressions for the sum can be computed in terms of the expressions for those sums.

# converts a sum of known terms to a single expression, given the coefficient on each term and the term's expression
def coeff_to_expr(coeffs, exprs):
    ncoeffs = len(coeffs)
    if ncoeffs != len(exprs):
        raise RuntimeError("Length of coefficient list does not match length of expression list")
    return esumlist([etimes(coeffs[i], exprs[i]) for i in range(ncoeffs)])

# converts a matrix-sum of known terms to a single expression, given the coefficient on each term the term's expression, and the expression for each root of unity given by the position within the column.
def mcoeff_to_expr(mcoeffs, exprs, rexprs):
    nroots = len(mcoeffs)
    if nroots != len(rexprs):
        raise RuntimeError("Height of coefficient matrix does not match number of roots")
    return esumlist([etimes(coeff_to_expr(mcoeffs[i], exprs), rexprs[i]) for i in range(nroots)])

# miscellaneous functions

# creates a sequence [1, n, n^2 % base, ..., n^(base - 2) % base], where base is prime and n is a primitive root of base
# the sequence is a multiplicative cycle (mod base)
def make_power_cycle(base):
    # assert base is prime
    # to do
    if base == 2:
        return [1]
    mult = 2
    while mult < base:
        cycle = []
        i = 0
        num = 1
        while i < base - 1:
            cycle.append(num)
            i += 1
            num = (num * mult) % base
            if num == 1:
                if i == base - 1:
                    return cycle
                else:
                    break
        if (base - 1) % i != 0:
            raise RuntimeError("The input value is not prime")
        mult += 1

# partitions a multiplicative cycle (mod nroots) into nparts parts and returns a list of the parts
def partition(nroots, cycle, nparts):
    if (nroots - 1) % nparts != 0:
        raise RuntimeError("Number of partitions must be factor of number of roots minus one")
    nsteps = (nroots - 1) // nparts
    ans = []
    for i in range(nparts):
        l = [0] * nroots
        for j in range(nsteps):
            l[cycle[nparts * j + i]] = 1
        ans.append(l)
    return ans

# generates all tuples of numbers whose values are between 0 and the corresponding entry in nums
# acts like an arbitrarily deep stack of "for i in range(n):" statements
def multi_range(nums):
    n_nums = len(nums)
    curr = [0] * n_nums
    yield tuple(curr)
    while True:
        # to increment tuple, find last value that can be incremented
        # increment and set all subsequent values to 0
        diff = [nums[i] - curr[i] for i in range(n_nums)]
        incrementable_inds = [i for i in range(n_nums) if diff[i] > 1]
        if len(incrementable_inds) == 0:
            # noting more to increment, nothing more to yield
            return
        last = incrementable_inds[-1]
        curr[last] += 1
        for i in range(last + 1, n_nums):
            curr[i] = 0
        yield tuple(curr)

# returns the product of all numbers in a list
def product(l):
    if len(l) == 0:
        return 1
    else:
        return reduce((lambda x, y: x * y), l)

# given a list of integers [a, b, c, ..., j, k] (mults) and an integer (num), finds u < a, v < b, ..., z < k such that num = u*b*c*...*k + v*c*...*k + ... + z
# then computes and returns the value z*j*...*a + ... + v*a + u
def bit_reverse(num, mults):
    mults = mults[:]
    remainders = [(num // product(mults[i + 1:])) % mults[i] for i in range(len(mults))]
    mults.reverse()
    remainders.reverse()
    return sum([remainders[i] * product(mults[i + 1:]) for i in range(len(mults))])

# list of known root expressions, which will get updated as needed with more memoized expressions
r_x = {
    2 : [1, -1],
    3 : [1, (['+', -1, ['r', 2, 0, -3, 1]], 2), (['+', -1, ['r', 2, 1, -3, 1]], 2)],
    5 : [1, (['+', -1, ['r', 2, 0, 5, 1], ['r', 2, 0, ['+', -10, ['r', 2, 1, 5, 2]], 1]], 4), (['+', -1, ['r', 2, 1, 5, 1], ['r', 2, 0, ['+', -10, ['r', 2, 0, 5, 2]], 1]], 4), (['+', -1, ['r', 2, 1, 5, 1], ['r', 2, 1, ['+', -10, ['r', 2, 0, 5, 2]], 1]], 4), (['+', -1, ['r', 2, 0, 5, 1], ['r', 2, 1, ['+', -10, ['r', 2, 1, 5, 2]], 1]], 4)]
}

# constructs radical expressions for nth roots of unity, where n (passed in as rnum) is prime
def roots_to_radicals(rnum):
    if rnum in r_x:
        return r_x[rnum]

    # prime factors of n - 1
    # to match the expressions I found in 2013, factors are placed in increasing order except for one 2 at the end.
    # the last factor needs to be 2 for the real and imaginary parts of the final answer to be separable
    # other than that, any permutation of factors leads to an equally valid, distinct expression
    facts = factorize(rnum // 2) + [2]
    # multiplicative cycle of some primitive root, mod n
    power_cycle = make_power_cycle(rnum)
    # n_terms: number of a-sums on each iteration (see below)
    n_terms = 1
    # all_a: list of all lists of a-sums (see below for what an a-sum is) from each loop iteration
    # all_a_x: expressions for all a-sums
    all_a = []
    all_a_x = []

    for i, c_size in enumerate(facts):
        # calculates:
        # - p_1 sums of (n - 1)/p_1 roots
        # - p_1*p_2 sums of (n - 1)/(p_1*p_2) roots
        # - p_1*p_2*p_3 sums of (n - 1)/(p_1*p_2*p_3) roots
        # etc, where a, b, c... are prime factors of n - 1
        # let p_k = c_size be the prime factor of n - 1 considered on the kth iteration
        n_terms *= c_size

        # a: list of sums of (n - 1)/(p_1*...*p_k) roots (hereafter called a-sums) stored as lists
        #   these sums can be grouped into (n - 1)/(p_1*...*p_{k - 1}) sets of p_k
        # a_x: expressions for a-sums in a
        # s: for each set of p_k a-sums a_0 to a_{p_k - 1}, a list of p_k sums (stored as lists or matrices where appropriate), where the i-th sum s_i is equal to a_j*r(p_k, i*j), for j from 0 to p_k - 1
        #   s is simply a list of all p_k sums for all (n - 1)/(p_1*...*p_{k - 1}) sets of a-sums
        # s_x: expressions for s-sums in s
        # ss: contains each s-sum, except for the first value in a p_k-size set, raised to the power p_k, expressed as lists
        # ss_coeff: coefficients in expression, in terms of 1 and a-sum values from p_{k - 1} level, for each value in ss
        # ss_x: expressions for values in ss
        a = []
        a_x = []
        s = []
        ss = []
        ss_coeff = []
        s_x = []
        ss_x = []

        a_values = partition(rnum, power_cycle, n_terms)

        cyc = make_cycle(c_size)

        # iterate over each set of p_k terms
        for h in multi_range(tuple(facts[:i])):
            # construct a-sums
            part_ind = 0
            mult = 1
            for j in range(i):
                part_ind += mult * h[j]
                mult *= facts[j]
            for j in range(c_size):
                a.append(a_values[j * (n_terms // c_size) + part_ind])

            # construct s-sums and ss values
            offset = 0
            mult = c_size
            for j in range(i - 1, -1, -1):
                offset += mult * h[j]
                mult *= facts[j]
            s.append(sumlist(a[offset:offset + c_size], rnum))
            ss.append(None)
            for j in range(1, c_size):
                if c_size == 2:
                    s.append(plus(a[offset], itimes(-1, a[offset + 1], rnum), rnum))
                    ss.append(power(s[offset + 1], c_size, rnum))
                else:
                    s.append(msumlist([xtimes(cyc[j * k % c_size], a[offset + k], rnum) for k in range(c_size)], rnum))
                    ss.append(mpower(s[offset + j], c_size, rnum, [c_size - 1, product(facts[:(i + 1)])], [make_power_cycle(c_size)[1], power_cycle[1]]))

            # construct terms with which to describe each ss expression as well as the 0th s-sum in each set.
            # these terms are 1 and the a-sums from the previous iteration, whose radical expressions are already found
            if i > 0:
                terms = [1] + all_a[i - 1]
            else:
                terms = [1]
            # build s0_coeff and ss_coeff
            s0_coeff = deconvert(s[offset], terms, rnum)
            ss_coeff.append(None)
            if c_size == 2:
                ss_coeff.append(deconvert(ss[offset + 1], terms, rnum))
            else:
                for j in range(1, c_size):
                    ss_coeff.append(mdeconvert(ss[offset + j], terms, rnum))

            # retrieve the radical expression for each term used to construct s0_coeff and ss_coeff
            if i > 0:
                terms_x = [1] + all_a_x[i - 1]
            else:
                terms_x = [1]
            # build s0_x and ss_x
            # s0_x is the 0th s_x expression in each set but not the 0th member of s_x because s_x concatenates expression lists from every set on the p_k level
            s0_x = coeff_to_expr(s0_coeff, terms_x)
            ss_x.append(None)
            if c_size == 2:
                ss_x.append(coeff_to_expr(ss_coeff[offset + 1], terms_x))
            else:
                for j in range(1, c_size):
                    ss_x.append(mcoeff_to_expr(ss_coeff[offset + j], terms_x, roots_to_radicals(c_size)))

            s_x.append(s0_x)

            # build the other s_x expressions (the p_k-th roots of the ss_x expressions)
            for j in range(1, c_size):
                si_xs = [['r', c_size, k, ss_x[offset + j], 1] for k in range(c_size)]
                set = False
                for k in range(c_size):
                    if c_size == 2:
                        s_j_float = to_float(s[offset + j], rnum)
                    else:
                        s_j_float = mat_to_float(s[offset + j], rnum)
                    if float_equal(s_j_float, expr_to_float(si_xs[k])):
                        s_x.append(si_xs[k])
                        set = True
                        break
                if not set:
                    raise RuntimeError("Unable to resolve expression")

            # build the a_x expressions by adding the s_x expressions together and multiplying by the appropriate p_k-th roots of unity
            for j in range(c_size):
                a_x.append(etimes(esumlist(s_x[offset:offset + c_size]), (1, c_size)))
                for k in range(1, c_size):
                    s_x[offset + k] = rtimes(-k, s_x[offset + k])

        all_a.append(a)
        all_a_x.append(a_x)

    # on last iteration, a-sums are single roots of unity. bit_reverse() reorders these roots
    # x: list of expressions for all n-th roots of unity in order
    x = [1] + [None] * (rnum - 1)
    for i in range(len(a_x)):
        xind = power_cycle[bit_reverse(i, facts)]
        x[xind] = a_x[i]
        assert float_equal(expr_to_float(a_x[i]), r(rnum, xind))
    r_x[rnum] = x
    return x

if __name__ == '__main__':
    rnum = int(input("Enter a prime p to find the pth roots of unity: "))
    x = roots_to_radicals(rnum)
    # the lines we've all been waiting for...
    # (uncomment to display all roots of unity and not just one)
    '''for i in range(1, rnum):
        print(expr_to_latex(x[i]), '\\\\')'''
    print(expr_to_latex(x[1]))
    print(expr_length(x[1]))
    
