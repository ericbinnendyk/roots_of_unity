from my_math import factorize, r, float_equal, gcd, gcd_list, prime_powers
from radical_expr import expr_to_float, etimes, eplus, rtimes, expr_to_latex, esumlist, copy, eprodlist
import sys

import my_math
my_math.be_quiet = True

# adds two root sums
def plus(m1, m2):
    if len(m1) != len(m2):
        raise RuntimeError("Cannot add matrices with inconsistent dimensions")
    nrow = len(m1)
    if type(m1[0]) == int:
        return [m1[i] + m2[i] for i in range(nrow)]
    return [plus(m1[i], m2[i]) for i in range(nrow)]

# sums a list of root sums
def sumlist(ml):
    if len(ml) == 0:
        raise RuntimeError("Cannot sum an empty list")
    if len(ml) == 1:
        return ml[0]
    else:
        return plus(sumlist(ml[:-1]), ml[-1])

'''def get_dims(m):
    dims = [len(m)]
    subm = m[0]
    while type(subm) != int:
        dims.append(len(subm))
        subm = subm[0]
    return dims'''

# multiplies two matrices
def times(m1, m2, dims):
    nrow = dims[0]
    assert nrow == len(m1) and nrow == len(m2)
    ans = new_mat(dims)
    for i in range(nrow):
        for j in range(nrow):
            k = (i + j) % nrow
            if len(dims) == 1:
                ans[k] += m1[i] * m2[j]
            else:
                ans[k] = plus(ans[k], times(m1[i], m2[j], dims[1:]))

    # rewrite so the first number is 0 (this does not change the intrinsic value and makes it easier to find common factors)
    if len(dims) == 1:
        ans = [ans[i] - ans[0] for i in range(nrow)]
    else:
        ans = [plus(ans[i], negate(ans[0])) for i in range(nrow)]

    return ans

def negate(m):
    if type(m[0]) == int:
        return [-m[i] for i in range(len(m))]
    else:
        return [negate(m[i]) for i in range(len(m))]

# takes root sum to integer power
# todo: redo this with memoization
def power(m, dims, n):
    assert type(n) == int and n > 0
    if n == 1:
        return m
    else:
        return times(power(m, dims, n - 1), m, dims)

# creates a list of roots of unity of specified degree, represented as lists
def make_cycle(num):
    cycle = []
    for i in range(num):
        root = [0] * num
        root[i] = 1
        cycle.append(root)
    return cycle

# creates a matrix of zeros with the specified number of rows and columns
def new_mat(dims):
    if len(dims) == 1:
        return [0] * dims[0]
    m = []
    for i in range(dims[0]):
        m.append(new_mat(dims[1:]))
    return m

# multiplies two sums of roots of unity of different degrees to obtain a matrix
def xtimes(col, m, dims):
    ans = new_mat([len(col)] + dims)
    for i in range(len(col)):
        if col[i] == 1:
            ans[i] = m
        else:
            assert col[i] == 0
    return ans

def mfactor(m, dims, fact):
    rnum = dims[0]
    if len(dims) == 1:
        return [m[i] // fact for i in range(rnum)]
    else:
        return [mfactor(m[i], dims[1:], fact) for i in range(rnum)]

def flatten(m, dims):
    if len(dims) == 1:
        return m
    else:
        rnum = dims[0]
        ans = []
        for i in range(rnum):
            ans.extend(flatten(m[i], dims[1:]))
        return ans

# converts a matrix to a float
def to_float(m, dims):
    nrow = dims[0]
    if len(dims) == 1:
        return sum([m[i] * r(nrow, i) for i in range(nrow)])
    return sum([to_float(m[i], dims[1:]) * r(nrow, i) for i in range(nrow)])

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

def remove_second_dim(a0, dims):
    for i in range(dims[0]):
        if len(dims) == 2:
            a0[i] = a0[i][0] - a0[i][1]
        else:
            a0[i] = plus(a0[i][0], negate(a0[i][1]))
    return a0

def rconj(m, dims, x):
    nrow = dims[0]
    m_conj = new_mat(dims)
    for i in range(nrow):
        k = (i * x) % nrow
        if len(dims) == 1:
            m_conj[k] += m[i]
        else:
            m_conj[k] = plus(m_conj[k], m[i])

    return m_conj

def root_to_radicals(rnum, n):
    # simplify the fraction n/rnum in the calculation e^(n/rnum*tau*i)
    div = gcd(rnum, n)
    rnum //= div
    n //= div

    facts = factorize(rnum)
    if len(facts) == 1:
        # rnum is prime
        l = [0] * rnum
        l[n] = 1
        return root_sum(l, [rnum], [rnum - 1])
    elif facts == [facts[0]] * len(facts):
        # rnum is prime power, p^x
        x = len(facts)
        p = facts[0]
        if p == 2:
            if x == 2:
                # rnum == 4
                if n == 1:
                    return ['r', 2, 0, -1, 1]
                if n == 3:
                    return ['r', 2, 1, -1, 1]
            else:
                twice_real = 0
                for i in range(2, x):
                    n_mod = n % p**(i + 1)
                    if p**(i - 1) < n_mod < 3*p**(i - 1):
                        which = 1
                    else:
                        which = 0
                    # this is the expression for 2*cos(n / p^(i + 1) * tau)
                    twice_real = ['r', 2, which, eplus(2, twice_real), 1]
                twice_imag = copy(twice_real)
                twice_imag[3] = eplus(-4, twice_imag[3])
                if 0 < n < p**i:
                    which = 0
                else:
                    which = 1
                twice_imag[2] = which
                # twice_imag is now 2i*sin(n / p^x * tau)
                return (eplus(twice_real, twice_imag), 2)
        else:
            # find expression for pth root, and take the pth root x - 1 times
            n_mod = n % p
            l = [0] * p
            l[n_mod] = 1
            ans = root_sum(l, [p], [p - 1])
            for i in range(1, x):
                which = ((n + p**i // 2) % p**(i + 1)) // p**i
                ans = ['r', p, which, ans, 1]
            return ans
    else:
        decomp = prime_powers(rnum)
        remainder = n
        rest = rnum
        coeffs = []
        for fact in decomp:
            coeff = 0
            while remainder % fact != 0:
                coeff += 1
                remainder = (remainder - rest // fact) % rest
            coeffs.append(coeff)
            remainder //= fact
            rest //= fact
        # for coeff in coeffs:
        #    print(coeff)
        return eprodlist([root_to_radicals(decomp[i], coeffs[i]) for i in range(len(decomp))])

def root_sum(a0, dims, degrees):
    if len(dims) > 1 and degrees[1] == 1:
        return root_sum(remove_second_dim(a0, dims), [dims[0]] + dims[2:], [degrees[0]] + degrees[2:])

    # assert len(a0) == dims[0]
    # assert dims[i] % syms[i] == 0 for i in range(len(syms))

    rnum = dims[0]
    d = degrees[0]
    power_cycle = make_power_cycle(rnum)

    if d == 1:
        if len(dims) == 1:
            return a0[0] - a0[1]
        else:
            return root_sum(plus(a0[0], negate(a0[1])), dims[1:], degrees[1:])

    if d == rnum - 1:
        fact = 2
    else:
        facts = factorize(d)
        fact = facts[-1]

    if fact == 2:
        a1 = rconj(a0, dims, power_cycle[d // fact])
        s0 = plus(a0, a1)
        #print("s0 ==", s0)
        s0_x = root_sum(s0, dims, [d // fact] + degrees[1:])
        s1 = plus(a0, negate(a1))
        #print("s1 ==", s1)
        mult = gcd_list(flatten(s1, dims))
        #print("mult ==", mult)
        if mult == 0:
            # s1 is matrix of zeros
            s1_x = 0
        else:
            s1_div = mfactor(s1, dims, mult)
            #print("s1_div ==", s1_div)
            s1s = power(s1_div, dims, fact)
            #print("s1s ==", s1s)
            s1s_x = root_sum(s1s, dims, [d // fact] + degrees[1:])
            s1_x = ['r', fact, 0, s1s_x, mult]
            s1_float = to_float(s1, dims)
            for i in range(fact):
                if float_equal(s1_float, expr_to_float(s1_x)):
                    break
                s1_x = rtimes(1, s1_x)
            if not float_equal(s1_float, expr_to_float(s1_x)):
                raise RuntimeError("Unable to resolve expression")
        a0_x = etimes(eplus(s0_x, s1_x), (1, fact))
        #print(expr_to_latex(a0_x))
        return a0_x
    else:
        a = []
        for i in range(fact):
            a.append(rconj(a0, dims, power_cycle[d // fact * i]))
        #print("a ==", a)
        s = []
        ss = []
        s.append(sumlist(a))
        ss.append(None)
        cyc = make_cycle(fact)
        for i in range(1, fact):
            s.append(sumlist([xtimes(cyc[i * j % fact], a[j], dims) for j in range(fact)]))
        #print("s ==", s)
        mult = gcd_list(flatten(s[1], [fact] + dims))
        for i in range(1, fact):
            s_i_div = mfactor(s[i], [fact] + dims, mult)
            ss.append(power(s_i_div, [fact] + dims, fact))
        s_x = []
        s_x.append(root_sum(s[0], dims, [d // fact] + degrees[1:]))
        ss_x = []
        ss_x.append(None)
        for i in range(1, fact):
            ss_x.append(root_sum(ss[i], [fact] + dims, [fact - 1] + [d // fact] + degrees[1:]))
            s_i_x = ['r', fact, 0, ss_x[-1], mult]
            s_i_float = to_float(s[i], [fact] + dims)
            expr_found = False
            for j in range(fact):
                if float_equal(s_i_float, expr_to_float(s_i_x)):
                    expr_found = True
                    break
                s_i_x = rtimes(1, s_i_x)
            if not expr_found:
                raise RuntimeError("Unable to resolve expression")
            s_x.append(s_i_x)
        a0_x = etimes(esumlist(s_x), (1, fact))
        #print(expr_to_latex(a0_x))
        return a0_x

if __name__ == '__main__':
    if len(sys.argv) >= 2:
        rnum = int(sys.argv[1])
    else:
        raise RuntimeError("No input value")
    if len(sys.argv) >= 3:
        which = int(sys.argv[2])
        if which < 0 or which >= rnum:
            raise RuntimeError("Second argument must be between 0 and first argument minus one")
    else:
        which = 1

    multiple_roots = len(sys.argv) >= 4

    if multiple_roots:
        num_roots = int(sys.argv[3])
        # rnum must be prime for this to work
        if len(factorize(rnum)) != 1:
            raise RuntimeError("Degree of root must be prime to define root sum")
        if (rnum - 1) % num_roots != 0:
            raise RuntimeError("Number of roots in sum must be factor of degree minus one")
        gap_size = (rnum - 1) // num_roots
        power_cycle = make_power_cycle(rnum)
        i = power_cycle.index(which)
        l = [0] * rnum
        for j in range(num_roots):
            l[power_cycle[i]] += 1
            i = (i + gap_size) % (rnum - 1)
        result = root_sum(l, [rnum], [(rnum - 1) // num_roots])
    else:
        result = root_to_radicals(rnum, which)

    print(expr_to_latex(result))
