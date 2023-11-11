from my_math import factorize, r, float_equal, gcd, gcd_list, prime_powers, is_prime, prime_power_sum, square_free
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
    ans = new_multisum(dims)
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
def new_multisum(dims):
    if len(dims) == 1:
        return [0] * dims[0]
    m = []
    for i in range(dims[0]):
        m.append(new_multisum(dims[1:]))
    return m

def mat_index_set(m, location, value):
    param1 = location[0]
    if type(m[param1]) == int:
        m[param1] = value
    else:
        mat_index_set(m[param1], location[1:], value)

# multiplies two sums of roots of unity of different degrees to obtain a matrix
def xtimes(col, m, dims):
    ans = new_multisum([len(col)] + dims)
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
    m_conj = new_multisum(dims)
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
    if len(facts) == 0:
        return 1
    if len(facts) == 1:
        # rnum is prime
        l = [0] * rnum
        l[n] = 1
        return multisum_to_radicals(l, [rnum], [rnum - 1])
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
            ans = multisum_to_radicals(l, [p], [p - 1])
            for i in range(1, x):
                which = ((n + p**i // 2) % p**(i + 1)) // p**i
                ans = ['r', p, which, ans, 1]
            return ans
    else:
        # rnum has multiple distinct prime factors
        # we express n as rnum/p1*a + rnum/p2*b + ... (mod rnum) where p1, p2... are factors in the prime power decomposition of rnum and a, b... are integers
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

def multisum_to_radicals(A, dims, degrees):
    print(A)
    if len(dims) > 1 and degrees[1] == 1:
        return multisum_to_radicals(remove_second_dim(A, dims), [dims[0]] + dims[2:], [degrees[0]] + degrees[2:])

    # assert len(A) == dims[0]
    # assert dims[i] % syms[i] == 0 for i in range(len(syms))

    p = dims[0]
    d = degrees[0]
    power_cycle = make_power_cycle(p)

    if d == 1:
        if len(dims) == 1:
            return A[0] - A[1]
        else:
            return multisum_to_radicals(plus(A[0], negate(A[1])), dims[1:], degrees[1:])

    if d == p - 1:
        c = 2
    else:
        facts = factorize(d)
        c = facts[-1]

    A_conj = []
    for i in range(c):
        A_conj.append(rconj(A, dims, power_cycle[d // c * i]))

    S_0_dims = dims[:]
    S_j_dims = dims[:]
    if c != 2:
        S_j_dims.insert(0, c)
    S_0_degrees = degrees[:]
    S_0_degrees[0] = d // c
    S_j_power_c_degrees = S_0_degrees[:]
    if c != 2:
        S_j_power_c_degrees.insert(0, c - 1)

    S = []
    S.append(sumlist(A_conj))
    if c == 2:
        S.append(plus(A_conj[0], negate(A_conj[1])))
    else:
        cyc = make_cycle(c)
        for i in range(1, c):
            S.append(sumlist([xtimes(cyc[i * j % c], A_conj[j], dims) for j in range(c)]))

    S_x = []
    S_x.append(multisum_to_radicals(S[0], dims, S_0_degrees))
    for j in range(1, c):
        divisor = gcd_list(flatten(S[j], S_j_dims))
        if divisor == 0:
            S_x.append(0)
        else:
            S_j_div = mfactor(S[j], S_j_dims, divisor)
            S_j_div_power_c = power(S_j_div, S_j_dims, c)
            S_j_div_power_c_x = multisum_to_radicals(S_j_div_power_c, S_j_dims, S_j_power_c_degrees)
            S_x.append(['r', c, 0, S_j_div_power_c_x, divisor])
            
            S_j_float = to_float(S[j], S_j_dims)
            expr_found = False
            for k in range(c):
                if float_equal(S_j_float, expr_to_float(S_x[j])):
                    expr_found = True
                    break
                S_x[j] = rtimes(1, S_x[j])
            if not expr_found:
                raise RuntimeError("Unable to resolve expression")
    A_x = etimes(esumlist(S_x), (1, c))
    return A_x

def cosine_in_radicals(num, denom):
    # canonize numerator and denominator
    div = gcd(num, denom)
    num //= div
    denom //= div
    num = num % denom
    facts = []
    if denom == 1:
        return 1
    if is_prime(denom):
        if denom == 2:
            return -1
        l = [0] * denom
        l[num] = 1
        l[denom - num] = 1
        return etimes(multisum_to_radicals(l, [denom], [(denom - 1) // 2]), (1, 2))
    else:
        facts = factorize(denom)

    # if the denominator is a prime power...
    if facts == [facts[0]] * len(facts):
        x = len(facts)
        p = facts[0]
        # if the denominator is a power of 2...
        # use the fact that 2*cos(n/2^(k + 1) * tau) = +/-sqrt(2 + 2*cos(n/2^k * tau))
        if facts[0] == 2:
            twice_real = 0 # = 2*cos(1/4 * tau) = 2*cos(3/4 * tau)
            for i in range(2, x):
                num_mod = num % p**(i + 1)
                if p**(i - 1) < num_mod < 3*p**(i - 1):
                    which = 1
                else:
                    which = 0
                # this is the expression for 2*cos(n / p^(i + 1) * tau)
                twice_real = ['r', 2, which, eplus(2, twice_real), 1]
            # to do: use etimes after you fix behavior of etimes
            if x == 2:
                return etimes(twice_real, (1, 2))
            return (twice_real, 2)
        # if the denominator is a power of any other prime, just sum two roots of unity and divide by two.
        else:
            # find expression for pth root of unity and complex conjugate, and take the pth root x - 1 times
            n_mod = num % p
            l1 = [0] * p
            l1[n_mod] = 1
            anti_n_mod = (p - num) % p
            l2 = [0] * p
            l2[anti_n_mod] = 1
            root1 = multisum_to_radicals(l1, [p], [p - 1]) # expression for a pth root of unity
            root2 = multisum_to_radicals(l2, [p], [p - 1]) # expression for the complex conjugate pth root of unity
            for i in range(1, x):
                which1 = ((num + p**i // 2) % p**(i + 1)) // p**i
                which2 = (p - which1) % p
                root1 = ['r', p, which1, root1, 1]
                root2 = ['r', p, which2, root2, 1]
            return (eplus(root1, root2), 2)
    # otherwise, the denominator has more than one distinct prime factor.
    # construct value as sum of two roots of unity, where each root is calculated as a product of p_k^x-th roots for each prime power p_k^x in decomposition of denom
    else:
        # to do: make prime powers list from facts instead
        decomp = prime_powers(denom)
        coeffs = prime_power_sum(num, decomp)
        anticoeffs = [decomp[i] - coeffs[i] for i in range(len(coeffs))]
        # if denom is squarefree, each prime factor is distinct and so we have a multisum of two roots of unity with dimensions of each of the prime factors
        # we solve this multisum using multisum_to_radicals
        if square_free(denom):
            if decomp[0] == 2:
                decomp = decomp[1:]
                l = new_multisum(decomp)
                mat_index_set(l, coeffs[1:], -1)
                mat_index_set(l, anticoeffs[1:], -1)
            else:
                l = new_multisum(decomp)
                mat_index_set(l, coeffs, 1)
                mat_index_set(l, anticoeffs, 1)
            if len(decomp) == 1:
                return etimes(multisum_to_radicals(l, decomp, [(decomp[0] - 1) // 2]), (1, 2))
            else:
                return etimes(multisum_to_radicals(l, decomp, [q - 1 for q in decomp]), (1, 2))
        # otherwise we just find radical expressions for each prime-power root individually and take the product using eprodlist
        else:
            root1 = eprodlist([root_to_radicals(decomp[i], coeffs[i]) for i in range(len(decomp))])
            root2 = eprodlist([root_to_radicals(decomp[i], anticoeffs[i]) for i in range(len(decomp))])
            return etimes(eplus(root1, root2), (1, 2))

def sine_in_radicals(num, denom):
    if denom % 4 != 0:
        denom *= 2
        num *= 2
        if denom % 4 != 0:
            denom *= 2
            num *= 2
    num -= denom // 4
    return cosine_in_radicals(num, denom)

if __name__ == '__main__':
    trig_options = ['sin', 'cos']
    if len(sys.argv) >= 2 and sys.argv[1] == '-t':
        if len(sys.argv) < 4:
            raise RuntimeError("-t option needs two parameters.")
        (num, denom) = map(int, sys.argv[3].split('/'))
        if sys.argv[2] not in trig_options:
            raise RuntimeError("{} is not a valid trig function.".format(sys.argv[2]))
        if sys.argv[2] == 'cos':
            expr = cosine_in_radicals(num, denom)
            print(expr_to_latex(expr))
        elif sys.argv[2] == 'sin':
            expr = sine_in_radicals(num, denom)
            print(expr_to_latex(expr))
        exit()

    if sys.argv[1] == '-h':
        print("python3 refined_nth_roots.py n")
        print("Calculates a radical expression for e^(2*pi*i/n), the first nth root of unity.")
        print("python3 refined_nth_roots.py n k")
        print("Calculates a radical expression for e^(2*k*pi*i/n), the kth nth root of unity.")
        print("python3 refined_nth_roots.py n k d")
        print("Calculates a radical expression for a sum of (n - 1)/d roots of unity starting at e^(2*k*pi*i/n) and making a power cycle. The value is the root of a degree-d polynomial.")
        print("python3 refined_nth_roots.py -t FUNC p/q")
        print("Calculates a radical expression for the value FUNC(2*pi*p/q), where FUNC is one of the following: {}".format(trig_options))

    if len(sys.argv) >= 2:
        rnum = int(sys.argv[1])
    else:
        raise RuntimeError("No input value")
    if len(sys.argv) >= 3:
        try:
            which = int(sys.argv[2])
        except:
            which = 1
        which = which % rnum
    else:
        which = 1

    if len(sys.argv) >= 4:
        degree = int(sys.argv[3])
        # rnum must be prime for this to work
        if len(factorize(rnum)) != 1:
            raise RuntimeError("Degree of root must be prime to define root sum")
        if (rnum - 1) % degree != 0:
            raise RuntimeError("Degree of sum must be factor of degree minus one")
        power_cycle = make_power_cycle(rnum)
        i = power_cycle.index(which)
        l = [0] * rnum
        for j in range((rnum - 1) // degree):
            l[power_cycle[i]] += 1
            i = (i + degree) % (rnum - 1)
        result = multisum_to_radicals(l, [rnum], [degree])
    else:
        result = root_to_radicals(rnum, which)

    print(expr_to_latex(result))
