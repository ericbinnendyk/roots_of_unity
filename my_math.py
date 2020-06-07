from math import pi
from cmath import exp
from functools import reduce
tau = 2*pi
global be_quiet
be_quiet = False
global float_check
float_check = True

def lcm(x, y):
    return x*y//gcd(x, y)

def gcd(x, y):
    return gcd_abs(abs(x), abs(y))

# for the purposes of this module, gcd(0, 0) == 0
def gcd_abs(x, y):
    if x == 0:
        return y
    if y % x == 0:
        return x
    return gcd_abs(y % x, x)

def gcd_list(l):
    if len(l) == 1:
        return l[0]
    ans = l[0]
    for i in range(1, len(l)):
        ans = gcd(ans, l[i])
        if ans == 1:
            return ans
    return ans

# finds the largest exp-th power that is a divisor of num
def largest_power_divisor(num, exp):
    div = 1
    pow = 2 ** exp
    while num % pow == 0:
        num //= pow
        div *= 2
    pow = 3 ** exp
    while num % pow == 0:
        num //= pow
        div *= 3
    i = 1
    while True:
        base = 6 * i - 1
        pow = base ** exp
        if pow > num:
            break
        while num % pow == 0:
            num //= pow
            div *= base
        base = 6 * i + 1
        pow = base ** exp
        if pow > num:
            break
        while num % pow == 0:
            num //= pow
            div *= base
        i += 1
    return div

# determines whether two complex floating point values _probably_ represent the same number
def float_equal(f1, f2):
    if not float_check:
        return True
    err = abs(f2 - f1)/(max(abs(f1), abs(f2)) + 1)
    if not be_quiet:
        if err <= 1e-10:
            print("Warning: Two \"equal\" floating point numbers differ by percent error > 10^-12")
        elif err <= 1e-8:
            print("Warning: Two \"equal\" floating point numbers differ by percent error > 10^-10")
        elif err <= 1e-6:
            print("Warning: Two \"equal\" floating point numbers differ by percent error > 10^-8")
    if err <= 1e-6:
        return True
    return False

# returns the which-th degree-th root of unity, as float
def r(degree, which):
    return exp(tau*(which*1j/degree))

# finds the prime factors of a number
def factorize(num):
    if type(num) != int or num == 0:
        raise RuntimeError("Invalid argument to factorize(): {}".format(num))
    facts = []
    if num < 0:
        facts.append(-1)
        num = -num
    while num % 2 == 0:
        num //= 2
        facts.append(2)
    while num % 3 == 0:
        num //= 3
        facts.append(3)
    i = 1
    while True:
        if num == 1:
            break
        p = 6 * i - 1
        while num % p == 0:
            num //= p
            facts.append(p)
        if num == 1:
            break
        p = 6 * i + 1
        while num % p == 0:
            num //= p
            facts.append(p)
        i += 1
    return facts

# finds the prime-power decomposition of a number
def prime_powers(num):
    facts = factorize(num)
    decomp = []
    prev_fact = 1
    for fact in facts:
        if fact != prev_fact:
            decomp.append(fact)
        else:
            decomp[-1] *= fact
        prev_fact = fact
    return decomp

# product of all elements in a list
def product(l):
    if len(l) == 0:
        return 1
    return reduce((lambda x, y: x * y), l)

# to do: use faster algorithm
def is_prime(n):
    try:
        return n > 0 and len(factorize(n)) == 1
    except:
        # number cannot be factorized
        return False

# express n as rnum/p1*a + rnum/p2*b + ... (mod rnum) where p1, p2... are the distinct prime powers whose values are given in decomp with product rnum, and a, b... are integers
def prime_power_sum(n, decomp):
    if decomp == []:
        return []
    rnum = product(decomp)
    remainder = n
    fact = decomp[0]
    coeff = 0
    while remainder % fact != 0:
        coeff += 1
        remainder = (remainder - rnum // fact) % rnum
    return [coeff] + prime_power_sum(remainder // fact, decomp[1:])

def square_free(n):
    facts = factorize(n)
    return all([facts[i + 1] > facts[i] for i in range(len(facts) - 1)])
