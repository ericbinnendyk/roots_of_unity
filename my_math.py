from math import pi
from cmath import exp
tau = 2*pi

def lcm(x, y):
    return x*y//gcd(x, y)

def gcd(x, y):
    return gcd_abs(abs(x), abs(y))

def gcd_abs(x, y):
    if y % x == 0:
        return x
    return gcd(y % x, x)

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
    err = abs(f2 - f1)/(max(abs(f1), abs(f2)) + 1)
    if err <= 1e-12:
        return True
    elif err <= 1e-10:
        print("Warning: Two \"equal\" floating point numbers differ by percent error > 10^-12")
        return True
    elif err <= 1e-8:
        print("Warning: Two \"equal\" floating point numbers differ by percent error > 10^-10")
        return True
    elif err <= 1e-6:
        print("Warning: Two \"equal\" floating point numbers differ by percent error > 10^-8")
        return True
    return False

# returns the which-th degree-th root of unity, as float
def r(degree, which):
    return exp(tau*(which*1j/degree))

# finds the prime factors of a number
def factorize(num):
    facts = []
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
