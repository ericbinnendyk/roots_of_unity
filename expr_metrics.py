from radical_expr import is_radical, is_sum
import my_math
from my_math import product, factorize
my_math.be_quiet = True

def expr_length(expr):
    if type(expr) == int:
        return 1
    if type(expr) == tuple:
        return expr_length(expr[0])
    if is_radical(expr):
        return expr_length(expr[3])
    if is_sum(expr):
        return sum([expr_length(sub_expr) for sub_expr in expr[1:]])
    raise RuntimeError("Not implemented yet. expr_length({})".format(expr))

def multisum_length(degrees):
    return product([sum_length(degree) for degree in degrees])

def sum_length(degree):
    if degree == 1:
        return 1
    if degree in lengths:
        return lengths[degree]
    if degree in fact_table:
        facts = fact_table[degree]
    else:
        facts = factorize(degree)
        fact_table[degree] = facts
    c = facts[0]
    if degree // c not in fact_table:
        fact_table[degree // c] = facts[1:]
    length = (1 + sum_length(c - 1)*(c - 1))*sum_length(degree // c)
    lengths[degree] = length
    return length

def root_expr_length(rnum):
    if len(factorize(rnum)) == 1:
        return sum_length(rnum - 1)
    else:
        raise RuntimeError("Input must be prime.")

lengths = {}
fact_table = {}

if __name__ == '__main__':
    from my_math import factorize
    from refined_nth_roots import root_to_radicals
    for rnum in range(2, 50):
        if len(factorize(rnum)) == 1:
            result = root_to_radicals(61, 1)
            print("{}\t{}".format(rnum, expr_length(result)))
