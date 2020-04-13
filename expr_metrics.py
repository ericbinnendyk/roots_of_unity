from radical_expr import is_radical, is_sum
import my_math
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

if __name__ == '__main__':
    from my_math import factorize
    from refined_nth_roots import root_to_radicals
    for rnum in range(2, 50):
        if len(factorize(rnum)) == 1:
            result = root_to_radicals(61, 1)
            print("{}\t{}".format(rnum, expr_length(result)))
