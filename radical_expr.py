from my_math import gcd, lcm, largest_power_divisor, float_equal, r

# types of radical expression:
# -integer (just an integer)
# -fraction (tuple of numerator, denominator)
#   numerator can be any expression except a fraction
#   denominator is positive integer
# -sum (list of terms to be summed, starting with '+')
#   each term can be anything but a sum or a fraction
#   if two terms can be summed into a non-sum term, they should be
# -radical (list of ['r', degree, which, radicand, mult])
#   degree is a prime number
#   which is a non-negative integer less than degree
#   mult is a positive integer
#   radicand can be any expression, including another radical
#   represents the value mult*(radicand^(1 / degree)). _which_ determines which of the possible choices of the degree-th root to choose

def is_sum(expr):
    return type(expr) == list and expr[0] == '+'

def is_radical(expr):
    return type(expr) == list and expr[0] == 'r'

# copies an expression so that it can be altered independently of the original
def copy(expr):
    if type(expr) != list:
        print("Warning: trying to copy a non-list expression")
        return expr
    expr2 = expr[:]
    for i in range(len(expr2)):
        if type(expr2[i]) == list:
            expr2[i] = copy(expr2[i])
    return expr2

# multiplies an nth degree radical expression by one of the nth roots of unity
def rtimes(which, expr):
    if type(expr) != list or expr[0] != 'r':
        raise RuntimeError("Cannot call rtimes on non-radical expression")
    ans = copy(expr)
    degree = expr[1]
    ans[2] = (expr[2] + which) % degree
    return ans

# sums a list of expressions
def esumlist(el):
    if len(el) == 0:
        raise RuntimeError("Cannot sum an empty list")
    if len(el) == 1:
        return el[0]
    else:
        return eplus(esumlist(el[:-1]), el[-1])

# adds two expressions
def eplus(e1, e2):
    if type(e1) == int:
        if e1 == 0:
            return e2
    if type(e2) == int:
        if e2 == 0:
            return e1

    if type(e1) == int:
        if type(e2) == tuple:
            assert(type(e2[1]) == int)
            assert(type(e2[0]) != tuple)
            ans = (eplus(e1 * e2[1], e2[0]), e2[1])
            return ans
            # simplify fraction -- find gcd of term multipliers
            # need two more functions: term_mult and l_gcd
            # but not yet
            # also implement this for symmetric case
            '''multlist = [ans[1]]
            if type(ans[0]) == int or type(ans[0]) == list and ans[0][0] == 'r':
                multlist.append(term_mult(ans[0]))
            elif type(ans[0]) == list and ans[0][0] == '+':
                for term in ans[0][1:]:
                    multlist.append(term_mult(term))
            else:
                raise RuntimeError("Trying to multiply expression of unknown type")
            div = l_gcd(multlist)'''
        if is_sum(e2):
            ans = copy(e2)
            ans_terms = ans[1:]
            for i, term in enumerate(ans_terms):
                if type(term) == int:
                    ans_terms[i] += e1
                    return ['+'] + ans_terms
            ans_terms = [e1] + ans_terms
            return ['+'] + ans_terms
        if is_radical(e2):
            return eplus(['+', e1], ['+', e2])
    if type(e1) == tuple:
        if type(e2) == int:
            assert(type(e1[1]) == int)
            assert(type(e1[0]) != tuple)
            ans = (eplus(e2 * e1[1], e1[0]), e1[1])
            return ans
        if type(e2) == tuple:
            denom = lcm(e1[1], e2[1])
            e1m = denom//e1[1]
            e2m = denom//e2[1]
            ans = (eplus(etimes(e1m, e1[0]), etimes(e2m, e2[0])), denom)
            ans = esimplify(ans)
            return ans
        if is_sum(e2):
            return eplus(e1, (e2, 1))            
        if is_radical(e2):
            return eplus(e1, (e2, 1))
    if is_sum(e1):
        if type(e2) == int:
            return eplus(e2, e1)
        if type(e2) == tuple:
            return eplus((e1, 1), e2)
        if is_sum(e2):
            # initialize answer to e1 terms
            ans_terms = copy(e1[1:])
            # for each term in e2...
            for i in range(len(e2) - 1):
                # ...add term to answer
                # if term is integer...
                if type(e2[i + 1]) == int:
                    # ...detect if there is an integer term in working answer
                    # if there is, add it
                    # if not, append term to end
                    match_found = False
                    for j in range(len(ans_terms)):
                        if type(ans_terms[j]) == int:
                            ans_terms[j] += e2[i + 1]
                            match_found = True
                            break
                    if not match_found:
                        ans_terms.append(e2[i + 1])
                # else if term is radical...
                elif is_radical(e2[i + 1]):
                    # ...look for a matching radical (same in everything but multiplier) in working answer
                    match_found = False
                    for j in range(len(ans_terms)):
                        if is_radical(ans_terms[j]):
                            if radicals_equal(e2[i + 1], ans_terms[j]):
                                ans_terms[j][4] += e2[i + 1][4]
                                match_found = True
                                break
                    if not match_found:
                        ans_terms.append(copy(e2[i + 1]))
                elif type(e2[i + 1]) == tuple:
                    raise RuntimeError("Fraction inside of sum - find common denominator to fix")
                else:
                    raise RuntimeError("Sum or unknown term inside of sum")

            # remove any 0 terms from answer
            ans_terms = [term for term in ans_terms if not (type(term) == int and term == 0)]

            # remove radicals with zero multiplicity
            ans_terms = [term for term in ans_terms if not (is_radical(term) and term[4] == 0)]

            # remove cycles of radicals that cancel each other out
            radical_table = []
            # radical_table: a table (pseudo-dictionary) of radicals appearing in ans_terms, arranged by degree and radicand
            # key: tuple of (degree, radicand)
            # value: list of tuples. each index corresponds to a conjugate root
            # each tuple contains:
            #   0. multiplier appearing on conjugate root in ans_terms, or 0 if root does not appear
            #   1. index of conjugate root in ans_terms, or -1 if root does not appear (error if root is detected more than once)
            for i, term in enumerate(ans_terms):
                if is_radical(term):
                    if term[4] < 0:
                        raise RuntimeError("Negative multipliers on radicals no longer supported - try replacing radical by sum of conjugates or negating radicand if odd degree")
                    key = (term[1], term[3])
                    keys = [x[0] for x in radical_table]
                    if key in keys:
                        kind = keys.index(key)
                        if radical_table[kind][1][term[2]] != (0, -1):
                            raise RuntimeError("Same radical appears more than once in expression")
                        radical_table[kind][1][term[2]] = (term[4], i)
                    else:
                        value = [(0, -1)] * term[1]
                        value[term[2]] = (term[4], i)
                        radical_table.append((key, value))
            for (key, value) in radical_table:
                mults = [x[0] for x in value]
                inds = [x[1] for x in value]
                minmult = min(mults)
                if minmult > 0:
                    for i in inds:
                        # if we get here then all the radicals in the cycle have appeared with positive multipliers in expression
                        # that means that none of the corresponding indices should be -1
                        assert(i != -1)
                        ans_terms[i][4] -= minmult
            ans_terms = [term for term in ans_terms if not (is_radical(term) and term[4] == 0)]
            # todo: sort terms in answer (for uniqueness)

            if len(ans_terms) == 0:
                return 0
            if len(ans_terms) == 1:
                return ans_terms[0]
            ans = ['+'] + ans_terms
            return ans
        if is_radical(e2):
            return eplus(e1, ['+', e2])
    if is_radical(e1):
        if type(e2) == int:
            return eplus(['+', e1], ['+', e2])
        if type(e2) == tuple:
            return eplus((e1, 1), e2)
        if is_sum(e2):
            return eplus(['+', e1], e2)
        if is_radical(e2):
            return eplus(['+', e1], ['+', e2])

    raise RuntimeError("Not implemented yet. eplus({}, {})".format(e1, e2))

# multiplies two expressions
def etimes(e1, e2):
    if type(e1) == int:
        if e1 == 0:
            return 0
        elif e1 == 1:
            return e2
    if type(e2) == int:
        if e2 == 0:
            return 0
        elif e2 == 1:
            return e1

    if type(e1) == int:
        if type(e2) == int:
            return e1 * e2
        if type(e2) == tuple:
            div = gcd(e1, e2[1])
            mult = e1 // div
            ans = (etimes(mult, e2[0]), e2[1] // div)
            if ans[1] == 1:
                return ans[0]
            else:
                return ans
        if is_sum(e2):
            terms = e2[1:]
            ans_terms = [etimes(e1, term) for term in terms]
            ans = ['+'] + ans_terms
            ans = remove_nested_sums(ans)
            return ans
        if is_radical(e2):
            if e1 >= 0:
                # this whole if statement should be commented out for the 23rd roots of unity
                if type(e2[3]) == tuple:
                    if gcd(e1, e2[3][1]) > 1:
                        degree = e2[1]
                        which = e2[2]
                        radicand = e2[3]
                        rad_mult = e2[4]
                        mult = e1 ** degree
                        div = gcd(mult, radicand[1])
                        num = etimes(mult, radicand[0])
                        effective_num = mult // div
                        lpd = largest_power_divisor(effective_num, degree)
                        num = edivout(num, lpd ** degree)
                        radicand = esimplify((num, radicand[1]))
                        rad_mult *= lpd
                        return ['r', degree, which, radicand, rad_mult]
                ans = copy(e2)
                ans[4] *= e1
                return ans
            else:
                degree = e2[1]
                ans = copy(e2)
                if degree == 2:
                    ans[2] = (ans[2] + 1) % 2
                    return etimes(-e1, ans)
                else:
                    ans[3] = etimes(-1, ans[3])
                    # make sure the right nth root is picked
                    root_found = False
                    for i in range(degree):
                        if not float_equal(-expr_to_float(e2), expr_to_float(ans)):
                            ans[2] = (ans[2] + 1) % degree
                        else:
                            root_found = True
                            break
                    if not root_found:
                        print("Warning: e1 * e2 == {} and ans^{} == {}, but cannot find right root to make -e2 == ans.".format(expr_to_float(e1) * expr_to_float(e2), degree, expr_to_float(ans[3])))
                    return etimes(-e1, ans)
                # I'm sure this code is all really nice but there's a way more convenient way to do it I just wasn't thinking of
                '''degree = e2[1]
                init_term = copy(e2)
                init_term[4] *= -e1
                ans_terms = [copy(init_term) for i in range(1, degree)]
                i = 1
                for term in ans_terms:
                    term[2] = (term[2] + i) % degree
                    i += 1
                if len(ans_terms) == 1:
                    return ans_terms[0]
                return ['+'] + ans_terms'''
    if type(e1) == tuple:
        if type(e2) == int:
            div = gcd(e2, e1[1])
            mult = e2 // div
            ans = (etimes(mult, e1[0]), e1[1] // div)
            if ans[1] == 1:
                return ans[0]
            else:
                return ans
        if type(e2) == tuple:
            ans = (etimes(e1[0], e2[0]), e1[1] * e2[1])
            ans = esimplify(ans)
            return ans
        if is_radical(e2):
            ans_num = etimes(e1[0], e2)
            ans = (ans_num, e1[1])
            ans = esimplify(ans)
            return ans
    if is_sum(e1):
        if type(e2) == int:
            terms = e1[1:]
            ans_terms = [etimes(term, e2) for term in terms]
            ans = ['+'] + ans_terms
            ans = remove_nested_sums(ans)
            return ans
        if type(e2) == tuple:
            ans_num = etimes(e1, e2[0])
            ans = (ans_num, e2[1])
            ans = esimplify(ans)
            return ans
        if is_sum(e2):
            terms = e1[1:]
            ans_terms = [etimes(term, e2) for term in terms]
            ans = esumlist(ans_terms)
            return ans
        if is_radical(e2):
            terms = e1[1:]
            ans_terms = [etimes(term, e2) for term in terms]
            ans = esumlist(ans_terms)
            return ans
    if is_radical(e1):
        if type(e2) == int:
            return etimes(e2, e1)
        if is_sum(e2):
            terms = e2[1:]
            ans_terms = [etimes(e1, term) for term in terms]
            ans = esumlist(ans_terms)
            return ans
        if is_radical(e2):
            if e1[1] == e2[1]:
                degree = e1[1]
                ans_radicand = etimes(e1[3], e2[3])
                ans = eroot(ans_radicand, degree)
                ans = etimes(ans, e1[4] * e2[4])
                '''if not float_equal(expr_to_float(e1) * expr_to_float(e2), expr_to_float(ans)):
                    print("Warning: e1 * e2 == {} while ans == {}. Maybe the wrong root was picked.".format(expr_to_float(e1) * expr_to_float(e2), expr_to_float(ans)))'''
                if is_radical(ans):
                    for i in range(degree):
                        ans[2] = i
                        if float_equal(expr_to_float(e1) * expr_to_float(e2), expr_to_float(ans)):
                            return ans
                    raise RuntimeError("Unable to resolve expression. etimes({}, {})".format(e1, e2))
                elif degree == 2:
                    if float_equal(expr_to_float(e1) * expr_to_float(e2), expr_to_float(ans)):
                        return ans
                    ans = etimes(ans, -1)
                    if float_equal(expr_to_float(e1) * expr_to_float(e2), expr_to_float(ans)):
                        return ans
                    raise RuntimeError("Unable to resolve expression. etimes({}, {})".format(e1, e2))
                else:
                    raise RuntimeError("Multiplication of two nth roots resulting in a rational value times nth root of unity is currently only implemented for n == 2")
            elif e1[1] > e2[1]:
                degree = e1[1]
                mult = e1[4]
                radicand = etimes(e1[3], epower(e2, degree))
                # to do: ans = eroot(radicand, degree) and multiply by mult
                ans = ['r', degree, 0, radicand, mult]
                for i in range(degree):
                    ans[2] = i
                    if float_equal(expr_to_float(e1) * expr_to_float(e2), expr_to_float(ans)):
                        return ans
                print("supposed value of ans: {}".format(ans))
                raise RuntimeError("Unable to resolve expression. etimes({}, {})".format(e1, e2))
            else:
                return etimes(e2, e1)

    raise RuntimeError("Not implemented yet. etimes({}, {})".format(e1, e2))

# takes the nth root of an expression (n should be prime)
# note: as the 0th choice of root is taken by default, the result should always be checked against the floating point expression it should equal and multiplied by the appropriate root of unity
def eroot(expr, n):
    if expr == 0:
        return 0
    fact = get_common_fact(expr)
    div = largest_power_divisor(fact, n)
    ans_radicand = edivout(expr, div ** n)
    if type(ans_radicand) == tuple:
        denom_div = largest_power_divisor(ans_radicand[1], n)
        if denom_div > 1:
            ans_radicand = (ans_radicand[0], ans_radicand[1] // (denom_div ** n))
            if ans_radicand == 1:
                ans_num = div
            else:
                ans_num = ['r', n, 0, ans_radicand, div]
            return (ans_num, denom_div)
    if ans_radicand == 1:
        ans = div
    else:
        ans = ['r', n, 0, ans_radicand, div]
    return ans

# takes expr to the nth power, paying attention to the case where expr is a radical
def epower(expr, n):
    if is_radical(expr):
        degree = expr[1]
        radicand = expr[3]
        mult = expr[4]
        innerexp = n - degree * (n // degree)
        outerexp = n // degree
        if outerexp > 0:
            if innerexp == 0:
                ans = 1
            else:
                ans = epower(expr, innerexp)
            ans = etimes(ans, epower(etimes(radicand, mult ** degree), outerexp))
            return ans
        else:
            radicand = epower(radicand, innerexp)
            ans = eroot(radicand, degree)
            ans[4] *= mult ** innerexp
            for i in range(degree):
                ans[2] = i
                if float_equal(expr_to_float(expr) ** innerexp, expr_to_float(ans)): 
                    return ans
            raise RuntimeError("Unable to resolve expression. epower({}, {})".format(expr, n))
    else:
        if n == 0:
            return 1
        else:
            return etimes(epower(expr, n - 1), expr)

# simplifies a fractional expression by reducing to lowest terms
# assumes all subexpressions have already been simplified
def esimplify(expr):
    if type(expr) != tuple:
        raise RuntimeError("Only fractions can be simplified with esimplify().")
    ans = None # this line indicates that the variable ans is used after the conditionals but only defined inside them.
    if type(expr[0]) == int:
        div = gcd(*expr)
        ans = (expr[0] // div, expr[1] // div)
    elif is_radical(expr[0]):
        div = gcd(expr[0][4], expr[1])
        expr[0][4] //= div
        ans = (expr[0], expr[1] // div)
    elif is_sum(expr[0]):
        div = get_common_fact(expr[0])
        div = gcd(div, expr[1])
        if div == 1:
            return expr
        ans_num = edivout(expr[0], div)
        ans_denom = expr[1] // div
        ans = (ans_num, ans_denom)
    if ans[1] == 1:
        return ans[0]
    else:
        return ans

# finds the common factor of the multipliers of all terms in a sum
def get_common_fact(expr):
    if is_sum(expr):
        sumlen = len(expr) - 1
        div = get_mult(expr[1])
        for i in range(1, sumlen):
            if div == 1:
                break
            div = gcd(div, get_mult(expr[i + 1]))
        return div
    elif is_radical(expr):
        return abs(expr[4])
    elif type(expr) == int:
        return abs(expr)
    elif type(expr) == tuple:
        return get_common_fact(expr[0])

# gets the multiplier on a radical, or an integer
def get_mult(expr):
    if type(expr) == int:
        return expr
    elif is_radical(expr):
        return expr[4]
    else:
        raise RuntimeError("Expression must be integer or radical")

# if terms in expr have multipliers all divisible by div, divides expr by div
def edivout(expr, div):
    if type(expr) == int:
        assert(expr % div == 0)
        return expr // div
    if is_radical(expr):
        assert(expr[4] % div == 0)
        expr[4] //= div
        return expr
    if is_sum(expr):
        sumlen = len(expr) - 1
        for i in range(sumlen):
            expr[i + 1] = edivout(expr[i + 1], div)
        return expr
    if type(expr) == tuple:
        divnum = edivout(expr[0], div)
        return (divnum, expr[1])

# removes problematic sums nested inside a sum
# note: does not remove nested sums in subexpressions
def remove_nested_sums(expr):
    if not is_sum(expr):
        raise RuntimeError("Can only remove nested sums from a sum")
    nested_sums_found = False
    for term in expr[1:]:
        if is_sum(term):
            nested_sums_found = True
            break
    if not nested_sums_found:
        return expr

    ans = ['+']
    for term in expr[1:]:
        if is_sum(term):
            for subterm in term[1:]:
                ans.append(subterm)
        else:
            ans.append(term)
    return ans

# determines whether two radicals can be added into a single radical, i.e., are equal in every aspect but multiplier
def radicals_equal(e1, e2):
    if not (is_radical(e1) and is_radical(e2)):
        raise RuntimeError("Trying to compare two non-radicals as radicals")
    return e1[1] == e2[1] and e1[2] == e2[2] and e1[3] == e2[3]

# converts expression to complex floating point value
def expr_to_float(expr):
    if type(expr) == int:
        return float(expr)
    if type(expr) == tuple:
        return expr_to_float(expr[0]) / expr_to_float(expr[1])
    if is_sum(expr):
        return sum([expr_to_float(part) for part in expr[1:]])
    if is_radical(expr):
        degree = expr[1]
        which = expr[2]
        radicand = expr[3]
        mult = expr[4]
        # make sure rounding errors don't affect the choice of nth root
        radicand_float = expr_to_float(radicand)
        if radicand_float.real < 0 and float_equal(radicand_float, radicand_float.real):
            radicand_float = radicand_float.real
        return mult * r(degree, which) * radicand_float**(1/degree)

# converts expression to LaTeX expression
def expr_to_latex(expr):
    if type(expr) == int:
        return str(expr)
    if type(expr) == tuple:
        return '\\frac{{{}}}{{{}}}'.format(expr_to_latex(expr[0]), expr_to_latex(expr[1]))
    if is_sum(expr):
        latex = ''
        num_terms = len(expr) - 1
        for i in range(num_terms):
            new_latex = expr_to_latex(expr[i + 1])
            if i > 0 and new_latex[0] != '-':
                latex += '+'
            latex += new_latex
        return latex
    if is_radical(expr):
        latex = ''
        degree = expr[1]
        which = expr[2]
        radicand = expr[3]
        mult = expr[4]
        latex = ''
        if degree == 2:
            if which == 1:
                latex += '-'
            if mult != 1:
                latex += str(mult) + ' '
            latex += '\\sqrt{{{}}}'.format(expr_to_latex(radicand))
        else:
            if mult != 1:
                latex += str(mult)
            if which != 0:
                latex += 'r_{}'.format(which)
            if mult != -1 or which != 0:
                latex += ' '
            latex += '\\sqrt[{}]{{{}}}'.format(degree, expr_to_latex(radicand))
        return latex
