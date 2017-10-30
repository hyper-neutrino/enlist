# Enlist by Alexander Liao
# Parts of this program are taken from Dennis's code for the Jelly programming language,
# in compliance to the MIT license and with his additionally expressed permission   

codepage  = """¡¢£¤¥¦©¬®µπ¿€ÆÇÐÑ×ØŒÞßæçðıȷñ÷øœþ !"#$%&'()*+,-./0123456789:;<=>?"""
codepage += """@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~¶"""
codepage += """°¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾±≤≠≥√·∆₱•†‡§⍺⍵ŝσ←↑→↓↔↕↙↘↶↷↻λẠḄḌẸḤỊḲḶṂṆỌṚṢṬỤṾẈỴẒȦḂ"""
codepage += """ĊḊĖḞĠḢİĿṀṄȮṖṘṠṪẆẊẎŻạḅḍẹḥịḳḷṃṇọṛṣṭụṿẉỵẓȧḃċḋėḟġḣŀṁṅȯṗṙṡṫẇẋẏż«»‘’“”"""

import re, math, operator, sympy, sys, locale, functools, itertools, random

pyrange = range

def range(*a):
    return list(map(sympy.Integer, pyrange(*a)))

def try_eval(string):
    number = "([0-9]+|[0-9]*\.[0-9]+)"
    if re.match("^({0}j|{0}(\s*\+\s*{0}j)?)$".format(number), string):
        return eval(re.sub(number, r"sympy.Rational('\1')", string.replace("j", "*sympy.I")))
    try:
        value = eval(string)
        if hasattr(value, "__iter__"): return list(value)
        return value
    except:
        return list(string)

def force_list(obj):
    if hasattr(obj, "__iter__"):
        return obj
    return [obj]

def range_list(obj):
    if hasattr(obj, "__iter__"):
        return obj
    return list(range(obj))

def digit_lister(function, base = 10):
    def inner(obj):
        if hasattr(obj, "__iter__"):
            return function(obj)
        else:
            return from_base(function(digits(obj, base)), base)
    return inner

def lfill(matrix, item):
    length = max(map(len, matrix))
    return [row + [item] * (length - len(row)) for row in matrix]

def rfill(matrix, item):
    length = max(map(len, matrix))
    return [[item] * (length - len(row)) + row for row in matrix]

def depth(obj):
    if hasattr(obj, "__iter__"):
        if len(obj) == 0: return 1
        return max(map(depth, obj)) + 1
    return 0

def last_input():
    return python_eval(sys.argv[-1] if len(sys.argv) > 3 else input())

def Operator(argnum):
    class Inner:
        def __init__(self, function):
            self.function = function
        def __call__(self, *args, **kwargs):
            if isinstance(args[0], tuple): return self.function(*args, **kwargs)
            return self.function((argnum, args[0]), *args[1:], **kwargs)
    return Inner

@Operator(2)
def reverse_args(function):
    return lambda x, y: dydeval(function, y, x)

def foreachleft(function):
    if function[0] == 0:
        return (1, lambda inp: [nileval(function) for val in range_list(inp)])
    elif function[0] == 1:
        return (1, lambda inp: [moneval(function, val) for val in range_list(inp)])
    elif function[0] == 2:
        return (2, lambda left, right: [dydeval(function, val, right) for val in range_list(left)])

def foreachright(function):
    if function[0] == 0:
        return (2, lambda left, right: [nileval(function) for val in range_list(right)])
    elif function[0] == 1:
        return (2, lambda left, right: [moneval(function, val) for val in range_list(right)])
    elif function[0] == 2:
        return (2, lambda left, right: [dydeval(function, left, val) for val in range_list(right)])

@Operator(1)
def vectorizeleft(function, maxlayers = -1, maxlayer_offset = 0):
    def inner(layers, *args):
        if layers == maxlayers or depth(args[0]) in [maxlayer_offset, 0]:
            return [nileval, moneval, dydeval][len(args)](function, *args)
        else:
            return [inner(layers + 1, *((element,) + args[1:])) for element in args[0]]
    return inner

def vecdyadleft(function, maxlayers = -1, maxlayer_offset = 0):
    inner = vectorizeleft(function, maxlayers, maxlayer_offset)
    return lambda left, right: inner(0, left, right)

def vecmonad(function, maxlayers = -1, maxlayer_offset = 0):
    inner = vectorizeleft(function, maxlayers, maxlayer_offset)
    return lambda argument: inner(0, argument)

@Operator(2)
def vecdyadright(function, maxlayers = -1, maxlayer_offset = 0):
    def inner(layers, left, right):
        if layers == maxlayers or depth(right) == maxlayer_offset or depth(right) == 0:
            return dydeval(function, left, right)
        else:
            return [inner(layers + 1, left, element) for element in right]
    return lambda left, right: inner(0, left, right)

@Operator(2)
def vecdyadboth(function, maxlayers = -1, maxlayer_offset = 0):
    def inner(layers, left, right):
        ldone = layers == maxlayers or depth(left) == maxlayer_offset
        rdone = layers == maxlayers or depth(right) == maxlayer_offset
        if ldone and rdone:
            return dydeval(function, left, right)
        elif ldone:
            return [inner(layers + 1, left, element) for element in right]
        elif rdone:
            return [inner(layers + 1, element, right) for element in left]
        else:
            return [inner(layers + 1, eleft, eright) for eleft, eright in zip(left, right)] + right[len(left):] + left[len(right):]
    return lambda left, right: inner(0, left, right)

register = 0

def registrar(function):
    def inner(*args):
        global register
        register = [nileval, moneval, dydeval][len(args)](function, *args)
        return register
    return inner

@Operator(2)
def reducer(function, block_size = (0, lambda: 0)):
    def inner(argument):
        argument = force_list(argument)
        size = nileval(block_size)
        if size == 0:
            return functools.reduce(lambda x, y: dydeval(function, x, y), argument)
        else:
            return [functools.reduce(lambda x, y: dydeval(function, x, y), argument[i : i + size]) for i in range(0, len(argument), size)]
    return (1, inner)

@Operator(2)
def oreduce(function, block_size = (0, lambda: 0)):
    def inner(argument):
        argument = force_list(argument)
        size = nileval(block_size)
        if size == 0:
            output = []
            while len(argument) > 1:
                output.append(dydeval(function, *argument[:2]))
                argument[:2] = output[-1:]
            return output + argument
        else:
            return [functools.reduce(lambda x, y: dydeval(function, x, y), argument[i : i + size]) for i in range(0, len(argument) - size)]
    return (1, inner)

@Operator(1)
def sorter(function):
    def inner(*args):
        return sorted(args[0], key = (lambda: nileval(function)) if function[0] == 0 else (lambda a: moneval(function, a)) if function[0] == 1 else (lambda a: dydeval(function, a, args[1])))
    return (max(1, function[0]), inner)

@Operator(2)
def uniquify(comparator):
    def inner(array):
        array = force_list(array)[:]
        values = []
        for element in array:
            for value in values:
                if dydeval(comparator, element, value):
                    break
            else:
                values.append(element)
        return values
    return inner

@Operator(1)
def keyuniquify(function):
    def inner(*args):
        array = force_list(args[0])[:]
        e = (lambda x: nileval(function)) if function[0] == 0 else (lambda x: moneval(function, x)) if function[0] == 1 else (lambda x: dydeval(function, x, args[1]))
        values = []
        for element in array:
            for value in values:
                if e(element) == e(value):
                    break
            else:
                values.append(element)
        return values
    return inner

@Operator(2)
def eqcollapser(comparator):
    def inner(array):
        array = force_list(array)[:]
        if len(array) == 0: return []
        values = [array.pop(0)]
        for element in array:
            if not dydeval(comparator, element, values[-1]):
                values.append(element)
        return values
    return inner

@Operator(1)
def keyeqcollapser(function):
    def inner(*args):
        array = force_list(args[0])[:]
        if len(array) == 0: return []
        e = (lambda x: nileval(function)) if function[0] == 0 else (lambda x: moneval(function, x)) if function[0] == 1 else (lambda x: dydeval(function, x, args[1]))
        values = [array.pop(0)]
        for element in array:
            if e(element) != e(values[-1]):
                values.append(element)
        return values
    return inner

def whileloop(condition, body):
    def inner(*args):
        args = list(args) or [0]
        while (condition[0] == 0 and nileval(condition)) or (condition[0] == 1 and moneval(condition, args[0])) or (condition[0] == 2 and dydeval(condition, *args)):
            args[0] = nileval(body) if body[0] == 0 else moneval(body, args[0]) if body[0] == 1 else dydeval(body, *args)
        return args[0]
    return (max(condition[0], body[0]), inner)

def nfind(amount, condition):
    def inner(*args):
        matches = nileval(amount)
        found = []
        current = args[0]
        while len(found) < matches:
            if (condition[0] == 0 and nileval(condition)) or (condition[0] == 1 and moneval(condition, current)) or (condition[0] == 2 and dydeval(condition, current, args[1])):
                found.append(current)
            current += 1
        return found
    return (max(1, condition[0]), inner)

def rotater(scale, layer):
    def inner(array, distance):
        if layer == 0 or depth(array) == 1:
            distance *= scale
            if distance > 0: return array[-distance:] + array[:-distance]
            if distance < 0: return array[ distance:] + array[: distance]
            return array
        else:
            next = rotater(scale, layer - 1)
            return [next(row, distance) for row in array]
    return inner

def force_matrix(array):
    if depth(array) >= 2: return   array
    if depth(array) == 1: return  [array]
    if depth(array) == 0: return [[array]]

def flatten(array, layer = -1):
    if layer == 0 or depth(array) <= 1: return array
    return flatten(sum(map(force_list, array), []), layer - 1)

def ternary(c, f, t):
    # if f[0] != t[0]: raise RuntimeError("Ternary clauses must have same arity")
    def inner(*args):
        if c[0] == 0: v = nileval(c)
        if c[0] == 1: v = moneval(c, args[0])
        if c[0] == 2: v = dydeval(c, *args)
        k = [f, t][bool(v)]
        if k[0] == 0: return nileval(k)
        if k[0] == 1: return moneval(k, args[0])
        if k[0] == 2: return dydeval(k, *args)
    return (max(c[0], t[0], f[0]), inner)

def factorial(num):
    r = sympy.Integer(1)
    for i in range(2, num + 1): r *= i
    return r

def digits(integer, base, bijective = False): # Taken directly from Jelly
    if integer == 0:
        return [0] * (not bijective)
    if bijective:
        base = abs(base)
    if base == 0:
        return [integer]
    if base == -1:
        digits = [1, 0] * abs(integer)
        return digits[:-1] if integer > 0 else digits
    sign = -1 if integer < 0 and base > 0 else 1
    integer *= sign
    if base == 1:
        return [sign] * integer
    digits = []
    while integer:
        integer -= bijective
        integer, digit = divmod(integer, base)
        digit += bijective
        if digit < 0:
            integer += 1
            digit -= base
        digits.append(sign * digit)
    return digits[::-1]

def from_base(digits, base):
    num = sympy.Integer(0)
    for digit in digits:
        num *= base
        num += digit
    return num

def listslices(array, number):
    if number == 1: return [array]
    length = -(-len(array) // number)
    return [array[:length]] + listslices(array[length:], number - 1)

def listsplit(array, element):
    slices = []
    for e in array:
        if not slices: slices += [[]]
        if e == element: slices += [[]]
        else: slices[-1] += [e]
    return slices

def partitions(array):
    if len(array) == 0: return [[]]
    if len(array) == 1: return [[array]]
    results = []
    for i in range(1, len(array) + 1):
        for j in partitions(array[i:]):
            results.append([array[:i]] + j)
    return results

def intpartitions(num):
    if num == 0: return []
    if num == 1: return [[1]]
    result = []
    for i in range(1, num):
        for j in intpartitions(num - i):
            result.append([i] + j)
    return result + [[num]]

def similar(x, y):
    if type(x) == type(y) == list:
        if len(x) == len(y) == 1 and type(x[0]) == type(x[1]) == str:
            return abs(ord(x[0]) - ord(y[0])) == 1 
        return len(x) == len(y)
    elif type(x) != list and type(y) != list:
        try:
            return abs(x - y) <= 1
        except:
            return False
    return False

def clone(array):
    if type(array) == list:
        return list(map(clone, array))
    return array

def mold(content, shape):
    shape = clone(shape)
    for index in range(len(shape)):
        if type(shape[index]) == list:
            shape[index] = mold(content, shape[index])
        else:
            item = content.pop(0)
            shape[index] = item
            content.append(item)
    return shape

def undiagonals(ds):
    ds = force_list(ds)
    ds = list(map(force_list, ds))
    lengths = list(map(len, ds))
    maxlen = max(lengths)
    index = lengths.index(maxlen)
    ds = ds[index:] + ds[:index]
    width = len([d for d in ds if len(d) == maxlen]) + len(ds[0]) - 1 
    matrix = [[sympy.Integer(0)] * width for i in range(len(ds[0]))]
    for i in range(len(ds)):
        if i < width:
            for j in range(len(ds[i])):
                matrix[j][i + j] = ds[i][j]
        else:
            bh = len(matrix) - i + width - 1
            for j in range(len(ds[i])):
                matrix[bh + j][j] = ds[i][j]
    return matrix

def diagonals(matrix):
    diag = []
    width = len(matrix[0])
    for i in range(width):
        diag += [[]]
        for j in range(min(len(matrix), width - i)):
            diag[-1] += [matrix[j][i + j]]
    for i in range(len(matrix) - 1, 0, -1):
        diag += [[]]
        for j in range(min(width, len(matrix) - i)):
            diag[-1] += [matrix[i + j][j]]
    return diag

def antidiagonals(matrix):
    return diagonals([row[::-1] for row in matrix])

def bdiagonals(matrix):
    d = diagonals(matrix)
    return d[-~-len(matrix):] + d[:-~-len(matrix)]

def bantidiagonals(matrix):
    d = antidiagonals(matrix)
    return d[-~-len(matrix):] + d[:-~-len(matrix)]

def median(array):
    if len(array) % 2 == 0:
        return (array[len(array) / 2] + array[len(array) / 2 - 1]) / 2
    else:
        return array[len(array) // 2]

def mode(array):
    counts = [array.count(e) for e in array]
    maxcount = max(counts)
    return [x for i, x in enumerate(array) if array.index(x) == i and counts[i] == maxcount]

def stdev(array):
    mean = sum(array) / len(array)
    return sympy.sqrt(sum((e - mean) ** 2 for e in array) / len(array))

def sublist_index(sub, array):
    if len(sub) > len(array): return False
    double = array + array
    for i in range(len(array)):
        if double[i:i + len(sub)] == sub:
            return i + 1
    else:
        return 0

def cyclic_predecessor(sub, array):
    return (array + array)[sublist_index(sub, array) + len(array) - 2:][:len(sub)]

def cyclic_successor(sub, array):
    return (array + array)[sublist_index(sub, array) + 1:][:len(sub)]

def powerset(array):
    array = range_list(array)
    values = []
    for t in range(len(array) + 1):
        values += list(map(list, itertools.combinations(array, t)))
    return values

def sublists(array):
    array = range_list(array)
    return [array[j:i + j + 1] for i in range(len(array)) for j in range(len(array) - i)]

def b_(value):
    if type(value) == list:
        return list(map(b_, value))
    if value == False: return sympy.Integer(0)
    if value == True : return sympy.Integer(1)
    return value

def u_(function):
    return lambda *a: b_(function(*a))

def getnil(fs):
    comp = []
    while fs[-1][0]:
        comp.append(fs.pop())
    comp.append(fs.pop())
    return (0, comp[::-1])

primes = set(map(sympy.Integer, {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71}))
composites = set(map(sympy.Integer, {4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 28, 30, 32, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 46, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 60, 62, 63, 64, 65, 66, 68, 69, 70}))

def PrimeQ(num):
    global primes, composites
    if num < 2: return False
    if num < 4: return True
    if num in primes: return True
    if num in composites: return False
    for prime in (primes | set(range(max(primes) + 2, int(num ** 0.5), 2))):
        if num % prime == 0:
            composites |= { num }
            return False
    primes |= { num }
    return True

def GCD(x, y):
    if x == 0: return y
    if x > y: return GCD(y, x)
    return GCD(y - x, x)

def LCM(x, y):
    return x * y / (GCD(x, y) or 1)

def equal(array):
    array = force_list(array)
    return sympy.Integer(all(element == array[0] for element in array))

def join(array, value):
    array = force_list(array)[:]
    last = [array.pop()] if array else []
    return sum(([element, value] for element in array), []) + last

def grid(array): # Taken directly from Jelly
    if depth(array) == 1:
        return join(array, ' ')
    if depth(array) == 2 and equal(list(map(len, array))):
        array = [[str(entry) for entry in row] for row in array]
        width = max(max([len(entry) for entry in row]) if row else 0 for row in array)
        array = [[list(entry.rjust(width)) for entry in row] for row in array]
        return join([join(row, ' ') for row in array], '\n')
    if depth(array) == 3 and all(type(item) == str for item in flatten(array)):
        array = [[''.join(entry) for entry in row] for row in array]
        width = max(max([len(entry) for entry in row]) if row else 0 for row in array)
        array = [[list(entry.ljust(width)) for entry in row] for row in array]
        return join([join(row, ' ') for row in array], '\n')
    return join(array, '\n')

def runlength_encode(array):
    array = force_list(array)
    results = []
    for element in array:
        if results and element == results[-1][0]:
            results[-1][1] += 1
        else:
            results.append([element, 1])
    return results

def group(array):
    array = force_list(array)
    results = []
    for element in array:
        if results and element == results[-1][0]:
            results[-1].append(element)
        else:
            results.append([element])
    return results

ucodepage  = """!¢£¤¥¦©¬®hπ?€ÆÇÐÑ×ØŒÞßæçðıȷñ÷øœþ ¡"#$%&,()*+’-.\0123456789:;<=>¿"""
ucodepage += """@ABCDEFGHIJKLMNOPQRSTUVWXYZ[/]v_`abcdefgµijklmuopqrstn^wxyz{|}~¶"""
ucodepage += """°¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾±≤≠≥√·∆₱•†‡§⍺⍵ŝσ←↓→↑↔↕↙↘↶↷↻λȦḂḊĖḢİḲĿṀṄȮỤṘṠṪṾẆẎŻẠḄ"""
ucodepage += """ĊḌẸḞĠḤỊḶṂṆỌṖṚṢṬẈỴẊẒȧḃḋėḥịḳŀṁṅȯṙṡṫụṿẇẏżạḅċḍẹḟġḣḷṃṇọṗṛṣṭẉẋỵẓ«»,,“”"""

rcodepage  = """¡¢£¤¥¦©¬®µπ¿€ÆÇÐÑ×ØŒÞßæçðıȷñ÷øœþ !"#$%&'()*+,-.\0123456789:;>=<?"""
rcodepage += """@ABCDEFGHIJKLMNOPQRSTUVWXYZ]/[^_`abcdefghijklmnopqrstuvwxyz}|{~¶"""
rcodepage += """°¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁾⁽±≥≠≤√·∆₱•†‡§⍺⍵ŝσ→↑←↓↔↕↘↙↷↶↻λẠḄḌẸḤỊḲḶṂṆỌṚṢṬỤṾẈỴẒȦḂ"""
rcodepage += """ĊḊĖḞĠḢİĿṀṄȮṖṘṠṪẆẊẎŻạḅḍẹḥịḳḷṃṇọṛṣṭụṿẉỵẓȧḃċḋėḟġḣŀṁṅȯṗṙṡṫẇẋẏż»«’‘”“"""

# Unused Characters for single character functions/operators

# ¡¢£  ¦   µ   ÆÇÐÑ ØŒ ßæçð  ñ øœþ       '()                      
#   BC    HI KLMNO      V XY       abcd f hi k m opq  tuvwxy      
#                                           λẠḄḌẸḤỊḲ Ṃ ỌṚ  ỤṾẈỴẒȦḂ
# Ċ ĖḞĠ  ĿṀ Ȯ Ṙ   Ẋ Żạḅḍ  ịḳḷṃ ọ   ụṿẉỵ ȧ  ḋ ḟġ ŀ  ȯṗ   ẇẋ        

functions = {
    "_":  (2, vecdyadboth(operator.sub)),
    "+":  (2, vecdyadboth(operator.add)),
    "±":  (2, vecdyadboth(lambda x, y: [x + y, x - y])),
    "*":  (2, vecdyadboth(operator.pow)),
    "×":  (2, vecdyadboth(operator.mul)),
    "÷":  (2, vecdyadboth(operator.truediv)),
    ":":  (2, vecdyadboth(operator.floordiv)),
    "%":  (2, vecdyadboth(operator.mod)),
    "&":  (2, vecdyadboth(lambda x, y: sympy.Integer(int(x) & int(y)))),
    "|":  (2, vecdyadboth(lambda x, y: sympy.Integer(int(x) | int(y)))),
    "^":  (2, vecdyadboth(lambda x, y: sympy.Integer(int(x) ^ int(y)))),
    "<":  (2, vecdyadboth(u_(operator.lt))),
    "≤":  (2, vecdyadboth(u_(operator.le))),
    "=":  (2, u_(operator.eq)),
    "e":  (2, vecdyadboth(u_(operator.eq))),
    "≈":  (2, u_(similar)),
    "n":  (2, vecdyadboth(u_(operator.ne))),
    "≠":  (2, u_(operator.ne)),
    "≥":  (2, vecdyadboth(u_(operator.ge))),
    ">":  (2, vecdyadboth(u_(operator.gt))),
    "»":  (2, vecdyadboth(max)),
    "«":  (2, vecdyadboth(min)),
    "®":  (0, lambda: register),
    ",":  (2, lambda x, y: [x, y]),
    ";":  (2, lambda x, y: force_list(x) + force_list(y)),
    "~":  (1, vecmonad(lambda x: sympy.Integer(~int(x)))),
    "√":  (1, vecmonad(sympy.sqrt)),
    "·":  (2, vecdyadboth(lambda x, y: sum(p * q for p, q in zip(force_list(x), force_list(y))), maxlayer_offset = 1)),
    "‘":  (1, vecmonad((-1).__add__)),
    "’":  (1, vecmonad(( 1).__add__)),
    "¹":  (1, lambda x: x),
    "²":  (1, vecmonad(lambda x: x * x)),
    "³":  (0, lambda: sympy.Integer(100)),
    "⁴":  (0, lambda: sympy.Integer(16)),
    "⁵":  (0, lambda: sympy.Integer(10)),
    "⁶":  (0, lambda: [" "]),
    "⁷":  (0, lambda: ["\n"]),
    "⁸":  (0, lambda: []),
    "⁹":  (0, lambda: sympy.Integer(256)),
    "⍺":  (0, lambda: sympy.Rational("0.1")),
    "⍵":  (0, lambda: 1), # TODO
    "π":  (0, lambda: sympy.pi),
    "σ":  (1, vecmonad(stdev, maxlayer_offset = 1)),
    "!":  (1, vecmonad(lambda x: (-1 if x < 0 else 1) * (factorial(abs(x)) if isinstance(x, sympy.Integer) else type(x)(math.gamma(x + 1))))),
    "A":  (1, vecmonad(abs)),
    "B":  (1, vecmonad(lambda x: digits(x, 2))),
    "D":  (1, vecmonad(lambda x: digits(x, 10))),
    "Ḋ":  (1, partitions),
    "E":  (1, equal),
    "Ė":  (1, lambda x: (lambda y: [[i + 1, e] for i, e in enumerate(y)])(force_list(x))),
    "F":  (1, flatten),
    "G":  (1, grid),
    "H":  (1, vecmonad(lambda x: digits(x, 16))),
    "Ḣ":  (1, lambda x: force_list(x).pop(0)),
    "ÆḢ": (1, lambda x: force_list(x)[0]),
    "İ":  (1, vecmonad(lambda x: ucodepage[codepage.index(x)] if type(x) == str else 1 / x)),
    "J":  (1, lambda x: list(range(1, len(force_list(x)) + 1))),
    "Ḷ":  (1, vecmonad(lambda x: list(range(0, x, -1 if x < 0 else 1)))),
    "P":  reducer(vecdyadboth(operator.mul)),
    "Ṗ":  (1, lambda x: list(map(list, itertools.permutations(x)))),
    "R":  (1, vecmonad(lambda x: list(range(1, x + 1)) if x > 0 else list(range(-1, x - 1, -1)))),
    "S":  reducer(vecdyadboth(operator.add)),
    "Ṣ":  (1, sorted),
    "Ṡ":  (1, vecmonad(lambda x: (1 if x > 0 else -1 if x else 0) if x.is_real else x.conjugate())),
    "T":  (1, lambda x: [i + 1 for i, e in enumerate(force_list(x)) if e]),
    "Ṫ":  (1, lambda x: force_list(x).pop()),
    "Ṭ":  (1, lambda x: (lambda y: [i + 1 in y for i in range(max(y))])(force_list(x))),
    "ÆṪ": (1, lambda x: force_list(x)[-1]),
    "U":  (1, uniquify(operator.eq)),
    "W":  (1, lambda x: [x]),
    "Ẇ":  (1, sublists),
    "X":  (1, lambda x: random.choice(x) if type(x) == list else sympy.Integer(random.randrange(1, x + 1)) if x % 1 == 0 else sympy.Rational(random.random() * x)),
    "Ẏ":  (1, lambda x: flatten(x, 1)),
    "Z":  (1, vecmonad(intpartitions)),
    "∆":  (1, vecmonad(lambda x: [q - p for p, q in zip(x, x[1:])], maxlayer_offset = 1)),
    "Æ∆": (1, lambda x: (x + 1) * x / 2),
    "Æm": (1, vecmonad(lambda x: sum(x) / len(x), maxlayer_offset = 1)),
    "Æṁ": (1, vecmonad(median, maxlayer_offset = 1)),
    "Æṃ": (1, vecmonad(mode, maxlayer_offset = 1)),
    "œc": (2, vecdyadboth(lambda x, y: factorial(x) / factorial(y) / factorial(x - y))),
    "œp": (2, vecdyadboth(lambda x, y: factorial(x) / factorial(x - y))),
    "œ←": (2, cyclic_predecessor),
    "œ→": (2, cyclic_successor),
    "æ←": (2, lambda x, y: y[y.index(x) - 1] if x in y else x),
    "æ→": (2, lambda x, y: y[y.index(x) + 1] if x in y else x),
    "æ«": (2, vecdyadboth(lambda x, y: x * 2 ** y)),
    "æ»": (2, vecdyadboth(lambda x, y: sympy.Integer(x * 2 ** -y))),
    "æ√": (2, vecdyadboth(lambda x, y: x ** (1 / y))),
    "æx": (2, vecdyadboth(lambda x, y: sympy.Integer(random.randrange(x, y)))),
    "œx": (2, vecdyadboth(lambda x, y: sympy.Rational(random.random() * (y - x) + x))),
    "↔":  (1, vecmonad(digit_lister(lambda x: x[::-1]), maxlayer_offset = 1)),
    "↕":  (1, lambda x: force_list(x)[::-1]),
    "←":  (2, rotater(-1, 1)),
    "→":  (2, rotater(+1, 1)),
    "↑":  (2, rotater(-1, 0)),
    "↓":  (2, rotater(+1, 0)),
    "¬":  (1, vecmonad(lambda x: not x)),
    "b":  (2, vecdyadboth(lambda x, y: digits(x, y))),
    "ḃ":  (2, vecdyadboth(lambda x, y: digits(x, y, bijective = True))),
    "ċ":  (2, vecdyadright(lambda l, r: list(map(list, itertools.combinations(l, r))))),
    "ė":  (2, lambda x, y: int(x in force_list(y))),
    "ẹ":  (2, lambda x, y: int(x not in force_list(y))),
    "g":  (2, vecdyadboth(GCD)),
    "ḣ":  (2, vecdyadright(lambda x, y: x[:y])),
    "ḥ":  (2, vecdyadright(lambda x, y: x[:-y])),
    "j":  (2, join),
    "l":  (2, vecdyadboth(LCM)),
    "m":  (2, vecdyadright(lambda l, r: digit_lister(lambda k: k[::r] if r else k + k[::-1])(l))),
    "ṁ":  (2, mold),
    "r":  (2, vecdyadboth(lambda l, r: list(range(l, r + (-1 if r < l else 1), -1 if r < l else 1)))),
    "ṙ":  (2, vecdyadboth(lambda l, r: list(range(l, r, -1 if r < l else 1)))),
    "ṛ":  (2, vecdyadboth(lambda l, r: (lambda d: list(range(l + d, r, d)))(-1 if r < l else 1))),
    "s":  (2, vecdyadright(lambda l, r: (lambda k: [k[i * r:i * r + r] for i in range(-(-len(k) // r))])(force_list(l)))),
    "ṡ":  (2, vecdyadright(lambda l, r: (lambda k: [k[i:i + r] for i in range(len(k) - r + 1)])(force_list(l)))),
    "ŝ":  (2, vecdyadright(lambda l, r: (lambda k: listslices(k, r))(force_list(l)))),
    "ṣ":  (2, listsplit),
    "ṫ":  (2, vecdyadright(lambda x, y: x[y - 1:])),
    "ṭ":  (2, vecdyadright(lambda x, y: x[-y:])),
    "ẏ":  (2, vecdyadright(flatten)),
    "z":  (2, lambda x, y: list(map(list, zip(*lfill(x, y))))),
    "ż":  (2, lambda x, y: (lambda a, b: [([a[i]] if i < len(a) else []) + ([b[i]] if i < len(b) else []) for i in range(max(len(a), len(b)))])(force_list(x), force_list(y))),
    "ẓ":  (2, lambda x, y: list(map(list, zip(force_list(x), force_list(y))))),
    "↙":  (1, lambda x: list(map(list, zip(*force_matrix(x))))),
    "↘":  (1, lambda x: list(map(list, zip(*force_matrix(x[::-1]))))[::-1]),
    "↶":  (1, lambda x: list(map(list, zip(*force_matrix(x))))[::-1]),
    "↷":  (1, lambda x: list(map(list, zip(*force_matrix(x[::-1]))))),
    "↻":  (1, lambda x: [y[::-1] for y in force_matrix(x)[::-1]]),
    "ŒB": (1, vecmonad(lambda x: digit_lister(lambda y: y[:-1] + y[::-1])(x), maxlayer_offset = 1)),
    "ŒḄ": (1,          lambda x: digit_lister(lambda y: y[:-1] + y[::-1])(x)                       ),
    "ŒD": (1, bdiagonals),
    "ŒḊ": (1, bantidiagonals),
    "ŒḌ": (1, undiagonals),
    "ŒM": (1, diagonals),
    "ŒṀ": (1, antidiagonals),
    "Œ_": (1, lambda x: []),
    "ŒT": (1, lambda x: sum(1 if e else 0 for e in x)),
    "ŒṖ": (1, powerset),
    "Œg": (1, group),
    "Œr": (1, runlength_encode),
    "Œṙ": (1, lambda x: sum([[e] * i for e, i in x], [])),
    "ÆR": (1, vecmonad(lambda x:             list(filter(PrimeQ, range(2, x + 1))))),
    "ÆC": (1, vecmonad(lambda x:         len(list(filter(PrimeQ, range(2, x + 1)))))),
    "ÆĊ": (1, vecmonad(lambda x: x - 1 - len(list(filter(PrimeQ, range(2, x + 1)))))),
    "ÆṪ": (1, vecmonad(lambda x: len([k for k in range(1, x) if GCD(k, x) == 1]))),
    "ÆS": (1, vecmonad(sympy. sin )),
    "ÆẠ": (1, vecmonad(sympy. cos )),
    "ÆT": (1, vecmonad(sympy. tan )),
    "ÆṢ": (1, vecmonad(sympy.asin )),
    "ÆA": (1, vecmonad(sympy.acos )),
    "ÆṬ": (1, vecmonad(sympy.atan )),
    "Æs": (1, vecmonad(sympy. sinh)),
    "Æa": (1, vecmonad(sympy. cosh)),
    "Æt": (1, vecmonad(sympy. tanh)),
    "Æṣ": (1, vecmonad(sympy.asinh)),
    "Æạ": (1, vecmonad(sympy.acosh)),
    "Æṭ": (1, vecmonad(sympy.atanh)),
    "ÆU": (1, eqcollapser(operator.eq)),
    "⁽":  (1, lambda x: (lambda y: [y[:-~i] for i in range(len(y))])(force_list(x))),
    "⁾":  (1, lambda x: (lambda y: [y[ i: ] for i in range(len(y))])(force_list(x))),
    "ØX": (0, lambda: sympy.Rational(random.random())),
    "œḷ": (2, lambda x, y: x),
    "œṛ": (2, lambda x, y: y),
}

operators = {
    "@":  (-1, lambda fs: (2, reverse_args(fs.pop()))),
    "$":  (-1, lambda fs: (1, [fs.pop(-2), fs.pop()])),
    "¥":  (-1, lambda fs: (2, [fs.pop(-2), fs.pop()])),
    "€":  (-1, lambda fs: foreachleft(fs.pop())),
    "₱":  (-1, lambda fs: foreachright(fs.pop())),
    "©":  (-1, lambda fs: registrar(fs.pop())),
    "/":  (-1, lambda fs: reducer(*([fs.pop(-2), fs.pop()] if fs[-1][0] == 0 else [fs.pop()]))),
    "\\": (-1, lambda fs: oreduce(*([fs.pop(-2), fs.pop()] if fs[-1][0] == 0 else [fs.pop()]))),
    "\"": (-1, lambda fs: (2, vecdyadboth(fs.pop()))),
    "`":  (-1, lambda fs: (1, (lambda f: lambda x: dydeval(f, x, x))(fs.pop()))),
    "{":  (-1, lambda fs: (2, (lambda f: lambda x, y: moneval(f, x))(fs.pop()))),
    "}":  (-1, lambda fs: (2, (lambda f: lambda x, y: moneval(f, y))(fs.pop()))),
    "?":  (-1, lambda fs: ternary(fs.pop(), fs.pop(), fs.pop())),
    "⁼":  (-1, lambda fs: (1, (lambda f: u_(lambda x: f(x) == x))(fs.pop()))),
    "¿":  (-1, lambda fs: whileloop(fs.pop(), fs.pop())),
    "#":  (-1, lambda fs: nfind(fs.pop() if fs[-1][0] == 0 else (0, last_input), fs.pop())),
    "Þ":  (-1, lambda fs: sorter(fs.pop())),
    "¤":  (-1, lambda fs: getnil(fs)),
    "⁺":  (-1, lambda fs: (1, uniquify(fs.pop()))),
    "Ð⁺": (-1, lambda fs: (max(1, fs[-1][0]), keyuniquify(fs.pop()))),
    "ÐU": (-1, lambda fs: (1, eqcollapser(fs.pop()))),
    "ÐỤ": (-1, lambda fs: (max(1, fs[-1][0]), keyeqcollapser(fs.pop()))),
}

overloads = ["•", "§", "†", "§", "‡", "§"]

def to_i(text):
    if text.startswith("-"):
        return "-" + to_i(text[1:])
    elif text == "":
        return "sympy.Integer(1)"
    else:
        return "sympy.Integer(" + repr(text) + ")"

def to_r(text):
    if text.startswith("-"):
        return "-" + to_r(text[1:])
    else:
        left, right = text.split(".")
        return "sympy.Rational(" + repr((left or "0") + "." + (right or "5")) + ")"

def to_n(text):
    if "ı" in text:
        left, right = text.split("ı", 1)
        return to_n(left or "0") + "+sympy.I*" + to_n(right or "1")
    elif "ȷ" in text:
        left, right = text.split("ȷ", 1)
        return to_n(left or "1") + "*10**" + to_n(right or "3")
    elif "." in text:
        return to_r(text)
    else:
        return to_i(text)

dgts = r"(?:[1-9][0-9]*)"
intg = r"(0|-?{d}|-)".format(d = dgts)
real = r"(-?{d}?\.[0-9]*)".format(d = dgts)
expn = r"{n}?ȷ{n}?".format(n = "({r}|{i})".format(r = real, i = intg))
cmpx = r"{n}?ı{n}?".format(n = "({e}|{r}|{i})".format(e = expn, r = real, i = intg))
numr = "(" + "|".join([cmpx, expn, real, intg]) + ")"
slst = r"(“(([^“”‘’»]|\\.)*))+(”|‘|’|»)"
strn = r"“(([^“”‘’»]|\\.)*)(”|‘|’|»)"
char = r"”(.)"
litr = "(" + "|".join([char, strn, slst, numr]) + ")"
elst = r"\[*" + litr + r"?(?:(?:\]*,\[*)" + litr + ")*" + r"\]*"
func = "(" + "|".join(map(re.escape, functions)) + ")"
oper = "(" + "|".join(map(re.escape, operators)) + ")"
spec = "(" + "|".join(map(re.escape, overloads)) + ")"

def str_eval(type):
    type = "”‘’»".index(type)
    if type == 0:
        return lambda code: repr(list(eval('"""%s"""' % code.replace('"', '\\"'))))
    if type == 1:
        return lambda code: repr(list(map(codepage.index, eval('"""%s"""' % code.replace('"', '\\"')))))
    if type == 2:
        return lambda code: (lambda str: "("+"+".join("sympy.Integer(250)**"+str(len(str)-index-1)+"*sympy.Integer("+repr(codepage.index(char)+1)+")"for index, char in enumerate(str))+")")(eval('"""%s"""' % code.replace('"', '\\"')))

def evalyank(code):
    match = re.match(char, code)
    if match:
        return (match.group(), "[" + repr(match.group()[1]) + "]")
    match = re.match(strn, code)
    if match:
        return (match.group(), str_eval(match.group()[-1])(match.group()[1:-1]))
    match = re.match(slst, code)
    if match:
        return (match.group(), list(map(str_eval(match.group()[-1]), re.split(r"(?<!\\)“", match.group()[1:-1]))))
    match = re.match(numr, code)
    if match:
        return (match.group(), to_n(match.group()))

def make_list(obj):
    if hasattr(obj, "__iter__"):
        return list(obj)
    else:
        return obj

def elsteval(code):
    raw = ""
    while code:
        yanked = evalyank(code)
        if yanked:
            raw += yanked[1] + " "
            code = code[len(yanked[0]):]
        else:
            raw += code[0]
            code = code[1:]
    return make_list(eval(raw))


def elstevalmatcher(match):
    value = elsteval(match.group())
    return (0, lambda: value)

matchers = [(m[0], re.compile(m[1]), m[2]) for m in [
    ("elst", elst, elstevalmatcher),
    ("func", func, lambda m: functions[m.group()]),
    ("oper", oper, lambda m: operators[m.group()]),
    ("spec", spec, lambda m: (-2, m.group())),
]]

def tokenize(code):
    code = "".join(char for char in code.replace("\n", "¶") if char in codepage)
    tokens = []
    while code:
        tokens = tokens or [[]]
        if code[0] == "¶": tokens.append([]); code = code[1:]; continue
        for matcher in matchers:
            token = matcher[1].match(code)
            if token:
                try:
                    tokens[-1].append(matcher[2](token))
                    code = code[len(token.group()):]
                    break
                except:
                    pass
        else:
            code = code[1:]
    return tokens

brackets = "•§†§‡§"

def parse(tokens):
    result = []
    index = 0
    while index < len(tokens):
        if type(tokens[index][1]) == str and tokens[index][1] in brackets:
            start = tokens[index][1]
            inner = []
            bcount = 1
            index += 1
            while bcount:
                if type(tokens[index][1]) == str and tokens[index][1] in brackets:
                    if brackets.find(tokens[index][1]) & 1 == 1:
                        bcount -= 1
                        if not bcount: index += 1; break
                    else:
                        bcount += 1
                inner.append(tokens[index])
                index += 1
            result.append((brackets.find(start) >> 1, parse(inner)))
        else:
            result.append(tokens[index])
            index += 1
    return result

def preexecute(tokens):
    func_stack = []
    for token in tokens:
        if 0 <= token[0] <= 2 or token[0] == -2:
            func_stack.append(token)
        elif token[0] == -1:
            func_stack.append(token[1](func_stack))
        else:
            raise RuntimeError("huh?")
    return func_stack

class Evaluator:
    def __init__(self, function):
        self.function = function
    def __call__(self, tokens, *args, **kwargs):
        if isinstance(tokens, list): return self.function(tokens[:], *args, **kwargs)
        else: return self.function([tokens], *args, **kwargs)

@Evaluator
def nileval(tokens, layer = 0, nest = False, links = [], index = -1):
    if tokens:
        if tokens[0][0] == 0:
            if isinstance(tokens[0][1], list):
                value = nileval(tokens.pop(0)[1], layer = layer + 1, nest = True)
            else:
                value = tokens.pop(0)[1]()
        elif tokens[0][0] == -2:
            value = 0
        else:
            value = 0
    else:
        value = 0
    return moneval(tokens, value, layer = layer)

@Evaluator
def moneval(tokens, argument, layer = 0, nest = False, links = [], index = -1):
    if nest and tokens and not any(map(operator.itemgetter(0), tokens)):
        values = [nileval([token], layer = layer + 1, nest = False) for token in tokens]
        if argument in values: return values[(values.index(argument) + 1) % len(values)]
        return argument
    if tokens and tokens[0][0] == 0:
        value = nileval(tokens.pop(0), layer = layer)
    else:
        value = None
    while tokens:
        v = argument if value is None else value
        if len(tokens) >= 3 and tokens[0][0] == tokens[1][0] == 2 and tokens[2][0] == 0:
            value = dydeval(tokens.pop(1), dydeval(tokens.pop(0), v, argument, layer), nileval(tokens.pop(0), layer), layer = layer)
        elif len(tokens) >= 2 and tokens[0][0] == 2 and tokens[1][0] == 1:
            value = dydeval(tokens.pop(0), v, tokens.pop(0)[1](argument), layer = layer)
        elif len(tokens) >= 2 and tokens[0][0] == 2 and tokens[1][0] == 0:
            value = dydeval(tokens.pop(0), v, nileval(tokens.pop(0), layer = layer), layer = layer)
        elif len(tokens) >= 2 and tokens[0][0] == 0 and tokens[1][0] == 2:
            value = dydeval(tokens.pop(1), nileval(tokens.pop(0), layer = layer), v, layer = layer)
        elif tokens[0][0] == 2:
            if isinstance(tokens[0][1], list):
                value = dydeval(tokens.pop(0), v, argument, layer = layer + 1, nest = True)
            else:
                value = tokens.pop(0)[1](v, argument)
        elif tokens[0][0] == 1:
            if isinstance(tokens[0][1], list):
                value = moneval(tokens.pop(0)[1], v, layer = layer + 1, nest = True)
            else:
                value = tokens.pop(0)[1](v)
        else:
            if value is not None:
                print(value, end = "")
            value = nileval(tokens.pop(0), layer = layer)
    return argument if value is None else value

@Evaluator
def dydeval(tokens, left, right, layer = 0, nest = False, links = [], index = -1):
    if len(tokens) >= 3 and tokens[0][0] == tokens[1][0] == tokens[2][0] == 2:
        if isinstance(tokens[0][1], list):
            value = dydeval(tokens.pop(0)[1], left, right, layer = layer + 1, nest = True)
        else:
            value = tokens.pop(0)[1](left, right)
    elif tokens and tokens[0] == 0:
        value = nileval(tokens.pop(0), layer = layer)
    else:
        value = None
    while tokens:
        v = left if value is None else value
        if len(tokens) >= 3 and tokens[0][0] == tokens[1][0] == 2 and tokens[2][0] == 0:
            value = dydeval(tokens.pop(1), dydeval(tokens.pop(0), v, right, layer = layer), nileval(tokens.pop(0), layer = layer), layer = layer)
        elif len(tokens) >= 2 and tokens[0][0] == tokens[1][0] == 2:
            value = dydeval(tokens.pop(0), v, dydeval(tokens.pop(0), left, right, layer = layer), layer = layer)
        elif len(tokens) >= 2 and tokens[0][0] == 2 and tokens[1][0] == 0:
            value = dydeval(tokens.pop(0), v, nileval(tokens.pop(0), layer = layer), layer = layer)
        elif len(tokens) >= 2 and tokens[0][0] == 0 and tokens[1][0] == 2:
            value = dydeval(tokens.pop(1), nileval(tokens.pop(0), layer = layer), v, layer = layer)
        elif tokens[0][0] == 2:
            if isinstance(tokens[0][1], list):
                value = dydeval(tokens.pop(0)[1], v, right, layer = layer + 1, nest = True)
            else:
                value = tokens.pop(0)[1](v, right)
        elif tokens[0][0] == 1:
            if isinstance(tokens[0][1], list):
                value = moneval(tokens.pop(0)[1], v, layer = layer + 1, nest = True)
            else:
                value = tokens.pop(0)[1](v)
        else:
            if value is not None:
                enlist_output(value, "")
            value = nileval(tokens.pop(0), layer = layer)
    return left if value is None else value

def evaluate(links, arguments):
    link = links[-1]
    if len(arguments) >= 1:
        functions["⍺"] = (0, lambda: arguments[0])
    if len(arguments) >= 2:
        functions["⍵"] = (0, lambda: arguments[1])
    # TODO other argument getters
    if len(arguments) >= 2:
        return dydeval(link, arguments[0], arguments[1], links = links, index = len(links) - 1)
    elif len(arguments) == 1:
        return moneval(link, arguments[0], links = links, index = len(links) - 1)
    else:
        return nileval(link, links = links, index = len(links) - 1)

def enlist_eval(code, arguments):
    return evaluate(list(map(preexecute, map(parse, tokenize(code)))), arguments)

def stringify(iterable, recurse = True):
    if type(iterable) != list:
         return 1 if iterable is True else 0 if iterable is False else iterable
    if len(iterable) == 1:
         return stringify(iterable[0])
    if str in map(type, iterable) and not list in map(type, iterable) or not iterable:
        return "".join(map(str, iterable))
    iterable = [stringify(item) for item in iterable]
    return stringify(iterable, False) if recurse else iterable

def unicode_to_jelly(string):
    return "".join(chr(codepage.find(char)) for char in str(string).replace("\n", "¶") if char in codepage)

def enlist_output(argument, end = "\n", transform = stringify):
    if locale.getdefaultlocale()[1][:3] == "UTF":
        print(transform(argument), end = end)
    else:
        print(unicode_to_jelly(transform(argument)), end = unicode_to_jelly(end))
    sys.stdout.flush()
    return argument

if __name__ == "__main__":
    args = list(map(try_eval, sys.argv[1:]))
    for i in range(len(args)):
        functions["³⁴⁵⁶⁷⁸⁹"[i]] = (0, lambda: args[i])
    enlist_output(enlist_eval(input(), args))
