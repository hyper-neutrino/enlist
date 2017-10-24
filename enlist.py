# Enlist by Alexander Liao
# Parts of this program are taken from Dennis's code for the Jelly programming language,
# in compliance to the MIT license and with his additionally expressed permission   

codepage  = """¡¢£¤¥¦©¬®µ½¿€ÆÇÐÑ×ØŒÞßæçðıȷñ÷øœþ !"#$%&'()*+,-./0123456789:;<=>?"""
codepage += """@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~¶"""
codepage += """°¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾±≤≠≥√·∆₱•†‡§⍺⍵⍶⍹←↑→↓↔↕↙↘↯↶↷↻ẠḄḌẸḤỊḲḶṂṆỌṚṢṬỤṾẈỴẒȦḂ"""
codepage += """ĊḊĖḞĠḢİĿṀṄȮṖṘṠṪẆẊẎŻạḅḍẹḥịḳḷṃṇọṛṣṭụṿẉỵẓȧḃċḋėḟġḣŀṁṅȯṗṙṡṫẇẋẏż«»‘’“”"""

import re, math, operator, sympy, sys, locale, functools

def try_eval(string):
    number = "([0-9]+|[0-9]*\.[0-9]+)"
    if re.match("^({0}j|{0}(\s*\+\s*{0}j)?)$".format(number), string):
        return eval(re.sub(number, r"sympy.Rational('\1')", string.replace("j", "*sympy\.I")))
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

def depth(obj):
    if hasattr(obj, "__iter__"):
        return max(map(depth, obj)) + 1
    return 0

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
        if layers == maxlayers or depth(args[0]) == maxlayer_offset:
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

@Operator(1)
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

# ¡¢£¤ ¦   µ½¿ ÆÇÐÑ ØŒÞßæçð  ñ øœþ   #   '()                     ?
#  ABCDEFGHIJKLMNOP  STUVWXYZ[ ]  `abcd fghijklm opqrstuvwxyz{ }  
# °         ⁺⁻⁼⁽⁾              ⍶⍹        ↯   ẠḄḌẸḤỊḲḶṂ ỌṚṢṬỤṾẈỴẒȦḂ
# ĊḊĖḞĠḢİĿṀ ȮṖṘṠṪẆẊẎŻạḅḍ ḥịḳḷṃ ọṛṣṭụṿẉỵẓȧḃċḋ ḟġḣŀṁ ȯṗṙṡṫẇẋẏż      

functions = {
    "_": (2, vecdyadboth(operator.sub)),
    "+": (2, vecdyadboth(operator.add)),
    "±": (2, vecdyadboth(lambda x, y: [x + y, x - y])),
    "*": (2, vecdyadboth(operator.pow)),
    "×": (2, vecdyadboth(operator.mul)),
    "÷": (2, vecdyadboth(operator.truediv)),
    ":": (2, vecdyadboth(operator.floordiv)),
    "%": (2, vecdyadboth(operator.mod)),
    "&": (2, vecdyadboth(operator.and_)),
    "|": (2, vecdyadboth(operator.or_)),
    "^": (2, vecdyadboth(operator.xor)),
    "<": (2, vecdyadboth(operator.lt)),
    "≤": (2, vecdyadboth(operator.le)),
    "=": (2, operator.eq),
    "e": (2, vecdyadboth(operator.eq)),
    "n": (2, vecdyadboth(operator.ne)),
    "≠": (2, operator.ne),
    "≥": (2, vecdyadboth(operator.ge)),
    ">": (2, vecdyadboth(operator.gt)),
    "»": (2, vecdyadboth(max)),
    "«": (2, vecdyadboth(min)),
    "®": (0, lambda: register),
    ",": (2, lambda x, y: [x, y]),
    ";": (2, lambda x, y: force_list(x) + force_list(y)),
    "~": (1, vecmonad(lambda x: sympy.Integer(~int(x)))),
    "√": (1, vecmonad(sympy.sqrt)),
    "!": (1, vecmonad(lambda x: math.gamma(x + 1))),
    "·": (2, vecdyadboth(lambda x, y: sum(p * q for p, q in zip(force_list(x), force_list(y))), maxlayer_offset = 1)),
    "‘": (1, vecmonad((-1).__add__)),
    "’": (1, vecmonad(( 1).__add__)),
    "¹": (1, lambda x: x),
    "²": (1, vecmonad(lambda x: x * x)),
    "³": (0, lambda: 100),
    "⁴": (0, lambda: 16),
    "⁵": (0, lambda: 10),
    "⁶": (0, lambda: " "),
    "⁷": (0, lambda: "\n"),
    "⁸": (0, lambda: []),
    "⁹": (0, lambda: 256),
    "Q": (1, lambda l: [l[i] for i in range(len(l)) if l.index(l[i]) == i]),
    "R": (1, vecmonad(lambda x: list(range(1, x + 1)))),
    "S": reducer(vecdyadboth(operator.add)),
    "↔": (1, vecmonad(lambda x: force_list(x)[::-1], maxlayer_offset = 1)),
    "∆": (1, vecmonad(lambda x: [q - p for p, q in zip(x, x[1:])])),
    "↕": (1, lambda x: force_list(x)[::-1]),
    "←": (2, rotater(-1, 1)),
    "→": (2, rotater(+1, 1)),
    "↑": (2, rotater(-1, 0)),
    "↓": (2, rotater(+1, 0)),
    "¬": (1, vecmonad(lambda x: int(not x))),
    "ė": (2, lambda x, y: int(x in force_list(y))),
    "ẹ": (2, lambda x, y: int(x not in force_list(y))),
    "↙": (1, lambda x: list(map(list, zip(*force_matrix(x))))),
    "↘": (1, lambda x: list(map(list, zip(*force_matrix(x[::-1]))))[::-1]),
    "↶": (1, lambda x: list(map(list, zip(*force_matrix(x))))[::-1]),
    "↷": (1, lambda x: list(map(list, zip(*force_matrix(x[::-1]))))),
    "↻": (1, lambda x: [y[::-1] for y in force_matrix(x)[::-1]]),
}

operators = {
    "@": (-1, lambda fs: (2, reverse_args(fs.pop()))),
    "$": (-1, lambda fs: (1, [fs.pop(), fs.pop()])),
    "¥": (-1, lambda fs: (2, [fs.pop(), fs.pop()])),
    "€": (-1, lambda fs: foreachleft(fs.pop())),
    "₱": (-1, lambda fs: foreachright(fs.pop())),
    "©": (-1, lambda fs: registrar(fs.pop())),
    "/": (-1, lambda fs: reducer(*([fs.pop(-2), fs.pop()] if fs[-1][0] == 0 else [fs.pop()]))),
    "\\":(-1, lambda fs: oreduce(*([fs.pop(-2), fs.pop()] if fs[-1][0] == 0 else [fs.pop()]))),
    "\"":(-1, lambda fs: (2, vecdyadboth(fs.pop()))),
}
overloads = ["•", "§", "†", "§", "‡", "§", "⍺", "⍵"]

def to_i(text):
    if text.startswith("-"):
        return -to_i(text[1:])
    elif text == "":
        return 1
    else:
        return sympy.Integer(text)

def to_r(text):
    if text.startswith("-"):
        return -to_r(text[1:])
    else:
        left, right = text.split(".")
        return sympy.Rational((left or "0") + "." + (right or "5"))

def to_n(text):
    if "ı" in text:
        left, right = text.split("ı", 1)
        return to_n(left or "0") + sympy.I * to_n(right or "1")
    elif "ȷ" in text:
        left, right = text.split("ȷ", 1)
        return to_n(left or "1") * 10 ** to_n(right or "3")
    elif "." in text:
        return to_r(text)
    else:
        return to_i(text)

dgts = r"(?:[1-9][0-9]*)"
intg = r"(0|-?{d}|-)".format(d = dgts)
real = r"(-?{d}?\.{d}?)".format(d = dgts)
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
        return lambda code: list(eval('"""%s"""' % code.replace('"', '\\"')))
    if type == 1:
        return lambda code: list(map(codepage.index, eval('"""%s"""' % code.replace('"', '\\"'))))
    if type == 2:
        return lambda code: (lambda str: sum(sympy.Integer(250) ** (len(str) - index - 1) * sympy.Integer(codepage.index(char) + 1) for index, char in enumerate(str)))(eval('"""%s"""' % code.replace('"', '\\"')))

def evalyank(code):
    match = re.match(char, code)
    if match:
        return (match.group(), match.group()[1])
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
            raw += repr(yanked[1]) + " "
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
        for matcher in matchers:
            token = matcher[1].match(code)
            if token:
                try:
                    tokens.append(matcher[2](token))
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
def nileval(tokens, layer = 0, nest = False):
    if tokens:
        if tokens[0][0] == 0:
            if isinstance(tokens[0][1], list):
                value = nileval(tokens.pop(0)[1], layer = layer + 1, nest = True)
            else:
                value = tokens.pop(0)[1]()
        elif tokens[0][0] == -2:
            if tokens[0][1] == "⍺":
                value = 100
            elif tokens[0][1] == "⍵":
                value = []
    else:
        value = 0
    return moneval(tokens, value, layer = layer)

@Evaluator
def moneval(tokens, argument, layer = 0, nest = False):
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
def dydeval(tokens, left, right, layer = 0, nest = False):
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


def evaluate(tokens, arguments):
    if len(arguments) >= 1:
        functions["⍺"] = (0, lambda: arguments[0])
    if len(arguments) >= 2:
        functions["⍵"] = (0, lambda: arguments[1])
    # TODO other argument getters
    if len(arguments) >= 2:
        return dydeval(tokens, arguments[0], arguments[1])
    elif len(arguments) == 1:
        return moneval(tokens, arguments[0])
    else:
        return nileval(tokens)

def enlist_eval(code, arguments):
    return evaluate(preexecute(parse(tokenize(code))), arguments)

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
