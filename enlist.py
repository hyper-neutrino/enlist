# Enlist by Alexander Liao
# Parts of this program are taken from Dennis's code for the Jelly programming language,
# in compliance to the MIT license and with his additionally expressed permission

codepage  = """................................ !"#$%&'()*+,-./0123456789:;<=>?"""
codepage += """@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~¡"""
codepage += """¢£¥§©«®°±¶·»¿ÀÁÂÃÄÅÆÇÈÉÊËÌÍÎÏÑÒÓÔÕÖ×ØÙÚÛÜßàáâãäåæçèéêëìíîïñòóôõö"""
codepage += """÷øùúûüĀāĒēĪīŌōŒœŪūΠπ‘’“”„†‡•‰‹›€₱℅№™←↑→↓∆√∞≈≠≤≥★♪✓ıȷ⍺⍵⍶⍹........"""

import re, math, operator, sympy, sys, locale

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

def reverse_args(function):
    return lambda x, y: function(y, x)

def foreachleft(function):
    if function[0] == 0:
        return (1, lambda inp: [function[1]() for val in range_list(inp)])
    elif function[0] == 1:
        return (1, lambda inp: [function[1](val) for val in range_list(inp)])
    elif function[0] == 2:
        return (2, lambda left, right: [function[1](val, right) for val in range_list(left)])

def foreachright(function):
    if function[0] == 0:
        return (2, lambda left, right: [function[1]() for val in range_list(right)])
    elif function[0] == 1:
        return (2, lambda left, right: [function[1](val) for val in range_list(right)])
    elif function[0] == 2:
        return (2, lambda left, right: [function[1](left, val) for val in range_list(right)])

def vectorizeleft(function, maxlayers = -1, maxlayer_offset = 0):
    def inner(layers, *args):
        if layers == maxlayers or depth(args[0]) == maxlayer_offset:
            return function(*args)
        else:
            return [inner(layers + 1, *((element,) + args[1:])) for element in args[0]]
    return inner

def vecdyadleft(function, maxlayers = -1, maxlayer_offset = 0):
    inner = vectorizeleft(function, maxlayers, maxlayer_offset)
    return lambda left, right: inner(0, left, right)

def vecmonad(function, maxlayers = -1, maxlayer_offset = 0):
    inner = vectorizeleft(function, maxlayers, maxlayer_offset)
    return lambda argument: inner(0, argument)

def vecdyadright(function, maxlayers = -1, maxlayer_offset = 0):
    def inner(layers, left, right):
        if layers == maxlayers or depth(right) == maxlayer_offset or depth(right) == 0:
            return function(left, right)
        else:
            return [inner(layers + 1, left, element) for element in right]
    return lambda left, right: inner(0, left, right)

def vecdyadboth(function, maxlayers = -1, maxlayer_offset = 0):
    def inner(layers, left, right):
        ldone = layers == maxlayers or depth(left) == maxlayer_offset
        rdone = layers == maxlayers or depth(right) == maxlayer_offset
        if ldone and rdone:
            return function(left, right)
        elif ldone:
            return [inner(layers + 1, left, element) for element in right] + right[len(left):]
        elif rdone:
            return [inner(layers + 1, element, right) for element in left] + left[len(right):]
        else:
            return [inner(layers + 1, eleft, eright) for eleft, eright in zip(left, right)] + right[len(left):] + left[len(right):]
    return lambda left, right: inner(0, left, right)

register = 0

def registrar(function):
    def inner(*args):
        global register
        register = function(*args)
        return register
    return inner

# ................................  "#   '       /               ?
#  ABCDEFGHIJKLMNOPQ ST VWXYZ \   `abcdefghijklmnopqrstuvwxyz    ¡
# ¢£     °    ¿ÀÁÂÃÄÅÆÇÈÉÊËÌÍÎÏÑÒÓÔÕÖ ØÙÚÛÜßàáâãäåæçèéêëìíîïñòóôõö
#  øùúûüĀāĒēĪīŌōŒœ ūΠπ    „   ‰‹›  ℅№™←↑→↓  ∞≈   ★♪✓    ⍶⍹........

functions = {
    "_": (2, vecdyadboth(operator.sub)),
    "+": (2, vecdyadboth(operator.add)),
    "±": (2, vecdyadboth(lambda x, y: [x + y, x - y]))
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
    "~": (1, vecmonad(lambda x: sympy.Integer(~int(x)))),
    "√": (1, vecmonad(sympy.sqrt)),
    "!": (1, vecmonad(lambda x: math.gamma(x + 1))),
    "·": (2, vecdyadboth(lambda x, y: sum(p * q for p, q in zip(force_list(x), force_list(y))), maxlayer_offset = 1)),
    "‘": (1, vecmonad((-1).__add__)),
    "’": (1, vecmonad(( 1).__add__)),
    "R": (1, vecmonad(lambda x: list(range(1, x + 1)))),
    "U": (1, vecmonad(lambda x: force_list(x)[::-1], maxlayer_offset = 1)),
    "∆": (1, vecmonad(lambda x: [q - p for p, q in zip(x, x[1:])])),
    "Ū": (1, lambda x: force_list(x)[::-1]),
}

operators = {
    "@": (-1, lambda fs: (2, reverse_args(fs.pop()[1]))),
    "$": (-1, lambda fs: (1, [fs.pop(), fs.pop()])),
    "¥": (-1, lambda fs: (2, [fs.pop(), fs.pop()])),
    "€": (-1, lambda fs: foreachleft(fs.pop())),
    "₱": (-1, lambda fs: foreachright(fs.pop())),
    "©": (-1, lambda fs: registrar(fs.pop())),
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

def nileval(tokens, layer = 0, nest = False):
    if not isinstance(tokens, list): return nileval([tokens], layer = layer)
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

def moneval(tokens, argument, layer = 0, nest = False):
    if not isinstance(tokens, list): return moneval([tokens], argument, layer = layer)
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

def dydeval(tokens, left, right, layer = 0, nest = False):
    if not isinstance(tokens, list): return dydeval([tokens], left, right, layer = layer)
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
            value = dydeval(tokens.pop(0), v, dydeval(tokens.pop(0, layer = layer), left, right), layer = layer)
        elif len(tokens) >= 2 and tokens[0][0] == 2 and tokens[1][0] == 0:
            value = dydeval(tokens.pop(0)[1], v, nileval(tokens.pop(0), layer = layer), layer = layer)
        elif len(tokens) >= 2 and tokens[0][0] == 0 and tokens[1][0] == 2:
            value = dydeval(tokens.pop(1), nileval(tokens.pop(0)[1], layer = layer), v, layer = layer)
        elif tokens[0][0] == 2:
            if isinstance(tokens[0][1], list):
                value = dydeval(tokens.pop(0), v, right, layer = layer + 1, nest = True)
            else:
                value = tokens.pop(0)[1](v, right)
        elif tokens[0][0] == 1:
            if isinstance(tokens[0][1], list):
                value = moneval(tokens.pop(0), v, layer = layer + 1, nest = True)
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
    if locale.getdefaultlocale()[1][0:3] == "UTF":
        print(transform(argument), end = end)
    else:
        print(unicode_to_jelly(transform(argument)), end = unicode_to_jelly(end))
    sys.stdout.flush()
    return argument

if __name__ == "__main__":
    enlist_output(enlist_eval(input(), list(map(try_eval, sys.argv[1:]))))
