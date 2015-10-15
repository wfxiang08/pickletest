#-*- encoding:utf-8 -*-

from types import *
from copy_reg import _inverted_registry, _extension_cache
import marshal
import sys
import struct
import re

__all__ = ["PickleError", "PicklingError", "UnpicklingError", "Unpickler",  "load", "loads"]

# These are purely informational; no code uses these.
format_version = "2.0"                  # File format version we write
compatible_formats = ["1.0",            # Original protocol 0
                      "1.1",            # Protocol 0 with INST added
                      "1.2",            # Original protocol 1
                      "1.3",            # Protocol 1 with BINFLOAT added
                      "2.0",            # Protocol 2
                      ]                 # Old format versions we can read

# Keep in synch with cPickle.  This is the highest protocol number we
# know how to read.
HIGHEST_PROTOCOL = 2

# Why use struct.pack() for pickling but marshal.loads() for
# unpickling?  struct.pack() is 40% faster than marshal.dumps(), but
# marshal.loads() is twice as fast as struct.unpack()!
mloads = marshal.loads

class PickleError(Exception):
    """A common base class for the other pickling exceptions."""
    pass

class PicklingError(PickleError):
    """This exception is raised when an unpicklable object is passed to the
    dump() method.

    """
    pass

class UnpicklingError(PickleError):
    """This exception is raised when there is a problem unpickling an object,
    such as a security violation.

    Note that other exceptions may also be raised during unpickling, including
    (but not necessarily limited to) AttributeError, EOFError, ImportError,
    and IndexError.

    """
    pass

# An instance of _Stop is raised by Unpickler.load_stop() in response to
# the STOP opcode, passing the object that is the result of unpickling.
class _Stop(Exception):
    def __init__(self, value):
        self.value = value

# Jython has PyStringMap; it's a dict subclass with string keys
try:
    from org.python.core import PyStringMap
except ImportError:
    PyStringMap = None

# UnicodeType may or may not be exported (normally imported from types)
try:
    UnicodeType
except NameError:
    UnicodeType = None

# Pickle opcodes.  See pickletools.py for extensive docs.  The listing
# here is in kind-of alphabetical order of 1-character pickle code.
# pickletools groups them by purpose.

MARK            = '('   # push special markobject on stack
STOP            = '.'   # every pickle ends with STOP
POP             = '0'   # discard topmost stack item
POP_MARK        = '1'   # discard stack top through topmost markobject
DUP             = '2'   # duplicate top stack item
FLOAT           = 'F'   # push float object; decimal string argument
INT             = 'I'   # push integer or bool; decimal string argument
BININT          = 'J'   # push four-byte signed int
BININT1         = 'K'   # push 1-byte unsigned int
LONG            = 'L'   # push long; decimal string argument
BININT2         = 'M'   # push 2-byte unsigned int
NONE            = 'N'   # push None
PERSID          = 'P'   # push persistent object; id is taken from string arg
BINPERSID       = 'Q'   #  "       "         "  ;  "  "   "     "  stack
REDUCE          = 'R'   # apply callable to argtuple, both on stack
STRING          = 'S'   # push string; NL-terminated string argument
BINSTRING       = 'T'   # push string; counted binary string argument
SHORT_BINSTRING = 'U'   #  "     "   ;    "      "       "      " < 256 bytes
UNICODE         = 'V'   # push Unicode string; raw-unicode-escaped'd argument
BINUNICODE      = 'X'   #   "     "       "  ; counted UTF-8 string argument
APPEND          = 'a'   # append stack top to list below it
BUILD           = 'b'   # call __setstate__ or __dict__.update()
GLOBAL          = 'c'   # push self.find_class(modname, name); 2 string args
DICT            = 'd'   # build a dict from stack items
EMPTY_DICT      = '}'   # push empty dict
APPENDS         = 'e'   # extend list on stack by topmost stack slice
GET             = 'g'   # push item from memo on stack; index is string arg
BINGET          = 'h'   #   "    "    "    "   "   "  ;   "    " 1-byte arg
INST            = 'i'   # build & push class instance
LONG_BINGET     = 'j'   # push item from memo on stack; index is 4-byte arg
LIST            = 'l'   # build list from topmost stack items
EMPTY_LIST      = ']'   # push empty list
OBJ             = 'o'   # build & push class instance
PUT             = 'p'   # store stack top in memo; index is string arg
BINPUT          = 'q'   #   "     "    "   "   " ;   "    " 1-byte arg
LONG_BINPUT     = 'r'   #   "     "    "   "   " ;   "    " 4-byte arg
SETITEM         = 's'   # add key+value pair to dict
TUPLE           = 't'   # build tuple from topmost stack items
EMPTY_TUPLE     = ')'   # push empty tuple
SETITEMS        = 'u'   # modify dict by adding topmost key+value pairs
BINFLOAT        = 'G'   # push float; arg is 8-byte float encoding

TRUE            = 'I01\n'  # not an opcode; see INT docs in pickletools.py
FALSE           = 'I00\n'  # not an opcode; see INT docs in pickletools.py

# Protocol 2

PROTO           = '\x80'  # identify pickle protocol
NEWOBJ          = '\x81'  # build object by applying cls.__new__ to argtuple
EXT1            = '\x82'  # push object from extension registry; 1-byte index
EXT2            = '\x83'  # ditto, but 2-byte index
EXT4            = '\x84'  # ditto, but 4-byte index
TUPLE1          = '\x85'  # build 1-tuple from stack top
TUPLE2          = '\x86'  # build 2-tuple from two topmost stack items
TUPLE3          = '\x87'  # build 3-tuple from three topmost stack items
NEWTRUE         = '\x88'  # push True
NEWFALSE        = '\x89'  # push False
LONG1           = '\x8a'  # push long from < 256 bytes
LONG4           = '\x8b'  # push really big long

_tuplesize2code = [EMPTY_TUPLE, TUPLE1, TUPLE2, TUPLE3]


__all__.extend([x for x in dir() if re.match("[A-Z][A-Z0-9_]+$",x)])
del x

def _keep_alive(x, memo):
    """Keeps a reference to the object x in the memo.

    Because we remember objects by their id, we have
    to assure that possibly temporary objects are kept
    alive by referencing them.
    We store a reference at the id of the memo, which should
    normally not be used unless someone tries to deepcopy
    the memo itself...
    """
    try:
        memo[id(memo)].append(x)
    except KeyError:
        # aha, this is the first one :-)
        memo[id(memo)]=[x]


# A cache for whichmodule(), mapping a function object to the name of
# the module in which the function was found.

classmap = {} # called classmap for backwards compatibility

def whichmodule(func, funcname):
    """Figure out the module in which a function occurs.

    Search sys.modules for the module.
    Cache in classmap.
    Return a module name.
    If the function cannot be found, return "__main__".
    """
    # Python functions should always get an __module__ from their globals.
    mod = getattr(func, "__module__", None)
    if mod is not None:
        return mod
    if func in classmap:
        return classmap[func]

    for name, module in sys.modules.items():
        if module is None:
            continue # skip dummy package entries
        if name != '__main__' and getattr(module, funcname, None) is func:
            break
    else:
        name = '__main__'
    classmap[func] = name
    return name


# Unpickling machinery

class Unpickler:
    # 接受文件对象
    def __init__(self, file):
        """This takes a file-like object for reading a pickle data stream.

        The protocol version of the pickle is detected automatically, so no
        proto argument is needed.

        The file-like object must have two methods, a read() method that
        takes an integer argument, and a readline() method that requires no
        arguments.  Both methods should return a string.  Thus file-like
        object can be a file object opened for reading, a StringIO object,
        or any other custom object that meets this interface.
        """
        # binded method, 似乎可以减少函数的调用开销，不用 file. 操作了
        self.readline = file.readline
        self.read = file.read
        self.memo = {}

    def load(self):
        """Read a pickled object representation from the open file.

        Return the reconstituted object hierarchy specified in the file.
        """
        self.mark = object() # any new unique object
        self.stack = []
        self.append = self.stack.append
        read = self.read
        dispatch = self.dispatch
        try:
            while 1:
                key = read(1)
                dispatch[key](self)

            # 直接通过: stopinst返回结果
        except _Stop, stopinst:
            return stopinst.value

    # Return largest index k such that self.stack[k] is self.mark.
    # If the stack doesn't contain a mark, eventually raises IndexError.
    # This could be sped by maintaining another stack, of indices at which
    # the mark appears.  For that matter, the latter stack would suffice,
    # and we wouldn't need to push mark objects on self.stack at all.
    # Doing so is probably a good thing, though, since if the pickle is
    # corrupt (or hostile) we may get a clue from finding self.mark embedded
    # in unpickled objects.
    def marker(self):
        stack = self.stack

        # 当前对象的一个记录?
        # 还有一个问题: mark可能嵌套，如何处理呢?
        mark = self.mark
        k = len(stack)-1
        while stack[k] is not mark: k = k-1
        return k



    # 这什么写法? 似乎对齐之后的代码都是在self作用域下
    dispatch = {}

    def load_eof(self):
        raise EOFError
    dispatch[''] = load_eof

    def load_proto(self):
        # 读取协议
        proto = ord(self.read(1))
        if not 0 <= proto <= 2:
            raise ValueError, "unsupported pickle protocol: %d" % proto
    dispatch[PROTO] = load_proto

    # 协议
    # 0， 1， 2分别对应着啥?
    #
    def load_persid(self):
        pid = self.readline()[:-1]
        self.append(self.persistent_load(pid))
    dispatch[PERSID] = load_persid

    def load_binpersid(self):
        pid = self.stack.pop()
        self.append(self.persistent_load(pid))
    dispatch[BINPERSID] = load_binpersid

    def load_none(self):
        self.append(None)
    dispatch[NONE] = load_none

    def load_false(self):
        self.append(False)
    dispatch[NEWFALSE] = load_false

    def load_true(self):
        self.append(True)
    dispatch[NEWTRUE] = load_true

    def load_int(self):
        # 如何解析int
        data = self.readline()
        if data == FALSE[1:]:
            val = False
        elif data == TRUE[1:]:
            val = True
        else:
            try:
                val = int(data)
            except ValueError:
                val = long(data)
        self.append(val)
    dispatch[INT] = load_int

    def load_binint(self):
        # mloads
        # struct.pack 似乎协议差不多
        self.append(mloads('i' + self.read(4)))
    dispatch[BININT] = load_binint

    # 1个字节的int
    def load_binint1(self):
        self.append(ord(self.read(1)))
    dispatch[BININT1] = load_binint1

    # 2个字节的int
    def load_binint2(self):
        self.append(mloads('i' + self.read(2) + '\000\000'))
    dispatch[BININT2] = load_binint2

    # 两种不同格式的long
    # 一种字符串格式的：一行一个long, 以"\n"结尾
    def load_long(self):
        self.append(long(self.readline()[:-1], 0))
    dispatch[LONG] = load_long

    # 二进制格式的long
    def load_long1(self):
        n = ord(self.read(1))
        bytes = self.read(n)
        self.append(decode_long(bytes))
    dispatch[LONG1] = load_long1

    # 4字节长度的long
    def load_long4(self):
        n = mloads('i' + self.read(4))
        bytes = self.read(n)
        self.append(decode_long(bytes))
    dispatch[LONG4] = load_long4

    def load_float(self):
        self.append(float(self.readline()[:-1]))
    dispatch[FLOAT] = load_float

    # mloads
    # unpack
    def load_binfloat(self, unpack=struct.unpack):
        self.append(unpack('>d', self.read(8))[0])
    dispatch[BINFLOAT] = load_binfloat

    def load_string(self):
        rep = self.readline()[:-1]
        for q in "\"'": # double or single quote
            if rep.startswith(q):
                if len(rep) < 2 or not rep.endswith(q):
                    raise ValueError, "insecure string pickle"
                rep = rep[len(q):-len(q)]
                break
        else:
            raise ValueError, "insecure string pickle"
        self.append(rep.decode("string-escape"))  # 这种编码需要处理
    dispatch[STRING] = load_string

    def load_binstring(self):
        len = mloads('i' + self.read(4))
        self.append(self.read(len))
    dispatch[BINSTRING] = load_binstring

    def load_unicode(self):
        self.append(unicode(self.readline()[:-1],'raw-unicode-escape'))
    dispatch[UNICODE] = load_unicode

    def load_binunicode(self):
        len = mloads('i' + self.read(4))
        self.append(unicode(self.read(len),'utf-8'))
    dispatch[BINUNICODE] = load_binunicode

    def load_short_binstring(self):
        len = ord(self.read(1))
        self.append(self.read(len))
    dispatch[SHORT_BINSTRING] = load_short_binstring

    def load_tuple(self):
        k = self.marker()
        # stack当前的状态
        # k: tuple的标记
        # k + 1: ..., tuple的数据
        self.stack[k:] = [tuple(self.stack[k+1:])]
    dispatch[TUPLE] = load_tuple

    # 其他格式的tuple的处理, 不用占用 k + 1个元素
    def load_empty_tuple(self):
        self.stack.append(())
    dispatch[EMPTY_TUPLE] = load_empty_tuple

    def load_tuple1(self):
        self.stack[-1] = (self.stack[-1],)
    dispatch[TUPLE1] = load_tuple1

    def load_tuple2(self):
        self.stack[-2:] = [(self.stack[-2], self.stack[-1])]
    dispatch[TUPLE2] = load_tuple2

    def load_tuple3(self):
        self.stack[-3:] = [(self.stack[-3], self.stack[-2], self.stack[-1])]
    dispatch[TUPLE3] = load_tuple3

    def load_empty_list(self):
        self.stack.append([])
    dispatch[EMPTY_LIST] = load_empty_list

    def load_empty_dictionary(self):
        self.stack.append({})
    dispatch[EMPTY_DICT] = load_empty_dictionary

    def load_list(self):
        k = self.marker()
        self.stack[k:] = [self.stack[k+1:]]
    dispatch[LIST] = load_list

    def load_dict(self):
        k = self.marker()
        d = {}

        # items的格式
        items = self.stack[k+1:]
        for i in range(0, len(items), 2):
            key = items[i]
            value = items[i+1]
            d[key] = value
        self.stack[k:] = [d]
    dispatch[DICT] = load_dict

    # INST and OBJ differ only in how they get a class object.  It's not
    # only sensible to do the rest in a common routine, the two routines
    # previously diverged and grew different bugs.
    # klass is the class to instantiate, and k points to the topmost mark
    # object, following which are the arguments for klass.__init__.
    def _instantiate(self, klass, k):
        args = tuple(self.stack[k+1:])
        del self.stack[k:]
        instantiated = 0
        if (not args and
                type(klass) is ClassType and
                not hasattr(klass, "__getinitargs__")):
            try:
                value = _EmptyClass()
                value.__class__ = klass
                instantiated = 1
            except RuntimeError:
                # In restricted execution, assignment to inst.__class__ is
                # prohibited
                pass

        # 通过构造函数在构造: klass对象
        if not instantiated:
            try:
                value = klass(*args)
            except TypeError, err:
                raise TypeError, "in constructor for %s: %s" % (
                    klass.__name__, str(err)), sys.exc_info()[2]
        self.append(value)

    def load_inst(self):
        module = self.readline()[:-1]
        name = self.readline()[:-1]
        klass = self.find_class(module, name)
        self._instantiate(klass, self.marker())
    dispatch[INST] = load_inst

    def load_obj(self):
        # Stack is ... markobject classobject arg1 arg2 ...
        k = self.marker()
        klass = self.stack.pop(k+1)
        self._instantiate(klass, k)
    dispatch[OBJ] = load_obj

    def load_newobj(self):
        args = self.stack.pop()
        cls = self.stack[-1]
        obj = cls.__new__(cls, *args)
        self.stack[-1] = obj
    dispatch[NEWOBJ] = load_newobj

    # 例如:
    # cdjango.db.models.base
    # model_unpickle
    # 其中:
    #      c 表示GLOBAL
    #      django.db.models.base 表示module
    #      model_unpickle 表示 name
    def load_global(self):
        module = self.readline()[:-1]
        name = self.readline()[:-1]
        klass = self.find_class(module, name)

        # 首先load和构建class
        self.append(klass)
    dispatch[GLOBAL] = load_global

    def load_ext1(self):
        code = ord(self.read(1))
        self.get_extension(code)
    dispatch[EXT1] = load_ext1

    def load_ext2(self):
        code = mloads('i' + self.read(2) + '\000\000')
        self.get_extension(code)
    dispatch[EXT2] = load_ext2

    def load_ext4(self):
        code = mloads('i' + self.read(4))
        self.get_extension(code)
    dispatch[EXT4] = load_ext4

    def get_extension(self, code):
        nil = []
        obj = _extension_cache.get(code, nil)
        if obj is not nil:
            self.append(obj)
            return
        key = _inverted_registry.get(code)
        if not key:
            raise ValueError("unregistered extension code %d" % code)
        obj = self.find_class(*key)
        _extension_cache[code] = obj
        self.append(obj)

    def find_class(self, module, name):
        # Subclasses may override this
        __import__(module)
        mod = sys.modules[module]
        klass = getattr(mod, name)
        return klass

    def load_reduce(self):
        # 所有的参数已经合并成为一个tuple, 然后stack顶部为: func, params tuple, 执行完毕之后func被结果替代
        stack = self.stack
        args = stack.pop()
        func = stack[-1]
        value = func(*args)
        stack[-1] = value

        # 例如: user = model_unpickle(User, [], django.db.models.base.simple_class_factory)
        #       (model_unpickle, (model, defers, factory), data)
    dispatch[REDUCE] = load_reduce

    def load_pop(self):
        del self.stack[-1]
    dispatch[POP] = load_pop

    def load_pop_mark(self):
        k = self.marker()
        del self.stack[k:]
    dispatch[POP_MARK] = load_pop_mark

    def load_dup(self):
        self.append(self.stack[-1])
    dispatch[DUP] = load_dup

    def load_get(self):
        self.append(self.memo[self.readline()[:-1]])
    dispatch[GET] = load_get

    def load_binget(self):
        i = ord(self.read(1))
        self.append(self.memo[repr(i)])
    dispatch[BINGET] = load_binget

    def load_long_binget(self):
        i = mloads('i' + self.read(4))
        self.append(self.memo[repr(i)])
    dispatch[LONG_BINGET] = load_long_binget

    def load_put(self):
        # 例如: p0 表示将 stack最后一个元素放入 memo中
        self.memo[self.readline()[:-1]] = self.stack[-1]
    dispatch[PUT] = load_put

    def load_binput(self):
        i = ord(self.read(1))
        self.memo[repr(i)] = self.stack[-1]
    dispatch[BINPUT] = load_binput

    def load_long_binput(self):
        i = mloads('i' + self.read(4))
        self.memo[repr(i)] = self.stack[-1]
    dispatch[LONG_BINPUT] = load_long_binput

    def load_append(self):
        stack = self.stack
        value = stack.pop()
        list = stack[-1]
        list.append(value)
    dispatch[APPEND] = load_append

    def load_appends(self):
        stack = self.stack
        mark = self.marker()
        list = stack[mark - 1]
        list.extend(stack[mark + 1:])
        del stack[mark:]
    dispatch[APPENDS] = load_appends

    def load_setitem(self):
        stack = self.stack
        value = stack.pop()
        key = stack.pop()
        dict = stack[-1]
        dict[key] = value
    dispatch[SETITEM] = load_setitem

    def load_setitems(self):
        stack = self.stack
        mark = self.marker()
        dict = stack[mark - 1]
        for i in range(mark + 1, len(stack), 2):
            dict[stack[i]] = stack[i + 1]

        del stack[mark:]
    dispatch[SETITEMS] = load_setitems

    def load_build(self):
        # 调用目标对象的_setstate_
        stack = self.stack
        state = stack.pop()
        inst = stack[-1]

        # 1. 如果有 __setstate__, 则直接调用 __setstate__
        setstate = getattr(inst, "__setstate__", None)
        if setstate:
            setstate(state)
            return

        # 2. 两种state
        #    slotstate, state
        slotstate = None
        if isinstance(state, tuple) and len(state) == 2:
            state, slotstate = state


        if state:
            try:
                # 直接将state中的数据拷贝到: __dict__中
                d = inst.__dict__
                try:
                    for k, v in state.iteritems():
                        d[intern(k)] = v
                # keys in state don't have to be strings
                # don't blow up, but don't go out of our way
                except TypeError:
                    d.update(state)

            except RuntimeError:
                # XXX In restricted execution, the instance's __dict__
                # is not accessible.  Use the old way of unpickling
                # the instance variables.  This is a semantic
                # difference when unpickling in restricted
                # vs. unrestricted modes.
                # Note, however, that cPickle has never tried to do the
                # .update() business, and always uses
                #     PyObject_SetItem(inst.__dict__, key, value) in a
                # loop over state.items().
                for k, v in state.items():
                    setattr(inst, k, v)
        # slotstate
        # 属性不是通过__dict__来表示的
        if slotstate:
            for k, v in slotstate.items():
                setattr(inst, k, v)
    dispatch[BUILD] = load_build

    # 碰到mark, 则直接添加 当前的mark到 stack中
    def load_mark(self):
        self.append(self.mark)
    dispatch[MARK] = load_mark

    def load_stop(self):
        # 例如: sb. 中的"."
        value = self.stack.pop()
        raise _Stop(value)
    dispatch[STOP] = load_stop

# Helper class for load_inst/load_obj

class _EmptyClass:
    pass

# Encode/decode longs in linear time.

import binascii as _binascii

def encode_long(x):
    r"""Encode a long to a two's complement little-endian binary string.
    Note that 0L is a special case, returning an empty string, to save a
    byte in the LONG1 pickling context.

    >>> encode_long(0L)
    ''
    >>> encode_long(255L)
    '\xff\x00'
    >>> encode_long(32767L)
    '\xff\x7f'
    >>> encode_long(-256L)
    '\x00\xff'
    >>> encode_long(-32768L)
    '\x00\x80'
    >>> encode_long(-128L)
    '\x80'
    >>> encode_long(127L)
    '\x7f'
    >>>
    """

    if x == 0:
        return ''
    if x > 0:
        ashex = hex(x)
        assert ashex.startswith("0x")
        njunkchars = 2 + ashex.endswith('L')
        nibbles = len(ashex) - njunkchars
        if nibbles & 1:
            # need an even # of nibbles for unhexlify
            ashex = "0x0" + ashex[2:]
        elif int(ashex[2], 16) >= 8:
            # "looks negative", so need a byte of sign bits
            ashex = "0x00" + ashex[2:]
    else:
        # Build the 256's-complement:  (1L << nbytes) + x.  The trick is
        # to find the number of bytes in linear time (although that should
        # really be a constant-time task).
        ashex = hex(-x)
        assert ashex.startswith("0x")
        njunkchars = 2 + ashex.endswith('L')
        nibbles = len(ashex) - njunkchars
        if nibbles & 1:
            # Extend to a full byte.
            nibbles += 1
        nbits = nibbles * 4
        x += 1L << nbits
        assert x > 0
        ashex = hex(x)
        njunkchars = 2 + ashex.endswith('L')
        newnibbles = len(ashex) - njunkchars
        if newnibbles < nibbles:
            ashex = "0x" + "0" * (nibbles - newnibbles) + ashex[2:]
        if int(ashex[2], 16) < 8:
            # "looks positive", so need a byte of sign bits
            ashex = "0xff" + ashex[2:]

    if ashex.endswith('L'):
        ashex = ashex[2:-1]
    else:
        ashex = ashex[2:]
    assert len(ashex) & 1 == 0, (x, ashex)
    binary = _binascii.unhexlify(ashex)
    return binary[::-1]

def decode_long(data):
    r"""Decode a long from a two's complement little-endian binary string.

    >>> decode_long('')
    0L
    >>> decode_long("\xff\x00")
    255L
    >>> decode_long("\xff\x7f")
    32767L
    >>> decode_long("\x00\xff")
    -256L
    >>> decode_long("\x00\x80")
    -32768L
    >>> decode_long("\x80")
    -128L
    >>> decode_long("\x7f")
    127L
    """

    nbytes = len(data)
    if nbytes == 0:
        return 0L
    ashex = _binascii.hexlify(data[::-1])
    n = long(ashex, 16) # quadratic time before Python 2.3; linear now
    if data[-1] >= '\x80':
        n -= 1L << (nbytes * 8)
    return n

# Shorthands

try:
    from cStringIO import StringIO
except ImportError:
    from StringIO import StringIO

def load(file):
    return Unpickler(file).load()

def loads(str):
    # 注意这里尽可能使用cStringIO.StringIO
    file = StringIO(str)
    return Unpickler(file).load()

# Doctest

def _test():
    import doctest
    return doctest.testmod()

if __name__ == "__main__":
    _test()
