#!/usr/bin/env python3
import sys, os
import subprocess as sp
import re, difflib
import json

Z3_BIN = '../build/z3'

HEADER = '\033[95m'
BLUE = '\033[94m'
GREEN = '\033[92m'
WARN = '\033[93m'
FAIL = '\033[91m'
ENDC = '\033[0m'
BOLD = '\033[1m'
UNDERLINE = '\033[4m'
        
TEST_DEF = r"([A-Za-z0-9\-]+) ([a-zA-Z /.0-9-_]+.smt2)"
ASSERT_DEF = r"[\s]+([a-zA-Z0-9-_]+) ((.*?;)+)"

TRACESTART = r"-------- \[([a-zA-Z_-]+)][ a-zA-Z_()]*([.\/a-zA-Z_]+):([0-9]+) ---------"
TRACEEND = r"------------------------------------------------"

PATHPREFIX = '../benchmarks/'

class Assert(object):

    def __init__(self):
        self.regex = r""
        self.expected = ''
        self.op = 'eq'
        self.group = 0
        self.TESTDEFS = {
            "eq":  self.test_eq,
            "lt":  self.test_lt,
            "gt":  self.test_gt
        }

    def test(self, match):
        found = match.group(self.group)
        m = re.match(self.regex, found)
        if not m:
            return False, "no match!"
        opfunc = self.TESTDEFS[self.op]
        return opfunc(m.group(1))

    def generic_reason(self,op,val):
        return " (ex:' " + str(self.expected) + "' "+str(op)+" is:'" + str(val) + "') group: " + str(self.group)

    def test_eq(self, val):
        return (int(val) == self.expected, self.generic_reason("!=", val))

    def test_lt(self, val):
        return (int(val) < self.expected, self.generic_reason(">=", val))

    def test_gt(self, val):
        return (int(val) > self.expected, self.generic_reason("=<", val))


class TraceTag(object):
    def __init__(self):
        self.tagname = ""
        self.message = ""
        self.asserts = []

    def test(self, trace_out):
        sys.stdout.write("  "*1 + self.tagname + ":")
        if not trace_out:
            sys.stdout.write(" " + FAIL +"FAIL"+ENDC + " no traces left in file!\n")
            return False
        if trace_out.tagname != self.tagname:
            sys.stdout.write(" " + FAIL +"FAIL"+ENDC + " unexpected trace tag!\n")
            return False

        m = re.search(self.message, trace_out.message)
        
        if not m:
            sys.stdout.write(" " + FAIL +"FAIL"+ENDC + " unexpected trace message!")
            return False

        ret = True
        for a in self.asserts:
            result,reason = a.test(m)
            if result:
                sys.stdout.write(" " + GREEN +"OK"+ENDC)
            else:
                sys.stdout.write(" " + FAIL +"FAIL"+ENDC + reason)
                ret = False
        sys.stdout.write("\n")
        return ret


class Test(object):
    def __init__(self):
        self.smtfile = ""
        self.name = ""
        self.stdout = ""
        self.traces = []

    def runtest(self):
        traces = set()
        for trace in self.traces:
            traces.add("-tr:"+trace.tagname)

        sys.stdout.write(BLUE+"Test '" + self.name + "' ("+self.smtfile+"):\n"+ ENDC)
        #print([Z3_BIN,self.smtfile] + list(traces))
        #stdout_is = ""
        p = sp.Popen([Z3_BIN, self.smtfile] + list(traces), stdout=sp.PIPE)
        stdout_is = p.stdout.read().decode("utf-8")
        
        stdout_is_list = stdout_is.splitlines(keepends=True)
        diff = list( difflib.ndiff(self.stdout, stdout_is_list) )

        if len(diff) > 1 or len(stdout_is_list) != len(self.stdout):
            sys.stdout.write("  "*1 + "stdout: " + FAIL+"FAIL"+ENDC + "\n")
            
            print("+++ stdout_is\n--- stdout_expected")
            print(''.join(diff), end="")
            print("--------")

        else:
            sys.stdout.write("  "*1 + "stdout: " + GREEN+"OK"+ENDC + "\n")
        try:
            f = open(".z3-trace")
        except:
            sys.stdout.write("  "*2 + FAIL +"FAIL"+ENDC + " no trace file generated!\n")

        for trace in self.traces:
            trace.test(read_next_tag(f))
        f.close()

class TraceOut(object):
    def __init__(self):
        self.tagname = ""
        self.message = ""

def read_asserts(f):
    asserts = []
    for asrt in f['asserts']:
        a = Assert()
        a.regex = asrt['text']
        a.op = asrt['op']
        a.expected = asrt['expected']
        a.group = asrt['group']
        asserts.append(a)
    return asserts


def read_traces(f):
    tags = []
    for trace in f['traces']:
        tag = TraceTag()
        tag.tagname = trace['tag']
        tag.message = trace['message']
        tag.asserts = read_asserts(trace)
        tags.append(tag)
    return tags

def read_tests(f):
    tests = []
    for testdef in f['testdefs']:
        t = Test()
        t.name = testdef['name']
        t.smtfile = PATHPREFIX + testdef['file']
        if type(testdef['stdout']) == str:
            t.stdout = testdef['stdout'].splitlines(keepends=True)
        else:
            t.stdout = testdef['stdout']
        t.traces = read_traces(testdef)
        tests.append(t)
    return tests

def read_next_tag(f):
    pos = f.tell()
    line = f.readline().rstrip("\n")
    m = re.match(TRACESTART, line)
    if not m:
        f.seek(pos)
        return None
    t = TraceOut()
    t.tagname = m.group(1)
    while True:
        line = f.readline()
        m = re.match(TRACEEND,line.rstrip("\n"))
        if m:
            break
        t.message += line
    return t
    

if len(sys.argv)!=2:
    print("usage: %s testdef.txt")
path = sys.argv[1]
f = open(path)
jf = json.load(f)
f.close()

tests = read_tests(jf)

for t in tests:
    t.runtest()
