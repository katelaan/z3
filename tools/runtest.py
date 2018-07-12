#!/usr/bin/env python3
import sys, os
import subprocess as sp
import re

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

class Assert(object):
    def __init__(self):
        self.regex = r""
        self.expected = r""
    def __str__(self):
        return "Assert: grp1 of r'%s' matches r'%s'"

class TraceTag(object):
    def __init__(self):
        self.tagname = ""
        self.asserts = []
    def __str__(self):
        ret = "Trace: " + self.tagname
        for a in self.asserts:
            ret + "\n" + str(a)
        return ret


class Test(object):
    def __init__(self):
        self.smtfile = ""
        self.name = ""
        self.stdout = ""
        self.traces = []

class TraceOut(object):
    def __init__(self):
        self.tagname = ""
        self.message = ""

def read_asserts(f):
    tags = []
    while True:
        pos = f.tell()
        line = f.readline().rstrip("\n")
        if line.startswith("#"):
            continue
        m = re.match(ASSERT_DEF,line)
        if not m:
            f.seek(pos)
            break
        tag = TraceTag()
        tag.tagname = m.group(1)
        assertdefs = m.group(2).split(";")[:-1]
        for i in range(0,len(assertdefs)//2*2,2):
            a = Assert()
            a.regex = assertdefs[i]
            a.expected = assertdefs[i+1]
            tag.asserts.append(a)
        tags.append(tag)
    return tags

def read_tests(f):
    tests = []
    while True:
        pos = f.tell()
        line = f.readline().rstrip("\n")
        if line.startswith("#"):
            continue
        m = re.match(TEST_DEF,line)
        if not m:
            f.seek(pos)
            break
        t = Test()
        t.name = m.group(1)
        t.smtfile = m.group(2)
        t.traces = read_asserts(f)
        while True:
            pos = f.tell()
            line = f.readline()
            m = re.match(TEST_DEF,line.rstrip("\n"))
            if m or line == '':
                f.seek(pos)
                break
            t.stdout += line
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
    

def run_test(test):
    traces = set()
    for trace in test.traces:
        traces.add("-tr:"+trace.tagname)

    #print([Z3_BIN,test.smtfile] + list(traces))
    p = sp.Popen([Z3_BIN,test.smtfile] + list(traces), stdout=sp.PIPE)
    stdout_is = p.stdout.read().decode("utf-8")

    #stdout_is = ""
    sys.stdout.write(BLUE+"Test '" + test.name + "' :\n"+ ENDC)
    if test.stdout != stdout_is:
        sys.stdout.write("  "*1 + "stdout: " + FAIL+"FAIL"+ENDC + "\n")
        sys.stdout.write("  "*2 + "'" + test.stdout + "' != '" + stdout_is + "'" )
    else:
        sys.stdout.write("  "*1 + "stdout: " + GREEN+"OK"+ENDC + "\n")
    try:
        f = open(".z3-trace")
    except:
        sys.stdout.write("  "*2 + FAIL +"FAIL"+ENDC + " trace file generated!\n")

    for trace in test.traces:
        sys.stdout.write("  "*1 + trace.tagname + ":")
        trace_out = read_next_tag(f)
        if not trace_out:
            sys.stdout.write(" " + FAIL +"FAIL"+ENDC + " no traces left in file!\n")
            break
        if trace_out.tagname != trace.tagname:
            sys.stdout.write(" " + FAIL +"FAIL"+ENDC + " unexpected trace message!\n")
            break
        for a in trace.asserts:
            m = re.search(a.regex, trace_out.message)
            m2 = re.match(a.expected, m.group(1))
            #sys.stdout.write("  "*2 + "r'" + a.regex + "' r'"+ a.expected +"' ")
            if not m2:
                sys.stdout.write(" " + FAIL +"FAIL"+ENDC + " " + a.expected + "!=" + m.group(1) + "\n")
            else:
                sys.stdout.write(" " + GREEN +"OK"+ENDC + "\n")

if len(sys.argv)!=2:
    print("usage: %s testdef.txt")
path = sys.argv[1]
f = open(path)

tests = read_tests(f)
f.close()

for t in tests:
    run_test(t)



