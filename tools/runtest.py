#!/usr/bin/env python3
import sys, os
import subprocess as sp
import psutil
import re, difflib
import json
import z3

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

Z3_ARRAY_DEF = r"^\s*\(define-fun ([A-Za-z]+) \(\) Array$$"

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
        self.stdout = None
        self.model = None
        self.loc_sort = "Int"
        self.traces = []

    def runtest(self):
        traces = set()
        for trace in self.traces:
            traces.add("-tr:"+trace.tagname)

        sys.stdout.write(BLUE+"Test '" + self.name + "' ("+self.smtfile+"):\n"+ ENDC)
        #print([Z3_BIN,self.smtfile] + list(traces))
        #stdout_is = ""
        p = psutil.Popen([Z3_BIN, self.smtfile] + list(traces), stdout=sp.PIPE)
        stdout_is = p.stdout.read().decode("utf-8")
        self.print_process_info(p)
        
        self.test_stdout(stdout_is)

        try:
            f = open(".z3-trace")
        except:
            sys.stdout.write("  "*2 + FAIL +"FAIL"+ENDC + " no trace file generated!\n")

        for trace in self.traces:
            trace.test(read_next_tag(f))
        f.close()

    def print_process_info(self, p):
        time = p.cpu_times().user
        ret = p.wait()
        sys.stdout.write("  process return code: {}\n".format(ret))
        sys.stdout.write("  total runtime (user): {}\n".format(time))


    def test_stdout(self, stdout_is):
        if(self.model):
            self.stdout_test_model(stdout_is)
        elif(self.stdout):
            self.stdout_diff(stdout_is)
    
    def stdout_diff(self,stdout_is):
        stdout_is_list = stdout_is.splitlines(keepends=True)
        self.stdout = self.stdout.splitlines(keepends=True)
        diff = list( difflib.ndiff(self.stdout, stdout_is_list) )

        if len(diff) > 1 or len(stdout_is_list) != len(self.stdout):
            sys.stdout.write("  "*1 + "stdout: " + FAIL+"FAIL"+ENDC + "\n")
            
            print("+++ stdout_is\n--- stdout_expected")
            print(''.join(diff), end="")
            print("--------")
        else:
            sys.stdout.write("  "*1 + "stdout: " + GREEN+"OK"+ENDC + "\n")

    def stdout_test_model(self,stdout_is):
        
        sys.stdout.write("  "*1 + "model: ")
        if not stdout_is.startswith("sat\n(model \n"):
            sys.stdout.write(FAIL+"FAIL"+ENDC + " could not parse model\n")
            return
        sys.stdout.write('\n')
        
        model_lines = stdout_is[12:-2].split('\n')
        next_line_is_def = False
        # translate array definitions to store calls
        for i,line in enumerate(model_lines):
            if next_line_is_def:
                tt = dict.fromkeys(map(ord, '()'), '')
                nums = line.translate(tt).split(" ")
                nums = [x for x in nums if x != ''] #remove ' ' elements
                nums_final = []
                last_was_neg = False
                for num in nums:
                    if num == "-":
                        last_was_neg
                        continue
                    if last_was_neg:
                        nums_final.append( "(- " + num + ")" )
                    else:
                        nums_final.append(num)

                expr = "((as const (Array {} Bool )) false)".format(self.loc_sort)
                for num in nums_final:
                    expr = "(store " + expr + " " + num + " true)"
                expr += ")"
                model_lines[i] = expr
                next_line_is_def = False
            else:
                m = re.match(Z3_ARRAY_DEF, line)
                if m:
                    model_lines[i] = "(define-fun {} () (Array {}  Bool) ".format(m.group(1), self.loc_sort)
                    next_line_is_def = True
        modelstring = "\n".join(model_lines)

        try:
            for model_assertion in self.model:
                sys.stdout.write("  "*2 + model_assertion + ": ")
                tmp = modelstring + "\n" + "(assert (not {}))".format(model_assertion)
                expr = z3.parse_smt2_string(tmp)
                if(z3.is_true(expr)):
                     sys.stdout.write(GREEN+"OK"+ENDC + "\n")
                else:
                    s = z3.Solver()
                    s.add(expr)
                    result = s.check()
                    if result == z3.unsat:
                        sys.stdout.write(GREEN+"OK"+ENDC + "\n")
                    elif result == z3.sat:
                        sys.stdout.write(FAIL+"FAIL"+ENDC + "\n")
                    else:
                        sys.stdout.write(WARN+"INCONCLUSIVE"+ENDC + "\n")
        except z3.Z3Exception as e:
            sys.stderr.write("{}".format(e))
            sys.stderr.write("\n")
        sys.stdout.write('\n')
        


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
        if 'stdout' in testdef:
            t.stdout = testdef['stdout']
        elif 'model' in testdef:
            t.model = testdef['model']
        if 'loc_sort' in testdef:
            t.loc_sort = testdef['loc_sort']
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
