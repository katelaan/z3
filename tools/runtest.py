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

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

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
        print("  "*1 + self.tagname + ":", end='')
        if not trace_out:
            print(" " + FAIL +"FAIL"+ENDC + " no traces left in file!")
            return False
        if trace_out.tagname != self.tagname:
            print(" " + FAIL +"FAIL"+ENDC + " unexpected trace tag!")
            return False

        m = re.search(self.message, trace_out.message)

        if not m:
            print(" " + FAIL +"FAIL"+ENDC + " unexpected trace message!")
            return False

        ret = True
        for a in self.asserts:
            result,reason = a.test(m)
            if result:
                print(" " + GREEN +"OK"+ENDC, end='')
            else:
                print(" " + FAIL +"FAIL"+ENDC + reason, end='')
                ret = False
        print()
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
        print(BLUE+"Test '" + self.name + "' ("+self.smtfile+"):"+ ENDC)
        #print([Z3_BIN,self.smtfile] + list(traces))
        #stdout_is = ""
        if not os.path.isfile(self.smtfile):
            print(FAIL + '  Skiping test -- file does not exist' + ENDC)
        else:
            traces = {"-tr:"+trace.tagname for trace in self.traces}
            p = psutil.Popen([Z3_BIN, self.smtfile] + list(traces), stdout=sp.PIPE)
            stdout_is = p.stdout.read().decode("utf-8")
            self.print_process_info(p)

            self.test_stdout(stdout_is)
            self._check_tags()

    def _check_tags(self):
        try:
            f = open(".z3-trace")
        except:
            print("  "*2 + FAIL +"FAIL"+ENDC + " no trace file generated!")
        else:
            for trace in self.traces:
                trace.test(read_next_tag(f))
        finally:
            f.close()

    def print_process_info(self, p):
        time = p.cpu_times().user
        ret = p.wait()
        print("  process return code: {}".format(ret))
        print("  total runtime (user): {}".format(time))


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
            print("  "*1 + "stdout: " + FAIL+"FAIL"+ENDC + "")
            print("+++ stdout_is\n--- stdout_expected")
            print(''.join(diff), end="")
            print("--------")
        else:
            print("  "*1 + "stdout: " + GREEN+"OK"+ENDC)

    def stdout_test_model(self,stdout_is):

        print("  "*1 + "model: ", end='')
        if not stdout_is.startswith("sat\n(model \n"):
            print(FAIL+"FAIL"+ENDC + " could not parse model")
            return
        print()

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
                print("  "*2 + model_assertion + ": ", end='')
                tmp = modelstring + "\n" + "(assert (not {}))".format(model_assertion)
                #print('Validating model: Will check expression\n' + tmp)
                expr = z3.parse_smt2_string(tmp)

                s = z3.Solver()
                s.add(expr)
                result = s.check()
                if result == z3.unsat:
                    print(GREEN+"OK"+ENDC)
                elif result == z3.sat:
                    print(FAIL+"FAIL"+ENDC)
                else:
                    print(WARN+"INCONCLUSIVE"+ENDC)
        except z3.Z3Exception as e:
            eprint("{}".format(e))


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


def run_tests_in_file(path):
    with open(path) as f:
        jf = json.load(f)
        tests = read_tests(jf)

        for t in tests:
            t.runtest()

def json_files_in(path):
    return [os.path.join(path,f) for f in os.listdir(path)
            if os.path.isfile(os.path.join(path, f))
            if 'json' in f]

def command_line_arg_to_paths(arg):
    if arg == 'all':
        return json_files_in('../testdef')
    else:
        return [arg]

if __name__ == '__main__':
    if len(sys.argv)!=2:
        print("usage: %s testdef.json")
        exit()

    arg = sys.argv[1]
    paths = command_line_arg_to_paths(arg)
    for path in paths:
        print(BOLD + 'Running tests in {}'.format(path) + ENDC)
        run_tests_in_file(path)
