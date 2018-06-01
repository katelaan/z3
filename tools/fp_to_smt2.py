#!/usr/bin/env python3

from argparse import ArgumentParser
import struct, sys, os

def error_exit(msg, code):
    sys.stderr.write( msg + os.linesep )
    sys.exit(code)

def usage():
    global argp
    argp.print_help()
    error_exit( "",1)
    
argp = ArgumentParser()

def myparser(v):
    if v.startswith("#x"):
        return int(v[2:],16)
    if v.startswith("#b"):
        return int(v[2:],2)
    return int(v)

group = argp.add_mutually_exclusive_group(required=True)
group.add_argument("-f", "--fp", type=float, help="floating point number in python syntax" ,dest="fp")
group.add_argument("-s", "--smt", type=myparser, nargs=3, help="floating point number in smt-fp syntax" ,dest="smt")

ops = argp.parse_args()

if ops.fp:
    fpin = ops.fp

    pack = struct.pack(">f", fpin)

    s = (pack[0] & 0x80) >> 7
    e = ((pack[0] & 0x7F) << 1) | ((pack[1] & 0x80) >> 7)
    m = [int(x) for x in pack[1:]]
    m[0] = m[0] & 0x7F


    out = "(fp" 
    out += " #b" + "".join('{:01b}'.format(s))
    out += " #b" + "".join('{:08b}'.format(e))
    out += " #b" + "".join('{:07b}'.format(m[0])) + "".join('{:08b}'.format(x) for x in m[1:])
    out += " )"
    print(out)

if ops.smt:
    s = ops.smt[0]
    e = ops.smt[1]
    m = ops.smt[2]
    
    v = (-1)**s * 2**(e-127) 
    mval = 1
    for i,bit in enumerate(bin(m)[2::][::-1]):
        mval += 2**(-(i+1)) * int(bit)

    v *= mval
    print(v)
