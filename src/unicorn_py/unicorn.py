import os
import sys
import subprocess as sp

def emulate(program=bytearray(), args=[],
            memory=1, verbose="info", help=False):
    if (help):
        rustproc = sp.Popen([get_unicorn_path(), 'emulate', '-h'])
        (stdoutdata, stderrdata) = rustproc.communicate()
    elif (len(args)):
        write_to_file(program)
        rustproc = sp.Popen([get_unicorn_path(), 'emulate',
                             '--memory', str(memory), '-v', str(verbose),
                             "tmp", str(" ".join(str(e) for e in args))])
        (stdoutdata, stderrdata) = rustproc.communicate()
        cleanup_file()
    else:
        write_to_file(program)
        rustproc = sp.Popen([get_unicorn_path(), 'emulate', '--memory',
                             str(memory), '-v', str(verbose), "tmp"])
        (stdoutdata, stderrdata) = rustproc.communicate()
        cleanup_file()

def disassemble(program=bytearray(), verbose="info", help=False):
    if (help):
        rustproc = sp.Popen([get_unicorn_path(), 'disassemble', '-h'])
        (stdoutdata, stderrdata) = rustproc.communicate()
    else:
        write_to_file(program)
        rustproc = sp.Popen([get_unicorn_path(), 'disassemble',
                             '-v', str(verbose), "tmp"])
        (stdoutdata, stderrdata) = rustproc.communicate()
        cleanup_file()

def beator(program=bytearray(), inputs=[], bitblast=False,
           dimacs=False, compile=False, fastminimize=False,
           maxheap=8, maxstack=32, memory=1, prune=False,
           solver="generic", timeout=-1, unroll=0,
           from_btor2=False, verbose="info", help=False, out='tmp'):
    #setting all arguments with defaults
    args = [get_unicorn_path(), 'beator', "--max-heap", str(maxheap),
            "--max-stack", str(maxstack), "--memory", str(memory),
            "-s", str(solver), "-o", str(out), "-v", str(verbose)]
    #append any optional flags
    if(bitblast):
        args.append("-b")
    if(dimacs):
        args.append("-d")
    if(compile):
        args.append("-c")
    if(fastminimize):
        args.append("--fast-minimize")
    if(len(inputs)>0):
        args.append("-i")
        for e in inputs:
            args.append(str(e))
    if(prune):
        args.append("-p")
    if(timeout!=-1):
        args.append("-t")
        args.append(str(timeout))
    if(unroll):
        args.append("-u")
        args.append(str(unroll))
    if(from_btor2):
        args.append("-f")
    #append name of the temporary input file
    args.append("tmp")
    if (help):
        rustproc = sp.Popen([get_unicorn_path(), 'beator', '-h'])
        (stdoutdata, stderrdata) = rustproc.communicate()
    else:
        write_to_file(program)
        rustproc = sp.Popen(args)
        (stdoutdata, stderrdata) = rustproc.communicate()
        res = read_from_file(out)
        cleanup_file()
        return res

def qubot(program=bytearray(), inputs=[], bitblast=False, dimacs=False,
          compile=False, emulate=False, fastminimize=False, maxheap=8,
          maxstack=32, memory=1, prune=False, solver="generic",
          timeout=-1, unroll=0, frombtor2=False, verbose="info",
          help=False, out='tmp'):
    args = [get_unicorn_path(), 'qubot', "--max-heap", str(maxheap),
            "--max-stack", str(maxstack), "--memory", str(memory),
            "-s", str(solver), "-o", str(out), "-v", str(verbose)]
    if(bitblast):
        args.append("-b")
    if(dimacs):
        args.append("-d")
    if(compile):
        args.append("-c")
    if(emulate):
        args.append("-e")
    if(fastminimize):
        args.append("--fast-minimize")
    if(len(inputs)>0):
        args.append("-i")
        for e in inputs:
            args.append(str(e))
    if(prune):
        args.append("-p")
    if(timeout!=-1):
        args.append("-t")
        args.append(str(timeout))
    if(unroll):
        args.append("-u")
        args.append(str(unroll))
    if(frombtor2):
        args.append("-f")
    args.append("tmp")
    if (help):
        rustproc = sp.Popen([get_unicorn_path(), 'qubot', '-h'])
        (stdoutdata, stderrdata) = rustproc.communicate()
    else:
        write_to_file(program)
        rustproc = sp.Popen(args)
        (stdoutdata, stderrdata) = rustproc.communicate()
        res = read_from_file(out)
        cleanup_file()
        return res

def dwave(qubo, runs=1000, chainstrength=1.0, verbose='info', help=False):
    if (help):
        rustproc = sp.Popen([get_unicorn_path(), 'dwave', '-h'])
        (stdoutdata, stderrdata) = rustproc.communicate()
    else:
        write_to_file(qubo)
        rustproc = sp.Popen([get_unicorn_path(), 'dwave', '-r', str(runs),
                             '--chain-strength', str(chainstrength), 'tmp'])
        (stdoutdata, stderrdata) = rustproc.communicate()
        cleanup_file()

def syntax():
    rustproc = sp.Popen([get_unicorn_path()], stdout=sp.PIPE)
    (stdoutdata, stderrdata) = rustproc.communicate()

#returns the absolute path of the unicorn executeable
def get_unicorn_path():
    return os.path.join(os.path.dirname(__file__),'../../target/debug/unicorn')

#writes bytearrays into files for rust
def write_to_file(program):
    with open("tmp","wb") as tmp:
        tmp.write(program)
        tmp.close()

#reads file into byte array
def read_from_file(filename):
    ba = bytearray()
    if(os.path.isfile(filename)):
        f = open(filename, 'rb')
        try:
            ba = bytearray(f.read())
        except:
            cleanup_file()
        finally:
            f.close()
    return ba

#deletes temporary input file for rust and outputfiles from rust
#if no other explicit output name was given
def cleanup_file():
    try:
        os.remove("tmp")
    except:
        return
