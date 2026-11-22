"""Runs an image under qemu and reports the largest number of instructions between two consecutive
system calls of one kind (one call per reactor step), the deepest stack, and the stack the image
asks for (`PT_GNU_STACK`). Usage: step-measure.py IMAGE INPUT x64|a64 read|write"""
import re, subprocess, sys, os, tempfile
img, inp, arch, kind = sys.argv[1:5]
home = os.path.expanduser("~")
q = home + "/tools/bin/qemu-x86_64" if arch == "x64" else "qemu-aarch64"
spreg = "RSP" if arch == "x64" else "SP"
log = tempfile.mktemp()
subprocess.run([q, "-one-insn-per-tb", "-d", "exec,cpu,strace,nochain", "-D", log, img],
               stdin=open(inp, "rb"), stdout=subprocess.DEVNULL)
n = 0; at = []; sp0 = None; spmin = None
sp_re = re.compile(r"\b" + spreg + r"=([0-9a-f]{16})")
call_re = re.compile(r"^\d+ " + kind + r"\(")
for line in open(log, errors="replace"):
    if line.startswith("Trace"):
        n += 1
    elif call_re.match(line):
        at.append(n)
    else:
        m = sp_re.search(line)
        if m:
            sp = int(m.group(1), 16)
            if sp0 is None: sp0 = sp
            spmin = sp if spmin is None else min(spmin, sp)
os.remove(log)
gaps = [b - a for a, b in zip(at, at[1:])]
req = subprocess.run(["readelf", "-lW", img], capture_output=True, text=True).stdout
req = int([l.split()[5] for l in req.splitlines() if "GNU_STACK" in l][0], 0)
print(f"{img}: {len(at)} {kind} calls, {n} instructions, largest step {max(gaps) if gaps else 0}, "
      f"stack {sp0 - spmin}, image's request {req}")
