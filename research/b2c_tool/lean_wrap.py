#!/usr/bin/env python3
"""Four-slot build semaphore and per-module timings, excluding semaphore wait."""
import fcntl, json, os, pathlib, resource, subprocess, sys, time
real = os.environ['B2C_REAL_LEAN']
args = ['-j4'] + sys.argv[1:]
module = next((a for a in args if a.endswith('.lean')), None)
if not module or not os.environ.get('B2C_BUILD_LOG'):
    os.execv(real,[real]+args)
lockdir=pathlib.Path(os.environ['B2C_LOCK_DIR']); lockdir.mkdir(parents=True,exist_ok=True)
while True:
    for i in range(min(4, int(os.environ.get('B2C_MAX_ACTIVE', '4')))):
        lock=open(lockdir/str(i),'w')
        try: fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB); break
        except BlockingIOError: lock.close()
    else: time.sleep(.05); continue
    break
start=time.monotonic(); before=resource.getrusage(resource.RUSAGE_CHILDREN)
rc=subprocess.call([real]+args)
after=resource.getrusage(resource.RUSAGE_CHILDREN)
row={'source':module,'module':os.path.relpath(module).removesuffix('.lean').replace('/','.'),'seconds':time.monotonic()-start,
     'cpu_seconds':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
     'exit_code':rc,'pid':os.getpid(),'start_unix':time.time()-(time.monotonic()-start),'slot':i}
with open(os.environ['B2C_BUILD_LOG'],'a') as f:
    fcntl.flock(f,fcntl.LOCK_EX); f.write(json.dumps(row)+'\n'); f.flush()
sys.exit(rc)
