'''
this script checks all python scripts in src directory
it runs every script, detects pass/failure based on return code, and report that
'''

import os
import glob
import subprocess

all_fpaths = glob.glob(os.path.join(os.path.dirname(__file__), 'src/*.py'))
all_fpaths.sort()

for fpath in all_fpaths:
    completed = subprocess.run(
        ["python", fpath], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    retcode = completed.returncode
    status = 'PASSED' if retcode == 0 else 'FAILED (%d)' % retcode
    bname = os.path.basename(fpath)
    print('%s: %s' % (bname, status))
