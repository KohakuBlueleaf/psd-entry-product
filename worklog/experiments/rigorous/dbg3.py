import sys
sys.argv=['run.py','6','1','100','6','3','1']
import run, rig
run.build()
T=run.T; n=run.n
for l in (0,1,18,19,20):
    print("l",l)
    for m in range(n-1):
        print("   m",m,"PJ",[c.str(6) for c in run.PJ[l][m]],"CJ",[c.str(4) for c in run.CJ[l][m]])
