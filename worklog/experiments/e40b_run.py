import numpy as np, sys
from multiprocessing import Pool
import e40_am_kernel as E
def job(a):
    n, r, seed = a
    v, x = E.run(n, r, 3, seed)
    return n, r, seed, v, np.round(np.abs(x[:n]) + 0.05, 4)
if __name__ == "__main__":
    jobs = [(n, r, s) for n in (4, 5, 6) for r in (1, 2, 3) for s in (1, 2, 3)]
    with Pool(27) as pool:
        for o in pool.imap_unordered(job, jobs):
            print(f"n={o[0]} rank<={o[1]} seed={o[2]}: min T = {o[3]:.3e}  p={o[4]}", flush=True)
