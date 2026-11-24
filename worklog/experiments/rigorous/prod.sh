#!/bin/bash
# pass A: whole compact chart q <= 24 with h = 1/100; tails; (pass B is launched separately where needed)
cd /mp34-1/math/matrix/experiments/rigorous
for n in "$@"; do
  taskset -c 32-63 ../.venv/bin/python run.py $n 24 100 6 3 32 2>&1 | tail -1 | cut -c1-600
  taskset -c 32-63 ../.venv/bin/python tails.py $n 12 24 6 100 6 100 2>&1 | tail -1
done
