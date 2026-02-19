#!/usr/bin/env python3
"""
Quick benchmark script for mergeSort comparison.

Runs benchmarks across different input sizes, fits n*log(n) curves
to aggregate times, and prints results. For detailed per-pattern
visualization, use bench2.py instead.
"""

import subprocess
import re
import numpy as np
from scipy.optimize import curve_fit
import matplotlib.pyplot as plt

def benchmark(i):
    result = subprocess.run(
        ['./.lake/build/bin/mergeSort', str(i)],
        capture_output=True, text=True, check=True
    )
    list_match = re.search(r'List\.mergeSort:\s+(\d+)\s+ms total', result.stdout)
    array_match = re.search(r'Array\.mergeSort:\s+(\d+)\s+ms total', result.stdout)
    if not list_match or not array_match:
        raise ValueError(f"Failed to parse output:\n{result.stdout}")
    return int(list_match.group(1)), int(array_match.group(1))

i_values = []
list_times = []
array_times = []

print("Running benchmarks...")
for i in range(1, 11):
    print(f"  Size: {i * 100_000} elements (5 runs)...", end=' ', flush=True)

    list_runs = []
    array_runs = []
    for _ in range(5):
        lt, at = benchmark(i)
        list_runs.append(lt)
        array_runs.append(at)

    list_avg = np.median(list_runs)
    array_avg = np.median(array_runs)

    i_values.append(i / 10)
    list_times.append(list_avg / 1000)
    array_times.append(array_avg / 1000)

    print(f"List: {list_avg:.0f}ms, Array: {array_avg:.0f}ms")

def model(i, A, B):
    return A * i + B * i * np.log(np.maximum(i, 1e-10))

list_popt, _ = curve_fit(model, i_values, list_times)
array_popt, _ = curve_fit(model, i_values, array_times)

print(f"\nBest fit parameters for A*i + B*i*log(i):")
print(f"  List.mergeSort:  A = {list_popt[0]:.6f}, B = {list_popt[1]:.6f}")
print(f"  Array.mergeSort: A = {array_popt[0]:.6f}, B = {array_popt[1]:.6f}")

plt.plot(i_values, list_times, 'o', label='List.mergeSort', color='blue')
plt.plot(i_values, array_times, 's', label='Array.mergeSort', color='red')
plt.plot(i_values, model(np.array(i_values), *list_popt), '-', color='blue', alpha=0.5,
         label=f'List fit: A={list_popt[0]:.3f}, B={list_popt[1]:.3f}')
plt.plot(i_values, model(np.array(i_values), *array_popt), '-', color='red', alpha=0.5,
         label=f'Array fit: A={array_popt[0]:.3f}, B={array_popt[1]:.3f}')
plt.xlabel('Input size (millions)')
plt.ylabel('Time (s)')
plt.title('MergeSort Aggregate Performance')
plt.legend()
plt.grid(True, alpha=0.3)
plt.savefig('mergeSort_comparison_simple.png', dpi=150)
print(f"\nPlot saved to mergeSort_comparison_simple.png")
plt.show()
