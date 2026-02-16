#!/usr/bin/env python3
"""
Benchmark script for comparing List.mergeSort and Array.mergeSort performance.

Runs benchmarks across different input sizes (100k to 1M elements),
fits performance curves, and generates comparison plots.
"""

import subprocess
import re
import numpy as np
from scipy.optimize import curve_fit
import matplotlib.pyplot as plt

def benchmark(i):
    """
    Run the benchmark for size i * 10^5 and extract List and Array times.

    Returns:
        tuple: (list_time_ms, array_time_ms) in milliseconds
    """
    result = subprocess.run(
        ['./.lake/build/bin/mergeSort', str(i)],
        capture_output=True,
        text=True,
        check=True
    )

    # Parse output like:
    # List.mergeSort:  34 ms total, 8 ms average
    # Array.mergeSort: 60 ms total, 15 ms average
    list_match = re.search(r'List\.mergeSort:\s+(\d+)\s+ms total', result.stdout)
    array_match = re.search(r'Array\.mergeSort:\s+(\d+)\s+ms total', result.stdout)

    if not list_match or not array_match:
        raise ValueError(f"Failed to parse benchmark output:\n{result.stdout}")

    list_time = int(list_match.group(1))
    array_time = int(array_match.group(1))

    return list_time, array_time

# Benchmark for i = 1, 2, ..., 10 (100k to 1M elements) with 5 runs each
i_values = []
list_times = []
array_times = []

print("Running benchmarks...")
for i in range(1, 11):
    print(f"  Size: {i * 100_000} elements (5 runs)...", end=' ', flush=True)

    list_runs = []
    array_runs = []

    for _ in range(5):
        list_time, array_time = benchmark(i)
        list_runs.append(list_time)
        array_runs.append(array_time)

    # Take average of middle 3 times to reduce noise
    list_middle_avg = np.mean(sorted(list_runs)[1:4])
    array_middle_avg = np.mean(sorted(array_runs)[1:4])

    i_values.append(i / 10)  # Convert to units of 1M elements
    list_times.append(list_middle_avg / 1000)  # Convert to seconds
    array_times.append(array_middle_avg / 1000)  # Convert to seconds

    print(f"List: {list_middle_avg:.0f}ms, Array: {array_middle_avg:.0f}ms")

# Fit the data to A*i + B*i*log(i) (expected complexity for merge sort)
def model(i, A, B):
    return A * i + B * i * np.log(i)

# Fit both curves
list_popt, _ = curve_fit(model, i_values, list_times)
array_popt, _ = curve_fit(model, i_values, array_times)

A_list, B_list = list_popt
A_array, B_array = array_popt

print("\nBest fit parameters for A*i + B*i*log(i):")
print(f"  List.mergeSort:  A = {A_list:.6f}, B = {B_list:.6f}")
print(f"  Array.mergeSort: A = {A_array:.6f}, B = {B_array:.6f}")

# Calculate speedup
speedups = [l / a for l, a in zip(list_times, array_times)]
avg_speedup = np.mean(speedups)
print(f"\nAverage speedup (Array vs List): {avg_speedup:.2f}x")

# Plot the results
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

# Plot 1: Absolute performance
ax1.plot(i_values, list_times, 'o', label='List.mergeSort (data)', color='blue')
ax1.plot(i_values, array_times, 's', label='Array.mergeSort (data)', color='red')
ax1.plot(i_values, model(np.array(i_values), *list_popt), '-',
         label=f'List fit: A={A_list:.3f}, B={B_list:.3f}', color='blue', alpha=0.5)
ax1.plot(i_values, model(np.array(i_values), *array_popt), '-',
         label=f'Array fit: A={A_array:.3f}, B={B_array:.3f}', color='red', alpha=0.5)
ax1.set_xlabel('Input size (millions of elements)')
ax1.set_ylabel('Time (seconds)')
ax1.set_title('MergeSort Performance Comparison')
ax1.legend()
ax1.grid(True, alpha=0.3)

# Plot 2: Speedup
ax2.plot([iv * 1_000_000 for iv in i_values], speedups, 'o-', color='green')
ax2.axhline(y=1.0, color='gray', linestyle='--', alpha=0.5, label='Equal performance')
ax2.set_xlabel('Input size (elements)')
ax2.set_ylabel('Speedup (List time / Array time)')
ax2.set_title(f'Array.mergeSort Speedup (avg: {avg_speedup:.2f}x)')
ax2.legend()
ax2.grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('mergeSort_comparison.png', dpi=150)
print(f"\nPlot saved to mergeSort_comparison.png")
plt.show()
