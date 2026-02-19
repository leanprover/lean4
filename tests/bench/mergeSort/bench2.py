#!/usr/bin/env python3
"""
Benchmark script for comparing List.mergeSort and Array.mergeSort performance.

Runs benchmarks across different input sizes (100k to 1M elements),
collects per-pattern results, and generates comparison plots.
"""

import subprocess
import re
import numpy as np
import matplotlib.pyplot as plt

PATTERNS = ["Reversed", "Sorted", "Random", "Partially sorted"]

def benchmark(i):
    """
    Run the benchmark for size i * 10^5 and extract per-pattern times.

    Returns:
        dict: { pattern: (list_ms, array_ms) }
    """
    result = subprocess.run(
        ['./.lake/build/bin/mergeSort', str(i)],
        capture_output=True,
        text=True,
        check=True
    )

    results = {}
    for pattern in PATTERNS:
        m = re.search(
            rf'{re.escape(pattern)}\s*:\s*List\s+(\d+)ms,\s*Array\s+(\d+)ms',
            result.stdout
        )
        if not m:
            raise ValueError(f"Failed to parse '{pattern}' from:\n{result.stdout}")
        results[pattern] = (int(m.group(1)), int(m.group(2)))

    return results

# Benchmark for i = 1, 2, ..., 10 (100k to 1M elements) with 3 runs each
sizes = list(range(1, 11))
num_runs = 3

# { pattern: { "list": [avg_per_size], "array": [avg_per_size] } }
data = {p: {"list": [], "array": []} for p in PATTERNS}

print("Running benchmarks...")
for i in sizes:
    n = i * 100_000
    print(f"  Size: {n:>10} elements ({num_runs} runs)...", end=' ', flush=True)

    runs = {p: {"list": [], "array": []} for p in PATTERNS}

    for _ in range(num_runs):
        results = benchmark(i)
        for p in PATTERNS:
            lt, at = results[p]
            runs[p]["list"].append(lt)
            runs[p]["array"].append(at)

    parts = []
    for p in PATTERNS:
        list_avg = np.median(runs[p]["list"])
        array_avg = np.median(runs[p]["array"])
        data[p]["list"].append(list_avg)
        data[p]["array"].append(array_avg)
        parts.append(f"{p}: L={list_avg:.0f} A={array_avg:.0f}")
    print(" | ".join(parts))

sizes_k = [i * 100 for i in sizes]  # in thousands

# --- Plotting ---
fig, axes = plt.subplots(2, 2, figsize=(14, 10))
fig.suptitle('MergeSort: List vs Array by Data Pattern', fontsize=14, fontweight='bold')

colors = {"list": "#2196F3", "array": "#F44336"}

for ax, pattern in zip(axes.flat, PATTERNS):
    list_ms = np.array(data[pattern]["list"])
    array_ms = np.array(data[pattern]["array"])

    ax.plot(sizes_k, list_ms, 'o-', color=colors["list"], label='List.mergeSort', markersize=5)
    ax.plot(sizes_k, array_ms, 's-', color=colors["array"], label='Array.mergeSort', markersize=5)

    ax.set_title(pattern, fontsize=12, fontweight='bold')
    ax.set_xlabel('Size (thousands)')
    ax.set_ylabel('Time (ms)')
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    # Annotate winner at largest size
    if list_ms[-1] < array_ms[-1]:
        ratio = array_ms[-1] / list_ms[-1]
        ax.annotate(f'List {ratio:.1f}x faster', xy=(0.98, 0.95),
                    xycoords='axes fraction', ha='right', va='top',
                    fontsize=9, color=colors["list"], fontweight='bold')
    else:
        ratio = list_ms[-1] / array_ms[-1]
        ax.annotate(f'Array {ratio:.1f}x faster', xy=(0.98, 0.95),
                    xycoords='axes fraction', ha='right', va='top',
                    fontsize=9, color=colors["array"], fontweight='bold')

plt.tight_layout()
plt.savefig('mergeSort_comparison.png', dpi=150)
print(f"\nPlot saved to mergeSort_comparison.png")

# --- Speedup summary plot ---
fig2, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

# Left: ratio per pattern across sizes
for pattern in PATTERNS:
    list_ms = np.array(data[pattern]["list"])
    array_ms = np.array(data[pattern]["array"])
    ratio = array_ms / np.maximum(list_ms, 1)
    ax1.plot(sizes_k, ratio, 'o-', label=pattern, markersize=5)

ax1.axhline(y=1.0, color='gray', linestyle='--', alpha=0.5)
ax1.set_xlabel('Size (thousands)')
ax1.set_ylabel('Array time / List time')
ax1.set_title('Ratio by Pattern (< 1 = Array faster)')
ax1.legend(fontsize=9)
ax1.grid(True, alpha=0.3)

# Right: aggregate
list_total = np.zeros(len(sizes))
array_total = np.zeros(len(sizes))
for p in PATTERNS:
    list_total += np.array(data[p]["list"])
    array_total += np.array(data[p]["array"])

ax2.plot(sizes_k, list_total, 'o-', color=colors["list"], label='List (aggregate)', markersize=5)
ax2.plot(sizes_k, array_total, 's-', color=colors["array"], label='Array (aggregate)', markersize=5)
ax2.set_xlabel('Size (thousands)')
ax2.set_ylabel('Total time (ms, 4 patterns)')
ax2.set_title('Aggregate Performance')
ax2.legend(fontsize=9)
ax2.grid(True, alpha=0.3)

plt.tight_layout()
plt.savefig('mergeSort_ratio.png', dpi=150)
print(f"Plot saved to mergeSort_ratio.png")
plt.show()
