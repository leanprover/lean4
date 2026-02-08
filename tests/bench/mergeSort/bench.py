import subprocess
import numpy as np
from scipy.optimize import curve_fit
import matplotlib.pyplot as plt

# Function to run the command and capture the elapsed time from stdout
def benchmark(i):
    result = subprocess.run([f'./.lake/build/bin/mergeSort', str(i)], capture_output=True, text=True)
    elapsed_time_ms = int(result.stdout.strip())  # Assuming the time is printed as a single integer in ms
    return elapsed_time_ms / 1e3  # Convert milliseconds to seconds

# Benchmark for i = 0.1, 0.2, ..., 1.0 with 5 runs each
i_values = []
times = []

for i in range(1, 11):
    run_times = sorted([benchmark(i) for _ in range(5)])
    middle_three_avg = np.mean(run_times[1:4])  # Take the average of the middle 3 times
    times.append(middle_three_avg)
    i_values.append(i / 1e1)

# Fit the data to A*i + B*i*log(i)
def model(i, A, B):
    return A * i + B * i * np.log(i)

popt, _ = curve_fit(model, i_values, times)
A, B = popt

# Print the fit parameters
print(f"Best fit parameters: A = {A}, B = {B}")

# Plot the results
plt.plot(i_values, times, 'o', label='Benchmark Data (Avg of Middle 3)')
plt.plot(i_values, model(np.array(i_values), *popt), '-', label=f'Fit: A*i + B*i*log(i)\nA={A:.3f}, B={B:.3f}')
plt.xlabel('i')
plt.ylabel('Time (s)')
plt.legend()
plt.show()
