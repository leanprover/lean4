# 28 March 21:34  
- file: 2023-03-28-3.ipynb
- indistinguishable ish
- We need to figure out what gave dramatic performance delta previously.
#### Hypotheses:

0. Note that the `time_elapsed_ms` that I gather now is the time spent *in Lean*.
   Previously, I gathered *total elapsed time* across the run of *make*.
   I decided to gather time inside lean, since it's much easier than having
   to also wrap around the per-file compilation in CMake madness, but this is
   not the info we need, potentially. If there is a code size reduction due to 
   better reset/reuse, then we should measure the time elapsed in leanc, or 
   as a proxy, the file size that's generated. Get file size by grabbing file.
1. Try the benching setup directly on Mac, maybe M1 is just better.
2. Directly make the change in the source code, rather than querying the runtime each time 
   for ctor enabled or disabled.
3. We currently also bench *everything* via the LEAN_RUNTIME_STATS.
   Bench *only* the time delta.

#### Sensible next experiments to try:

- First try 2+3, since this is closest to the baseline benching setup.
- Also try 2+3 on macbook, since this is exactly the baseling benching setup.

# 27 Mar 16:23 

