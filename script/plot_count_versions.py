import matplotlib.pyplot as plt
import pandas as pd
import numpy as np
import sys
from io import StringIO

# Reading data from stdin
input_data = sys.stdin.read()

# Using StringIO to simulate a file-like object for pandas
data_io = StringIO(input_data)

# Reading data into DataFrame
df = pd.read_csv(data_io, sep="\s+", names=['Version', 'Count'])

# Splitting versions into prefix and suffix
df['Prefix'] = df['Version'].apply(lambda x: x.split('-')[0])
df['Suffix'] = df['Version'].apply(lambda x: '-'.join(x.split('-')[1:]) if '-' in x else '')

# Grouping and summing by prefix
grouped = df.groupby('Prefix').sum().reset_index()

# Setting the color map
color_map = {'': 'blue'}  # Default color for versions without suffix
suffixes = df['Suffix'].unique()
greens = plt.cm.Greens(np.linspace(0.3, 0.9, len(suffixes)))

for i, suffix in enumerate(suffixes):
    if suffix:  # Assign green shades to versions with suffixes
        color_map[suffix] = greens[i]

# Plotting the bar chart with new color scheme
plt.figure(figsize=(10, 6))
for prefix in grouped['Prefix']:
    subset = df[df['Prefix'] == prefix]
    bottom = 0
    for _, row in subset.iterrows():
        color = color_map[row['Suffix']]
        plt.bar(prefix, row['Count'], bottom=bottom, label=row['Version'], color=color)
        bottom += row['Count']

plt.title('Version Contributions with Distinctive Colors')
plt.xlabel('Version Prefix')
plt.ylabel('Count')
plt.xticks(rotation=45)
plt.legend(title='Version', bbox_to_anchor=(1.05, 1), loc='upper left')

# Save to a file
output_file_path = 'version_contribution_chart_colored.png'
plt.savefig(output_file_path)
