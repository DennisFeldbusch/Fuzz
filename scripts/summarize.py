# script to read multiple files and calculate the average of the values and the standard deviation

import sys
import numpy as np
import os
import csv
import glob
import matplotlib.pyplot as plt

# filenames hardcoded
path = sys.argv[1]
print(path)

dir = '../results/'+path+'/'

filenames = glob.glob(dir+"plot_data-*")

# files have multiple lines and each line has 2 columns separated by a space
# first column is the time and second column is the value
# we will read the second column and calculate the average and standard deviation across all files of the same time

# create a matrix to store the values
values = []
failure = []
max_time = 0
i = 0
for filename in filenames: 
    unique_data = []
    with open(filename, 'r') as f:
        reader = csv.reader(f, delimiter='\t')
        next(reader, None)

        # create an array with the size of reader
        #remove duplicates
        seen = set()
        for row in reader:
            if row[0] not in seen:
                unique_data.append(row)
                seen.add(row[0])
                max_time = max(max_time, int(row[0]))
            else: 
                unique_data.append(row)
                
        values.append([])
        failure.append([])

        for j in range(max_time+1):
            values[i].append(np.nan)
            failure[i].append(np.nan)
        

        for row in unique_data:
            values[i][int(row[0])] = row[1]
            failure[i][int(row[0])] = row[2]


    i = i + 1

f = open('../results/'+path+'/result-plot_data-avg', 'w')

values = np.array(values)
values = values.astype(np.float64)
values = values[~np.all(values == 0, axis=1)]
values = values[:, ~np.all(values == 0, axis=0)]

# forward-fill in missing values 
for i in range(len(values)):
    mask = np.isnan(values[i])
    idx = np.where(~mask,np.arange(mask.size),0)
    np.maximum.accumulate(idx, out=idx)
    values[i] = values[i][idx]

values_avg = np.nanmean(values, axis=0, where=values!=0)
values_std = np.nanstd(values, axis=0, where=values!=0)

#ci = 0.99
for i in range(len(values_avg)):
    if np.isnan(values_avg[i]):
        continue
    else:
        values_std[i] = values_std[i] * 2.58 / np.sqrt(len(values))

failure = np.array(failure)
failure = failure.astype(np.float64)
failure = failure[:, ~np.all(failure == 0, axis=0)]
failure_avg = np.mean(failure, axis=0, where=failure!=0)

f.write("time avg asmp asmm\n")
for i in range(len(values_avg)):
    # if the value is nan, then we will write 0
    if np.isnan(values_avg[i]):
        f.write(str(i) + " " + str(0) + " " + str(0) + " " + str(0) + "\n")
    else:
        f.write(str(i) + " " + str(values_avg[i]) + " " + str(values_std[i] + values_avg[i]) + " " + str(values_avg[i] - values_std[i]) + "\n")
