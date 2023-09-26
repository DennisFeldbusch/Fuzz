# script to read multiple files and calculate the average of the values and the standard deviation

import sys
import numpy as np

# filenames hardcoded
filenames = ['../jqf-ga5-01/plot_data', '../jqf-ga5-02/plot_data','../jqf-ga5-03/plot_data']
# files have multiple lines and each line has 2 columns separated by a space
# first column is the time and second column is the value
# we will read the second column and calculate the average and standard deviation across all files of the same time

# create a matrix to store the values
values = [[], [],[]]
time = [[], [],[]]
i = 0
for filename in filenames: 
    # open the file
    f = open(filename, 'r')
    # read all lines
    lines = f.readlines()
    # close the file
    f.close()
    # initialize the array to store the values
    # loop over all lines
    for line in lines:
        # split the line into two columns
        columns = line.split()
        # convert the second column to a float and append to the array
        values[i].append(int(columns[1]))
        time[i].append(int(columns[0]))
    i = i + 1


f = open('plot_data-ga5', 'a')
for i in range(len(values[0])):
    # calculate the average and standard deviation of the values at the same time
    avg = np.average([values[0][i], values[1][i], values[2][i]])
    std = np.std([values[0][i], values[1][i], values[2][i]])
    time_avg = np.average([time[0][i], time[1][i], time[2][i]])
    # print the time, average and standard deviation
    print(time_avg, avg, avg-std, avg+std)
    ## write to file
    f.write(str(time_avg) + " " + str(avg) + " " + str(avg-std) + " " + str(avg+std) + "\n")