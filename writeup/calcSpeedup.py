import os

data = open("speedupData.txt", "r")
data_lines = data.readlines()

vectorSum = 0
scalarSum = 0
for i in data_lines:
    i = i.split(",")
    vectorSum += int(i[2])
    scalarSum += int(i[6])

print(scalarSum/vectorSum)
    