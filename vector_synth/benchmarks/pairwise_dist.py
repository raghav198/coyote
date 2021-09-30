arr1 = [[1,2], [2,3], [3,4]]
arr2 = [[4,5], [5,6], [6,7]]

def calc_distance(arr1, arr2):
    output = [0] * len(arr1) * len(arr2)
    for i in range(len(arr1)):
        for j in range(len(arr2)):
            output[len(arr1) * i + j] = (arr1[i][0] + arr2[j][0]) * (arr1[i][0] + arr2[j][0]) + (arr1[i][1] + arr2[j][1]) * (arr1[i][1] + garr2[j][1]) 
    return(output)