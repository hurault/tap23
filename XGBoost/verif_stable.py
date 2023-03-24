import copy
import logging
import numpy as np
import pandas as pd
import sys
import csv
from xgboost import XGBClassifier
import xgboost as xgb
from sklearn.model_selection import train_test_split # for spliting the data
logging.disable(sys.maxsize)

# Function that print help for usage of the script
def help() :
    print("--------------------------------")
    print("verif the stability of a dataset or a model")
    print("verif_stable -m takes a model (json file) and a dataset and verify that the model is monotonic (increasing) on this dataset. \n")
    print("verif_stable -d takes a dataset and verify that the dataset is monotonic (increasing). \n")
    print("\verif_stable usage :\n")
    print("python3 verif_stable.py -m <model-json-file> <dataset-csv-file> ")
    print("example :\n python3 verif_stable.py -m models/car_evaluation.json datasets/car_evaluation.csv\n")
    print("python3 verif_stable.py -d <model-json-file> <dataset-csv-file> ")
    print("example :\n python3 verif_stable.py -d datasets/car_evaluation.csv\n")
    print("--------------------------------")
    sys.exit()
	
# f1 <= f2 ?
def leq(f1,f2) :
    u = True
    if (len(f1)==len(f2)) :
        for i in range(len(f1)) :
            u = (u==True and f1[i]<= f2[i])
    else :
        u = False  
    return u


# Print iterations progress
def printProgressBar (iteration, total, prefix = '', suffix = '', decimals = 1, length = 100, fill = '█', printEnd = "\r"):
    """
    Call in a loop to create terminal progress bar
    @params:
        iteration   - Required  : current iteration (Int)
        total       - Required  : total iterations (Int)
        prefix      - Optional  : prefix string (Str)
        suffix      - Optional  : suffix string (Str)
        decimals    - Optional  : positive number of decimals in percent complete (Int)
        length      - Optional  : character length of bar (Int)
        fill        - Optional  : bar fill character (Str)
        printEnd    - Optional  : end character (e.g. "\r", "\r\n") (Str)
    """
    percent = ("{0:." + str(decimals) + "f}").format(100 * (iteration / float(total)))
    filledLength = int(length * iteration // total)
    bar = fill * filledLength + '-' * (length - filledLength)
    print(f'\r{prefix} |{bar}| {percent}% {suffix}', end = printEnd)
    # Print New Line on Complete
    if iteration == total: 
        print()



def verify (instances,predictions) :
    nb_instances = len(instances)
    # sorted by classes
    index_class = {}
    nb_class = 0
    dataset_by_class = []
    for i in range(nb_instances) :
        if not (predictions[i] in index_class) :
            index_class[predictions[i]] = nb_class
            nb_class = nb_class+1
            dataset_by_class.append([])
        (dataset_by_class[index_class[predictions[i]]]).append(instances[i])


    nb_traitee = 0
    f1 = []
    f2 = []
    f3 = []
    broken = []
    printProgressBar(0, nb_instances, prefix = 'Progress:', suffix = 'Complete', length = 50)
    for c in range(nb_class) :
        datasetc = dataset_by_class[c]
        for i1 in range(len(datasetc)) :
            printProgressBar(nb_traitee, nb_instances, prefix = 'Progress:', suffix = 'Complete', length = 50)
            f1 = datasetc[i1]
            nb_traitee = nb_traitee +1
            for i3 in range(len(datasetc)) :
                if i3 != i1 :
                    f3 = datasetc[i3]
                    if leq(f1,f3) :
                        #on cherche dans les autres classes
                        for c2 in range(nb_class) :
                            if c2 != c :
                                datasetc2 = dataset_by_class[c2]
                                for i2 in range(len(datasetc2)) :
                                    f2 = datasetc2[i2]
                                    if leq(f1,f2) & leq(f2,f3) :
                                        broken.append([f1,f2,f3])

                                    
    if len(broken) > 0 :
        print("Stability constraints have been broken for instances :")
        for i in range (len(broken)) :
            print(broken[i][0])
            print(broken[i][1])
            print(broken[i][2])
            print ("\n")
        print (len(broken))
    else :
        print("Stability constraints have been respected.")


if (sys.argv[1] == "-h" or len(sys.argv) < 3):
    help()

if (sys.argv[1] == "-m") :
    ### Verify model predictions in regards of a dataset
    if  len(sys.argv) < 4:
        help()
    else :
        ### read data
        csv_file = sys.argv[3]
        dataset = pd.read_csv(csv_file) # Datasets needs header

        ### splitting the Data
        # Number of features
        feature_names = list(dataset.columns)
        nb_feature = len(feature_names) # including the output
        # Firsts columns are the features 
        X = dataset.iloc[:,0:(nb_feature-1)]
        # Last column is the target
        Y = dataset.iloc[:,(nb_feature-1)] # not used
        # Find the number of classes
        nb_classes = len(set(Y))

        
        ### Xgboost Learning API

        ### load the model
        model = xgb.Booster()
        model.load_model(sys.argv[2])

        ### Making predictions on the Test Data
        # split the data into a 0:100 train:test ratio -> ugly!
        test_size = 0.5
        X_train, X_test, y_train, y_test = train_test_split(X, Y, test_size=test_size, random_state=7)
        dtrain = xgb.DMatrix(data=X_train.values,
                            label=y_train.values)
        dtest = xgb.DMatrix(data=X_test.values,
                            label=y_test.values)
        # prediction
        y_pred_train = model.predict(dtrain)
        y_pred_test = model.predict(dtest)
        predictions_test = [round(value) for value in y_pred_test]
        predictions_train = [round(value) for value in y_pred_train]
        instances = np.concatenate((X_train.values,X_test.values))
        predictions = np.concatenate((predictions_train,predictions_test))
        verify (instances,predictions)
else :
    if (sys.argv[1] == "-d") :
        csv_file = sys.argv[2]
        dataset = pd.read_csv(csv_file) # Datasets needs header
        ### splitting the Data
        # Number of features
        feature_names = list(dataset.columns)
        nb_feature = len(feature_names) # including the output
        # Firsts columns are the features 
        X = dataset.iloc[:,0:(nb_feature-1)]
        # Last column is the target
        Y = dataset.iloc[:,(nb_feature-1)]
        verify(X.values,Y)


