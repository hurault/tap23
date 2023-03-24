import sys # for reading the line aguments
import pandas as pd # for read csv files
from xgboost import XGBClassifier
import xgboost as xgb
from sklearn.model_selection import train_test_split # for spliting the data
import numpy as np


def verify (instances,predictions) :
### Check monotony increasing
    nb_inst = len(instances)
    nb_broken = 0
    nb_comp = 0
    for i in range (nb_inst) :
        inst1 = instances[i]
        for j in range (i+1,nb_inst) :
            inst2 = instances[j]
            inf = True
            sup = True
            for k in range(nb_feature-1) : # the output is listed in the features
                inf = (inf and inst1[k] <= inst2[k])
                sup = (sup and inst1[k] >= inst2[k])
            if (inf==True) or (sup==True) :
                nb_comp = nb_comp + 1
            if (inf == True) and (predictions[i] > predictions[j]) :
                
                print("Monotonicity constraints have been broken for instances " + str(i) + " and " + str(j) + " :")
                print(inst1)
                print (" -> ") 
                print(predictions[i])
                print(inst2)
                print(" -> ")
                print(predictions[j])
                
                nb_broken = nb_broken+1
            if (sup == True) and (predictions[i] < predictions[j]) :
                
                print("Monotonicity constraints have been broken for instances " + str(i) + " and " + str(j) + " :")
                print(inst1)
                print (" -> ") 
                print(predictions[i])
                print(inst2)
                print(" -> ")
                print(predictions[j])
                
                nb_broken = nb_broken+1
    print ("Comparable instances : ",end="")
    print(nb_comp)
    print ("Times constraints are broken : ",end="")
    print(nb_broken)

def help() : 
    print("--------------------------------")
    print("verif the monotony (increasing) of a dataset or a model")
    print("verif_mono -m takes a model (json file) and a dataset and verify that the model is monotonic (increasing) on this dataset. \n")
    print("verif_mono -d takes a dataset and verify that the dataset is monotonic (increasing). \n")
    print("\verif_mono usage :\n")
    print("python3 verif_mono.py -m <model-json-file> <dataset-csv-file> ")
    print("example :\n python3 verif_mono.py -m models/car_evaluation.json datasets/car_evaluation.csv\n")
    print("python3 verif_mono.py -d <model-json-file> <dataset-csv-file> ")
    print("example :\n python3 verif_mono.py -d datasets/car_evaluation.csv\n")
    print("--------------------------------")
    sys.exit()

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
        ### Verify dataset
        ### read data
        csv_file = sys.argv[2]
        dataset = pd.read_csv(csv_file) # Datasets needs header
        
        ### splitting the Data
        # Number of features
        feature_names = list(dataset.columns)
        nb_feature = len(feature_names) # including the output
        # Firsts columns are the features 
        X = dataset.iloc[:,0:(nb_feature-1)]
        # Last column is the target
        Y = dataset.iloc[:,(nb_feature-1)] # not used
        verify (X.values,Y)

    else :
        help()
