import pandas as pd # for read csv files
import sys # for reading the line aguments
from xgboost import XGBClassifier
import xgboost as xgb
from sklearn.model_selection import train_test_split # for spliting the data
from sklearn.metrics import accuracy_score # for calculte the accuracy

if (sys.argv[1] == "-h" or len(sys.argv) < 2):
    print("--------------------------------")
    print("build_mono takes a dataset (csv file) and will generate a model file for a monotonic classifier for said dataset. \n")
    print("all features should be monotonic increasing\n")
    print("\nbuild_mono usage :\n")
    print("python3 build_mono.py <dataset-csv-file> ")
    print("example :\n python3 build_mono.py datasets/car_evaluation.csv")
    print("--------------------------------")
    sys.exit()


### read data
csv_file = sys.argv[1]
dataset = pd.read_csv(csv_file) # Datasets needs header

### splitting the Data
# Number of features
feature_names = list(dataset.columns)
nb_feature = len(feature_names) # including the output
# Firsts columns are the features 
X = dataset.iloc[:,0:(nb_feature-1)]
# Last column is the target
Y = dataset.iloc[:,(nb_feature-1)]
# Find the number of classes
nb_classes = len(set(Y))
# split the data into a 67:33 train:test ratio
test_size = 0.33
X_train, X_test, y_train, y_test = train_test_split(X, Y, test_size=test_size, random_state=7)

### Training the XGBoost Model

### Xgboost Learning API
dtrain = xgb.DMatrix(data=X_train.values,
                     label=y_train.values)
dtest = xgb.DMatrix(data=X_test.values,
                     label=y_test.values)

# parameters of learning
# create the monotony constraint : all increasing
feature_monotones = [1] * (len(feature_names)-1)

params = {
    'objective' : "multi:softmax",
    'num_class' : nb_classes,
    'verbosity': 0,  # 0 is silent, 3 is debug
    'monotone_constraints' : '(' + ','.join([str(m) for m in feature_monotones]) + ')',# Monotony constraints
    'booster' : 'gbtree'
}

# Use CV to find the best number of trees
bst_cv = xgb.cv(params, dtrain, 500, nfold = 2, early_stopping_rounds=10)

model = xgb.train(params=params,
                dtrain=dtrain,
                num_boost_round = bst_cv.shape[0],
                verbose_eval=None)

### Making predictions on the Test Data
y_pred = model.predict(dtest)
predictions = [round(value) for value in y_pred]

### Testing the XGBoost Model Performance
accuracy = accuracy_score(y_test, predictions)
print("Accuracy: %.2f%%" % (accuracy * 100.0))


### Saving the model
# Get the name of the dataset
dirs = sys.argv[1].split('/')
name = (dirs[len(dirs)-1].split('.'))[0]
model.save_model("models/"+name+".json")
# model.save_model("models/"+name+".txt") # Not needed both format
