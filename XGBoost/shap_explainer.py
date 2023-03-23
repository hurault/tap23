import sys # for reading the line aguments
from xgboost import XGBClassifier
import xgboost as xgb
import shap
import pandas as pd # for read csv files
import numpy as np
from types import SimpleNamespace
from shap import Explanation
from shap.plots import waterfall

if (len(sys.argv) < 3 or sys.argv[1] == "-h"):
    print("--------------------------------")
    print("shap_explainer takes a model (json file) and a dataset and explain the prediction of the model on the dataset. \n")
    print("\shap_explainer usage :\n")
    print("python3 shap_explainer <model-json-file> <dataset-csv-file>")
    print("example :\n python3 shap_explainer.py models/car_evaluation.json datasets/car_evaluation.csv \n")
    print("--------------------------------")
    sys.exit()

### load the model
model = xgb.Booster()
model.load_model(sys.argv[1])


### read data
csv_file = sys.argv[2]
dataset = pd.read_csv(csv_file) # Datasets needs header
### splitting the Data
# Number of features
feature_names = list(dataset.columns)
nb_feature = len(feature_names) # including the output
# Firsts columns are the features 
X = dataset.iloc[:,0:(nb_feature-1)]

# explain the model
# (same syntax works for LightGBM, CatBoost, scikit-learn, transformers, Spark, etc.)
explainer = shap.Explainer(model)
shap_values = explainer(X)

# afficher les valeurs SHAP pour la première observation avec la "base value"
exp = Explanation(shap_values.values[:,:,1], 
                  shap_values.base_values[:,1], 
                  data=X.values, 
                  feature_names=X.columns)
shap.plots.beeswarm(exp)