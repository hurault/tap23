import sys # for reading the line aguments
import xgboost as xgb

if (len(sys.argv) < 3 or sys.argv[1] == "-h"):
    print("--------------------------------")
    print("predict takes a model (json file), an instance and will make a prediction. \n")
    print("predict usage :\n")
    print("python3 predict.py <model-json-file> ([feature 1],...,[feature n])")
    print("example :\n python3 predict.py models/car_evaluation.json \"(-3,-3,2,2,0,0)\"\n")
    print("--------------------------------")
    sys.exit()


### load the model
model = xgb.Booster()
model.load_model(sys.argv[1])

### create the instance
st = (sys.argv[2].replace(" ", "")) #remove space
st = st[1:len(st)-1] # remove ( and )
fs = st.split(',') # separate each feature
instance = [float(f) for f in fs] # converte the feature into float
di = xgb.DMatrix([instance])

pred = model.predict(di)
print (round(pred[0]))