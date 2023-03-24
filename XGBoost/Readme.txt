Generation of monotonic models using XGBoost

Files :
    - build_mono.py : build monotonic classifier (the model is generated in the models directory)
    - predict.py : run a classifier
    - verif_mono.py : check if a model or a dataset is monotonic
    - verif_stable : check if a model or a dataset is stable
    - build_and_check.sh : build the four models (car_evaluation, heart, pokemon and placement) and check monotony and stability

datasets :
    - the four datasets (csv)

Usage : 
./build_and_check.sh 
