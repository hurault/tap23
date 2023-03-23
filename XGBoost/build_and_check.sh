#!/bin/bash
echo "car_evaluation"
python3 build_mono.py datasets/car_evaluation.csv
echo "Monotonic ?"
python3 verif_mono.py -m models/car_evaluation.json datasets/car_evaluation.csv
echo "Stable ?"
python3 verif_stable.py -m models/car_evaluation.json datasets/car_evaluation.csv
echo "heart"
python3 build_mono.py datasets/heart.csv
echo "Monotonic ?"
python3 verif_mono.py -m models/heart.json datasets/heart.csv
echo "Stable ?"
python3 verif_stable.py -m models/heart.json datasets/heart.csv
echo "placement"
python3 build_mono.py datasets/placement.csv
echo "Monotonic ?"
python3 verif_mono.py -m models/placement.json datasets/placement.csv
echo "Stable ?"
python3 verif_stable.py -m models/placement.json datasets/placement.csv
echo "pokemon"
python3 build_mono.py datasets/pokemon.csv
echo "Monotonic ?"
python3 verif_mono.py -m models/pokemon.json datasets/pokemon.csv
echo "Stable ?"
python3 verif_stable.py -m models/pokemon.json datasets/pokemon.csv