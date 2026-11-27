#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 -B extract.py
"${CXX:-g++}" -std=c++17 -O2 rgbd_probe.cpp -o rgbd_probe
./rgbd_probe
