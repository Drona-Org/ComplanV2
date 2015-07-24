#!/bin/bash

echo "Compiling Complan.."
echo ""

cd ../../Complan
make clean
make
cd ../Test/TestGenerateMotionPlan

echo ""
echo ""
echo "Running Complan.."
echo ""

g++ ../../Complan/*.o test.cpp -o test
./test
