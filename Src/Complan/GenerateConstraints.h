/*
File: GenerateConstraints.h
Authors: 
Indranil Saha (isaha@cse.iitk.ac.in)
Ankush Desai(ankush@eecs.berkeley.edu)

This file is used for generating Z3 constraints.
*/

void GenerateVariableDeclarations(ofstream &ofp, int number_of_points);
void GenerateInitialLocationConstraints(ofstream &ofp, RobotPosition pos_start);
void GenerateFinalDestinationConstraints(ofstream &ofp, RobotPosition pos_end, int number_of_points);
void GenerateObstacleConstraints(ofstream &ofp, int length_x, int length_y, RobotPosition_Vector obstacles);
void GenerateTransitionConstraints(ofstream &ofp, MotionPrimitive_Vector primitives, int length_x, int length_y, RobotPosition_Vector obstacles, int number_of_points);
void GenerateCostConstraint(ofstream &ofp, int number_of_points, float total_cost);
void GenerateOutputConstraints(ofstream &ofp, int number_of_points);
string FloatToReal(float flf);
template <typename T> string ToSTR(const T& t);

#define MAX_SIZE_OF_WORKSPACE 100
