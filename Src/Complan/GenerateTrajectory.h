/*
File: GenerateTrajectory.h
Authors:
Indranil Saha (isaha@cse.iitk.ac.in)
Ankush Desai(ankush@eecs.berkeley.edu)

This file is used for generating the trajectory, as a sequence of the motion primitives.
*/

bool GenerateTrajectory(MotionPrimitive_Vector , MotionPrimitive_Cost , int , int , RobotPosition_Vector , RobotPosition , RobotPosition, int*);
void OptimizeTrajectory(MotionPrimitive_Vector , MotionPrimitive_Cost , int , int , RobotPosition_Vector , RobotPosition , RobotPosition , int );
