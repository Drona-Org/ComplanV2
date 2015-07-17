#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <math.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "MotionPrimitives.h"
#include "InputParser.h"
#include "GenerateConstraints.h"
#include "GenerateTrajectory.h"
#include "Z3OutputParser.h"
#include "Complan.h"

using namespace std;



void generateMotionPlan(
int start_location, /* start location */
int dest_location, /* destination location */
int* list_of_obstacles, /* ids of the workspace blocks occupied by obstacles */
int number_of_obstacles, /* number of workspace blocks occupied by obstacles */
int (&output_seq_of_locations)[100], /* pointer to the array of locations */
int & output_size /* size of the output array */
)
{
  prim_vec_t primitives;
  dimension_t dimension;
  pos_vec_t obstacles;
  workspace_t workspace;
  prim_cost_t prim_cost;
  int trajectory_length;
  string line;
  int count;
  int x, y;
  position pos_start, pos_end, pos_obs;
  

  readPrimitives(primitives);
  //writePrimitives(primitives);

  getPrimitiveCost(primitives, prim_cost);
  //writePrimitiveCost(prim_cost);

  readDimension(dimension);
  //writeDimension(dimension);

  findLocation(dimension, start_location, x, y);
  pos_start.x = x;
  pos_start.y = y;

  findLocation(dimension, dest_location, x, y);
  pos_end.x = x;
  pos_end.y = y;

  for (count = 0; count < number_of_obstacles; count++)
  {
    findLocation(dimension, list_of_obstacles[count], x, y);
    pos_obs.x = x;
    pos_obs.y = y;
    obstacles.push_back(pos_obs);
  }   
  
  trajectory_length = generateTrajectory(primitives, prim_cost, dimension.length_x, dimension.length_y, obstacles, pos_start, pos_end);

  optimizeTrajectory(primitives, prim_cost, dimension.length_x, dimension.length_y, obstacles, pos_start, pos_end, trajectory_length);

  char filename[100];
  int index;
  sprintf_s(filename, 100, "%s", "plan_opt");
  vector< vector<int> > X, Y;
  X.clear();
  extractTrajectoryPositionXInformation(filename, X);
  Y.clear();
  extractTrajectoryPositionYInformation(filename, Y);
  if (X.size() != Y.size())
  {
    cout << "The size of X array is not equal to the size of Y array!!" << endl;
    exit(0);
  }
  else
  {
    output_size = (X[0]).size();
    //output_seq_of_locations[output_size];
    for (count = 0; count < output_size; count++)
    {
      //cout << (X[0])[count] << " " << (Y[0])[count] << endl;
      findIndex(dimension, (X[0])[count], (Y[0])[count], index);
      cout << index << endl;
      output_seq_of_locations[count] = index;
    }
  }
}
