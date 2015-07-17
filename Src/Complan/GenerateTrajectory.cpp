#include <iostream>
#include <fstream>
#include <string>
#include <stdlib.h>
#include "MotionPrimitives.h"
#include "InputParser.h"
#include "GenerateConstraints.h"
#include "Z3OutputParser.h"

using namespace std;

const unsigned int max_traj_length = 30;


void generateZ3File(prim_vec_t primitives, int length_x, int length_y, pos_vec_t obstacles, position pos_start, position pos_end, int number_of_points, float total_cost)
{
  ofstream ofp;

  ofp.open("constraints.smt2");

  /* Declare the variables */
  declareVariables(ofp, number_of_points);


  /* Write the General Constraints */
  writeInitialLocationConstraints(ofp, pos_start);
  ofp << endl;

  writeObstacleConstraints(ofp, length_x, length_y, obstacles);
  ofp << endl;

  writeTransitionConstraints(ofp, primitives, length_x, length_y, obstacles, number_of_points);
  ofp << endl;

  writeCostConstraint(ofp, number_of_points, total_cost);
  ofp << endl;

  /* Write the specification constraints */
  writeFinalDestinationConstraints(ofp, pos_end, number_of_points);

  /* Check the satisfiability of the constraints and output the model */
  ofp << "(check-sat)" << endl;
  //ofp << "(get-model)" << endl;
  writeOutputConstraints(ofp, number_of_points);

  ofp.close();
}


int generateTrajectory(prim_vec_t primitives, prim_cost_t prim_cost, int length_x, int length_y, pos_vec_t obstacles, position pos_start, position pos_end)
{
  ifstream ifp;
  string line;
  unsigned int count;
  float cost;
  ofstream ofp;

  count = 2;
  while (1)
  {
    cost = count * prim_cost.max_cost;
    generateZ3File(primitives, length_x, length_y, obstacles, pos_start, pos_end, count, cost);
    system("z3 constraints.smt2 > z3_output");

    ifp.open("z3_output");
    if (ifp.is_open())
    {
      getline(ifp, line);
      ifp.close();
    }
    if (line == "unsat")
    {
      count = count + 1;
      if (count > max_traj_length)
      {
        cout << "Trajectory does not exist.." << endl;
        exit(0);
      }
    }
    else if (line == "sat")
    {
      system("cp z3_output z3_output_sat");
      break;
    }
    else
    {
      cout << "unknown output from z3.." << endl;
      count = count + 1;
      if (count > max_traj_length)
      {
        exit(0);
      }
    }
    if (count > max_traj_length)
      break;
  }
  system("perl processoutputfile.pl");
  system("mv planner_output plan_noopt");
  return count;
}


void optimizeTrajectory(prim_vec_t primitives, prim_cost_t prim_cost, int length_x, int length_y, pos_vec_t obstacles, position pos_start, position pos_end, int trajectory_length)
{
  float max_total_cost, min_total_cost, current_cost;
  ifstream ifp;
  string line;
  ofstream ofp;

  max_total_cost = trajectory_length * prim_cost.max_cost;
  min_total_cost = trajectory_length * prim_cost.min_cost;
  current_cost = (max_total_cost + min_total_cost) / 2;

  system("mv z3_output z3_output_sat");
  while (max_total_cost - min_total_cost > prim_cost.min_cost_diff)
  {
    generateZ3File(primitives, length_x, length_y, obstacles, pos_start, pos_end, trajectory_length, current_cost);
    system("z3 constraints.smt2 > z3_output");

    ifp.open("z3_output");
    getline(ifp, line);
    ifp.close();

    if (line == "unsat")
    {
      min_total_cost = current_cost;
    }
    else if (line == "sat")
    {
      //max_total_cost = extractTrajectoryCostInformation();
      max_total_cost = current_cost;
      system("mv z3_output z3_output_sat");
    }
    else
    {
      cout << "unknown output from z3.." << endl;
      min_total_cost = current_cost;
    }
    current_cost = (max_total_cost + min_total_cost) / 2;
    //cout << "max cost = " << max_total_cost << endl;
    //cout << "min cost = " << min_total_cost << endl;
    //cout << "current cost = " << current_cost << endl;
  }

  system("mv z3_output_sat z3_output");
  system("perl processoutputfile.pl");
  system("mv planner_output plan_opt");
  //cout << "Cost  = " << extractTrajectoryCostInformation() << endl << endl;
}

