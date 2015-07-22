#include <iostream>
#include "..\..\Complan\Complan.h"
#include <Windows.h>
using namespace std;

int main()
{
  int count;
  int output_seq_of_locations[100] = {};
  int output_size = 0;
  int obs[1] = {};
  GenerateMotionPlanFor(5, 13, obs, 0, output_seq_of_locations, &output_size);
  cout << "Trajectory Length = " << output_size << endl;
  cout << "Trajectory: " << endl;
  for (count = 0; count < output_size; count++)
  {
	  cout << output_seq_of_locations[count] << endl;
  }
  /*DeleteFile("plan_opt");
  DeleteFile("plan_noopt");
  DeleteFile("z3_output");
  DeleteFile("Constraints.smt2");*/

  GenerateMotionPlanFor(10, 4, obs, 0, output_seq_of_locations, &output_size);
  cout << "Trajectory Length = " << output_size << endl;
  cout << "Trajectory: " << endl;
  for (count = 0; count < output_size; count++)
  {
	  cout << output_seq_of_locations[count] << endl;
  }

  GenerateMotionPlanFor(2, 16, obs, 0, output_seq_of_locations, &output_size);
  cout << "Trajectory Length = " << output_size << endl;
  cout << "Trajectory: " << endl;
  for (count = 0; count < output_size; count++)
  {
	  cout << output_seq_of_locations[count] << endl;
  }
  GenerateMotionPlanFor(13, 16, obs, 0, output_seq_of_locations, &output_size);
  cout << "Trajectory Length = " << output_size << endl;
  cout << "Trajectory: " << endl;
  for (count = 0; count < output_size; count++)
  {
	  cout << output_seq_of_locations[count] << endl;
  }
  GenerateMotionPlanFor(16, 13, obs, 0, output_seq_of_locations, &output_size);
  cout << "Trajectory Length = " << output_size << endl;
  cout << "Trajectory: " << endl;
  for (count = 0; count < output_size; count++)
  {
	  cout << output_seq_of_locations[count] << endl;
  }
  GenerateMotionPlanFor(2, 13, obs, 0, output_seq_of_locations, &output_size);
  
  cout << "Trajectory Length = " << output_size << endl;
  cout << "Trajectory: " << endl;
  for(count = 0; count < output_size; count++)
  {
    cout << output_seq_of_locations[count] << endl;
  }
  getchar();
  return 0;
}

