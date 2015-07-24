#include <iostream>

#ifdef PLAT_WINDOWS
#include "..\..\Complan\Complan.h"
#else
#include "../../Complan/Complan.h"
#endif

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
  //getchar();
  return 0;
}

