#include <iostream>
#include "..\..\Complan\Complan.h"

using namespace std;

int main()
{
  int count;
  int output_seq_of_locations[100];
  int output_size = 0;
  int obs[] = {9};
  //generateMotionPlan(5, 13, (int[0]){}, 0, output_seq_of_locations, output_size);
  //generateMotionPlan(10, 4, (int[2]){6,7}, 2, output_seq_of_locations, output_size);
  //generateMotionPlan(2, 16, (int[1]){9}, 1, output_seq_of_locations, output_size);
  generateMotionPlan(13, 16, obs, 1, output_seq_of_locations, output_size);
  //generateMotionPlan(16, 13, (int[0]){}, 0, output_seq_of_locations, output_size);
  //generateMotionPlan(2, 13, (int[2]){9}, 1, output_seq_of_locations, output_size);
  
  cout << "Trajectory Length = " << output_size << endl;
  cout << "Trajectory: " << endl;
  for(count = 0; count < output_size; count++)
  {
    cout << output_seq_of_locations[count] << endl;
  }
  return 0;
}

