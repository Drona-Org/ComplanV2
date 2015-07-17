#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <math.h>
#include <stdlib.h>
#include "MotionPrimitives.h"
#include "InputParser.h"
using namespace std;

void readPrimitives(prim_vec_t &primitives)
{
  ifstream ifp;

  string line;
  string str;
  int location, location1, location2, location3;
  position pos_tmp;
  int xmin, ymin, xmax, ymax;
  
  state q_i, q_f;
  position pos_f;
  string fls;
  float cost;
  pos_vec_t swath;
  position pos_min;
  position pos_max;

  ifp.open("2d_template.txt");

  if (ifp.is_open())
  {
    while (getline(ifp, line))
    {
      //cout << line << endl;
      location = line.find(":");

      if (line.substr(0, location) == "q_i")
      {
        istringstream (line.substr(location+2, 1)) >> q_i.velocity;
      }

      if (line.substr(0, location) == "q_f")
      {
	istringstream (line.substr(location+2, 1)) >> q_f.velocity;
      }

      if (line.substr(0, location) == "pos_f")
      {
        location1 = line.find('[');
        location2 = line.find(',');
        location3 = line.find(']');
        istringstream (line.substr(location1 + 1, location2 - location1 - 1)) >> pos_f.x;
        istringstream (line.substr(location2 + 2, location3 - location2 - 2)) >> pos_f.y;
      }

      if (line.substr(0, location) == "cost")
      {
        fls = line.substr(location + 1);
        istringstream (fls) >> cost;
      }

      if (line.substr(0, location) == "swath")
      {
        str = line.substr(location+1);
        xmin = 10000; ymin = 10000; xmax = -10000; ymax = -10000;
        location = str.find(';');
        while (location != -1)
        {
          location1 = str.find('[');
          location2 = str.find(',');
          location3 = str.find(']');
          istringstream (str.substr(location1 + 1, location2 - location1 - 1)) >> pos_tmp.x;
          istringstream (str.substr(location2 + 2, location3 - location2 - 2)) >> pos_tmp.y;
          swath.push_back(pos_tmp);
          if (pos_tmp.x < xmin) 
            xmin = pos_tmp.x;
          if (pos_tmp.y < ymin) 
            ymin = pos_tmp.y;
          if (pos_tmp.x > xmax) 
            xmax = pos_tmp.x;
          if (pos_tmp.y > ymax) 
            ymax = pos_tmp.y;
          str = str.substr(location+1);
          location = str.find(';');
          //cout << pos_tmp.x << "  ---  " << pos_tmp.y << endl;
        }
        location1 = str.find('[');
        location2 = str.find(',');
        location3 = str.find(']');
        istringstream (str.substr(location1 + 1, location2 - location1 - 1)) >> pos_tmp.x;
        istringstream (str.substr(location2 + 2, location3 - location2 - 2)) >> pos_tmp.y;
        //cout << pos_tmp.x << "  ---  " << pos_tmp.y << endl;
        swath.push_back(pos_tmp);
        if (pos_tmp.x < xmin) 
          xmin = pos_tmp.x;
        if (pos_tmp.y < ymin) 
          ymin = pos_tmp.y;
        if (pos_tmp.x > xmax) 
          xmax = pos_tmp.x;
        if (pos_tmp.y > ymax) 
          ymax = pos_tmp.y;
        pos_min.x = xmin;
        pos_min.y = ymin;
        pos_max.x = xmax;
        pos_max.y = ymax;        
        Primitive prim(q_i, q_f, pos_f, cost, swath, pos_min, pos_max);
        primitives.push_back(prim); 
        swath.erase (swath.begin(), swath.end());
      }
    }
    ifp.close();
  }
}


void writePrimitives(prim_vec_t primitives)
{
  unsigned int count1, count2;
  state q_i, q_f;
  position pos_f;
  string cost;
  pos_vec_t swath;
  position pos_min;
  position pos_max;

  cout << endl << "PRIMITIVES:" << endl << endl;
  for(count1 = 0; count1 < primitives.size(); count1++)
  {
    cout << "Primitive " << count1 << endl;

    q_i = primitives[count1].get_q_i();
    cout << "q_i: " << q_i.velocity << endl;

    q_f = primitives[count1].get_q_f();
    cout << "q_f: " << q_f.velocity << endl;

    pos_f = primitives[count1].get_pos_f();
    cout << "pos_f: " << pos_f.x << " " << pos_f.y << endl;

    cost = primitives[count1].get_cost();
    cout << "cost: " << cost << endl;

    swath = primitives[count1].get_swath();
    cout << "swath: ";
    for(count2 = 0; count2 < swath.size(); count2++)
    {
      cout << swath[count2].x << " " << swath[count2].y << " | ";
    }
    cout << endl;
    
    pos_min = primitives[count1].get_pos_min();
    cout << "pos_min: " << pos_min.x << " " << pos_min.y << endl;

    pos_max = primitives[count1].get_pos_max();
    cout << "pos_max: " << pos_max.x << " " << pos_max.y << endl;

    cout << endl;
  }
}


void getPrimitiveCost(prim_vec_t primitives, prim_cost_t & prim_cost)
{
  unsigned int count1, count2;
  float str1, str2;
 
  prim_cost.max_cost = 0;
  prim_cost.min_cost = 100000;
  prim_cost.min_cost_diff = 100000;

  for (count1 = 0; count1 < primitives.size(); count1++)
  {
    str1 = primitives[count1].get_cost();
    if (str1 > prim_cost.max_cost)
      prim_cost.max_cost = str1;
    if (str1 < prim_cost.min_cost)
      prim_cost.min_cost = str1;

    for (count2 = count1 + 1; count2 < primitives.size(); count2++)
    {
      str2 = primitives[count2].get_cost();
      if (fabs(str1 - str2) > 0.0001 && fabs(str1 - str2) < prim_cost.min_cost_diff)
        prim_cost.min_cost_diff = fabs(str1 - str2);
    }
  }
}


void writePrimitiveCost(prim_cost_t prim_cost)
{
  cout << endl << "PRIMITIVE COST INFORMATION:" << endl << endl;
  cout << "prim_max_cost = " << prim_cost.max_cost << endl;
  cout << "prim_min_cost = " << prim_cost.min_cost << endl;
  cout << "prim_min_cost_diff = " << prim_cost.min_cost_diff << endl;
}


void readDimension(dimension_t &dimension)
{
  ifstream ifp;
  string line;

  ifp.open("dimension.txt");
  if (ifp.is_open())
  {
    getline(ifp, line);
    istringstream (line) >> dimension.length_x;

    getline(ifp, line);
    istringstream (line) >> dimension.length_y;
  }
  else
  {
    cout << "dimension.txt file cannot be opened.." << endl;
    exit(0);
  }
}


void writeDimension(dimension_t dimension)
{
  cout << endl << "DIMENSION:" << endl << endl;
  cout << dimension.length_x << endl;
  cout << dimension.length_y << endl;
  cout << endl;
}


void findLocation(dimension_t dimension, int id, int &x, int &y)
{
  x = (id - 1) / dimension.length_x;
  y = (id - 1) % dimension.length_x;
  if (((id - 1) / dimension.length_x) %2 == 1)
  {
    y = dimension.length_y - y - 1;
  }
}


void findIndex(dimension_t dimension, int x, int y, int &id)
{
  if (x % 2 == 0 )
  {
    id = dimension.length_x * x + y + 1;
  }
  else
  {
    id = dimension.length_x * x + (dimension.length_y - y);
  }
}
