struct w
{
  unsigned int length_x;
  unsigned int length_y;
  unsigned int number_of_uavs;
  position *pos_start;
  position *pos_end;
  unsigned int number_of_points;
  string total_cost;
};

typedef struct w workspace_t;


struct d
{  
  unsigned int length_x;
  unsigned int length_y;
};

typedef struct d dimension_t;


struct c
{
  float max_cost;
  float min_cost;
  float min_cost_diff;
};

typedef struct c prim_cost_t;

 
typedef std::vector<Primitive> prim_vec_t;


void readPrimitives(prim_vec_t & ); 
void writePrimitives(prim_vec_t );
void getPrimitiveCost(prim_vec_t , prim_cost_t & );
void writePrimitiveCost(prim_cost_t );
void readDimension(dimension_t &);
void writeDimension(dimension_t);
void findLocation(dimension_t , int , int &, int &);
void findIndex(dimension_t , int , int , int &);
