void declareVariables(ofstream & , int );
void writeInitialLocationConstraints(ofstream & , position );
void writeFinalDestinationConstraints(ofstream & , position, int );
void writeObstacleConstraints(ofstream & , int , int , pos_vec_t );
void writeTransitionConstraints(ofstream & , prim_vec_t , int , int , pos_vec_t , int );
void writeCostConstraint(ofstream & , int , float );
void writeOutputConstraints(ofstream & , int );
string floatToReal(float );
template <typename T> string tostr(const T& );

#define MAX_SIZE_OF_WORKSPACE 100
