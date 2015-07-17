__declspec(dllexport)
void generateMotionPlan(
int , 		/* start location */
int , 		/* destination location */
int * , 		/* ids of the workspace blocks occupied by obstacles */
int , 		/* number of workspace blocks occupied by obstacles */
int (&)[100] , 	/* pointer to the array of locations */
int &    	/* size of the output array */
);
