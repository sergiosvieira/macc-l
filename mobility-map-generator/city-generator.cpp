
/******************************************************
// c++ code for creating topologies for city environment
// Josiane Nzouonta 
// created 3/13/2006
// Update 6/22/2006
// 01/15/2007
Include the generation of a new file to 
contain the macroscopic movement of the nodes.
This file contains the segment and road id
that each node traverses for the duration of 
the simulation



********************************************************/
#include <algorithm>
#include <iostream>
#include <cstdlib>
#include <time.h>
#include <list>
#include <vector>
#include <fstream>
#include <cstring>
#include <math.h>
#include <cstdio>
#include <map>

#define MEMORYLESS
//#define DEBUG

using namespace std;


enum carMove {LEFT, RIGHT, STRAIGHT, UTURN};
enum trafficLightColor {RED, YELLOW, GREEN};
//enum trafficLightColor {GREEN};


const double RED_LIGHT_LENGTH = 9.0;
const double YELLOW_LIGHT_LENGTH = 4.0;
const double GREEN_LIGHT_LENGTH = 11.0;

//const double RED_LIGHT_LENGTH = 5.0;
//const double YELLOW_LIGHT_LENGTH = 1.0;
//const double GREEN_LIGHT_LENGTH = 4.0;

vector<int> ns_id_vect;
bool start_ns_printing = false;
int max_num_cars;
int method;
int warm_up;

struct car {
  float x;
  float y;
  int id;
  float desiredv;
  float currv;
  float destx;
  float desty;
  float prevx;
  float prevy;
  float prevv;
  float maxv;
  float minv;
  int targetlane;
  int presentlane;
  int preferredlane;
  int road_segment_id;
  int nextsegment;
	int prevsegment;
  carMove nextmove;
  bool intransition;
  bool changed_end_dest;
  bool within_end_intersect;
  bool reentry;
  int ns2_id;
  bool freeze;
  bool printed_ns2;
  string macroscopic_mvt;
};

struct road_lane {
  int road_lane_id;
  list<car> lane;
  list<car> waitlist;
  double xstart;
  double ystart;
  double xend;
  double yend;
  double const_b;
};


struct road_segment {
  int road_segment_id;
  int road_id;
  vector<road_lane> lanes;
  bool firstsegment;
  bool entry_segment;
  int segment_flow;
  int segment_flow_param;
  int entrysegm_flow_param;
  int start_intersect_id;
  int end_intersect_id;
  int end_light_id;
  double slope_a;
  double const_b;
  bool is_vertical;
  double xstart;
  double ystart;
  double xend;
  double yend;
  double vectx;
  double vecty;
};

struct road {
  int road_id;
  int flow;
  int flow_param;
  double avg_speed;
  bool entryroad;
  vector<int> segments;
};

struct trafficLight {
  int light_id;
  trafficLightColor color;
  double length;
  int road_id;
};

struct intersection {
  vector<int> entry;
  vector<int> exit;
  vector<int> exitflows;
  vector<int> lights;
  int intersection_id;
  double xpos;
  double ypos;
  bool entry_intersect;
  bool steady_state_flag;
};

struct mapstruct {
  vector<road> roads;
  vector<road_segment> segments;
  vector<intersection> intersections;
  vector<trafficLight> lights;
  double lanewidth;
  double default_braking;
};


bool startString(string s1, string tofind) {
  if (s1.find(tofind, 0) != string::npos && s1.find(tofind, 0) == 0)
    return true;
  else
    return false;		
}




double mypow (double x, int power) {
  double result = x;
  for (int i=2; i<=power; i++) {
    result =  result * x;
  }
  return result;
}



float dist_in_x(float hyp, float base) {
  return sqrt(mypow(hyp,2) - mypow(base, 2));
}

float find_distance(float x, float y) {
  return sqrt(mypow(x,2) + mypow(y,2));
}

float find_distance(float x1, float y1, float x2, float y2) {
  return sqrt(mypow(x1-x2,2) + mypow(y1-y2,2));
}

float find_distance(mapstruct &themap, list<car>::iterator iter, int sgid, int laneid, bool usex=true) {
  double tmp, xstart, ystart, xend, yend, x2, y2;

  xstart = themap.segments[sgid].lanes[laneid].xstart;
  ystart = themap.segments[sgid].lanes[laneid].ystart;
  xend = themap.segments[sgid].lanes[laneid].xend;
  yend = themap.segments[sgid].lanes[laneid].yend;

  if (usex) {
    x2 = iter->x;
    y2 = iter->y;
  }
  else {
    x2 = iter->prevx;
    y2 = iter->prevy;
  }

  // get projection onto segment
  if (themap.segments[sgid].is_vertical) {
    x2 = xend;
  }
  else if (themap.segments[sgid].slope_a == 0) {
    y2 = yend;
  }
  else {
    double perpendi_slope = -1/themap.segments[sgid].slope_a;
    double perpendi_const = y2 - perpendi_slope*x2;
    double thisline_const = ystart - themap.segments[sgid].slope_a*xstart;

    x2 = (thisline_const - perpendi_const)/(perpendi_slope - themap.segments[sgid].slope_a);
    y2 = themap.segments[sgid].slope_a *x2 + thisline_const;
  }

  // compute distances
  tmp = find_distance(xstart, ystart, x2, y2);
 
  if (find_distance(xend, yend, x2, y2) > find_distance(xend, yend, xstart, ystart) ) {
    tmp = -1*tmp;
  }

  return tmp;
}



bool are_parallel(road_segment segm1, road_segment segm2) {
  
  double det = segm1.vectx*segm2.vecty - segm1.vecty*segm2.vectx;
  if (det == 0)
    return true;
  else
    return false;
}



//mapstruct &themap, 
bool are_parallel_approx(road_segment segm1, road_segment segm2) {
  
double same_x, same_y, diff1_x, diff1_y;
double diff2_x, diff2_y, vect1_x, vect1_y, vect2_x, vect2_y;
double unit1_x, unit1_y, unit2_x, unit2_y;
if (segm1.end_intersect_id == segm2.end_intersect_id) {
	same_x = segm1.xend;
	same_y = segm1.yend;
	diff1_x = segm1.xstart;
	diff1_y = segm1.ystart;
	diff2_x = segm2.xstart;
	diff2_y = segm2.ystart;

}
else if (segm1.end_intersect_id == segm2.start_intersect_id) {
	same_x = segm1.xend;
	same_y = segm1.yend;
	diff1_x = segm1.xstart;
	diff1_y = segm1.ystart;
	diff2_x = segm2.xend;
	diff2_y = segm2.yend;
}
else if (segm1.start_intersect_id == segm2.end_intersect_id) {
	same_x = segm1.xstart;
	same_y = segm1.ystart;
	diff1_x = segm1.xend;
	diff1_y = segm1.yend;
	diff2_x = segm2.xstart;
	diff2_y = segm2.ystart;
}
else if (segm1.start_intersect_id == segm2.start_intersect_id) {
	same_x = segm1.xstart;
	same_y = segm1.ystart;
	diff1_x = segm1.xend;
	diff1_y = segm1.yend;
	diff2_x = segm2.xend;
	diff2_y = segm2.yend;
}

	vect1_x = diff1_x - same_x;
	vect1_y = diff1_y - same_y;
	//vect2_x = diff1_x - diff2_x;
	//vect2_y = diff1_y - diff2_y;
	vect2_x = diff2_x - same_x;
	vect2_y = diff2_y - same_y;

	unit1_x = vect1_x/find_distance(vect1_x, vect1_y);
	unit1_y = vect1_y/find_distance(vect1_x, vect1_y);
	unit2_x = vect2_x/find_distance(vect2_x, vect2_y);
	unit2_y = vect2_y/find_distance(vect2_x, vect2_y);
	
	double theta;
	theta = acos(unit1_x*unit2_x + unit1_y*unit2_y);
	theta = theta*180/((double)22/(double)7);
	if (15 < theta && theta < 165) 
		return false;
	else
		return true;

}


double find_lanesegm_length (mapstruct &themap, int sgid, int laneid) {
  double xstart = themap.segments[sgid].lanes[laneid].xstart;
  double ystart = themap.segments[sgid].lanes[laneid].ystart;
  double xend = themap.segments[sgid].lanes[laneid].xend;
  double yend = themap.segments[sgid].lanes[laneid].yend;

  return find_distance(xstart, ystart, xend, yend);
}



double find_offset_on_lane (mapstruct &themap, int sgid, int laneid, float x, float y) {

  // will make use of 2D math vector formulas
  double xstart = themap.segments[sgid].lanes[laneid].xstart;
  double ystart = themap.segments[sgid].lanes[laneid].ystart;
  double xend = themap.segments[sgid].lanes[laneid].xend;
  double yend = themap.segments[sgid].lanes[laneid].yend;

  double vectx = xend - xstart;  
  double vecty = yend - ystart; 
  //double segmlength = find_distance (vectx, vecty);
  double offset = 0;
  if (themap.segments[sgid].is_vertical)
    offset = (y - ystart)/vecty;
  else
    offset = (x - xstart)/vectx;

  return offset;
}


void find_position_lane (mapstruct &themap, int sgid, int laneid, double dist, float &x, float &y) {

  // will make use of 2D math vector formulas
  double xstart = themap.segments[sgid].lanes[laneid].xstart;
  double ystart = themap.segments[sgid].lanes[laneid].ystart;
  double xend = themap.segments[sgid].lanes[laneid].xend;
  double yend = themap.segments[sgid].lanes[laneid].yend;

  double vectx = xend - xstart;  
  double vecty = yend - ystart; 
  double lanelength = find_distance (vectx, vecty);
  double offset = dist/lanelength;

  x = xstart + offset*vectx;
  y = ystart + offset*vecty;

  return;
}

void intersect_two_lanes (mapstruct &themap, int segm1, int lane1, int segm2, int lane2, float &x, float &y) {

  if (themap.segments[segm1].is_vertical && themap.segments[segm2].is_vertical) {
			double newdestlength =
						find_distance(themap.segments[segm1].lanes[lane1].xstart, 
															themap.segments[segm1].lanes[lane1].ystart, 
															themap.segments[segm1].lanes[lane1].xend, 
															themap.segments[segm1].lanes[lane1].yend);
			newdestlength += themap.lanewidth * 2;
			find_position_lane (themap, segm1, lane1, newdestlength, x, y);			
  }
  else if (themap.segments[segm1].is_vertical &&
					 !themap.segments[segm2].is_vertical) {
    x = themap.segments[segm1].lanes[lane1].const_b;
    y = themap.segments[segm2].slope_a*x +
				themap.segments[segm2].lanes[lane2].const_b;
  }
  else if (themap.segments[segm2].is_vertical &&
					 !themap.segments[segm1].is_vertical) {
    x = themap.segments[segm2].lanes[lane2].const_b;
    y = themap.segments[segm1].slope_a*x +
				themap.segments[segm1].lanes[lane1].const_b;
  }
  else if (themap.segments[segm1].slope_a == 0 &&
					 (themap.segments[segm2].is_vertical ||
					 themap.segments[segm2].slope_a!=0)) {
    y = themap.segments[segm1].lanes[lane1].const_b;
    if (themap.segments[segm2].is_vertical) {
      x = themap.segments[segm2].lanes[lane2].const_b;
    }
    else {
      x = (y - themap.segments[segm2].lanes[lane2].const_b)/themap.segments[segm2].slope_a;// x = (y-b)/a
    }
  }
  else if (themap.segments[segm2].slope_a == 0 &&
					 (themap.segments[segm1].is_vertical ||
					 themap.segments[segm1].slope_a!=0)) {
    y = themap.segments[segm2].lanes[lane2].const_b;
    if (themap.segments[segm1].is_vertical) {
      x = themap.segments[segm1].lanes[lane1].const_b;
    }
    else {
      x = (y - themap.segments[segm1].lanes[lane1].const_b)/themap.segments[segm1].slope_a;// x = (y-b)/a
    }
  }
	// oblique lines
  else {
		if (are_parallel_approx(themap.segments[segm1], themap.segments[segm2]) ) {
			double newdestlength = find_distance(themap.segments[segm1].lanes[lane1].xstart, 
															themap.segments[segm1].lanes[lane1].ystart, 
															themap.segments[segm1].lanes[lane1].xend, 
															themap.segments[segm1].lanes[lane1].yend);
			newdestlength += themap.lanewidth * 2;
			find_position_lane (themap, segm1, lane1, newdestlength, x, y);			
		}
		else {
    	x = (themap.segments[segm1].lanes[lane1].const_b - themap.segments[segm2].lanes[lane2].const_b)/
      	(themap.segments[segm2].slope_a - themap.segments[segm1].slope_a);
    	y = themap.segments[segm1].slope_a*x + themap.segments[segm1].lanes[lane1].const_b;
		}
  }
  return;

}


float max(float x1, float x2) {
  if (x1 <= x2)
    return x2;
  else
    return x1;
}

float min(float x1, float x2) {
  if (x1 <= x2)
    return x1;
  else
    return x2;
}


// Euclidian algorithm for finding gcd
int gcd (int a, int b) {
  if (b == 0)
    return a;

  return gcd (b, a%b);

}


void setdest (list<car>::iterator &iter, double x, double y) {
  iter->destx = x;
  iter->desty = y;

  return;
}


bool steady_state (mapstruct &themap) {

	if (warm_up > 0) {
		return false;
	}
	
	if (method == 2) {
		if ((int)ns_id_vect.size() != max_num_cars) //3/26/2007
			return false;
		else
			return true;
	}

  bool result = true;
  for (int i=1; i<(int)themap.intersections.size(); i++) {
    if (!themap.intersections[i].steady_state_flag) {
      cout<<"intersection i="<<i<<" x "<<themap.intersections[i].xpos<<" y "<<themap.intersections[i].ypos<<endl;
      result = false;
      break;
    }
  }
  return result; //3/26/2007
	
}



//This function records nodes mvt at a macroscopic level
// the flag is used to identify movements in/out of the map
// flag = 0 => in map area (default) or sink to map (set in update_waiting_list() function)
// flag = -1 => map to sink (set in node_exit() function)
void update_macroscopic_view (double t, mapstruct &themap, 
															list<car>::iterator& iter, int flag) {
	if (steady_state(themap) && start_ns_printing ) {
		int thissgid, start_intersect, end_intersect, roadid;
		if (flag == 0) {
			thissgid = iter->road_segment_id;
			start_intersect =
					themap.segments[iter->road_segment_id].start_intersect_id;
			end_intersect = themap.segments[iter->road_segment_id].end_intersect_id;
			roadid = themap.segments[iter->road_segment_id].road_id;
		}
		else if (flag == -1) {
			thissgid = -1;
			start_intersect = themap.segments[iter->road_segment_id].end_intersect_id;
			end_intersect = 0; //sink intersect
			roadid = -1; //undefined
		}
		else if (flag == -2) {
			char * tmpstr = new char[100];
			sprintf(tmpstr, "%.2f\tn_(%d)\t%d\t->\t%d\t%d\n", 
							0.0, iter->ns2_id, 0, -1, -1);
			iter->macroscopic_mvt = tmpstr ;
			delete[] tmpstr;
			return;
		}

		if (iter->prevsegment != thissgid) {
			char * tmpstr = new char[100];
			sprintf(tmpstr, "%.2f\tn_(%d)\t%d\t->\t%d\t%d\n", 
							t, iter->ns2_id, start_intersect, end_intersect, roadid);
			iter->macroscopic_mvt = tmpstr;
			// from sink back to map area
			if (iter->prevsegment == -1 && thissgid >=0) {
				sprintf(tmpstr, "%.2f\tn_(%d)\t%d\t->\t%d\t%d\n", 
								t, iter->ns2_id, 0, start_intersect, -1);
				iter->macroscopic_mvt = tmpstr + iter->macroscopic_mvt;
			}
			delete[] tmpstr; 
			iter->prevsegment = thissgid;
		}
	}
	return;
}



void print_firstentry_ns2 (double t, mapstruct &themap, 
													 list<car>::iterator &iter, string &str2) {
  if (steady_state(themap) && start_ns_printing) {
	char * tmpstr = new char[100];
	//double save_y;
	sprintf(tmpstr, "$ns_ at %.2f \"$node_(%d) off\" \n", 0.0, iter->ns2_id);
	str2 += tmpstr;
	sprintf(tmpstr, "$node_(%d) set X_ %.2f \t;#ref \n", iter->ns2_id, iter->x);
	str2 += tmpstr;
	sprintf(tmpstr, "$node_(%d) set Y_ %.2f \t;#ref \n", iter->ns2_id, 1.0);
	str2 += tmpstr;
	update_macroscopic_view (t, themap, iter, -2);
	
	//sprintf(tmpstr, "$ns_ at %.2f \"$node_(%d) set X_ %.1f\" \t;#ref \n", t, iter->ns2_id, iter->x);
	//str2 += tmpstr;
	sprintf(tmpstr, "$ns_ at %.2f \"$node_(%d) set Y_ %.2f\" \t;#ref \n",
					t, iter->ns2_id, iter->y);
	str2 += tmpstr;
	sprintf(tmpstr, "$ns_ at %.2f \"$node_(%d) on\" \n", t, iter->ns2_id);	
	str2 += tmpstr;
	delete[] tmpstr; 
	iter->printed_ns2 = true;
  }
  return;
}


void print_reentry_ns2 (double t, mapstruct &themap, 
			list<car>::iterator &iter, double speedneeded, string &str2) {
  if (steady_state(themap) && start_ns_printing) {
    char * tmpstr = new char[100];
    //sprintf(tmpstr, "$ns_ at %.2f \"$node_(%d) set Y_ %.2f\" \t;#ref \n", t-1.0, iter->ns2_id, iter->y);
    //str2 += tmpstr;
    if (!iter->printed_ns2) {
      print_firstentry_ns2 (t, themap, iter, str2);
    }
    sprintf(tmpstr, 
	"$ns_ at %.2f \"$node_(%d) setdest %.2f %.2f %.2f\" \n",
	t, iter->ns2_id, iter->x, iter->y, speedneeded);
    str2 += tmpstr;
    sprintf(tmpstr, "$ns_ at %.2f \"$node_(%d) on\" \n", t+0.01, iter->ns2_id);
    str2 += tmpstr;
    delete[] tmpstr; 
  }
  return;
}


void print_exit_ns2 (double t, mapstruct &themap, 
		list<car>::iterator &car1, double speedneeded, 
		double xstart, string &str2) {
	if (steady_state(themap) && start_ns_printing) {
		if (!car1->printed_ns2) {
			return;
		}
		char * tmpstr = new char[100];	
		if (speedneeded != max(speedneeded, 0.0)) 
			speedneeded = -1*speedneeded;
		sprintf(tmpstr, "$ns_ at %.2f \"$node_(%d) off\" \n", t, car1->ns2_id);	
		str2 += tmpstr;

		sprintf(tmpstr, 
			"$ns_ at %.2f \"$node_(%d) setdest %.2f %.2f %.2f\" \n",
			t, car1->ns2_id, xstart, 1.0, speedneeded);
		str2 += tmpstr;
		update_macroscopic_view (t, themap, car1, -1);
	}
	return;
}



void print_ns2 (double t, mapstruct &themap, list<car>::iterator& car1,
		string &str2) {

  if (steady_state(themap) && start_ns_printing) {
	char * tmpstr = new char[100];
	if (!car1->printed_ns2 && t>0) {
		print_firstentry_ns2 (t, themap, car1, str2);
	}
	if (!car1->printed_ns2) {
	  sprintf(tmpstr, "$node_(%d) set X_ %.2f \t;#ref \n", 
						car1->ns2_id, car1->prevx);
	  str2 += tmpstr;
	  sprintf(tmpstr, "$node_(%d) set Y_ %.2f \t;#ref \n", 
						car1->ns2_id, car1->prevy);
	  str2 += tmpstr;
	  car1->printed_ns2 = true;
	}
	sprintf(tmpstr, 
		"$ns_ at %.2f \"$node_(%d) setdest %.1f %.1f %.1f\" \n", 
		t, car1->ns2_id, car1->x, car1->y, car1->currv); 
	str2 += tmpstr;
	delete[] tmpstr; 

	update_macroscopic_view (t, themap, car1, 0);
  }
  return;
}


	void create_map(mapstruct &themap, double carsize, double braking, string filename) {
	
		double lanewidth = carsize+2;
	
		ifstream infile;
		infile.open(filename.c_str());
		if (!infile) {
			cout<<"Couldn't open map file!\n"<<endl;
			exit(EXIT_FAILURE);
		}
	
		string line;
		int tmpint, road_id=0, segment_id=0, lane_id=0, thisroadsegment;
		road* tmproad;
		road_segment* tmpsegment;
		intersection* tmpintersect;
		themap.lanewidth = lanewidth;
		themap.default_braking = braking;
		// source/sink intersection
		intersection intersectzero;
		intersectzero.intersection_id = 0;
		themap.intersections.push_back(intersectzero);
	
		// start reading file
		while ( getline(infile, line,'\n')) {
			if (line[0] == '#') {
				continue;
			}
	
			if (startString(line,"<ROAD>")) {
				tmproad = new road;
				road_id = themap.roads.size(); //++
				tmproad->road_id = road_id;
				thisroadsegment = 0;
			}
			else if (startString(line,"</ROAD>")) {
				//check that road contains at least one segment
				if (tmproad->segments.size() > 0) {
		themap.roads.push_back(*tmproad);
		delete tmproad;
				}
			}
			else if (startString(line,"FLOW")) {
				tmproad->flow = atoi(line.substr(5, line.length()-5).c_str());
			}
			else if (startString(line,"SPEED")) {
				tmproad->avg_speed = atof(line.substr(6, line.length()-6).c_str());
			}
			else if (startString(line,"ENTRY")) {
				tmproad->entryroad = atoi(line.substr(6, line.length()-6).c_str());
			}
			else if (startString(line,"<INTERSECTION>")) {
				tmpintersect = new intersection;
				tmpintersect->steady_state_flag = false; 
				tmpintersect->entry_intersect = false;
			}
			else if (startString(line,"</INTERSECTION>")) {
				themap.intersections.push_back(*tmpintersect);
				delete tmpintersect;
			}
			else if (startString(line,"<SEGMENT>")) {
				tmpsegment = new road_segment;
				segment_id = themap.segments.size(); //++;
				thisroadsegment++;
				tmpsegment->road_segment_id = segment_id;
				tmpsegment->road_id = road_id;
				tmpsegment->segment_flow = -1;
				tmpsegment->entry_segment = 0;
				tmpsegment->entrysegm_flow_param = 0;
				lane_id = 0;
				if (thisroadsegment <= 1) { tmpsegment->firstsegment = true; }
				else { tmpsegment->firstsegment = false; }
			}
			else if (startString(line,"</SEGMENT>")) {
				//segment should contain at least one lane
				if (tmpsegment->lanes.size() > 0) {
		themap.segments.push_back(*tmpsegment);
		tmproad->segments.push_back(tmpsegment->road_segment_id);
		delete tmpsegment;
				}
			}
			else if (startString(line,"SEGM_FLOW")) {
				tmpsegment->segment_flow = atoi(line.substr(10, line.length()-10).c_str());
			}
			else if (startString(line,"SEGM_ENTRY")) {
				tmpsegment->entry_segment = atoi(line.substr(11, line.length()-11).c_str());
			}
			else if (startString(line,"IID")) {
				tmpintersect->intersection_id = atoi(line.substr(4, line.length()-4).c_str());
			}
			else if (startString(line,"XPOS")) {
				tmpintersect->xpos = atof(line.substr(5, line.length()-5).c_str());
			}
			else if (startString(line,"YPOS")) {
				tmpintersect->ypos = atof(line.substr(5, line.length()-5).c_str());
			}
			else if (startString(line,"START")) {
				tmpsegment->start_intersect_id = atoi(line.substr(6, line.length()-6).c_str());
				themap.intersections[tmpsegment->start_intersect_id].exit.push_back(tmpsegment->road_segment_id);
			}
			else if (startString(line,"END")) {
				tmpsegment->end_intersect_id = atoi(line.substr(4, line.length()-4).c_str());
				themap.intersections[tmpsegment->end_intersect_id].entry.push_back(tmpsegment->road_segment_id);
			}
			else if (startString(line,"LANE")) {
				tmpint = atoi(line.substr(5, line.length()-5).c_str());
				while (tmpint > 0 ) {
		road_lane tmplane;
		lane_id++;
		tmplane.road_lane_id = lane_id;
		tmpsegment->lanes.push_back(tmplane);
		tmpint--;
				}
			}
					
		}
	
		int i, j, k, l, start_intersect, end_intersect;
		double xstart, ystart, xend, yend, slope_a, const_b, shortestdist;
		double segwidth, const_west, const_east, const_north, const_south;
		double slope_start, const_start, const_end, slope_end; 
		bool is_vertical_end, is_vertical_start;
		int direction, numlanes;
	
	
		// compute the slopes of segment  
		for (i=0; i<(int)themap.segments.size(); i++) {
	
			start_intersect = themap.segments[i].start_intersect_id;
			end_intersect = themap.segments[i].end_intersect_id;
			xstart = themap.intersections[start_intersect].xpos;
			ystart = themap.intersections[start_intersect].ypos;
			xend = themap.intersections[end_intersect].xpos;
			yend = themap.intersections[end_intersect].ypos;
	
			double vectx = xend - xstart;
			double vecty = yend - ystart;
			
			double clockvectx = vecty;
			double clockvecty = (-1)*vectx;
			double segmlength = find_distance(vectx, vecty);
			bool single_segm = true;
			segwidth = lanewidth * themap.segments[i].lanes.size();
			// check if one or two segments between start and end intersect
			// this influences on the start/end pos of segment
			for (j=0; j<(int)themap.segments.size(); j++) {
				if ((themap.segments[i].road_segment_id != themap.segments[j].road_segment_id) && 
				(themap.segments[j].start_intersect_id == end_intersect) &&
				(themap.segments[j].end_intersect_id == start_intersect)) {
					single_segm = false;
					break;
				}
			}
			// more than one segment between the 2 intersect points
			// for e.g. one segment in each direction -- 2way road portion
			if (!single_segm) {
				segwidth = segwidth/2;
				xstart = xstart + (segwidth/segmlength)*clockvectx;
				ystart = ystart + (segwidth/segmlength)*clockvecty;
				xend = xstart + vectx;
				yend = ystart + vecty;
			}
			// stores segment parameters
			themap.segments[i].xstart = xstart;
			themap.segments[i].ystart = ystart;
			themap.segments[i].xend = xend;
			themap.segments[i].yend = yend;    
			themap.segments[i].vectx = vectx;
			themap.segments[i].vecty = vecty;
	
			if(xstart == xend) {
				themap.segments[i].is_vertical = true;
				themap.segments[i].slope_a = 0;
				themap.segments[i].const_b = xstart;
			}
			else {
				themap.segments[i].is_vertical = false;
				themap.segments[i].slope_a = (yend - ystart)/(xend - xstart);
				themap.segments[i].const_b = ystart - themap.segments[i].slope_a*xstart;
			}
		}
	
		
		// compute start/end points for each lane
		for (i=0; i<(int)themap.segments.size(); i++) {
	
			slope_a = themap.segments[i].slope_a;
			const_b = themap.segments[i].const_b;
			xstart = themap.segments[i].xstart;
			ystart = themap.segments[i].ystart;
			xend = themap.segments[i].xend;
			yend = themap.segments[i].yend;
			shortestdist = find_distance(xstart, ystart, xend, yend);
			// initialize to segment values
			slope_start = slope_a;
			const_start = const_b;
			slope_end = slope_a;
			const_end = const_b;
			segwidth = lanewidth * themap.segments[i].lanes.size();
			vector<int> vstartintersect = themap.intersections[themap.segments[i].start_intersect_id].entry;
			for (k=0; k<(int)themap.intersections[themap.segments[i].start_intersect_id].exit.size(); k++)
				vstartintersect.push_back(themap.intersections[themap.segments[i].start_intersect_id].exit[k]);
	
			vector<int> vendintersect = themap.intersections[themap.segments[i].end_intersect_id].entry;
			for (k=0; k<(int)themap.intersections[themap.segments[i].end_intersect_id].exit.size(); k++)
				vendintersect.push_back(themap.intersections[themap.segments[i].end_intersect_id].exit[k]);
	
			// remove current segment from vstartintersect and vendintersect vectors
			// and also segments that are parallel to current segment
			for (k=0; k<(int)vstartintersect.size(); k++) {
				//if (themap.segments[i].road_segment_id == themap.segments[vstartintersect[k]].road_segment_id) {
				if (are_parallel(themap.segments[vstartintersect[k]], themap.segments[i])) {
					vstartintersect.erase(vstartintersect.begin()+k, vstartintersect.begin()+k+1);
					k--;
				}
			}
			for (k=0; k<(int)vendintersect.size(); k++) {
				//if (themap.segments[i].road_segment_id == themap.segments[vendintersect[k]].road_segment_id) {
				if (are_parallel(themap.segments[vendintersect[k]], themap.segments[i])) {
					vendintersect.erase(vendintersect.begin()+k, vendintersect.begin()+k+1);
					k--;
				}
			}
	
	
			double tmpdist;
			
			// find end position of lanes of segments[i]	
			for (k=0; k<(int)vendintersect.size(); k++) {
				j = vendintersect[k];
	
				if (are_parallel(themap.segments[j], themap.segments[i])) {
					continue;
				}
	
				segwidth = lanewidth * themap.segments[j].lanes.size();
				if (themap.segments[j].is_vertical && !themap.segments[i].is_vertical) {
					const_west = themap.segments[j].const_b - segwidth/2;
					const_east = themap.segments[j].const_b + segwidth/2;
					double yvalwest = slope_a*const_west + const_b;// y = ax+b
					double yvaleast = slope_a*const_east + const_b;
					tmpdist = find_distance(xstart, ystart, const_west, yvalwest);
					if (tmpdist < shortestdist) {
						shortestdist = tmpdist;
						const_end = const_west;
						is_vertical_end = true;
					}
					tmpdist = find_distance(xstart, ystart, const_east, yvaleast);
					if (tmpdist < shortestdist) {
						shortestdist = tmpdist;	  
						const_end = const_east;
						is_vertical_end = true;
					}
				}
				else if (themap.segments[j].slope_a == 0 && (themap.segments[i].is_vertical || slope_a!=0)) {
					const_north = themap.segments[j].const_b + segwidth/2;
					const_south = themap.segments[j].const_b - segwidth/2;
					double xvalnorth, xvalsouth;
					if (themap.segments[i].is_vertical) {
						xvalnorth = xend;
						xvalsouth = xend;
					}
					else {
						xvalnorth = (const_north - const_b)/slope_a;// x = (y-b)/a
						xvalsouth = (const_south - const_b)/slope_a;
					}
					tmpdist = find_distance(xstart, ystart, xvalnorth, const_north);
					if (tmpdist < shortestdist) {
						shortestdist = tmpdist;
						slope_end = 0;
						const_end = const_north;
						is_vertical_end = false;
					}
					tmpdist = find_distance(xstart, ystart, xvalsouth, const_south);
					if (tmpdist < shortestdist) {
						shortestdist = tmpdist;
						slope_end = 0;
						const_end = const_south;
						is_vertical_end = false;
					}
				}
				else {
				
					double xvalwest, yvalwest, xvaleast, yvaleast;

					if (are_parallel_approx(themap.segments[i], themap.segments[j]) ) {
					double x, y, vectx, vecty, perpendx, perpendy, dist;
					
					vectx = themap.segments[i].vectx;
					vecty = themap.segments[i].vecty;
					vectx = -1*vectx;
					vecty = -1*vecty;
										
					dist = find_distance(vectx, vecty);
					x = themap.segments[i].xend + vectx*(segwidth/dist);
					y = themap.segments[i].yend + vecty*(segwidth/dist);
					
					if (yend > ystart) {
						perpendx = -1*vecty;
						perpendy = vectx;
					}
					else {
						perpendx = vecty;
						perpendy = -1*vectx;
					}
					
					xvalwest = x - ((segwidth/2)/dist)*perpendx;
					yvalwest = y - ((segwidth/2)/dist)*perpendy;
					xvaleast = x + ((segwidth/2)/dist)*perpendx;
					yvaleast = y + ((segwidth/2)/dist)*perpendy;

				}
				else {	
					
					double xendeast, yendeast, xendwest, yendwest;
					double vectx, vecty, perpendx, perpendy, dist;
					double start_j_x, start_j_y, end_j_x, end_j_y;

					if (themap.segments[i].end_intersect_id == themap.segments[j].end_intersect_id) {
						start_j_x = themap.segments[j].xend;
						start_j_y = themap.segments[j].yend;
						end_j_x = themap.segments[j].xstart;
						end_j_y = themap.segments[j].ystart;
					}
					else {
						start_j_x = themap.segments[j].xstart;
						start_j_y = themap.segments[j].ystart;
						end_j_x = themap.segments[j].xend;
						end_j_y = themap.segments[j].yend;
					}
					
					vectx = end_j_x - start_j_x;
					vecty = end_j_y - start_j_y;
					
					dist = find_distance(vectx, vecty);
					
					if (end_j_y > start_j_y) {
						perpendx = vecty;
						perpendy = -1*vectx;
					}
					else {
						perpendx = -1*vecty;
						perpendy = vectx;
					}
					
					
					xendwest = start_j_x - ((segwidth/2)/dist)*perpendx;
					yendwest = start_j_y - ((segwidth/2)/dist)*perpendy;
					xendeast = start_j_x + ((segwidth/2)/dist)*perpendx;
					yendeast = start_j_y + ((segwidth/2)/dist)*perpendy;
					
					const_west = yendwest - themap.segments[j].slope_a*xendwest;
					const_east = yendeast - themap.segments[j].slope_a*xendeast;
					if (themap.segments[i].is_vertical) {
						xvalwest = const_b;
						yvalwest = themap.segments[j].slope_a*xvalwest + const_west;
						xvaleast = const_b;
						yvaleast = themap.segments[j].slope_a*xvaleast + const_east;
					}
					else {
						xvalwest = (const_west - const_b)/(slope_a - themap.segments[j].slope_a);
						yvalwest = slope_a*xvalwest + const_b;
						xvaleast = (const_east - const_b)/(slope_a - themap.segments[j].slope_a);
						yvaleast = slope_a*xvaleast + const_b;
					}

				}

					tmpdist = find_distance(xstart, ystart, xvalwest, yvalwest);
					if (tmpdist < shortestdist) {
						shortestdist = tmpdist;
						if (themap.segments[i].is_vertical) slope_end = 0;
						else if (slope_a==0) slope_end = themap.segments[j].slope_a;
						else slope_end = -1/slope_a;
						const_end = yvalwest - slope_end*xvalwest;
						is_vertical_end = false;
					}
					tmpdist = find_distance(xstart, ystart, xvaleast, yvaleast);
					if (tmpdist < shortestdist) {
						shortestdist = tmpdist;
						if (themap.segments[i].is_vertical) slope_end = 0;
						else if (slope_a==0) slope_end = themap.segments[j].slope_a;
						else slope_end = -1/slope_a;
						const_end = yvaleast - slope_end*xvaleast;
						is_vertical_end = false;
					}
				}
			}
	
	
	
			shortestdist = find_distance(xstart, ystart, xend, yend);	
	
	
			// find start position of lanes of segments[i]
			for (k=0; k<(int)vstartintersect.size(); k++) {
				j = vstartintersect[k];
	
				if (are_parallel(themap.segments[j], themap.segments[i])) {
					continue;
				}
	
				segwidth = lanewidth * themap.segments[j].lanes.size();
				if (themap.segments[j].is_vertical && !themap.segments[i].is_vertical) {
					const_west = themap.segments[j].const_b - segwidth/2;
					const_east = themap.segments[j].const_b + segwidth/2;
					double yvalwest = slope_a*const_west + const_b;// y = ax+b
					double yvaleast = slope_a*const_east + const_b;
					tmpdist = find_distance(xend, yend, const_west, yvalwest);
					if (tmpdist < shortestdist) {
						shortestdist = tmpdist;
						const_start = const_west;
						is_vertical_start = true;
					}
					tmpdist = find_distance(xend, yend, const_east, yvaleast);
					if (tmpdist < shortestdist) {
						shortestdist = tmpdist;	  
						const_start = const_east;
						is_vertical_start = true;
					}
				}
				else if (themap.segments[j].slope_a == 0 && (themap.segments[i].is_vertical || slope_a!=0)) {
					const_north = themap.segments[j].const_b + segwidth/2;
					const_south = themap.segments[j].const_b - segwidth/2;
					double xvalnorth, xvalsouth;
					if (themap.segments[i].is_vertical) {
						xvalnorth = xstart;
						xvalsouth = xstart;
					}
					else {
						xvalnorth = (const_north - const_b)/slope_a;// x = (y-b)/a
						xvalsouth = (const_south - const_b)/slope_a;
					}
					tmpdist = find_distance(xend, yend, xvalnorth, const_north);
					if (tmpdist < shortestdist) {
						shortestdist = tmpdist;
						slope_start = 0;
						const_start = const_north;
						is_vertical_start = false;
					}
					tmpdist = find_distance(xend, yend, xvalsouth, const_south);
					if (tmpdist < shortestdist) {
						shortestdist = tmpdist;
						slope_start = 0;
						const_start = const_south;
						is_vertical_start = false;
					}
				}
				else {
					

					double xvalwest, yvalwest, xvaleast, yvaleast;
					if (are_parallel_approx(themap.segments[i], themap.segments[j]) ) {

					double x, y, vectx, vecty, perpendx, perpendy, dist;
					
					vectx = themap.segments[i].vectx;
					vecty = themap.segments[i].vecty;
					
					dist = find_distance(vectx, vecty);
					x = themap.segments[i].xstart + vectx*(segwidth/dist);
					y = themap.segments[i].ystart + vecty*(segwidth/dist);
					
					if (yend > ystart) {
						perpendx = vecty;
						perpendy = -1*vectx;
					}
					else {
						perpendx = -1*vecty;
						perpendy = vectx;
					}
					
					xvalwest = x - ((segwidth/2)/dist)*perpendx;
					yvalwest = y - ((segwidth/2)/dist)*perpendy;
					xvaleast = x + ((segwidth/2)/dist)*perpendx;
					yvaleast = y + ((segwidth/2)/dist)*perpendy;

				}
				else {
					double xendeast, yendeast, xendwest, yendwest;
					double vectx, vecty, perpendx, perpendy, dist;
					double start_j_x, start_j_y, end_j_x, end_j_y;
					
					
					if (themap.segments[i].start_intersect_id == themap.segments[j].start_intersect_id) {
						start_j_x = themap.segments[j].xstart;
						start_j_y = themap.segments[j].ystart;
						end_j_x = themap.segments[j].xend;
						end_j_y = themap.segments[j].yend;
					}
					else {
						start_j_x = themap.segments[j].xend;
						start_j_y = themap.segments[j].yend;
						end_j_x = themap.segments[j].xstart;
						end_j_y = themap.segments[j].ystart;
					}
					
					vectx = end_j_x - start_j_x;
					vecty = end_j_y - start_j_y;
					
					dist = find_distance(vectx, vecty);
					
					if (end_j_y > start_j_y) {
						perpendx = vecty;
						perpendy = -1*vectx;
					}
					else {
						perpendx = -1*vecty;
						perpendy = vectx;
					}
					
					
					xendwest = start_j_x - ((segwidth/2)/dist)*perpendx;
					yendwest = start_j_y - ((segwidth/2)/dist)*perpendy;
					xendeast = start_j_x + ((segwidth/2)/dist)*perpendx;
					yendeast = start_j_y + ((segwidth/2)/dist)*perpendy;
					
					const_west = yendwest - themap.segments[j].slope_a*xendwest;
					const_east = yendeast - themap.segments[j].slope_a*xendeast;
					if (themap.segments[i].is_vertical) {
						xvalwest = const_b;
						yvalwest = themap.segments[j].slope_a*xvalwest + const_west;
						xvaleast = const_b;
						yvaleast = themap.segments[j].slope_a*xvaleast + const_east;
					}
					else {
						xvalwest = (const_west - const_b)/(slope_a - themap.segments[j].slope_a);
						yvalwest = slope_a*xvalwest + const_b;
						xvaleast = (const_east - const_b)/(slope_a - themap.segments[j].slope_a);
						yvaleast = slope_a*xvaleast + const_b;
					}

				}

					tmpdist = find_distance(xend, yend, xvalwest, yvalwest);
					if (tmpdist < shortestdist) {
						shortestdist = tmpdist;
						if (themap.segments[i].is_vertical) slope_start = 0;
						else if (slope_a==0) slope_start = themap.segments[j].slope_a;
						else slope_start = -1/slope_a;
						const_start = yvalwest - slope_start*xvalwest;
						is_vertical_start = false;
					}
					tmpdist = find_distance(xend, yend, xvaleast, yvaleast);
					if (tmpdist < shortestdist) {
						shortestdist = tmpdist;
						if (themap.segments[i].is_vertical) slope_start = 0;
						else if (slope_a==0) slope_start = themap.segments[j].slope_a;
						else slope_start = -1/slope_a;
						const_start = yvaleast - slope_start*xvaleast;
						is_vertical_start = false;
					}
				}
			}
	
	
	
			// compute individual start/end of each lane of segments[i]
			numlanes = themap.segments[i].lanes.size();
			direction = 1;
			// current segment is vertical
			if (themap.segments[i].is_vertical) {
				if (yend < ystart) {
					direction = -1;
				}
				if (vendintersect.size() == 0) {
					slope_end = 0;
					const_end = yend;
					is_vertical_end = false;
				}
				if (vstartintersect.size() == 0) {
					slope_start = 0;
					const_start = ystart;
					is_vertical_start = false;
				}
	
				for(l=0; l<numlanes; l++) {
					themap.segments[i].lanes[l].xstart = xend + ((float)(numlanes-1)/2- l)*lanewidth*direction;
					themap.segments[i].lanes[l].ystart = slope_start*themap.segments[i].lanes[l].xstart + const_start;
					themap.segments[i].lanes[l].xend = xstart + ((float)(numlanes-1)/2 - l)*lanewidth*direction;
					themap.segments[i].lanes[l].yend = slope_end*themap.segments[i].lanes[l].xend + const_end;
					themap.segments[i].lanes[l].const_b = const_b + ((float)(numlanes-1)/2 - l)*lanewidth*direction; 
				}
			}
			//current segment is horizontal
			else if (themap.segments[i].slope_a == 0) {
				if (xend < xstart) {
					direction = -1;
				}
				if (vendintersect.size() == 0) {
					slope_end = 0;
					const_end = xend;
					is_vertical_end = true;
				}
				if (vstartintersect.size() == 0) {
					slope_start = 0;
					const_start = xstart;
					is_vertical_start = true;
				}
	
				for(l=0; l<numlanes; l++) {
					themap.segments[i].lanes[l].ystart = yend + (l-(float)(numlanes-1)/2)*lanewidth*direction;
					themap.segments[i].lanes[l].yend = ystart + (l-(float)(numlanes-1)/2)*lanewidth*direction;
					themap.segments[i].lanes[l].const_b = const_b + (l-(float)(numlanes-1)/2)*lanewidth*direction; 
					if (is_vertical_start)
						themap.segments[i].lanes[l].xstart = const_start;
					else
						themap.segments[i].lanes[l].xstart = (themap.segments[i].lanes[l].ystart-const_start)/slope_start;
				
					if (is_vertical_end)
						themap.segments[i].lanes[l].xend = const_end;
					else
						themap.segments[i].lanes[l].xend = (themap.segments[i].lanes[l].yend-const_end)/slope_end;
				}
			}
			// current segment is oblique
			else {
				if (yend < ystart) {
					direction = -1;
				}
				if (vendintersect.size() == 0) {
					slope_end = -1/slope_a;
					const_end = yend - slope_end*xend;
					is_vertical_end = false;
				}
				if (vstartintersect.size() == 0) {
					slope_start = -1/slope_a;
					const_start = ystart - slope_start*xstart;
					is_vertical_start = false;
				}
	
				double x_median, y_median;
				double clockvectx, clockvecty, segmlength;
				if (is_vertical_start) {
					x_median = const_start;
					y_median = slope_a*x_median + const_b;
					for(l=0; l<numlanes; l++) {
						themap.segments[i].lanes[l].xstart = x_median;
						themap.segments[i].lanes[l].ystart = y_median + (l-(float)(numlanes-1)/2)*(lanewidth/cos(atan(slope_a)))*direction;
					}
				}
				else {
					clockvectx = yend - ystart;
					clockvecty = (-1)*(xend - xstart);
						
					segmlength = find_distance(clockvectx, clockvecty);
					x_median = (const_start-const_b)/(slope_a-slope_start);
					y_median = slope_a*x_median + const_b;
					for(l=0; l<numlanes; l++) {
						themap.segments[i].lanes[l].xstart = x_median + ((float)(numlanes-1)/2 - l)
																													*(lanewidth/segmlength)
																													*clockvectx;
						themap.segments[i].lanes[l].ystart = y_median + ((float)(numlanes-1)/2 - l)
																													*(lanewidth/segmlength)
																													*clockvecty;
					}	    
				}	
	
				if (is_vertical_end) {
					x_median = const_end;
					y_median = slope_a*x_median + const_b;
					for(l=0; l<numlanes; l++) {
						themap.segments[i].lanes[l].xend = x_median;
						themap.segments[i].lanes[l].yend = y_median + (l-(float)(numlanes-1)/2)
																													*(lanewidth/cos(atan(slope_a)))
																													*direction;
					}
				}
				else {
					clockvectx = yend - ystart;
					clockvecty = (-1)*(xend - xstart);
					segmlength = find_distance(clockvectx, clockvecty);
					x_median = (const_end-const_b)/(slope_a-slope_end);
					y_median = slope_a*x_median + const_b;
					for(l=0; l<numlanes; l++) {
						themap.segments[i].lanes[l].xend = x_median + ((float)(numlanes-1)/2 - l)
																											*(lanewidth/segmlength)
																											*clockvectx;
						themap.segments[i].lanes[l].yend = y_median + ((float)(numlanes-1)/2 - l)
																											*(lanewidth/segmlength)
																											*clockvecty;
					}    
				}
				for (l=0; l<numlanes; l++) {
					themap.segments[i].lanes[l].const_b = themap.segments[i].lanes[l].yend 
																								- slope_a*themap.segments[i].lanes[l].xend; 
				}
			}
		}
	
		#ifdef DEBUG
		// print computed values
		for (i=0; i<(int)themap.segments.size(); i++) {
			start_intersect = themap.segments[i].start_intersect_id;
			end_intersect = themap.segments[i].end_intersect_id;
			for (j=0; j<(int)themap.segments[i].lanes.size(); j++) {
				cerr<<start_intersect<<" -> "<<end_intersect<<" lane "<<j
						<<" start: "<<themap.segments[i].lanes[j].xstart<<", "
						<<themap.segments[i].lanes[j].ystart<<" end: "
						<<themap.segments[i].lanes[j].xend<<", "
						<<themap.segments[i].lanes[j].yend<<" const_b: "
						<<themap.segments[i].lanes[j].const_b<<endl;
			}
		}
		#endif
			
		//exit(1);
		return;
	}
	


void compute_exitflows (double simulationtime, mapstruct &themap) {


  vector<intersection> allintersect(themap.intersections);
  int i, j, k, netflow;
 

	// initialize flow of segments to default to road flow
	// unless it was specified in map file
  for (i=0; i<(int)themap.segments.size(); i++) {
    if (themap.segments[i].segment_flow == -1)
      themap.segments[i].segment_flow = themap.roads[themap.segments[i].road_id].flow;
  }


  // compute exitflows that are independent of simulation time
  int sum, highest, greatestdivisor, intersectzero = 0;


  sum = 0;

  // compute exitflows of sink intersection == intersection 0
  for (i=0; i<(int)themap.segments.size(); i++) {
    if (themap.segments[i].entry_segment) {
      sum += themap.segments[i].segment_flow;
    }
  }
  highest = sum;
  for (i=0; i<(int)themap.segments.size(); i++) {
    if (themap.segments[i].entry_segment) {
      greatestdivisor = gcd(themap.segments[i].segment_flow, sum);
      if (highest > greatestdivisor) {
	highest = greatestdivisor;
      }
    }
  }
  for (i=0; i<(int)themap.segments.size(); i++) {
    if (themap.segments[i].entry_segment) {
      netflow = themap.segments[i].segment_flow/highest;
      themap.segments[i].entrysegm_flow_param = netflow;
      themap.intersections[themap.segments[i].start_intersect_id].entry_intersect = true;
			// should check that intersect not already in vector!!!!!!
			vector<int>::iterator dup_iter;
			dup_iter = find(themap.intersections[intersectzero].exit.begin(), 
											themap.intersections[intersectzero].exit.end(), 
											themap.segments[i].start_intersect_id);
			if (dup_iter == themap.intersections[intersectzero].exit.end() ) {
				themap.intersections[intersectzero].exit.push_back(themap.segments[i].start_intersect_id);
				for (j=0; j<netflow; j++) {	
					themap.intersections[intersectzero].exitflows.push_back(themap.segments[i].start_intersect_id);
				}
			}
    }
  }


  // at other intersections
  for (i=1; i<(int)themap.intersections.size(); i++) {
    sum = 0;
    // find total entry flow
    for (j=0; j<(int)themap.intersections[i].exit.size(); j++) {
      sum += themap.segments[themap.intersections[i].exit[j]].segment_flow;
    }

    // find smallest of common divisor
    highest = sum;
    for (j=0; j<(int)themap.intersections[i].exit.size(); j++) {
      greatestdivisor = gcd(themap.segments[themap.intersections[i].exit[j]].segment_flow, sum);
      if (highest > greatestdivisor) {
	highest = greatestdivisor;
      }
    }

    // compute simulation time independent segment flows
    // and populate exitflows vectors of intersections
    for (j=0; j<(int)themap.intersections[i].exit.size(); j++) {
      netflow = themap.segments[themap.intersections[i].exit[j]].segment_flow/highest;
      themap.segments[themap.intersections[i].exit[j]].segment_flow_param = netflow;
      for(k=0; k<netflow; k++) {
	themap.intersections[i].exitflows.push_back(themap.intersections[i].exit[j]);
      }
    }
  }

#ifdef DEBUG
  // print values
  for (i=0; i<(int)themap.segments.size(); i++)
    cerr<<"seg: "<<themap.segments[i].road_segment_id<<" flow: "<<themap.segments[i].segment_flow<<" param: "<<themap.segments[i].segment_flow_param<<endl;
#endif
    
  return;
}



int find_next_segment(mapstruct &themap, int intersect, int fromsink = -1) {
  int result=-1;
  
  if (intersect < 0 ) return result;
  // check if new segment ends on an entry intersection
  // in which case apply border logic
  // this does not modify the result=-1 logic...
  if (fromsink != -1 && 
			(themap.intersections[intersect].entry_intersect==true || 
			(int) themap.intersections[intersect].exit.size() == 0)) {
    // current intersection is not sink and going towards an entry_intersect 
    // => apply logic here
    // case 1: all cars arriving should go to sink
    if (method == 1) {
      result = -1;
      return result;
    }
    // case 3: 50% of all cars arriving go to sink and 50% go back in
    else if (method == 3) {      
      // but for now just interested in case 1 and 2; 
    }
    //case 2: all cars arriving go back in
    else if (method == 2) {
      // assume map has 2 way road for all entry_intersect in map file
      // so just go below
    }
  }  
  
  #ifdef MEMORYLESS
    int i, sgid;
    double flowsum=0.0, randnum=0.0, tmpdbl;
		map<int, double> entryflows;
		map<double, int> keyflows;
		vector<double> v;
    for (i=0; i< (int)themap.intersections[intersect].exit.size(); i++) {
			sgid = themap.intersections[intersect].exit[i];
			// check if we are making a u-turn
			if (themap.segments[sgid].end_intersect_id == fromsink) {
				entryflows[sgid] = themap.segments[sgid].segment_flow/100; 
				flowsum += themap.segments[sgid].segment_flow/100;
				continue;
			}
			entryflows[sgid] = themap.segments[sgid].segment_flow; 
			flowsum += themap.segments[sgid].segment_flow;  
		}
		
		tmpdbl = 0.0;
		for (i=0; i< (int)themap.intersections[intersect].exit.size(); i++) {
			sgid = themap.intersections[intersect].exit[i];
			entryflows[sgid] = tmpdbl + entryflows[sgid]/flowsum;
			tmpdbl = entryflows[sgid];
			keyflows[tmpdbl] = sgid;
			v.push_back(tmpdbl);
		}
		
		sort(v.begin(), v.end());
		
		randnum = ((double)rand()/((double)(RAND_MAX) + (double)(1.0))); // in [0,1)
		for (i=0; i < (int)v.size(); i++) {
			if (randnum < v[i]) 
				break;
		}
		/*
    for (i=0; i< (int)themap.intersections[intersect].exit.size(); i++) {
      tmpdbl = themap.segments[themap.intersections[intersect].exit[i]].segment_flow/flowsum;
      if (sum <= randnum && randnum < (sum+tmpdbl)) {
        result = themap.intersections[intersect].exit[i];
				break;
      }
      sum += tmpdbl;
    }
		*/
		
		if (keyflows.find(v[i]) != keyflows.end())
			result = keyflows[v[i]];
		else
			result = 0;
		
		
    // update steady_state_flag
    if (themap.intersections[intersect].exitflows.size() == 0) {
      themap.intersections[intersect].steady_state_flag = true;
    }
    else {
      for (i=0; i< (int)themap.intersections[intersect].exitflows.size(); i++) {
        if (result == themap.intersections[intersect].exitflows[i]) {
          themap.intersections[intersect].exitflows.erase(themap.intersections[intersect].exitflows.begin()+i);
        }
      }
    }
		
  #else
    int num = themap.intersections[intersect].exitflows.size();
    if (num > 0) {
      num = (int)rand()%(num);
      result = themap.intersections[intersect].exitflows[num];
      themap.intersections[intersect].exitflows.erase(themap.intersections[intersect].exitflows.begin()+num);
    }
    ///*
    //below added for when reusing nodes
    else {
      themap.intersections[intersect].steady_state_flag = true;
      if (themap.intersections[intersect].exit.size() > 0) {
        int i,j, sgid;
        for (i=0; i<(int)themap.intersections[intersect].exit.size(); i++) {
	  sgid = themap.intersections[intersect].exit[i];
	  for (j=0; j<themap.segments[sgid].segment_flow_param; j++) {
	    themap.intersections[intersect].exitflows.push_back(themap.segments[sgid].road_segment_id);
	  }
        }
        num = themap.intersections[intersect].exitflows.size();
        num = (int)rand()%(num);
        result = themap.intersections[intersect].exitflows[num];
        themap.intersections[intersect].exitflows.erase(themap.intersections[intersect].exitflows.begin()+num);
      }
    }
    // */
 #endif

  
  return result;
}




int find_next_road_entrysegm(mapstruct &themap) {
  int resultintersect=-1, fromsink = -1, resultsgid=-1;
  //int roadid;
  int intersectzero = 0, intersectid;
  
  #ifdef MEMORYLESS
    int i, j;
    double flowsum=0.0, randnum=0.0, tmpdbl;
		map<int, double> entryflows;
		map<double, int> keyflows;
		vector<double> v;
    for (i=0; i< (int)themap.intersections[intersectzero].exit.size(); i++) {
      intersectid = themap.intersections[intersectzero].exit[i];
			entryflows[intersectid] = 0.0;
      for (j=0; j< (int)themap.intersections[intersectid].exit.size(); j++) {
				entryflows[intersectid] += 
									(double)themap.segments[themap.intersections[intersectid].exit[j]].entrysegm_flow_param;
        flowsum += (double)themap.segments[themap.intersections[intersectid].exit[j]].entrysegm_flow_param; 
      }
    }
		
		tmpdbl = 0;
		for (i=0; i< (int)themap.intersections[intersectzero].exit.size(); i++) {
			intersectid = themap.intersections[intersectzero].exit[i];
			entryflows[intersectid] = tmpdbl + entryflows[intersectid]/flowsum;
			tmpdbl = entryflows[intersectid];
			keyflows[tmpdbl] = intersectid;
			v.push_back(tmpdbl);
		}
		
		sort(v.begin(), v.end());
		
    randnum = ((double)rand()/((double)(RAND_MAX) + (double)(1.0))); //[0,1)
		for (i=0; i < (int)v.size(); i++) {
			if (randnum < v[i]) 
				break;
		}
		
		if (keyflows.find(v[i]) != keyflows.end())
			resultintersect = keyflows[v[i]];
		else {
			if (themap.intersections[intersectzero].exit.size() > 0)
				resultintersect = themap.intersections[intersectzero].exit[0];
			else {
				fprintf(stderr, "No entry intersect specified! \n");
				exit(1);
			}
		}
			
		
    // update steady_state_flag
    if (themap.intersections[intersectzero].exitflows.size() == 0) {
      themap.intersections[intersectzero].steady_state_flag = true;
    }
    else {
      for (i=0; i< (int)themap.intersections[intersectzero].exitflows.size(); i++) {
        if (resultintersect == themap.intersections[intersectzero].exitflows[i]) {
          themap.intersections[intersectzero].exitflows.erase(themap.intersections[intersectzero].exitflows.begin()+i);
        }
      }
    }
  #else
    int num;
    num = themap.intersections[intersectzero].exitflows.size();
    if (num > 0) {
      num = (int)rand()%(num);
      resultintersect = themap.intersections[intersectzero].exitflows[num];
      themap.intersections[intersectzero].exitflows.erase(themap.intersections[intersectzero].exitflows.begin()+num);
    }
    //below added to enable node reuse
    else {
      themap.intersections[intersectzero].steady_state_flag = true;
      if (themap.intersections[intersectzero].exit.size() > 0) {
        int i,j,k;
        for (i=0; i<(int)themap.intersections[intersectzero].exit.size(); i++) {
	  // now considering segment entry points
	  intersectid = themap.intersections[intersectzero].exit[i];
	  for (k=0; k<(int)themap.intersections[intersectid].exit.size(); k++) {
	    for (j=0; j<themap.segments[themap.intersections[intersectid].exit[k]].entrysegm_flow_param; j++) {
				themap.intersections[intersectzero].exitflows.push_back(intersectid);
	    }
	  }  
        }
        num = themap.intersections[intersectzero].exitflows.size();
        num = (int)rand()%(num);
        resultintersect = themap.intersections[intersectzero].exitflows[num];
        themap.intersections[intersectzero].exitflows.erase(themap.intersections[intersectzero].exitflows.begin()+num);
      }
    }
  #endif

  // calling find_next_segment() to get segment id
  resultsgid = find_next_segment(themap, resultintersect, fromsink);

  return resultsgid;
}



carMove find_next_move (mapstruct &themap, int thissegment, int nextsegment) {
  if (nextsegment == -1 )  {
    return STRAIGHT;
  }
  else if (themap.segments[thissegment].road_id == themap.segments[nextsegment].road_id) {
    if (themap.segments[thissegment].start_intersect_id == themap.segments[nextsegment].end_intersect_id)
      return UTURN;
    else
      return STRAIGHT;
  }
  else {
    int startintersectthis = themap.segments[thissegment].start_intersect_id;
    int endintersectthis = themap.segments[thissegment].end_intersect_id;
    int endintersectnext = themap.segments[nextsegment].end_intersect_id;

    double xstartthis = themap.intersections[startintersectthis].xpos;
    double ystartthis = themap.intersections[startintersectthis].ypos;
    double xendthis = themap.intersections[endintersectthis].xpos;
    double yendthis = themap.intersections[endintersectthis].ypos;
    double xendother = themap.intersections[endintersectnext].xpos;
    double yendother = themap.intersections[endintersectnext].ypos; 
    
    // applying 2D math vector formulas
    // vectors E1 = P1-P2; E2 = P3-P2
    double E1_x = xstartthis - xendthis;
    double E1_y = ystartthis - yendthis;
    double E2_x = xendother - xendthis;
    double E2_y = yendother - yendthis;
    
    double clockwise = E1_x *E2_y - E1_y *E2_x;
    if (clockwise >= 0)
      return RIGHT;
    else
      return LEFT;

  }

}


int findtargetlane (float speed, double avgspeed, double speedrange, int numlanes) {
		
  float minspeed = (float)(avgspeed - speedrange/2);
  //double maxspeed = avgspeed + speedrange/2;
  float increase;
  int i;
  increase = (float)(speedrange/numlanes);

  i = 0;
  while (i< numlanes) {
    minspeed += increase;
    if ( speed <= minspeed ) {
      //result = i;
			break;
    }
    i++;
  }
	//result = i;
	if (i == numlanes) {
	  #ifdef DEBUG
  	cerr<<i<<endl;
		#endif
	}
  return i;
}


void update_car (mapstruct &themap, list<car>::iterator &car1, double dist) {
  double xend, yend;
  //double tmpdbl, tmpdbl2;

  xend = car1->destx;
  yend = car1->desty;

  if (xend == car1->x && yend == car1->y) {
    xend = 2*xend;
    yend = 2*yend;
  }

  double vectx = xend - car1->x;
  double vecty = yend - car1->y;

  double length = find_distance(vectx, vecty);
  double offset = dist/length;
  car1->x = car1->x + offset*vectx;
  car1->y = car1->y + offset*vecty;

  return;
}


void change_traffic_light_color (mapstruct &themap, int light_id ) {
	
  trafficLightColor newcolor;
  // find new color
  if (themap.lights[light_id].color == RED)
    newcolor = GREEN;
  else if (themap.lights[light_id].color == GREEN)
    newcolor = YELLOW;
  else
    newcolor = RED;

  // change color
  if (newcolor == RED ) {
    themap.lights[light_id].color = RED;
    themap.lights[light_id].length = RED_LIGHT_LENGTH;
  }
  else if (newcolor == YELLOW) {
    themap.lights[light_id].color = YELLOW;
    themap.lights[light_id].length = YELLOW_LIGHT_LENGTH;
  }
  else if (newcolor == GREEN) {
    themap.lights[light_id].color = GREEN;
    themap.lights[light_id].length = GREEN_LIGHT_LENGTH;
  }
  return;
}


int get_traffic_light_id (mapstruct &themap, int intersect_id, int sgid) {

  int i, j, result = -1;
  for (i=0; i<(int)themap.intersections[intersect_id].lights.size(); i++) {
    j = themap.intersections[intersect_id].lights[i];
    if (themap.segments[sgid].road_id == themap.lights[j].road_id) {
      result = j;
      break;
    }
  }
  return result;
}


void add_traffic_light (mapstruct &themap, int intersect_id, int sgid) {
  //int i,j;
  int light_id = get_traffic_light_id(themap, intersect_id, sgid);
  if (light_id == -1 ) {
    trafficLight newlight;
    newlight.light_id = themap.lights.size();
		newlight.color = GREEN; //RED;
		newlight.length = GREEN_LIGHT_LENGTH; //RED_LIGHT_LENGTH;
    newlight.road_id = themap.segments[sgid].road_id;
    themap.lights.push_back(newlight);
    themap.intersections[intersect_id].lights.push_back(newlight.light_id);
    themap.segments[sgid].end_light_id = newlight.light_id;
  }
  else {
    themap.segments[sgid].end_light_id = light_id;
  }
  return;
}


void update_traffic_lights(mapstruct &themap, double interval) {
  // ASSUME AT MOST TWO LIGHTS (two different ROADS) PER INTERSECTION!!!!!! 
	// OTHERWISE SHOULD MODIFY HERE!!!!!
	
  int i;
  for (i=0; i<(int)themap.lights.size(); i++) {
    themap.lights[i].length -= interval;
    if (themap.lights[i].length <= 0) {
      change_traffic_light_color (themap, themap.lights[i].light_id); 
    }
  }

  return;
}


void initialize_traffic_lights(mapstruct &themap) {
  
  int i, j;
  int light_id, intersect_id, sgid;

  // first create the lights at intersections
  for (i=0; i<(int)themap.intersections.size(); i++) {
    for (j=0; j<(int)themap.intersections[i].entry.size(); j++) {
      intersect_id = themap.intersections[i].intersection_id;
      sgid = themap.intersections[i].entry[j];
      add_traffic_light(themap, intersect_id, sgid);
    }
  }

  // for each intersection, randomly select one light as green light
  // at this stage[TODO IMPROVE THIS]
  for (i=0; i<(int)themap.intersections.size(); i++) {
    if (themap.intersections[i].entry.size() > 0) {
      intersect_id = themap.intersections[i].intersection_id;
      sgid = (int)rand()%themap.intersections[i].entry.size();
      sgid = themap.intersections[i].entry[sgid];
      light_id =  get_traffic_light_id(themap, intersect_id, sgid);
      change_traffic_light_color (themap, light_id);
    }
  }

  return;
}




//void initialize_cars (double simulationtime, mapstruct &themap, int numcars, double carsize, double safedistmargin, double speedrange, string &str2, int run_num) {
void initialize_cars (double simulationtime, mapstruct &themap, int numcars, double carsize, double safedistmargin, double speedrange, string &str2) {

  // this function randomly select destinations and entries
  // for the cars according to the flows on the roads
  int i;
	//int j;
  vector<int> entrysegmts;
  vector<int> flows;
  //char* tmpstr = new char[100];


  double mincardist, minspeed, speed, xstart, ystart;
  int roadid, sgid, previntersect, nextintersect, numberlanes, laneid;
  int car_id = 0;
  list<car>::iterator car1, iter;

  for (i=0; i< numcars; i++) {

    sgid = find_next_road_entrysegm(themap);
    roadid = themap.segments[sgid].road_id;


    numberlanes = themap.segments[sgid].lanes.size();
    previntersect = themap.segments[sgid].start_intersect_id;
    nextintersect = themap.segments[sgid].end_intersect_id;
    //mincardist = (1600*themap.roads[roadid].avg_speed*2.25) / themap.roads[roadid].flow;
		mincardist = (60*60*themap.roads[roadid].avg_speed*numberlanes) / themap.roads[roadid].flow;
    //if (mincardist-distdeviation/2 > carsize+safedistmargin)
    //mincardist -= distdeviation/2;
    minspeed = themap.roads[roadid].avg_speed - speedrange/2;

    laneid = (int)rand()%numberlanes;
    xstart = themap.segments[sgid].lanes[laneid].xstart;
    ystart = themap.segments[sgid].lanes[laneid].ystart;
    speed = (themap.roads[roadid].avg_speed - speedrange/2) + ((int)rand()%(int)(speedrange + 1));

    // insert in lane
    car temp;

    temp.id = car_id++;
    temp.desiredv = speed;
    temp.currv = 0;
    temp.prevv = 0;
    temp.maxv = 1.1*speed;
    temp.minv = 0.9*speed;
    temp.road_segment_id = sgid;
    temp.presentlane = laneid;
    temp.targetlane = findtargetlane(speed, themap.roads[roadid].avg_speed, speedrange, numberlanes);
    temp.nextsegment = find_next_segment(themap, nextintersect, previntersect);
    temp.nextmove = find_next_move(themap, sgid, temp.nextsegment);
    if (temp.nextmove == LEFT || temp.nextmove == UTURN)
      temp.preferredlane = numberlanes-1;
    else if (temp.nextmove == RIGHT)
      temp.preferredlane = 0;
    else
      temp.preferredlane = temp.targetlane;

    temp.destx = themap.segments[sgid].lanes[laneid].xend;
    temp.desty = themap.segments[sgid].lanes[laneid].yend;
    temp.intransition = false;
    temp.changed_end_dest = false;
    temp.within_end_intersect = false;
    temp.reentry = true;
    temp.printed_ns2 = false;
		temp.macroscopic_mvt = "";
		temp.prevsegment = -2;

    // determine which lane to insert to: current lane or waitlist
    if (themap.segments[sgid].lanes[laneid].waitlist.size() > 0) {
      temp.reentry = false;
      iter = themap.segments[sgid].lanes[laneid].waitlist.end();
      car1 = themap.segments[sgid].lanes[laneid].waitlist.insert(iter, temp);
      iter = car1;
      iter--;
      car1->x = iter->x;
      car1->y = iter->y;
      update_car(themap, car1, (-1)*mincardist);
      car1->prevx = car1->x;
      car1->prevy = car1->y;

    }
    else if (themap.segments[sgid].lanes[laneid].lane.size() == 0) {
      iter = themap.segments[sgid].lanes[laneid].lane.end();
      car1 = themap.segments[sgid].lanes[laneid].lane.insert(iter, temp);
      car1->x = themap.segments[sgid].lanes[laneid].xstart;
      car1->y = themap.segments[sgid].lanes[laneid].ystart;

      // commented next 2 lines so cars don't start in mid-segment anymore
      //double segm_length = find_lanesegm_length (themap, sgid, laneid);
      //find_position_lane (themap, sgid, laneid, segm_length/2, car1->x, car1->y);
      car1->prevx = car1->x;
      car1->prevy = car1->y;
    }
    else {
      iter = themap.segments[sgid].lanes[laneid].lane.end();
      car1 = themap.segments[sgid].lanes[laneid].lane.insert(iter, temp);
      iter = car1;
      iter--;
      car1->x = iter->x;
      car1->y = iter->y;
      update_car(themap, car1, (-1)*mincardist);
      car1->prevx = car1->x;
      car1->prevy = car1->y;
    }

    // initialize car in ns-2 or in waitlist
    // only cars in current list should be initialized in ns-2
    if (find_offset_on_lane (themap, sgid, laneid, car1->x, car1->y) >= 0) {
      ns_id_vect.push_back(car1->id);
      int ns_id = ns_id_vect.size();
      car1->ns2_id = ns_id-1;
      //sprintf(tmpstr, "$node_(%d) set X_ %.1f\n", car1->ns2_id, car1->x);
      //str2 += tmpstr;
      //sprintf(tmpstr, "$node_(%d) set Y_ %.1f\n", car1->ns2_id, car1->y);
      //str2 += tmpstr;
    }
    else if (themap.segments[sgid].lanes[laneid].waitlist.size() == 0){
      car1->reentry = false;
      themap.segments[sgid].lanes[laneid].waitlist.push_back(*car1);
      themap.segments[sgid].lanes[laneid].lane.erase(car1);
    }
  }

  return;
}


void update_segment_info(mapstruct &themap, list<car>::iterator &car1, int sgid, double speedrange ) {

    double minspeed;
    int thisroad = themap.segments[sgid].road_id;
    int numberlanes = themap.segments[sgid].lanes.size();
    int previntersect = themap.segments[sgid].start_intersect_id;
    int nextintersect = themap.segments[sgid].end_intersect_id;
    double avgspeed = themap.roads[thisroad].avg_speed;
    int car1_road = themap.segments[car1->road_segment_id].road_id;

    minspeed = avgspeed - speedrange/2;
    double speed;
    //carMove nextmove;
    speed = minspeed + ((int)rand()%(int)(speedrange + 1));


    // passing from segments on same road
    // this is updated here
    if (car1->road_segment_id != sgid) {
      // don't change desired speed for same road
      if(car1_road == thisroad) {
				speed = car1->desiredv;
      }
      car1->road_segment_id = sgid;
      setdest(car1, themap.segments[sgid].lanes[car1->presentlane].xend, themap.segments[sgid].lanes[car1->presentlane].yend);
    }

    car1->targetlane = findtargetlane(speed, avgspeed, speedrange, numberlanes);
    car1->desiredv = speed;
    car1->maxv = 1.1*speed;
    car1->minv = 0.9*speed;
    //car1->presentlane = ((int)rand()%numberlanes) + 1;
    car1->nextsegment = find_next_segment(themap, nextintersect, previntersect);	//3/26/07
    car1->nextmove = find_next_move(themap, car1->road_segment_id, car1->nextsegment);// check where segment_id is updated in car
    if (car1->nextmove == LEFT || car1->nextmove == UTURN)
			car1->preferredlane = numberlanes-1;
    else if (car1->nextmove == RIGHT)
			car1->preferredlane = 0;
    else
			car1->preferredlane = car1->targetlane;

    return;
}


double speedEstimate(double interval, double braking, double locfrontthis, double locfrontother, double carsize, 
		     double desiredspeedthis, double prevspeedthis, double prevspeedother, double estimate, int id) {
  // formula of car following model
  // V_n(t+T) = b_n*T + [b_n^2*T^2 - b_n*(2*(X_(n-1)(t) - S_(n-1) - X_n(t)) - V_n(t)*T - (V_(n-1)(t)^2)/b# ) ]^1/2	

  double result=0.0;
  double temp = 0.0;

  temp = 2*(locfrontother - (carsize+2) - locfrontthis) - (prevspeedthis*interval) - (mypow(prevspeedother, 2)/estimate);
  temp = sqrt(mypow(braking, 2)*mypow(interval, 2) - (braking*temp));		
  result = braking*interval + temp;

  #ifdef DEBUG
  //if (result2 != result2) {
  cerr<<id<<" front this= "<<locfrontthis<<"  front oth= "<<locfrontother<<" nod_cv= "<<prevspeedthis<<" oth_pv= "<< prevspeedother<<" estim= "<<estimate<<" res= "<<result<<endl;
  //}
  #endif
  
  return result;

}


bool is_behind(mapstruct &themap, list<car>::iterator car1, list<car>::iterator car2, bool usex=true) {
  bool result = false;
  double tmp1, tmp2;
  //double xstart, ystart, xend, yend, x1, y1, x2, y2;
  //if (car1->road_segment_id == car2->road_segment_id) {

  int sgid = car2->road_segment_id;
  int laneid = car2->presentlane;


  tmp1 = find_distance(themap, car1, sgid, laneid);
  if (usex) {
    tmp2 = find_distance(themap, car2, sgid, laneid);
  }
  else {
    tmp2 = find_distance(themap, car2, sgid, laneid, false);
  }

  if (tmp1 < tmp2)
    result = true;
  else
    result = false;

  return result;
}




void save_car_state(list<car>::iterator &car1) {
	car1->prevv = car1->currv;
	car1->prevx = car1->x;
	car1->prevy = car1->y;

	return;
}


// JN* A VERIFIER 3/26/07
void position_lateral (mapstruct &themap, int newsegm_id, int newlane_id, list<car>::iterator &car1) {
  double xstart, ystart;
  xstart = themap.segments[newsegm_id].lanes[newlane_id].xstart;
  ystart = themap.segments[newsegm_id].lanes[newlane_id].ystart;

  // vertical segment
  if (themap.segments[newsegm_id].is_vertical) {
    car1->y = car1->y;
    car1->x = xstart;
  }
  // horizontal segment
  else if (themap.segments[newsegm_id].slope_a==0 ) {
    car1->x = car1->x;
    car1->y = ystart;
  }
  else {
    double perpendi_slope = -1/themap.segments[newsegm_id].slope_a;
    double perpendi_const = car1->y - perpendi_slope*car1->x;
    double thisline_const = ystart - themap.segments[newsegm_id].slope_a*xstart;

    car1->x = (thisline_const - perpendi_const)/(perpendi_slope - themap.segments[newsegm_id].slope_a);
    car1->y = themap.segments[newsegm_id].slope_a * car1->x + thisline_const;
  }
  car1->road_segment_id = newsegm_id;
  car1->presentlane = newlane_id;

  return;
}


double adjustSpeedRoutine (mapstruct &themap, list<car>::iterator &iter, bool usex, list<car>::iterator &tmpiter, bool usex2, double dist1, 
			 double dist2, int sgid, int laneid, double interval, double braking, double carsize) {

  double forwardthis, forwardother, xstart, ystart, xend, yend, speed;
  xstart = themap.segments[sgid].lanes[laneid].xstart;
  ystart = themap.segments[sgid].lanes[laneid].ystart;
  xend = themap.segments[sgid].lanes[laneid].xend;
  yend = themap.segments[sgid].lanes[laneid].yend;
  double tempv;

  if (usex)
    forwardthis = find_distance(themap, iter, sgid, laneid) + dist1;
  else
    forwardthis = find_distance(themap, iter, sgid, laneid, false) + dist1;

  if (tmpiter->id != iter->id && usex2) {
    forwardother = find_distance(themap, tmpiter, sgid, laneid) + dist2;
    tempv = tmpiter->currv;
  }
  else if (tmpiter->id != iter->id) {
    forwardother = find_distance(themap, tmpiter, sgid, laneid, false) + dist2;
    tempv = tmpiter->prevv;
  }
  else if (tmpiter->id == iter->id && !usex2) {
    forwardother = find_distance(xstart-xend, ystart-yend)+carsize+2;
    tempv = 0;
  }
  else {
    if (! iter->intransition) {
      xend = iter->destx;
      yend = iter->desty;
    }
    forwardother = find_distance(xstart-xend, ystart-yend)+3*carsize/2 + 2;
    tempv = 0; //iter->desiredv;
  }

  #ifdef DEBUG
  cerr<<"in routin xstart "<<xstart<<" ystart "<<ystart<<" fis "<<forwardthis<<" foth "<<forwardother<<endl;
  #endif
  
  if (forwardthis < 0.0 ) {
      forwardother = forwardother + (-2)*forwardthis;
      forwardthis = forwardthis + (-2)*forwardthis;
  }

  speed = speedEstimate(interval, braking, forwardthis, forwardother, carsize, 
			iter->desiredv, iter->currv, tempv, braking, iter->id);
  if (speed != speed) {
    return speed;
  }
  if ((speed-iter->currv)/interval > 2*(-1)*braking ) { //(-1)*braking
    speed = iter->currv + 2*(-1)*braking; // (-1)*braking*interval;2.50*interval
  }
  //if ((speed-iter->currv)/interval < braking) 
  //speed = iter->currv + braking*interval;
  if (speed > iter->maxv){
    speed = iter->maxv;
  }
  if (speed <= 0.00){
    speed = 0.00;
  }
  return speed;
}




void adjustSpeedFormula (double t, mapstruct &themap, list<car>::iterator &iter, list<car> &lanenext, int sgid, int laneid,
			 double interval, double braking, double carsize, bool urgency, int lane, int num, string &str2, int othersegm = -1) {//int lane, int num,

  list<car>::iterator tmpiter, tmpiter1, tmpiter2;
  double speednextsegm, speedstopsign;
  double tmpdbl1, tmpdbl2;

  trafficLightColor light = themap.lights[themap.segments[iter->road_segment_id].end_light_id].color;
  carMove nextmove = iter->nextmove;
  int nextsgid = iter->nextsegment;
  // set freeze parameter to false
  iter->freeze = true;
  
  #ifdef DEBUG  
  cerr<<"adjust formula car id="<<iter->id<<" ns2_id="<<iter->ns2_id<<" x="<<iter->x<<" y="<<iter->y<<" light="<<light<<" desv="<<iter->desiredv<<endl;
  #endif
  
  if (light == GREEN && nextmove == STRAIGHT) {
    // adjust speed with next segment
    speednextsegm = iter->desiredv;
    if (nextsgid != -1 && themap.segments[nextsgid].lanes[iter->presentlane].lane.size() > 0) {
      tmpiter2 = themap.segments[nextsgid].lanes[iter->presentlane].lane.end();
      tmpiter2--;
      #ifdef DEBUG
      cerr<<"adjust speed with front segm id = "<<tmpiter2->id<<endl;
      #endif
      speednextsegm = adjustSpeedRoutine (themap, iter, 1, tmpiter2, 0, carsize/2, carsize/2, 
					   nextsgid, tmpiter2->presentlane, interval, themap.default_braking, carsize);
    }


    tmpiter = lanenext.begin();
    while ( tmpiter != lanenext.end() && is_behind(themap, iter, tmpiter, false) ) {
      tmpiter++;
    }
    // first car adjust speed with stop sign
    if (tmpiter == lanenext.begin()) {
      save_car_state(iter);
      #ifdef DEBUG
      cerr<<"adjust speed green first car "<<endl;
      #endif
      tmpdbl1 = adjustSpeedRoutine (themap, iter, 1, iter, 1, carsize/2, carsize/2, sgid, laneid, interval, braking, carsize);
    }
    // non-first car adjust speed with car in front
    else {
      tmpiter--;
      save_car_state(iter);
      #ifdef DEBUG
      cerr<<"adjust speed green front = "<<tmpiter->id<<endl;
      #endif
      tmpdbl1 = adjustSpeedRoutine (themap, iter, 1, tmpiter, 0, carsize/2, carsize/2, sgid, laneid, interval, braking, carsize);
      tmpiter++;
    }
    tmpdbl2 = min(tmpdbl1, speednextsegm);
    if (((tmpdbl2 - iter->currv)/interval) < braking)
      tmpdbl2 = iter->currv - (-1)*interval*braking;
    if (! (tmpdbl1 != tmpdbl1)) {
      iter->currv = max(tmpdbl2, 0.0);
      update_car(themap, iter, iter->currv*interval);
      iter->freeze = false;
    }
    iter = lanenext.insert(tmpiter, *iter);
    return;
  }


  // adjust speed with next segment
  speednextsegm = iter->desiredv;
  if (nextsgid!= -1 && nextmove == STRAIGHT  && themap.segments[nextsgid].lanes[iter->presentlane].lane.size() > 0) {
    tmpiter2 = themap.segments[nextsgid].lanes[iter->presentlane].lane.end();
    tmpiter2--;
    #ifdef DEBUG
    cerr<<"adjust speed with straight front segm id = "<<tmpiter2->id<<endl;
    #endif
    speednextsegm = adjustSpeedRoutine (themap, iter, 1, tmpiter2, 0, carsize/2, carsize/2, 
					nextsgid, tmpiter2->presentlane, interval, themap.default_braking, carsize);
  }    
  else if (nextsgid != -1 && nextmove!= UTURN && themap.segments[nextsgid].lanes[0].lane.size() > 0) {
    tmpiter2 = themap.segments[nextsgid].lanes[0].lane.end();
    tmpiter2--;
    #ifdef DEBUG
    cerr<<"adjust speed with front segm id = "<<tmpiter2->id<<endl;
    #endif
    speednextsegm = adjustSpeedRoutine (themap, iter, 1, tmpiter2, 0, carsize/2, carsize/2, 
					nextsgid, tmpiter2->presentlane, interval, themap.default_braking, carsize);
  }   

  // adjust speed to stop sign if possible
  #ifdef DEBUG
  cerr<<"adjust stop sign "<<endl;
  #endif
  if (light == GREEN || iter->within_end_intersect) 
    speedstopsign = adjustSpeedRoutine (themap, iter, 1, iter, 1, carsize/2, carsize/2, sgid, laneid, interval, braking, carsize);
  else
    speedstopsign = adjustSpeedRoutine (themap, iter, 1, iter, 0, carsize/2, carsize/2, sgid, laneid, interval, braking, carsize);
    
  if (speedstopsign != speedstopsign)
    speedstopsign = iter->currv;

  // adjust speed with front car
  tmpiter = lanenext.begin();
  while ( tmpiter != lanenext.end() && is_behind(themap, iter, tmpiter, false) ) {
    tmpiter++;
  }
  if (tmpiter == lanenext.begin()) {
    save_car_state(iter);
    #ifdef DEBUG
    cerr<<"adjust speed first car "<<endl;
    #endif
    //tmpdbl1 = adjustSpeedRoutine (themap, iter, 1, iter, 0, carsize/2, carsize/2, sgid, laneid, interval, braking, carsize);
    tmpdbl1 = speedstopsign;
  }
  else {
    tmpiter--;
    save_car_state(iter);
    #ifdef DEBUG
    cerr<<"adjust speed front = "<<tmpiter->id<<endl;
    #endif
    tmpdbl1 = adjustSpeedRoutine (themap, iter, 1, tmpiter, 0, carsize/2, carsize/2, sgid, laneid, interval, braking, carsize);
    tmpiter++;
  }
  
  // compute new speed
  tmpdbl2 = min(speedstopsign, speednextsegm);
  if (((tmpdbl2 - iter->currv)/interval) < braking)
    tmpdbl2 = iter->currv - (-1)*interval*braking;
  tmpdbl2 = min(tmpdbl1, tmpdbl2);
      
  if (! (tmpdbl1 != tmpdbl1)) {
    iter->currv = max(tmpdbl2, 0.0);
    //iter->currv = tmpdbl2;
    update_car(themap, iter, iter->currv*interval);
    iter->freeze = false;
  }
  iter = lanenext.insert(tmpiter, *iter);

  return;
}



int checkLaneChange (double t, mapstruct &themap, list<car> targetlanecurr, list<car> targetlanenext, list<car>::iterator iter, 
		     double interval, double carsize, double braking, double safetydist) {
  list<car>::iterator tmpiter;
  list<car>::iterator backcurr, frontcurr, backtarget, fronttarget;
  int result = -1;
  double temp;
  double forwardthis, forwardother, xstart, ystart;
  int sgid, laneid;

  #ifdef DEBUG
  cerr<<"in check chg lane size "<<targetlanecurr.size()<<endl;
  #endif

  if (targetlanecurr.size() == 0) {
    #ifdef DEBUG
    cerr<<"-2 from point 1"<<endl;
    #endif
    return -2;
  }

  tmpiter = targetlanecurr.begin();
  while (tmpiter != targetlanecurr.end() && is_behind(themap, iter, tmpiter) ) {
    tmpiter++;
  }
  backcurr = tmpiter;
  if (backcurr == targetlanecurr.end() ) {
    frontcurr = --tmpiter;
    sgid = frontcurr->road_segment_id;
    laneid = frontcurr->presentlane;
    xstart = themap.segments[frontcurr->road_segment_id].lanes[frontcurr->presentlane].xstart;
    ystart = themap.segments[frontcurr->road_segment_id].lanes[frontcurr->presentlane].ystart;
    forwardthis = find_distance(themap, iter, frontcurr->road_segment_id, frontcurr->presentlane) + carsize;
    forwardother = find_distance(themap, frontcurr, frontcurr->road_segment_id, frontcurr->presentlane) + carsize/2;
    //forwardother = find_distance(xstart-frontcurr->x, ystart-frontcurr->y) + carsize/2;
    #ifdef DEBUG
    cerr<<"1- xstart "<<xstart<<" ystart "<<ystart<<" fis "<<forwardthis<<" fot "<<forwardother<<endl;
    #endif
    if (forwardthis < 0.0 ) {
      forwardother = forwardother + (-2)*forwardthis;
      forwardthis = forwardthis + (-2)*forwardthis;
    }
    temp = speedEstimate(interval, braking, forwardthis, forwardother, carsize, 
			 iter->desiredv, iter->currv, frontcurr->currv, braking, iter->id);
    if (temp != temp ) {
      result = -1;
      #ifdef DEBUG
      cerr<<"no chg result is nan front = "<<frontcurr->id<<endl;
      #endif
    }
    else if ((temp - iter->currv)/interval < braking) {
      result = -1;
      #ifdef DEBUG
      cerr<<"no change hard brak front = "<<frontcurr->id<<endl;
      #endif
    }
    else if ((forwardother - carsize - forwardthis) < safetydist) {
	     //find_headway(xstart, ystart, frontcurr->x, frontcurr->y, -1*carsize/2, iter->x, iter->y, carsize) 	
      result = -1;
      #ifdef DEBUG
      cerr<<"no chg headway = "<<(forwardother - carsize - forwardthis)<<endl;
      #endif
    }
    else {
      result = -2;
      #ifdef DEBUG
      cerr<<"-2 from point 2 front = "<<frontcurr->id<<endl;
      #endif
    }	
  }
  else if (backcurr == targetlanecurr.begin() ) {
    sgid = backcurr->road_segment_id;
    laneid = backcurr->presentlane;
    xstart = themap.segments[backcurr->road_segment_id].lanes[backcurr->presentlane].xstart;
    ystart = themap.segments[backcurr->road_segment_id].lanes[backcurr->presentlane].ystart;
    forwardthis = find_distance(themap, backcurr, backcurr->road_segment_id, backcurr->presentlane) + carsize/2;
    //forwardthis = find_distance(xstart-backcurr->x, ystart-backcurr->y) + carsize/2;
    forwardother = find_distance(themap, iter, backcurr->road_segment_id, backcurr->presentlane) + carsize/2;
    #ifdef DEBUG
    cerr<<"2- xstart "<<xstart<<" ystart "<<ystart<<" fis "<<forwardthis<<" fot "<<forwardother<<endl;
    #endif
    if (forwardother < 0.0 ) {
      forwardthis = forwardthis + (-2)*forwardother;
      forwardother = forwardother + (-2)*forwardother;
    }
    temp = speedEstimate(interval, braking, forwardthis, forwardother, carsize, 
			 backcurr->desiredv, backcurr->currv, iter->currv, braking, iter->id);
    if (temp != temp ) {
      result = -1;
      #ifdef DEBUG
      cerr<<"no chg result nan back  = "<<backcurr->id<<endl;
      #endif
    }
    else if ((temp - backcurr->currv)/interval < braking) {
      result = -1;
      #ifdef DEBUG
      cerr<<"no chg hard brak back = "<<backcurr->id<<endl;
      #endif
    }
    else if ((forwardother - carsize - forwardthis)< safetydist) {
      //find_headway(xstart, ystart, iter->x, iter->y, -1*carsize/2, backcurr->x, backcurr->y, carsize/2) 
      result = -1;
      #ifdef DEBUG
      cerr<<"no chg headway = "<<(forwardother - carsize - forwardthis)<<" back = "<<backcurr->id<<endl;
      #endif
    }
    else {
      result = -2;
      #ifdef DEBUG
      cerr<<"-2 from point 3 back = "<<backcurr->id<<endl;
      #endif
    }
  }
  else {
    frontcurr = backcurr;
    frontcurr--;
    sgid = frontcurr->road_segment_id;
    laneid = frontcurr->presentlane;
    xstart = themap.segments[backcurr->road_segment_id].lanes[backcurr->presentlane].xstart;
    ystart = themap.segments[backcurr->road_segment_id].lanes[backcurr->presentlane].ystart;
    forwardthis = find_distance(themap, backcurr, backcurr->road_segment_id, backcurr->presentlane) + carsize/2;
    //forwardthis = find_distance(xstart-backcurr->x, ystart-backcurr->y) + carsize/2;
    forwardother = find_distance(themap, iter, backcurr->road_segment_id, backcurr->presentlane) + carsize/2;
    #ifdef DEBUG
    cerr<<"3- xstart "<<xstart<<" ystart "<<ystart<<" fis "<<forwardthis<<" fot "<<forwardother<<endl;
    #endif
    if (forwardother < 0.0 ) {
      forwardthis = forwardthis + (-2)*forwardother;
      forwardother = forwardother + (-2)*forwardother;
    }
    temp = speedEstimate(interval, braking, forwardthis, forwardother, carsize, 
			 backcurr->desiredv, backcurr->currv, iter->currv, braking, iter->id);
    if (temp != temp ) {
      result = -1;
      #ifdef DEBUG
      cerr<<"no chg result is nan back = "<<backcurr->id<<endl;
      #endif
    }
    else if ((temp - backcurr->currv)/interval < braking) {
      result = -1;
      #ifdef DEBUG
      cerr<<"no chg hard brak back = "<<backcurr->id<<endl;
      #endif
    }
    else if ((forwardother - carsize - forwardthis) < safetydist) {
      //find_headway(xstart, ystart, iter->x, iter->y, -1*carsize/2, backcurr->x, backcurr->y, carsize/2) < (carsize/2)) {
      result = -1;
      #ifdef DEBUG
      cerr<<"no chg headway = "<<(forwardother - carsize - forwardthis) <<" back = "<<backcurr->id<<endl;
      #endif
    }
    else {
      xstart = themap.segments[frontcurr->road_segment_id].lanes[frontcurr->presentlane].xstart;
      ystart = themap.segments[frontcurr->road_segment_id].lanes[frontcurr->presentlane].ystart;
      forwardthis = find_distance(themap, iter, frontcurr->road_segment_id, frontcurr->presentlane) + carsize;
      forwardother = find_distance(themap, frontcurr, frontcurr->road_segment_id, frontcurr->presentlane) + carsize/2;
      #ifdef DEBUG
      cerr<<"4- xstart "<<xstart<<" ystart "<<ystart<<" fis "<<forwardthis<<" fot "<<forwardother<<endl;
      #endif
      if (forwardthis < 0.0 ) {
	forwardother = forwardother + (-2)*forwardthis;
	forwardthis = forwardthis + (-2)*forwardthis;
      }     
      temp = speedEstimate(interval, braking, forwardthis, forwardother, carsize, 
			   iter->desiredv, iter->currv, frontcurr->currv, braking, iter->id);
      if (temp != temp ) {
	result = -1;
	#ifdef DEBUG
	cerr<<"no chg result is nan front = "<<frontcurr->id<<endl;
	#endif
      }
      else if ((temp - iter->currv)/interval < braking) {
	result = -1;
	#ifdef DEBUG
	cerr<<"no chg hard brak front = "<<frontcurr->id<<endl;
	#endif
      }
      else if ((forwardother - carsize - forwardthis) < safetydist) {
	result = -1;
	#ifdef DEBUG
	cerr<<"no chg headway "<<(forwardother - carsize - forwardthis)<<" front = "<<frontcurr->id<<endl;
	#endif
      }
      else {
	result = -2;
	#ifdef DEBUG
	cerr<<"-2 from point 4 back = "<<backcurr->id<<" front "<<frontcurr->id<<endl;
	#endif
      }
    }
  }


  if (result != -1 && targetlanenext.size() != 0) {
    tmpiter = targetlanenext.begin();
    while ( tmpiter != targetlanenext.end() && is_behind(themap, iter, tmpiter) ) {
      tmpiter++;
    }
				
    backtarget = tmpiter;
    if (backtarget == targetlanenext.end() ) {
      fronttarget = --tmpiter;
      xstart = themap.segments[fronttarget->road_segment_id].lanes[fronttarget->presentlane].xstart;
      ystart = themap.segments[fronttarget->road_segment_id].lanes[fronttarget->presentlane].ystart;
      forwardthis = find_distance(themap, iter, fronttarget->road_segment_id, fronttarget->presentlane) + carsize;
      forwardother = find_distance(themap, fronttarget, fronttarget->road_segment_id, fronttarget->presentlane) + carsize/2;
      if (forwardthis < 0.0 ) {
	forwardother = forwardother + (-2)*forwardthis;
	forwardthis = forwardthis + (-2)*forwardthis;
      }
      temp = speedEstimate(interval, braking, forwardthis, forwardother, carsize, 
			   iter->desiredv, iter->currv, fronttarget->prevv, braking, iter->id);
      if (temp != temp ) {
	result = -1;
	#ifdef DEBUG
	cerr<<"no chg result is nan frontt = "<<fronttarget->id<<endl;
	#endif
      }
      else if ((temp - iter->currv)/interval < braking) {
	result = -1;
	#ifdef DEBUG
	cerr<<"no chg hard brak frontt = "<<fronttarget->id<<endl;
	#endif
      }
      else if ((forwardother - carsize - forwardthis) < safetydist) {
	result = -1;
	#ifdef DEBUG
	cerr<<"no chg headway "<<(forwardother - carsize - forwardthis)<<" frontt = "<<fronttarget->id<<endl;
	#endif
      }
      else {
	result = -2;
	#ifdef DEBUG
	cerr<<"-2 from point 5 frontt = "<<fronttarget->id<<endl;
	#endif
      }
    }
    else if (backtarget == targetlanenext.begin() ) {
      xstart = themap.segments[backtarget->road_segment_id].lanes[backtarget->presentlane].xstart;
      ystart = themap.segments[backtarget->road_segment_id].lanes[backtarget->presentlane].ystart;
      forwardthis = find_distance(themap, backtarget, backtarget->road_segment_id, backtarget->presentlane) + carsize/2;
      //forwardthis = find_distance(xstart-backtarget->x, ystart-backtarget->y) + carsize/2;
      forwardother = find_distance(themap, iter, backtarget->road_segment_id, backtarget->presentlane) + carsize/2;
      if (forwardother < 0.0 ) {
	forwardthis = forwardthis + (-2)*forwardother;
	forwardother = forwardother + (-2)*forwardother;
      }

      temp = speedEstimate(interval, braking, forwardthis, forwardother, carsize, 
			   backtarget->desiredv, backtarget->currv, iter->currv, braking, iter->id);
      if (temp != temp ) {
	result = -1;
	#ifdef DEBUG
	cerr<<"no chg result nan backt = "<<backtarget->id<<endl;
	#endif
      }
      else if ((temp - backtarget->currv)/interval < braking) {
	result = -1;
	#ifdef DEBUG
	cerr<<"no chg hard brak backt = "<<backtarget->id<<endl;
	#endif
      }
      else if ((forwardother - carsize - forwardthis) < safetydist) {
	result = -1;
	#ifdef DEBUG
	cerr<<"no chg headway "<<(forwardother - carsize - forwardthis)<<" backt = "<<backtarget->id<<endl;
	#endif
      }
      else {
	result = backtarget->id;
	#ifdef DEBUG
	cerr<<result<<" from point 6 backt = "<<backtarget->id<<endl;
	#endif
      }
    }
    else {
      fronttarget = backtarget;
      fronttarget--;
      xstart = themap.segments[backtarget->road_segment_id].lanes[backtarget->presentlane].xstart;
      ystart = themap.segments[backtarget->road_segment_id].lanes[backtarget->presentlane].ystart;
      forwardthis = find_distance(themap, backtarget, backtarget->road_segment_id, backtarget->presentlane) + carsize/2;
      forwardother = find_distance(themap, iter, backtarget->road_segment_id, backtarget->presentlane) + carsize/2;
      if (forwardother < 0.0 ) {
	forwardthis = forwardthis + (-2)*forwardother;
	forwardother = forwardother + (-2)*forwardother;
      }
      temp = speedEstimate(interval, braking, forwardthis, forwardother, carsize, 
			   backtarget->desiredv, backtarget->currv, iter->currv, braking, iter->id);
      if (temp != temp ) {
	result = -1;
	#ifdef DEBUG
	cerr<<"no chg result nan backt = "<<backtarget->id<<endl;
	#endif
      }
      else if ((temp - backtarget->currv)/interval < braking) {
	result = -1;
	#ifdef DEBUG
	cerr<<"no chg hard brak backt = "<<backtarget->id<<endl;
	#endif
      }
      else if ((forwardother - carsize - forwardthis) < safetydist) {
	result = -1;
	#ifdef DEBUG
	cerr<<"no chg headway "<<(forwardother - carsize - forwardthis)<<" backt = "<<backtarget->id<<endl;
	#endif
      }
      else {
	xstart = themap.segments[fronttarget->road_segment_id].lanes[fronttarget->presentlane].xstart;
	ystart = themap.segments[fronttarget->road_segment_id].lanes[fronttarget->presentlane].ystart;
	forwardthis = find_distance(themap, iter, fronttarget->road_segment_id, fronttarget->presentlane) + carsize;
	forwardother = find_distance(themap, fronttarget, fronttarget->road_segment_id, fronttarget->presentlane) + carsize/2;
	if (forwardthis < 0.0 ) {
	  forwardother = forwardother + (-2)*forwardthis;
	  forwardthis = forwardthis + (-2)*forwardthis;
	}
	temp = speedEstimate(interval, braking, forwardthis, forwardother, carsize, 
			     iter->desiredv, iter->currv, fronttarget->prevv, braking, iter->id);
	if (temp != temp ) {
	  result = -1;
	  #ifdef DEBUG
	  cerr<<"no chg result is nan frontt = "<<fronttarget->id<<endl;
	  #endif
	}
	else if ((temp - iter->currv)/interval < braking) {
	  result = -1;
	  #ifdef DEBUG
	  cerr<<"no chg hard brak frontt = "<<fronttarget->id<<endl;
	  #endif
	}
	else if ((forwardother - carsize - forwardthis) < safetydist) {
	  result = -1;
	  #ifdef DEBUG
	  cerr<<"no chg headway "<<(forwardother - carsize - forwardthis)<<" frontt = "<<fronttarget->id<<endl;
	  #endif
	}
	else {
	  result = backtarget->id;
	  #ifdef DEBUG
	  cerr<<result<<" from point 7 frontt = "<<fronttarget->id<<" backt = "<<backtarget->id<<endl;
	  #endif
	}
      }
    }
  }

  return result;
}


void check_present_lane(double t, mapstruct &themap, list<car>::iterator &iter, list<car> &lanenext, int sgid, int laneid,
			double carsize, float interval, double braking, bool urgency,  
			int lane, string &str2, int othersegm = -1) {
		
  list<car>::iterator tmpiter;
  //double tmpdbl1, tmpdbl2;
  #ifdef DEBUG
  cerr<<"in check present lane "<<endl;
  #endif
  // speed is within desired interval
  adjustSpeedFormula (t, themap, iter, lanenext, sgid, laneid, interval, braking, carsize, urgency, lane, 1, str2, othersegm);				

  print_ns2(t, themap, iter, str2);

  return;
}


bool on_exit_lane_intersect (mapstruct &themap, car iter, double carsize) {
  int sgid = iter.road_segment_id;
  int laneid = iter.presentlane;
  double xinters = themap.segments[sgid].lanes[laneid].xstart;
  double yinters = themap.segments[sgid].lanes[laneid].ystart;
  double dist = find_distance(xinters-iter.x, yinters-iter.y);

  if (dist < 2*carsize) {
    #ifdef DEBUG
    cerr<<"from on exit funct "<<endl;
    #endif
    return true;
  }
  else
    return false;

}


void request_lane_change (double t, mapstruct &themap, list<car>::iterator &iter, int infrontof, 
			  list<car> &lanenextother, double carsize, float interval, double braking, 
			  double safetydist, int othersegm, int otherlane, string &str2, int nostopline =0 ) {


  list<car>::iterator tmpiter, tmpiter1;
  //double temp, temp1, timeneed;
  double minprogression, tmpdbl1;

  //  if (urgency)
  //  minprogression = carsize/2;
  //else
    minprogression = carsize/2;

    // adjust to current other lane
    tmpdbl1 = iter->maxv;
    tmpiter = themap.segments[othersegm].lanes[otherlane].lane.begin();
    while ( tmpiter != themap.segments[othersegm].lanes[otherlane].lane.end() &&  is_behind(themap, iter, tmpiter) ) {
      tmpiter++;
    }

    if (tmpiter != themap.segments[othersegm].lanes[otherlane].lane.begin() && 
	themap.segments[othersegm].lanes[otherlane].lane.size() > 0 ) {
      tmpiter--;
      tmpdbl1  = adjustSpeedRoutine (themap, iter, 1, tmpiter, 1, carsize/2, carsize/2, othersegm, 
				     otherlane, interval, braking, carsize);
    }


  // lane change possible
  //change to end of lanenextother
  if (infrontof == -2 && lanenextother.size()==0) { 
    #ifdef DEBUG
    cerr<<"req lane chg 1"<<endl;
    #endif
    iter = lanenextother.insert(lanenextother.end(), *iter);
    tmpiter = lanenextother.end();
    tmpiter--;
 
    // save state
    save_car_state(tmpiter);

    //compute new position
    position_lateral (themap, othersegm, otherlane, tmpiter);
    setdest(tmpiter, themap.segments[othersegm].lanes[otherlane].xend, themap.segments[othersegm].lanes[otherlane].yend);
    update_car(themap, tmpiter, minprogression);
    if (tmpiter->within_end_intersect) {
      tmpiter->currv  = adjustSpeedRoutine (themap, tmpiter, 1, tmpiter, 1, carsize/2, carsize/2, othersegm, 
					    otherlane, interval, braking, carsize);
    }
    else {
      tmpiter->currv  = adjustSpeedRoutine (themap, tmpiter, 1, tmpiter, nostopline, carsize/2, carsize/2, othersegm, 
					    otherlane, interval, braking, carsize);
    }
  }
  else if (infrontof == -2 ) { 
    #ifdef DEBUG
    cerr<<"req lane chg 2"<<endl;
    #endif
    iter = lanenextother.insert(lanenextother.end(), *iter);
    tmpiter = lanenextother.end();
    tmpiter--;

    tmpiter1 = --tmpiter;
    tmpiter++;

    // save state
    save_car_state(tmpiter);

    //compute new position
    position_lateral (themap, othersegm, otherlane, tmpiter);
    setdest(tmpiter, themap.segments[othersegm].lanes[otherlane].xend, themap.segments[othersegm].lanes[otherlane].yend);
    update_car(themap, tmpiter, minprogression);
    tmpiter->currv  = adjustSpeedRoutine (themap, tmpiter, 1, tmpiter1, 0, carsize/2, carsize/2, othersegm, 
					    otherlane, interval, braking, carsize);
  }
  else {	// change to somewhere else, not end of target lane
    #ifdef DEBUG
    cerr<<"req lane chg 3 infr = "<<infrontof<<endl;
    #endif
    tmpiter = lanenextother.begin();
    while ( tmpiter != lanenextother.end() && tmpiter->id != infrontof ) {
      tmpiter++;
    }
    iter = lanenextother.insert(tmpiter, *iter);
    tmpiter--;

    save_car_state(tmpiter);
    //compute new position
    position_lateral (themap, othersegm, otherlane, tmpiter);
    setdest(tmpiter, themap.segments[othersegm].lanes[otherlane].xend, themap.segments[othersegm].lanes[otherlane].yend);
    update_car(themap, tmpiter, minprogression);
    // check if newly inserted node is head of list
    if (tmpiter == lanenextother.begin()) {
      #ifdef DEBUG
      cerr<<"in rqt lane chg hd infr = "<<infrontof<<endl;
      #endif
      if (tmpiter->within_end_intersect) {
	tmpiter->currv = adjustSpeedRoutine (themap, tmpiter, 1, tmpiter, 1, carsize/2, carsize/2, othersegm, 
					   otherlane, interval, braking, carsize);
      }
      else {
	tmpiter->currv = adjustSpeedRoutine (themap, tmpiter, 1, tmpiter, nostopline, carsize/2, carsize/2, othersegm, 
					   otherlane, interval, braking, carsize);
      }
    } 
    // newly inserted node in not head of list
    else {
      tmpiter1 = --tmpiter;
      tmpiter++;

      #ifdef DEBUG
      cerr<<"in rqt lane chg not hd infr = "<<infrontof<<endl;
      #endif
      tmpiter->currv  = adjustSpeedRoutine (themap, tmpiter, 1, tmpiter1, 0, carsize/2, carsize/2, othersegm, 
					    otherlane, interval, braking, carsize);
    }
  }			
  iter->currv = min(iter->currv, tmpdbl1);
  iter->destx = iter->x;
  iter->desty = iter->y;


  return;
}


void transition_car (mapstruct &themap, list<car>::iterator iter, list<car> &lanenext, float interval) {
  
  // mark node in bewteen lanes
  double timeneed = find_distance(iter->prevx-iter->x, iter->prevy-iter->y)/iter->currv;
  if (timeneed > interval) {
    iter->intransition = true;
    iter->x = iter->prevx;
    iter->y = iter->prevy;
    update_car(themap, iter, iter->currv*interval);
    list<car>::iterator tmpiter = lanenext.begin();
    while(tmpiter!=lanenext.end() && is_behind(themap, iter, tmpiter)) {
      tmpiter++;
    }
    lanenext.insert(tmpiter, *iter);
  }

  return;
}


void chgRequestTurnNear (double t, mapstruct &themap, list<car>::iterator &iter, vector<list<car> >&lanenext, double safetydist,
		   double braking, float interval, double carsize, string &str2) {

  int thissegm = iter->road_segment_id;
  int laneid = iter->presentlane;
  int otherlane;
  int infronttarget = -1;
  int numberlanes = themap.segments[thissegm].lanes.size();
  numberlanes--;
  bool urgency = true;
  double tmpdbl1, tmpdbl2;
  list<car>::iterator tmpiter2;

  #ifdef DEBUG
  cerr<<"segm "<<thissegm<<" "<<themap.segments[thissegm].start_intersect_id<<"->"<<themap.segments[thissegm].end_intersect_id<<endl;
  #endif
  if (!on_exit_lane_intersect (themap, *iter, carsize) ) {
    if (iter->preferredlane > laneid) {
      otherlane = laneid+1;
      #ifdef DEBUG
      cerr<<"oth lan1 = "<<otherlane<<" this segm = "<<thissegm<<endl;
      cerr<<"lane size "<<themap.segments[thissegm].lanes[laneid+1].lane.size()<<endl;
      #endif
      infronttarget = checkLaneChange(t, themap, themap.segments[thissegm].lanes[laneid+1].lane, 
				  lanenext[laneid+1], iter, interval, carsize, braking, safetydist);
    }
    else {
      otherlane = laneid-1;
      #ifdef DEBUG
      cerr<<"oth lan2 = "<<otherlane<<" this segm = "<<thissegm<<endl;
      cerr<<"lane size "<<themap.segments[thissegm].lanes[laneid-1].lane.size()<<endl;
      #endif
      infronttarget = checkLaneChange(t, themap, themap.segments[thissegm].lanes[laneid-1].lane, 
				  lanenext[laneid-1], iter, interval, carsize, braking, safetydist);
    }

    if (infronttarget != -1 ) {
      #ifdef DEBUG
      cerr<<"req chg 1 "<<endl;
      #endif
      request_lane_change (t, themap, iter,  infronttarget, 
			  lanenext[otherlane], carsize, interval, braking,
			  safetydist, thissegm, otherlane, str2);
     transition_car (themap, iter, lanenext[laneid], interval);
    }
    else {
      // try reducing 1.5m/s speed if going to lesser speed lane if possible
      tmpdbl1 = iter->currv;
      tmpdbl2 = tmpdbl1;
      tmpdbl2 = tmpdbl2 - 1.5;
      tmpdbl2 = max(tmpdbl2, 0.0);

      adjustSpeedFormula (t, themap, iter, lanenext[laneid], thissegm, laneid, 
			    interval, braking, carsize, urgency, laneid, 8, str2);
      if (otherlane < laneid && tmpdbl2 < iter->currv && iter->freeze==false) {
				iter->x = iter->prevx;
				iter->y = iter->prevy;
				iter->currv = tmpdbl2;
				update_car(themap, iter, iter->currv*interval);
      }
    }
  }
  else {
    infronttarget = -1;
    adjustSpeedFormula (t, themap, iter, lanenext[laneid], thissegm, laneid, 
			    interval, braking, carsize, urgency, laneid, -8, str2);	
  }    


  if (infronttarget !=-1 && !iter->intransition) {
    // print_ns2(t, themap, iter, str2);
    setdest(iter, themap.segments[iter->road_segment_id].lanes[iter->presentlane].xend,
	    themap.segments[iter->road_segment_id].lanes[iter->presentlane].yend);
  }
  //output position
  print_ns2(t, themap, iter, str2);

  return;
}



void chgRequestAwayTurn (double t, mapstruct &themap, list<car>::iterator &iter, vector<list<car> >&lanenext, double safetydist,
		   double braking, float interval, double carsize, string &str2) {

  int thissegm = iter->road_segment_id;
  int laneid = iter->presentlane, otherlane;
  int infronttarget = -1;
  int numberlanes = themap.segments[thissegm].lanes.size();
  numberlanes--;
  bool urgency = false;
  list<car>::iterator tmpiter2;

  #ifdef DEBUG
  cerr<<"segm "<<thissegm<<" "<<themap.segments[thissegm].start_intersect_id<<"->"<<themap.segments[thissegm].end_intersect_id<<endl;
  #endif
  if (!on_exit_lane_intersect (themap, *iter, carsize) ) {
    if (iter->preferredlane > laneid) {
      otherlane = laneid+1;
      #ifdef DEBUG
      cerr<<"oth lan1 = "<<otherlane<<" away this segm = "<<thissegm<<endl;
      cerr<<"lane size "<<themap.segments[thissegm].lanes[laneid+1].lane.size()<<endl;
      #endif
      infronttarget = checkLaneChange(t, themap, themap.segments[thissegm].lanes[laneid+1].lane, 
				  lanenext[laneid+1], iter, interval, carsize, braking, safetydist);
    }
    else {
      otherlane = laneid-1;
      #ifdef DEBUG
      cerr<<"oth lan2 = "<<otherlane<<" away this segm = "<<thissegm<<endl;
      cerr<<"lane size "<<themap.segments[thissegm].lanes[laneid-1].lane.size()<<endl;
      #endif
      infronttarget = checkLaneChange(t, themap, themap.segments[thissegm].lanes[laneid-1].lane, 
				  lanenext[laneid-1], iter, interval, carsize, braking, safetydist);
    }

    if (infronttarget != -1 ) {
      #ifdef DEBUG
      cerr<<"req chg 1 away "<<endl;
      #endif
      request_lane_change (t, themap, iter,  infronttarget, 
			  lanenext[otherlane], carsize, interval, braking, 
			  safetydist, thissegm, otherlane, str2);
     transition_car (themap, iter, lanenext[laneid], interval);
    }
    else {
      adjustSpeedFormula (t, themap, iter, lanenext[laneid], thissegm, laneid, 
			    interval, braking, carsize, urgency, laneid, 8, str2);	
    }
  }
  else {
    infronttarget = -1;
    adjustSpeedFormula (t, themap, iter, lanenext[laneid], thissegm, laneid, 
			    interval, braking, carsize, urgency, laneid, -8, str2);	
  }    

  if (infronttarget != -1 && !iter->intransition) {
    //print_ns2(t, themap, iter, str2);
    setdest(iter, themap.segments[iter->road_segment_id].lanes[iter->presentlane].xend,
	    themap.segments[iter->road_segment_id].lanes[iter->presentlane].yend);
  }

  //output position
  print_ns2(t, themap, iter, str2);

  return;
}




void update_in_transition(double t, mapstruct &themap, 
													list<car>::iterator &iter, int sgid, 
													int index , list<car> &lanenext, double braking,
													float interval, double carsize, string &str2 ) {

  if (iter->presentlane == index && iter->road_segment_id == sgid) {
    #ifdef DEBUG
    cerr<<"in update transition dest lane from sgid "<<sgid<<" lane "<<index<<endl;
    #endif
    int thissegm = iter->road_segment_id;
		// check if within_lane_boundary ? don't know

    adjustSpeedFormula (t, themap, iter, lanenext, iter->road_segment_id,
												iter->presentlane, interval, braking, carsize, 
												false, iter->presentlane, 9, str2);
		if (find_distance(iter->prevx,iter->prevy, iter->destx, iter->desty) <
				find_distance(iter->prevx, iter->prevy, iter->x, iter->y)) {
			double timeneed = (find_distance(iter->prevx,iter->prevy, 
												iter->destx, iter->desty))/iter->currv;
			iter->x = iter->destx;
			iter->y = iter->desty;
			iter->intransition = false;
			print_ns2(t, themap, iter, str2);
			setdest(iter, themap.segments[thissegm].lanes[index].xend,
							themap.segments[thissegm].lanes[index].yend);
			update_car(themap, iter, (interval-timeneed)*iter->currv);
			t = t+timeneed;
			//print_ns2(t, themap, iter, str2);
			//iter->near_stop_turning = false;
			#ifdef DEBUG
			cerr<<"now in transition = false "<<endl;
			#endif
		}
		print_ns2(t, themap, iter, str2);
	}
  else {
    #ifdef DEBUG
    cerr<<"in update transition prev lane  from sgid "<<sgid<<" lane "<<index<<endl;
    #endif
    int segm = iter->road_segment_id;
    int laneid = iter->presentlane;
    list<car>::iterator tmpiter =
				themap.segments[segm].lanes[laneid].lane.begin();
    while(tmpiter!= themap.segments[segm].lanes[laneid].lane.end() &&
					tmpiter->id != iter->id) {
      tmpiter++;
    }
    if (tmpiter->intransition) {
      list<car>::iterator tmpiter2 = lanenext.begin();
      while(tmpiter2 != lanenext.end() && is_behind(themap, iter, 
						tmpiter2, false)) {
				tmpiter2++;
      }
      lanenext.insert(tmpiter2, *tmpiter);
    }
  }
  return;
}


bool move_car_loop(vector< list<car>::iterator > &abslane, mapstruct &themap, int segment_id) {
  int i=0;
  bool result = false;
  while ( i < (int)themap.segments[segment_id].lanes.size() ) {
    if (abslane[i] != themap.segments[segment_id].lanes[i].lane.end() ) {
      result = true;
      return result;
    }
    i++;
  }		
  return result;
}


bool near_stop_sign(mapstruct &themap, list<car>::iterator car1, float interval, double carsize) {
	int sgid = car1->road_segment_id;
	int numlane = car1->presentlane;
  double xend = themap.segments[sgid].lanes[numlane].xend;
  double yend = themap.segments[sgid].lanes[numlane].yend;
	double distend = find_distance(car1->x-xend,car1->y-yend);
	if (car1->nextsegment == -1) {
		double xstart = themap.segments[sgid].lanes[numlane].xstart;
		double ystart = themap.segments[sgid].lanes[numlane].ystart;
		double x1 = find_distance(xstart-xend,ystart-yend);
		double x2 = find_distance(xstart-car1->x,ystart-car1->y);
		if (x1 <= x2+carsize/2) {
			return true;
		}
		return false;
	}
	
  if (distend <= themap.roads[themap.segments[sgid].road_id].avg_speed*interval ||
      distend <= car1->desiredv*interval ||
      distend <= carsize || 
			car1->changed_end_dest == true)// PROBABLY TO CHANGE!!!!!!
    return true;
  else
    return false;
}


bool intended_turn_near(mapstruct &themap, list<car>::iterator car1, double startinterval) {
  double xend = themap.segments[car1->road_segment_id].lanes[car1->presentlane].xend;
  double yend = themap.segments[car1->road_segment_id].lanes[car1->presentlane].yend;
  // if (car1->nextmove == STRAIGHT)
  // return false;
  //else {
    // is car within startinterval of turn
  double timeneed = find_distance(car1->x-xend, car1->y-yend)/car1->desiredv;
  if (timeneed <= startinterval) {
      return true;
  }
  else {
      return false;
  }
    //}
}


double find_new_braking(mapstruct &themap, list<car>::iterator car1, double braking, double startinterval) {

  double xend = themap.segments[car1->road_segment_id].lanes[car1->presentlane].xend;
  double yend = themap.segments[car1->road_segment_id].lanes[car1->presentlane].yend;
  double result;
  result = (2 - find_distance(car1->x-xend, car1->y-yend)/(startinterval*car1->desiredv) )*braking;
  return result;

}



void insert_waiting_list(double t, mapstruct &themap, int roadid, int sgid, list<car>::iterator &car1, double speedrange, string &str2) {
  double dist;
  list<car>::iterator iter, tmpiter;
  int numberlanes, laneid=0, nextintersect;
  double speed, xsave, ysave, xstart, ystart;
  


  numberlanes = themap.segments[sgid].lanes.size();
  laneid = (int)rand()%numberlanes;
  nextintersect = themap.segments[sgid].end_intersect_id;
  xsave = car1->x;
  ysave = car1->y;
  xstart = themap.segments[sgid].lanes[laneid].xstart;
  ystart = themap.segments[sgid].lanes[laneid].ystart;


  //dist = (1600*themap.roads[roadid].avg_speed*2.25) / themap.roads[roadid].flow;
	dist = (60*60*themap.roads[roadid].avg_speed*numberlanes) / themap.roads[roadid].flow;
  speed = (themap.roads[roadid].avg_speed - speedrange/2) + ((int)rand()%(int)(speedrange + 1));

  // insert in waitlist 
  iter = themap.segments[sgid].lanes[laneid].waitlist.end();
  car1 = themap.segments[sgid].lanes[laneid].waitlist.insert(iter, *car1);

  car1->desiredv = speed;
  car1->currv = 0;
  car1->prevv = 0;
  car1->maxv = 1.1*speed;
  car1->minv = 0.9*speed;
  car1->road_segment_id = sgid;
  car1->presentlane = laneid;
  car1->targetlane = findtargetlane(speed, themap.roads[roadid].avg_speed,
																		speedrange, numberlanes);
  car1->nextsegment = find_next_segment(themap, nextintersect);
  car1->nextmove = find_next_move(themap, sgid, car1->nextsegment);
  if (car1->nextmove == LEFT || car1->nextmove == UTURN)
     car1->preferredlane = numberlanes-1;
  else if (car1->nextmove == RIGHT)
     car1->preferredlane = 0;
  else
     car1->preferredlane = car1->targetlane;

  car1->destx = themap.segments[sgid].lanes[laneid].xend;
  car1->desty = themap.segments[sgid].lanes[laneid].yend;
  car1->intransition = false;
  car1->within_end_intersect = false;
  car1->changed_end_dest = false;

  if (themap.segments[sgid].lanes[laneid].waitlist.size() > 1) {
    iter = car1;
    iter--;
    car1->x = iter->x;
    car1->y = iter->y;
    update_car(themap, car1, (-1)*dist);
    car1->prevx = car1->x;
    car1->prevy = car1->y;
  }
  else {
    car1->x = themap.segments[sgid].lanes[laneid].xstart;
    car1->y = themap.segments[sgid].lanes[laneid].ystart;
    update_car(themap, car1, (-1)*dist);
    car1->prevx = car1->x;
    car1->prevy = car1->y;
  }

  // printing for  ns-2
	double speedneeded = find_distance(xstart, 1.0, xsave, ysave)/1.0;
	print_exit_ns2 (t, themap, car1, speedneeded, xstart, str2);

  return;
}



void node_exit(double t, mapstruct &themap, list<car>::iterator &car1, double speedrange, string &str2) {
  //char * tmpstr = new char[100];

  // find next road for this car
  //int next_road_id = find_next_road(themap);
  //insert_waiting_list(t, themap, next_road_id, car1, speedrange, str2);

  int next_entry_road_sgid = find_next_road_entrysegm(themap);
	int roadid = themap.segments[next_entry_road_sgid].road_id;
  insert_waiting_list(t, themap, roadid, next_entry_road_sgid, 
											car1, speedrange, str2);

  return;
}


string print (mapstruct &themap, list<car>::iterator car1) {
  string str = "";
  char * tmpstr = new char [300];
  sprintf(tmpstr, "id %d x %.2f y %.2f currv %.2f desiredv %.2f segm %d->%d nextsegm %d->%d targlane %d presentlane %d preflane %d prevx %.2f prevy %.2f prevv %.2f nextmov %d destx %.2f desty %.2f \n",
	  car1->ns2_id, car1->x, car1->y, car1->currv, car1->desiredv, themap.segments[car1->road_segment_id].start_intersect_id, themap.segments[car1->road_segment_id].end_intersect_id, 
	  themap.segments[car1->nextsegment].start_intersect_id, themap.segments[car1->nextsegment].end_intersect_id, car1->targetlane, car1->presentlane, 
	  car1->preferredlane, car1->prevx, car1->prevy, car1->prevv, car1->nextmove, car1->destx, car1->desty);
  str += tmpstr;

  return str;

}


void refresh_waiting_list(double t, mapstruct &themap, float interval, 
													int sgid, int laneid, double carsize, 
													double braking, double safetydist, 
													string &str2, string &macrostr) {
	
	if ( ! themap.segments[sgid].lanes[laneid].waitlist.size() > 0)
		return;
		
  double dist, xstart, ystart;
  list<car>::iterator iter, tmpiter;
  int infronttarget;
	int count = 0, sizebefore;
	
  dist = themap.roads[themap.segments[sgid].road_id].avg_speed*interval;
  xstart = themap.segments[sgid].lanes[laneid].xstart;
  ystart = themap.segments[sgid].lanes[laneid].ystart;
  iter = themap.segments[sgid].lanes[laneid].waitlist.begin();

  while (iter != themap.segments[sgid].lanes[laneid].waitlist.end()) {
		sizebefore = themap.segments[sgid].lanes[laneid].waitlist.size();
		count++;
    if (find_offset_on_lane (themap, sgid, laneid, iter->x, iter->y) < 0) {
      update_car(themap, iter, dist);
    }
    if (find_offset_on_lane (themap, sgid, laneid, iter->x, iter->y) >= 0 && 
			iter == themap.segments[sgid].lanes[laneid].waitlist.begin()) {
      iter->x = xstart;
      iter->y = ystart;
      infronttarget = checkLaneChange(t, themap,
																			themap.segments[sgid].lanes[laneid].lane,
																			themap.segments[sgid].lanes[laneid].lane,
																			iter, interval, carsize, braking,
																			safetydist);	
      if (infronttarget != -1) {
				if (iter->reentry == true) {
					//sprintf(tmpstr, "$ns_ at %.2f \"$node_(%d) set Y_ %.2f\" \t;#ref \n", t-1.0, iter->ns2_id, iter->y);
					//str2 += tmpstr;
					double speedneeded = find_distance(xstart, 1.0, iter->x, iter->y)/1.0;
					if (!iter->printed_ns2 ) {
						print_firstentry_ns2 (t, themap, iter, str2);
						//record macroscopic trace in node structure
						macrostr += iter->macroscopic_mvt;
						iter->macroscopic_mvt = "";
					}
					print_reentry_ns2 (t, themap, iter, speedneeded, str2);
				}
				else {
					iter->reentry = true;
					ns_id_vect.push_back(iter->id);
					int ns_id = ns_id_vect.size();
					iter->ns2_id = ns_id-1;
					print_firstentry_ns2 (t, themap, iter, str2);
					//record macroscopic trace in node structure
					macrostr += iter->macroscopic_mvt;
					iter->macroscopic_mvt = "";
				}
				themap.segments[sgid].lanes[laneid].lane.push_back(*iter);
				update_macroscopic_view (t, themap, iter, 0);
				tmpiter = iter;
				iter++;
				themap.segments[sgid].lanes[laneid].waitlist.erase(tmpiter);
				
      }
      else {
				iter++;
      }
    }
    else {
      iter++;
    }
  }
  return;
}


bool chg_road_segment_loop (mapstruct &themap, int currsegm, int currlane, list<car>::iterator iter, double carsize) {
  

  carMove nextmove = iter->nextmove;
  if (nextmove == RIGHT || nextmove == UTURN) { return true; }
  bool result = false;
  double xstart = themap.segments[currsegm].lanes[currlane].xstart;
  double ystart = themap.segments[currsegm].lanes[currlane].ystart;
  double xend = themap.segments[currsegm].lanes[currlane].xend;
  double yend = themap.segments[currsegm].lanes[currlane].yend;
  int nextsegm = iter->nextsegment;
  int targetlane;
  if (nextmove == STRAIGHT){
    targetlane = currlane;}
  else if (nextmove == RIGHT){
    targetlane = 0;}
  else{
    targetlane = themap.segments[nextsegm].lanes.size()-1;}
  float realdestx, realdesty;

  if (nextmove == STRAIGHT) {
    double intersection_width = find_distance(xend, yend, themap.segments[nextsegm].lanes[targetlane].xstart, 
					      themap.segments[nextsegm].lanes[targetlane].ystart);
    find_position_lane (themap, nextsegm, currlane, -1*intersection_width/2, realdestx, realdesty);
  }

  if (nextmove == LEFT) {
      intersect_two_lanes (themap, currsegm, currlane, nextsegm, targetlane, 
			   realdestx, realdesty);
      double newdestlength = find_distance(xstart, ystart, realdestx, realdesty);
      newdestlength -= carsize/2;
      find_position_lane (themap, currsegm, currlane, newdestlength, realdestx, realdesty);   
  }

  if (find_distance(xstart, ystart, realdestx, realdesty) <= find_distance(xstart, ystart, iter->x, iter->y)) {
    result = true;
  }
  return result;    
}




void change_road_segment(double t, mapstruct &themap, int sgid, int index, vector<list<car>::iterator> &iter, 
		       vector<list<car> > &lanenext, double speedrange, double carsize, 
		       float interval, double braking,  double safetydist, string &str2) {

	
  if (iter[index]->nextsegment == -1) {
		//update_macroscopic_view (t, themap, iter[index], -1);
		node_exit(t, themap, iter[index], speedrange, str2);
		return;
  }
	
  int currsegm = iter[index]->road_segment_id;
  int nextsegm = iter[index]->nextsegment;
  int currlane = iter[index]->presentlane;
  int infronttarget, targetlane;
  bool urgency = true;
  int numberlanes = themap.segments[currsegm].lanes.size();
  numberlanes--;
  list<car>::iterator tmpiter2;
  double xstart = themap.segments[currsegm].lanes[currlane].xstart;
  double ystart = themap.segments[currsegm].lanes[currlane].ystart;
  double xend = themap.segments[currsegm].lanes[currlane].xend;
  double yend = themap.segments[currsegm].lanes[currlane].yend;
  carMove nextmove = iter[index]->nextmove;
  if (nextmove == STRAIGHT){
    targetlane = currlane;}
  else if (nextmove == RIGHT){
    targetlane = 0;}
  else{
    targetlane = themap.segments[nextsegm].lanes.size()-1;}


  #ifdef DEBUG
  cerr<<print(themap, iter[index])<<endl;
  #endif
  //if (!iter[index]->within_end_intersect && 
	//    find_distance(xstart, ystart, iter[index]->x, iter[index]->y) >= find_distance(xstart, ystart, xend, yend)) {
	if (!iter[index]->within_end_intersect && 
	    find_distance(xstart, ystart, iter[index]->x, iter[index]->y) >= 
			find_distance(xstart, ystart, xend, yend)) {
    iter[index]->within_end_intersect = true;
		#ifdef DEBUG
		cerr<<"changed within_end_intersect -> TRUE "<<endl;
		#endif
  }

  // set new destination point
  if (! iter[index]->changed_end_dest) {
     //JN* 04/06/2007
		if (nextmove == STRAIGHT) {
      setdest(iter[index], themap.segments[nextsegm].lanes[targetlane].xstart, 
							themap.segments[nextsegm].lanes[targetlane].ystart);      
    }

    else {// Turn
      intersect_two_lanes (themap, currsegm, currlane, nextsegm, targetlane, iter[index]->destx, iter[index]->desty);
    }
		//JN* 04/06/2007 

    adjustSpeedFormula (t, themap, iter[index], lanenext[index], currsegm, currlane, 
			interval, braking, carsize, urgency, iter[index]->presentlane, 8, str2);
    iter[index]->changed_end_dest = true;
		#ifdef DEBUG
		cerr<<"changed changed_end_dest -> TRUE "<<endl;
		#endif
    
  }
  // already changed dest -- just adjust if car is positioned before stop line
  else if (! iter[index]->within_end_intersect) {
    adjustSpeedFormula (t, themap, iter[index], lanenext[index], currsegm, currlane, 
			interval, braking, carsize, urgency, iter[index]->presentlane, 8, str2);
  }
  // car is already after stop line
  else {
    if ( chg_road_segment_loop (themap, currsegm, currlane, iter[index], carsize) ) {    
      #ifdef DEBUG
      cerr<<"in changing segment "<<endl;
      #endif
      infronttarget = checkLaneChange(t, themap, themap.segments[nextsegm].lanes[targetlane].lane, 
				      themap.segments[nextsegm].lanes[targetlane].lane, iter[index], 
				      interval, carsize, themap.default_braking, safetydist);
      if (infronttarget != -1) {
	#ifdef DEBUG
	cerr<<"making change of segm "<<endl;
	#endif
	update_segment_info(themap, iter[index], nextsegm, speedrange );
	iter[index]->presentlane = targetlane;
	setdest(iter[index], themap.segments[nextsegm].lanes[targetlane].xend, 
		themap.segments[nextsegm].lanes[targetlane].yend);
	iter[index]->within_end_intersect = false;
	iter[index]->changed_end_dest = false;
	#ifdef DEBUG
		cerr<<"changed within_end_intersect -> FALSE changed_end_dest-> FALSE "<<endl;
	#endif
	adjustSpeedFormula (t, themap, iter[index], 
											 themap.segments[nextsegm].lanes[targetlane].lane,
											 nextsegm, iter[index]->presentlane, interval,
											 themap.default_braking, carsize, urgency,
											 iter[index]->presentlane, 8, str2);
	if (nextmove != STRAIGHT) {
	  iter[index]->x = iter[index]->prevx;
	  iter[index]->y = iter[index]->prevy;
	  find_position_lane (themap, nextsegm, targetlane, carsize,
												iter[index]->destx, iter[index]->desty);	
	  update_car(themap, iter[index], iter[index]->currv*interval);
	  iter[index]->intransition = true;
	}
      }
      else {
				adjustSpeedFormula (t, themap, iter[index], lanenext[index], 
														currsegm, currlane, interval, braking, 
														carsize, urgency, iter[index]->presentlane, 
														8, str2);
      }
    }
    else {
      adjustSpeedFormula (t, themap, iter[index], lanenext[index], 
													currsegm, currlane, interval, braking, 
													carsize, urgency, iter[index]->presentlane, 
													8, str2);
    }
  }

	print_ns2(t, themap, iter[index], str2);
	//update_macroscopic_view (t, themap, iter[index], 0);
	
  #ifdef DEBUG
  cerr<<print(themap, iter[index])<<endl;
  #endif
  return;
}



void move_car_per_lane(double t, mapstruct &themap, int sgid, int index,
											  vector<list<car>::iterator> &iter, 
												list<car>::iterator &abslane, 
												vector<list<car> > &lanenext, double speedrange, 
												double carsize, float interval, double braking, 
												double speedmargin, double safetydist, 
												string &str2, string &macrostr) {

	bool urgency;
	double newbraking;
	car carsave;
	list<car>::iterator tmpiter;
	if ( abslane != themap.segments[sgid].lanes[index].lane.end() ) {
		//cerr<<iter->id<<endl;
		
		carsave = *iter[index];
		newbraking = find_new_braking(themap, iter[index], braking, 20*interval);
		if (newbraking < braking) {
			braking = newbraking;
		}
		if (iter[index]->intransition) {
			#ifdef DEBUG
			cerr<<"in intransition id = "<<iter[index]->id<<endl;
			#endif
			update_in_transition(t, themap, iter[index], sgid, index,
													 lanenext[index], braking, interval, 
													 carsize, str2);
			return;
		}
		
		//check if node at end stop sign of segment
		// if so, change to new segment
		if((near_stop_sign(themap, iter[index], interval, carsize) ||
				iter[index]->within_end_intersect))
			// && iter[index]->presentlane == iter[index]->preferredlane) 
			{
			#ifdef DEBUG
			cerr<<"in near stop sign "<<endl;
			#endif
			if (iter[index]->presentlane != iter[index]->preferredlane) {
				#ifdef DEBUG
				cerr<<"Node is not in preferred lane "<<endl;
				#endif
			}
			change_road_segment(t, themap, sgid, index, iter, lanenext, 
													speedrange, carsize, interval, braking, 
													safetydist, str2);
		}
		// node is within proximity of intended turn
		else if (intended_turn_near(themap, iter[index], 20*interval) ) {
			if (iter[index]->nextmove == STRAIGHT) {
				#ifdef DEBUG
				cerr<<"in intended turn straight "<<endl;
				#endif
				urgency = false;
				check_present_lane(t, themap, iter[index], lanenext[index], 
													 sgid, iter[index]->presentlane, carsize, 
													 interval, braking, urgency,
													 iter[index]->presentlane, str2,
													 iter[index]->nextsegment);
				//return;
			}
			else {
				#ifdef DEBUG
				cerr<<"in intended turn L/R "<<endl;
				#endif
				urgency = true;
				//check if node is in its preferred lane
				if(iter[index]->preferredlane == iter[index]->presentlane) {	
					#ifdef DEBUG
					cerr<<"already in pref lane "<<endl;
					#endif
					check_present_lane(t, themap, iter[index], lanenext[index], sgid,
														iter[index]->presentlane, carsize, interval,
														braking, 
					urgency, iter[index]->presentlane, str2);
				}
				// node is not in its preferred lane
				else {
					//double newbraking = 
					//find_new_braking(themap, iter[index], braking, 20*interval);
					double newbraking = braking;
					#ifdef DEBUG
					cerr<<"new braking value = "<<newbraking<<endl;
					#endif
					chgRequestTurnNear (t, themap, iter[index], lanenext, safetydist,
									newbraking, interval, carsize, str2);
				}
			}
		}
		// node is not in proximity of turn
		else {
			#ifdef DEBUG
			cerr<<"in not proximity id "<<iter[index]->id<<endl;
			#endif
			urgency = false;
			//check if node is in his target lane
			if(iter[index]->preferredlane == iter[index]->presentlane) {	
				//iter[index]->targetlane
				check_present_lane(t, themap, iter[index], 
													 lanenext[index], sgid, 
													 iter[index]->presentlane, carsize, 
													 interval, braking, urgency,
													 iter[index]->presentlane, str2);
			}
			// node is not in its target lane
			else {
				chgRequestAwayTurn (t, themap, iter[index], 
														lanenext, safetydist, braking, 
														interval, carsize, str2);
			}
		}
		
		// restore previous values into current lane
		tmpiter = themap.segments[sgid].lanes[carsave.presentlane].lane.begin();
		while (tmpiter !=
						 themap.segments[sgid].lanes[carsave.presentlane].lane.end() &&
						 tmpiter->id != iter[index]->id){
			tmpiter++;
		}
		if (tmpiter != 
					themap.segments[sgid].lanes[carsave.presentlane].lane.end()) {
			*tmpiter = carsave;
		}
		
		//record macroscopic trace in node structure
		macrostr += iter[index]->macroscopic_mvt;
		iter[index]->macroscopic_mvt = "";
	
	}

  return;
}


void move_cars (double t, mapstruct &themap, int sgid, double speedrange, double carsize, float interval, 
		double braking, double speedmargin, double safetydist, string &str2, string &macrostr) {

  // create vectors of lists to replace the static list variables 
  // enable to have one function independently of number of lanes in segment

  vector< list<car> > lanenext;
  vector< list<car>::iterator > abslane;
  vector< list<car>::iterator > iter;
  vector< list<car>::iterator > iternext;
  int i;

  for (i=0; i< (int)themap.segments[sgid].lanes.size(); i++ ) {
    list<car> lanenext1;
    lanenext.push_back(lanenext1);
    list<car>::iterator abslane1;
    abslane1 = themap.segments[sgid].lanes[i].lane.begin();
    abslane.push_back(abslane1);
    list<car>::iterator iter1;
    iter.push_back(iter1);
    list<car>::iterator iternext1 = lanenext[i].begin();
    iternext.push_back(iternext1);
  }

		
  while ( move_car_loop(abslane, themap, sgid) ) {
		
    for (i=0; i< (int)themap.segments[sgid].lanes.size(); i++ ) {
      iter[i] = abslane[i];
    }

    for (i=0; i< (int)themap.segments[sgid].lanes.size(); i++ ) {
      move_car_per_lane(t, themap, sgid, i, iter, abslane[i], 
												lanenext, speedrange, carsize, interval, 
												braking, speedmargin, safetydist, str2, 
												macrostr);
    }

    for (i=0; i< (int)themap.segments[sgid].lanes.size(); i++ ) {
      if (abslane[i] != themap.segments[sgid].lanes[i].lane.end() )
				abslane[i]++;
    }

  }	// end while move_car_loop at time t

  for (i=0; i< (int)themap.segments[sgid].lanes.size(); i++ ) {
    themap.segments[sgid].lanes[i].lane.clear();
  }

  for (i=0; i< (int)themap.segments[sgid].lanes.size(); i++ ) {
    themap.segments[sgid].lanes[i].lane = lanenext[i];
    refresh_waiting_list(t, themap, interval, sgid, i, 
												 carsize, braking, safetydist, 
												 str2, macrostr);
  }

  list<car>::iterator tmpiter;
  for (i=0; i< (int)themap.segments[sgid].lanes.size(); i++ ) {
    tmpiter = lanenext[i].begin();
    while (tmpiter != lanenext[i].end()) {
      #ifdef DEBUG
      cerr<<print(themap, tmpiter);
      #endif
      tmpiter++;
    }
  }

  for (i=0; i< (int)themap.segments[sgid].lanes.size(); i++ ) {
    lanenext[i].clear();
  }

  return;
}

// used to count average number of cars on topology
void estimatecarsnumber (double &t, mapstruct &themap, int &count) {
	
	if (warm_up >= 0) {
		warm_up--;
		t = -1;
		return;
	}
	
  if (steady_state(themap)) {
    int i, j;
    if (!start_ns_printing) {
			// to enforce that the printing starts at the same time for 
			// all nodes. Otherwise could start forsome 1s before others
			// and not all nodes would have mvt for t=0s
      start_ns_printing = true;
      t = -1;
    }
    else {
      for (i=0; i<(int)themap.segments.size(); i++) {
        for (j=0; j<(int)themap.segments[i].lanes.size(); j++) {
	  			count += themap.segments[i].lanes[j].lane.size();
        }
      }
    }
  }
  else {
    // do not start counting until after in steady state
    // therefore set t back to 0;
    t = -1;
  }
  return;
}

// main function
int main(int argc, char* argv[]) {

  // number of cars 
  int numcars = 100;

  //simulation number.
  //int run_num = 1;

  // duration
  float simulationtime = 1000.0;

  //Map file name
  string mapfilename = "./citymapsample";

  //Warm up period.
  warm_up = 2000;

  char szCityMapFileName[ 1024 ];
  char szmvtoutfilename[ 1024 ];
  char szmacrooutfilename[ 1024 ];

  sprintf( szmvtoutfilename, "./mvtcity_%d", numcars );
  string mvtoutfilename = szmvtoutfilename;
  sprintf( szmacrooutfilename, "./macrocity_%d", numcars );
  string macroutfilename = szmacrooutfilename;

  if( argc == 7 )
  {
    simulationtime = atof( argv[ 1 ] );
    numcars = atoi( argv[ 2 ] );
    warm_up = atoi( argv[ 3 ] );
    sprintf( szCityMapFileName, "%s", argv[ 4 ] );
    mapfilename = szCityMapFileName;
    sprintf( szmvtoutfilename, "%s", argv[ 5 ] );
    mvtoutfilename = szmvtoutfilename;
    sprintf( szmacrooutfilename, "%s", argv[ 6 ] );
    macroutfilename = szmacrooutfilename;
  }
  else if( argc == 1 )
  {
    //Use default values.
    //printf( "Using default parameters (numcars = %d, run_num = %d).\n", numcars, run_num );
  }
  else
  {
    printf( "\nError: Program did not receive expected arguments.\n" );
    printf( "Run the program with either no arguments for default behaviour or as follows\n" );
    printf( "Program_Name <SimulTime> <NumOfCars> <WarmUpTime> <CityFileName> <OutMvtFileName> <OutMacroFileName>\n" );
    exit( 0 );
  }
  printf( "Using parameters (time = %.2f, numofcars = %d, warm_up = %d, citymap = %s, mvtfilename = %s, macrofilename = %s).\n\n", simulationtime, numcars, warm_up, mapfilename.c_str(), mvtoutfilename.c_str( ), macroutfilename.c_str( ) );
  printf( "Press any key to continue... or Ctrl+C to stop\n" );
  getchar();

  printf( "Continuing ...\n" );

  // speed interval range
  float speedrange = 10.0;
  // node speed margin 
  float speedmargin = 5.0;
  // computation time interval
  float interval = 1.0;
  // car braking speed
  float braking = -2.50;
  // car size 
  float carsize = 8.0;
  // safe distance between cars
  float safedistance = carsize/2;
  //string for holding text
  string str = "";
  string str2 = "";
	string macroscopicstr = "";
  int carsontopo = 0;

	max_num_cars = numcars;
  method = 2; // 1 == all cars arriving at entry_intersect go to sink
  		// 2 == all cars arriving at entry_intersect go back in
		// 3 == some cars wiil go to sink and others go back in


  ofstream mvtoutfile;
  mvtoutfile.open(mvtoutfilename.c_str());
  ofstream macroutfile;
  macroutfile.open(macroutfilename.c_str());
  

  if (! mvtoutfile) {
    cout<<"Couldn't open file "<<mvtoutfile<<"!\n"<<endl;
    exit(EXIT_FAILURE);
  }
  if (! macroutfile) {
    cout<<"Couldn't open file "<<macroutfile<<"!\n"<<endl;
    exit(EXIT_FAILURE);
  }


  int i,j;
  double t;
  srand (time(NULL));
  mapstruct themap;

  create_map(themap, carsize, braking, mapfilename);
  compute_exitflows (simulationtime, themap);
  initialize_traffic_lights(themap);
  initialize_cars (simulationtime, themap, numcars,  carsize, safedistance, speedrange, str2);


	// start of adjust position interval 1s
  for (t=0; t<= simulationtime; t+=interval) {
    for (i=0; i<(int)themap.roads.size(); i++) {
      for (j=themap.roads[i].segments.size(); j>0; j--) {
		move_cars(t, themap, themap.roads[i].segments[j-1], 
			speedrange, carsize, interval, braking, 
			speedmargin, safedistance, str2, macroscopicstr);
      }
    }
    update_traffic_lights(themap, interval);
    estimatecarsnumber (t, themap, carsontopo);
  }

  carsontopo = carsontopo/(int)(t-1);
  int ns_number_nodes = ns_id_vect.size();
  char* tmpstr = new char[100];
  sprintf(tmpstr, "#number cars: %d \t avg # cars on topo: %d \t cars in ns2: %d \n", numcars, carsontopo, ns_number_nodes);
  str2 = tmpstr + str2;
  delete [] tmpstr;
  
  mvtoutfile<<str2.c_str()<<endl;
  macroutfile<<macroscopicstr.c_str()<<endl;
  mvtoutfile.close();
	macroutfile.close();


  return 0;
}






