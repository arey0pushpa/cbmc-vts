// Ankit Shukla, 6.11.2018 (Austria)
/* Copyright 2018 Ankit Shukla
This file is free a software; you can redistribute
it and/or modify it under the terms of the GNU General Public License as published by
the Free Software Foundation and included in this library; either version 3 of the
License, or any later version. */

/*!
  \brief Encoding of finding a Vesicle Traffic System (VTS) network
  with a given connectivity  connectivity (In terms of graph connectedness).
  
	RUN the file with 

> cbmc vts.c --unwindset c::main.L1:B1,c:main.L2:B2,...

	Provide L_i by:
  1.	locating the line number of 'DYNAMIC CODE' comment on the loop]
	2.  find the matching loop number L_i by running

> cbmc vts.c --show-loops

TODOS:

1. Take arbitrary input from the console.

2. Add test cases.

3. Show the formatted output. 

4. Help option in the software run.


PROPERTIES IN VTS:

V1. For an edge to exist it should have one molecule present.

V2. If a molecule is active on an edge, it should be present on the edge.

V3. A molecule should be present to be active on a node.

V4. The edge labels are subset of the node labels of the source and target nodes.

V5. Self edges are not allowed.

V6. We fix first half as Q-SNAREs and rest as R-SNAREs.

V7. Each edge must fuse with its destination node.

V8. Each node has a deterministic target.

R1-R4. Regulation on nodes and edges

S1-S2. Constraints for stability condition

C1-C4. k-Connectivity constraints.

*/

//#include <ctype.h>
#include <stdio.h>    // printf() and scanf()
#include <stdlib.h>

#define M 4
#define N 2
#define snareLength 4
#define bigLen 16  // 2 ^ M
#define len 3

_Bool nondet_bool();
unsigned int nondet_uint();

typedef unsigned __CPROVER_bitvector[M] bitvector;
typedef unsigned __CPROVER_bitvector[snareLength] snareVector;
typedef unsigned __CPROVER_bitvector[bigLen] bigVector;

// Constrine the value between 0 and 1
unsigned int nondet() {
  unsigned int num = nondet_uint();
  __CPROVER_assume(num >= 0 && num <= 1);
  return num;
};

unsigned int zeroTon(unsigned int n) {
  unsigned int result = nondet_uint();
  __CPROVER_assume(result >= 0 && result <= n);
  return result;
};

// bigVector biig = 0b1;

bigVector nondetBV() {
  bigVector bee;
  //   __CPROVER_assume(bee >= 0b0 && bee <= 0b1111);
  return bee;
}

//  Define the Structure of the container
struct EdgeSet {
  int ith;
  int jth;
  unsigned int count;
  snareVector vSnare;
  snareVector tSnare;
  unsigned int zebra[snareLength];
  snareVector combinedMask;
};

int main(int argc, char** argv)

{
  /*
int mflag = 0;
int nflag = 0;
int index;
int c;

while ((c = getopt(argc, argv, "mns")) != -1) switch (c) {
case 'm':
  mflag = 1;
  break;
case 'n':
  nflag = 1;
  break;
default:
  printf("Please provide the value of m and n");
  abort();
}
exit(0);
  */

  // Create Boolean variables for the properties used in the VTS
  _Bool Ck = 0, Cf = 1, C0, C1, C2 = 1, C3 = 1, C4 = 1, strongly_connected = 1;

  // Other useful variables
  unsigned int pos, i, j, k, l, w, x, y, iVal, jVal, g, g0, gl, lastg, ng, nl,
      nl2;
  unsigned int edgePos, ticks, valj, vali, calc;

  // Count total number of edges in the input graph
  unsigned int edgeCount;

  // Create dummy zero vectors and function vectors (ABF: arbitarary bool func)
  bigVector b0 = 0b0, b1 = 0b1;
  bigVector vSnareChoicet[snareLength], vSnareChoicef[snareLength], result, vt,
      vf, vl, vl2;

  // Create a Node of the size 2 * N
  // SNARES are divided into two categories V and T
  bitvector Vnodes[N];
  bitvector Tnodes[N];

  bitvector fareTotal, inTotal, outTotal, outVSnareTotal, inVSnareTotal,
      outTSnareTotal, inTSnareTotal;
  snareVector total, cond2Total, cond2fareTotal, centTotal, placeHolder, v, t,
      f, lastv, lastv2, nv, nv2, v0, v2;
  snareVector Tedge[N][N], Vedge[N][N], Vedge2[N][N], Tedge2[N][N], fComp,
      bComp;

  //  OnOffMatrix is the N * T  t-snare matrix
  //  where N:nodes are rows and T snares are column
  snareVector onOffMatrix[N], stCorres, ew;

  // Input an arbitary graph
  unsigned int graph[N][N];

  // Pre-calculate the total required length(#edges) for the containerBag
  edgeCount = 0;
  for (i = 0; i < N; i++) {
    for (j = 0; j < N; j++) {
      if (i != j) {
	__CPROVER_assume(graph[i][j] >= 0 && graph[i][j] <= 2);
	if (graph[i][j] == 1)
	  edgeCount += 1;
	else if (graph[i][j] == 2)
	  edgeCount += 2;
      } else
	__CPROVER_assume(graph[i][j] == 0);
    }
  }
  __CPROVER_assume(edgeCount == len);

  struct EdgeSet edgeset[len];

  //  Initialise the edgeset structure with i, j, edgeWeigth, vsnare, tsnare
  edgePos = 0;
  for (i = 0; i < N; i++) {
    for (j = 0; j < N; j++) {
      if ((graph[i][j] == 1) || (graph[i][j] == 2)) {
	edgeset[edgePos].ith = i;  // Record the source node
	edgeset[edgePos].jth = j;  // Record the target Node

	// Only molecule present at the nodes are allowed to fly out.
	__CPROVER_assume((edgeset[edgePos].vSnare & (~Vnodes[i])) == 0);
	__CPROVER_assume((edgeset[edgePos].tSnare & (~Tnodes[i])) == 0);

	// Additional Vedge[i][j] and Tedge[i][j] is
	// used to be lookup value in global steady state check condition.
	Vedge[i][j] = edgeset[edgePos].vSnare;
	Tedge[i][j] = edgeset[edgePos].tSnare;
	edgePos = edgePos + 1;
      }

      if ((graph[i][j] == 2)) {
	edgeset[edgePos].ith = i;  // Record the Source Node
	edgeset[edgePos].jth = j;  // Record the Target Node

	// Only molecule present at the nodes are
	// allowed to fly out.
	__CPROVER_assume((edgeset[edgePos].vSnare & (~Vnodes[i])) == 0);
	__CPROVER_assume((edgeset[edgePos].tSnare & (~Tnodes[i])) == 0);

	// Additional Vedge2[i][j] and Tedge2[i][j] is
	// used to be lookup value in global steady
	// state check condition.
	Vedge2[i][j] = edgeset[edgePos].vSnare;
	Tedge2[i][j] = edgeset[edgePos].tSnare;
	edgePos = edgePos + 1;
      }
    }
  }

  /* Graph has to be Strongly Connected +  3-Connected but not 2-Strongly
   connected Not adding this constrint as Input graph will be satisfying
   this Constraint*/
  // FIRST CONSTARAINT ON THE GRAPH
  // The code for make sure that it'll be 3 connected and not four
  // connected

  C4 = 0;
  for (i = 0; i < N; i++) {
    calc = 0;
    for (j = 0; j < len; j++) {  // 20 UNWINDINGS
      if ((edgeset[j].ith == i) || (edgeset[j].jth == i)) {
	calc = calc + 1;
      }
    }
    __CPROVER_assume(calc >= 3);
    if (calc < 4) {
      C4 = 1;
    }
  }

  //  Edgeweight is not allowed to be zero : build C0 to represent that :
  C0 = 1;
  for (j = 0; j < len; j++) {
    C0 = (C0 && (edgeset[j].vSnare != 0));
  }

  for (i = 0; i < N; i++) {
    __CPROVER_assume(Vnodes[i] != 0);
  }

  C1 = 1;
  for (i = 0; i < len; i++) {		   // For each Edge
    for (j = 0; j < snareLength; j++) {    // for each molecule
      if (edgeset[i].vSnare & (1 << j)) {  // Present molecules
	vali = edgeset[i].ith;		   // store the source node
	valj = edgeset[i].jth;		   // Store the target node
	// If there is a back edge from taget to source
	// we are done.
	if (((graph[valj][vali] == 1) && (Vedge[valj][vali] & (1 << j))) ||
	    ((graph[valj][vali] == 2) && ((Vedge2[valj][vali] & (1 << j)) ||
					  (Vedge[valj][vali] & (1 << j))))) {
	  C1 = C1 && 1;
	}
	// Else continue checking for the cycle
	else {
	  // g0 is unsigned int checks if there is
	  // an edge btw two nodes
	  //  It should be on some cycle, So
	  //  assume that it'll be between 0 and
	  //  N-2 As we are Only considering
	  //  elementary cycles.
	  unsigned int big;
	  __CPROVER_assume(big >= 1 && big <= (N - 2));
	  unsigned int path[big];  // An array to store the
				   // path taken by
				   // molecule.

	  //  Make sure every int is between 0 and
	  //  N-1 that represent the node
	  for (l = 0; l < big; l++) {  // Dynamic
	    path[l] = zeroTon(N - 1);
	  }

	  g0 = graph[valj][path[0]];  // g0 is unsigned
				      // int checks if
				      // there is an edge
				      // btw two nodes
	  v0 = Vedge[valj][path[0]];  // snareVector gets the
				      // edgeweight of the
				      // corresponding edge.
	  v2 = Vedge2[valj][path[0]];

	  gl = graph[path[big - 1]][vali];
	  vl = Vedge[path[big - 1]][vali];  // snareVector gets
					    // the edgeweight of
					    // the corresponding
					    // edge.
	  vl2 = Vedge2[path[big - 1]][vali];

	  if ((((g0 == 1) && (v0 & (1 << j))) ||
	       ((g0 == 2) && ((v0 & (1 << j)) || (v2 & (1 << j))))) &&
	      (((gl == 1) && (vl & (1 << j))) ||
	       ((gl == 2) && ((vl & (1 << j)) || (vl2 & (1 << j)))))) {
	    C1 = C1 && 1;
	  }

	  else {
	    C1 = 0;
	  }

	  if (big > 1) {
	    for (k = 0; k < big - 1; k++) {  // Dynamic
	      ng = graph[path[k]][path[k + 1]];
	      nv = Vedge[path[k]][path[k + 1]];
	      nv2 = Vedge2[path[k]][path[k + 1]];
	      if (((ng == 1) && (nv & (1 << j))) ||
		  ((ng == 2) && ((nv & (1 << j)) || (nv2 & (1 << j))))) {
		C1 = C1 && 1;
	      } else {
		C1 = 0;
	      }
	    }
	  }

	}  // else Outside closed
      }
    }  // jth for closed
  }    //  ith for closed

  for (i = 0; i < len; i++) {		   // For each Edge
    for (j = 0; j < snareLength; j++) {    // for each molecule
      if (edgeset[i].tSnare & (1 << j)) {  // Present molecules
	vali = edgeset[i].ith;		   // store the source node
	valj = edgeset[i].jth;		   // Store the target node

	if (((graph[valj][vali] == 1) && (Tedge[valj][vali] & (1 << j))) ||
	    ((graph[valj][vali] == 2) && (Tedge2[valj][vali] & (1 << j)) ||
	     (Tedge[valj][vali] & (1 << j)))) {
	  C1 = C1 && 1;
	}

	else {
	  unsigned int big;
	  __CPROVER_assume(big >= 1 && big <= (N - 2));

	  unsigned int path[big];  // An array to store the
				   // path taken by
				   // molecule.

	  //  Make sure every int is between 0 and
	  //  N-1 that represent the node1
	  for (l = 0; l < big; l++) {  // Dynamic
	    path[l] = zeroTon(N - 1);
	  }

	  g0 = graph[valj][path[0]];  // g0 is unsigned
				      // int checks if
				      // there is an edge
				      // btw two nodes
	  v0 = Tedge[valj][path[0]];  // snareVector gets the
				      // edgeweight of the
				      // corresponding edge.
	  v2 = Tedge2[valj][path[0]];

	  gl = graph[path[big - 1]][vali];
	  vl = Tedge[path[big - 1]][vali];  // snareVector gets
					    // the edgeweight of
					    // the corresponding
					    // edge.
	  vl2 = Tedge2[path[big - 1]][vali];

	  if ((((g0 == 1) && (v0 & (1 << j))) ||
	       ((g0 == 2) && ((v0 & (1 << j)) || (v2 & (1 << j))))) &&
	      (((gl == 1) && (vl & (1 << j))) ||
	       ((gl == 2) && ((vl & (1 << j)) || (vl2 & (1 << j)))))) {
	    C1 = C1 && 1;
	  }

	  else {
	    C1 = 0;
	  }
	  if (big > 1) {
	    for (k = 0; k < big - 1; k++) {  // Dynamic
	      ng = graph[path[k]][path[k + 1]];
	      nv = Tedge[path[k]][path[k + 1]];
	      nv2 = Tedge2[path[k]][path[k + 1]];
	      if (((ng == 1) && (nv & (1 << j))) ||
		  ((ng == 2) && ((nv & (1 << j)) || (nv2 & (1 << j))))) {
		C1 = C1 && 1;
	      } else {
		C1 = 0;
	      }
	    }
	  }
	}  // else Outside closed
      }
    }  // jth for closed
  }    //  ith for closed

  for (i = 0; i < snareLength; i++) {
    vSnareChoicet[i] = nondetBV();
  }

  for (j = 0; j < snareLength; j++) {
    vSnareChoicef[j] = nondetBV();
  }

  C2 = 1;
  C3 = 1;
  for (i = 0; i < len; i++) {
    ticks = 0;
    Ck = 0;
    for (j = 0; j < snareLength; j++) {
      v = edgeset[i].vSnare;
      t = edgeset[i].tSnare;
      valj = edgeset[i].jth;
      vali = edgeset[i].ith;

      if (v & (1 << j)) {
	vt = vSnareChoicet[j];
	result = (vt & (1 << t));
	if (result == 0) {
	  edgeset[i].zebra[ticks] = j;
	  ticks = ticks + 1;
	  fComp = (Tnodes[valj] & onOffMatrix[valj]);
	  bComp = (Tnodes[vali] & onOffMatrix[vali]);
	  vf = vSnareChoicef[j];
	  if ((vf & (1 << fComp)) && ((vf & (1 << bComp)) == 0)) {
	    Ck = 1;
	  }
	}
      }
    }

    edgeset[i].count = ticks;

    if (Ck == 1) {
      C2 = C2 && 1;
    } else {
      C2 = C2 && 0;
    }

    for (k = 0; k < N; k++) {
      if (k != edgeset[i].jth) {
	bComp = Tnodes[k] & onOffMatrix[k];
	for (l = 0; l < edgeset[i].count; l++) {  // THIS IS DYNAMIC CODE
	  vf = vSnareChoicef[edgeset[i].zebra[l]];
	  if ((vf & (1 << bComp)) == 0) {
	    C3 = C3 && 1;
	  } else {
	    C3 = C3 && 0;
	  }
	}
      }
    }
  }

  for (i = 0; i < N; i++) {
    printf("\n VNodes[%d] = %d", i, Vnodes[i]);
    printf(" TNodes[%d] = %d", i, Tnodes[i]);
  }

  for (i = 0; i < len; i++) {
    printf(
	"The edge No.%d has this config : \n There is an edge "
	"between graph[%d][%d]",
	i, edgeset[i].ith, edgeset[i].jth);
    printf(" SourceNodes[%d] (v : t) = (%d , %d)", edgeset[i].ith,
	   Vnodes[edgeset[i].ith], Tnodes[edgeset[i].ith]);
    printf(" TargetNodes[%d] (v : t) = (%d , %d) ", edgeset[i].jth,
	   Vnodes[edgeset[i].jth], Tnodes[edgeset[i].jth]);
    printf(" vSnare =  %d \n tSnare = %d ", edgeset[i].vSnare,
	   edgeset[i].tSnare);
    printf(" combinedMask = %d \n counts = %d \n", edgeset[i].combinedMask,
	   edgeset[i].count);
  }

  for (i = 0; i < snareLength; i++) {
    printf(" vSnareChoicet[%d] = %d", i, vSnareChoicet[i]);
  }

  for (j = 0; j < snareLength; j++) {
    printf(" vSnareChoicef[%d] = %d", j, vSnareChoicef[j]);
  }
  for (i = 0; i < N; i++) {
    printf(" The onOffMatrix[%d] = %d ", i, onOffMatrix[i]);
  }

  for (i = 0; i < N; i++) {
    for (j = 0; j < N; j++) {
      printf("Graph[%d][%d] = %d", i, j, graph[i][j]);
    }
  }

  printf(
      "\nThe value of : \n C0 = %d \n C1 : %d \n C2 : %d , C3 : %d C4 : "
      "%d , strongly_connected = %d \n",
      C0, C1, C2, C3, C4, strongly_connected);
  printf(" the value of mr.Ticks is %d and len was %d ", ticks, len);

  // assert(0);
  __CPROVER_assert(!(C0 && C1 && strongly_connected && C2 && C3 && C4),
		   "Graph that satisfy friendZoned model exists");
  return 0;
}

