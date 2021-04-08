#ifndef PERMUTATION_H_
#define PERMUTATION_H_
#include<vector>
#include "G_q.h"
#include <NTL/ZZ.h>
NTL_CLIENT

#include "Mod_p.h"

class Permutation {
public:
	Permutation();
	virtual ~Permutation();

	//creates permutation of length N and returns is as a vector
	static	vector<long>* permutation(long N);
	//creates a permutation of a mxn matrix
	static	void perm_matrix(vector<vector<vector<long>* >* >* pi, long n, long m);
};

#endif /* PERMUTATION_H_ */
