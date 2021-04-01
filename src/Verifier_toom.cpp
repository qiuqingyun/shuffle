/*
 * Verifier_toom.cpp
 *
 *  Created on: 25.04.2011
 *      Author: stephaniebayer
 */

#include "Verifier_toom.h"

#include <vector>
#include "Cipher_elg.h"
#include "G_q.h"
#include "Mod_p.h"
#include "Functions.h"
#include "ElGammal.h"
#include "multi_expo.h"
#include "func_ver.h"
#include <fstream>
#include <sstream>

#include <time.h>
#include <NTL/ZZ.h>
NTL_CLIENT

extern G_q G;
extern G_q H;
extern Pedersen Ped;
extern ElGammal El;
extern long mu;
extern long mu_h;
extern long m_r;

Verifier_toom::Verifier_toom()
{
	// TODO Auto-generated constructor stub
}

Verifier_toom::Verifier_toom(vector<long> num)
{
	// sets the values of the matrix according to the input
	m = num[1];		   //number of rows
	n = num[2];		   //number of columns
	omega = num[3];	   //windowsize for multi-expo-technique
	omega_sw = num[4]; //windowsize for multi-expo-technique sliding window and LL
	omega_LL = num[7]; //windowsize for multi-expo-technique of LL
	this->num = num;

	c_A = new vector<Mod_p>(m + 1);					 //allocate the storage for the commitments of Y
	c_B = new vector<Mod_p>(m);						 //allocate the storage for the commitments of T
	c_B_small = new vector<Mod_p>(m_r);				 //commitments after reduction with challenges x
	C_small = new vector<vector<Cipher_elg> *>(m_r); //reduced Ciphertexte, with challenges x

	chal_x6 = new vector<ZZ>(2 * m);					   // allocate the storage for the vector of Vandermonde challenges t, ... t^n
	chal_y6 = new vector<ZZ>(n);						   // allocate the storage for the vector of Vandermonde challenges t, ... t^n
	chal_x8 = new vector<ZZ>(2 * m + 1);				   //challenge from round 8
	basis_chal_x8 = new vector<vector<long> *>(2 * m + 2); //basis of vector e for multi-expo technique
	mul_chal_x8 = new vector<ZZ>(2 * m + 2);			   //shifted vector e, e(0) = 1, used for multi-expo
	x = new vector<ZZ>(mu_h);							   //challenges to reduce ciphertexts

	//Commitments vectors
	c_Dh = new vector<Mod_p>(m);		 //commitments to the matrix W
	c_Ds = new vector<Mod_p>(m + 1);	 //contains a_W*t_1
	c_Dl = new vector<Mod_p>(2 * m + 1); //commitments to the values Cl
	c_a_c = new vector<Mod_p>(mu_h);	 //commitment to the values used to reencrypt the E_x
	c_a = new vector<Mod_p>(2 * mu);	 //commitment to the values in the matrix a
	//Vector of product of the diagonals of permuted Ciphertexts from round 5
	E = new vector<Cipher_elg>(2 * mu);
	C_c = new vector<Cipher_elg>(mu_h); //Ciphertexts to prove correctness of reduction

	D_h_bar = new vector<ZZ>(n);   //sum over the rows in D_h
	d_bar = new vector<ZZ>(n);	   // chal_x8*D_h(m-1) +d
	Delta_bar = new vector<ZZ>(n); //chal_x8*d_h+Delta
	B_bar = new vector<ZZ>(n);	   // sum over the rows in B multiplied by chal^i

	A_bar = new vector<ZZ>(n);	//sum over the rows in Y times the challenges
	Ds_bar = new vector<ZZ>(n); // sum over the rows in U times thes challenges
}

Verifier_toom::~Verifier_toom()
{

	delete c_A;
	delete c_B;
	delete chal_x6;
	delete chal_y6;
	delete chal_x8;
	delete mul_chal_x8;
	Functions::delete_vector(basis_chal_x8);
	delete x;
	delete c_Dh;
	delete c_Ds;
	delete c_Dl;
	delete c_a;
	delete E;
	delete D_h_bar;
	delete d_bar;
	delete Delta_bar;
	delete B_bar;
	delete A_bar;
	delete Ds_bar;

	delete c_B_small;
	delete c_a_c;
	delete C_c;
}

string Verifier_toom::round_2(string in_name)
{
	long i;
	string name;
	ZZ ord = H.get_ord();
	time_t rawtime;
	time(&rawtime);
	//sets a_Y to the values in the file name
	ifstream ist(in_name.c_str());
	if (!ist)
		cout << "Can't open " << in_name;
	for (i = 0; i < m; i++)
	{ //接收round_1中Prover的承诺
		ist >> c_A->at(i);
	}
	ist.close();

	string container = "\0", in_temp;
	ist.open(in_name.c_str(), ios::in);
	while (ist >> in_temp)
	{ //接收round_1中Prover的承诺
		container += in_temp;
	}
	stringstream pk_ss;
	pk_ss << El.get_pk().get_val();
	container += pk_ss.str();
	ist.close();
	hashStr[0] = sha.hash(container);
	
	return name;
}

string Verifier_toom::round_4(string in_name)
{
	long i;
	ZZ ord = H.get_ord();
	string name;
	time_t rawtime;
	time(&rawtime);
	//sets a_T to the values in the file
	ifstream ist(in_name.c_str());
	if (!ist)
		cout << "Can't open " << in_name;
	for (i = 0; i < m; i++)
	{ //接收round_3中Prover的承诺
		ist >> c_B->at(i);
	}

	ist >> chal_x2;
	ist.close();

	string container1 = "\0", container2;
	ist.open(in_name.c_str(), ios::in);
	while (!ist.eof())
	{ //接收round_1中Prover的承诺
		ist >> container2;
		if (!ist.eof())
			container1 += container2;
	}
	stringstream pk_ss;
	pk_ss << El.get_pk().get_val();
	container1 += pk_ss.str();
	container2 += pk_ss.str();
	ist.close();
	hashStr[1] = sha.hash(container1);
	hashStr[2] = sha.hash(container2);
	
	return name;
}

string Verifier_toom::round_6(string in_name)
{
	ZZ tem;
	ZZ ord = H.get_ord();
	long i, l;
	string name;
	time_t rawtime;
	time(&rawtime);

	//reads the values out of the file name
	ifstream ist(in_name.c_str());
	if (!ist)
		cout << "Can't open " << in_name;
	ist >> c_z;
	// cout<<c_z<<endl;
	// cout<<endl;
	for (i = 0; i < m; i++)
	{
		ist >> c_Dh->at(i);
		// cout<<"c_Dh: " << c_Dh->at(i) << " ";
	}
	// cout << endl;
	for (i = 0; i < mu_h; i++)
	{
		ist >> C_c->at(i);
		// cout << C_c->at(i) << " ";
	}
	// cout << endl;
	for (i = 0; i < mu_h; i++)
	{
		ist >> c_a_c->at(i);
		// cout << c_a_c->at(i) << " ";
	}
	ist >> chal_y4;
	ist >> chal_z4;
	ist.close();

	string container1 = "\0", container2;
	ist.open(in_name.c_str(), ios::in);
	while (!ist.eof())
	{ //接收round_1中Prover的承诺
		ist >> container2;
		if (!ist.eof())
			container1 += container2;
	}
	stringstream pk_ss;
	pk_ss << El.get_pk().get_val();
	container1 += pk_ss.str();
	container2 += pk_ss.str();
	ist.close();
	hashStr[3] = sha.hash(container1);
	hashStr[4] = sha.hash(container2);
	
	return name;
}

string Verifier_toom::round_8(string in_name)
{
	long i, l;
	string name;
	time_t rawtime;
	time(&rawtime);
	//reads the values out of the file name

	ifstream ist(in_name.c_str());
	if (!ist)
		cout << "Can't open " << in_name;

	for (i = 0; i <= 2 * m; i++)
	{ //33
		ist >> c_Dl->at(i);
		// cout << c_Dl->at(i) << " ";
	}
	// cout << endl;
	ist >> c_D0;
	// cout << c_D0 << endl;
	ist >> c_Dm;
	// cout << c_Dm << endl;
	ist >> c_d;
	// cout << c_d << endl;
	ist >> c_Delta;
	// cout << c_Delta << endl;
	ist >> c_dh;
	// cout << c_dh << endl;
	ist >> a_c_bar;
	// cout << a_c_bar << endl;
	ist >> r_ac_bar;
	// cout << r_ac_bar << endl;
	for (i = 0; i < 8; i++)
	{
		ist >> E->at(i);
		// cout << E->at(i) << " ";
	}
	// cout << endl;
	ist >> c_B0;
	// cout << c_B0 << endl;
	for (i = 0; i < 8; i++)
	{
		ist >> c_a->at(i);
		// cout << c_a->at(i) << " ";
	}
	// cout << endl;
	l = 2 * m;
	for (i = 0; i < l; i++)
	{
		ist >> chal_x6->at(i);
		// cout << chal_x6->at(i) << " ";
	}
	// cout << endl;

	for (i = 0; i < n; i++)
	{
		ist >> chal_y6->at(i);
		// cout << chal_y6->at(i) << " ";
	}
	// cout << endl;
	ist.close();
	string container = "\0", in_temp;
	ist.open(in_name.c_str(), ios::in);
	while (ist >> in_temp)
	{
		container += in_temp;
	}
	stringstream pk_ss;
	pk_ss << El.get_pk().get_val();
	container += pk_ss.str();
	ist.close();
	hashStr[5] = sha.hash(container);
	
	return name;
}

int Verifier_toom::round_10(vector<vector<Cipher_elg> *> *cc, vector<vector<Cipher_elg> *> *Cc)
{
	time_t tstart = clock();
	int b;
	long i;
	ZZ ord = H.get_ord();
	//reads the values out of the file name
	this->round_2("prove_1.pro");
	this->round_4("prove_2.pro");
	this->round_6("prove_3.pro");
	this->round_8("prove_4.pro");
	string in_name = "prove_5.pro";
	ifstream ist(in_name.c_str());
	if (!ist)
		cout << "Can't open " << in_name;
	for (i = 0; i < n; i++)
	{
		ist >> D_h_bar->at(i);
		// cout<<"D_h_bar: " << D_h_bar->at(i) << " ";
	}
	// cout << endl;
	ist >> r_Dh_bar;
	// cout<<"r_Dh_bar: " << r_Dh_bar << "\n\n";

	for (i = 0; i < n; i++)
	{
		ist >> d_bar->at(i);
		// cout << d_bar->at(i) << " ";
	}
	// cout << endl;
	ist >> r_d_bar;
	// cout << r_d_bar << "\n\n";
	for (i = 0; i < n; i++)
	{
		ist >> Delta_bar->at(i);
		// cout << Delta_bar->at(i) << " ";
	}
	// cout << endl;
	ist >> r_Delta_bar;
	// cout << r_Delta_bar << "\n\n";

	for (i = 0; i < n; i++)
	{
		ist >> A_bar->at(i);
		// cout << A_bar->at(i) << " ";
	}
	// cout << endl;
	ist >> r_A_bar;
	// cout << r_A_bar << "\n\n";
	for (i = 0; i < n; i++)
	{
		ist >> Ds_bar->at(i);
		// cout << Ds_bar->at(i) << " ";
	}
	// cout << endl;
	ist >> r_Ds_bar;
	// cout << r_Ds_bar << "\n\n";
	ist >> r_Dl_bar;
	// cout << r_Dl_bar << "\n\n";

	for (i = 0; i < n; i++)
	{
		ist >> B_bar->at(i);
		// cout << B_bar->at(i) << " ";
	}
	// cout << endl;
	ist >> r_B_bar;
	// cout << r_B_bar << "\n\n";
	ist >> a_bar;
	// cout << a_bar << "\n\n";
	ist >> r_a_bar;
	// cout << r_a_bar << "\n\n";
	ist >> rho_bar;
	// cout << rho_bar << "\n\n";

	int chal_x8_size;
	ist >> chal_x8_size;
	// cout << chal_x8_size << "\n\n";
	for (i = 0; i < chal_x8_size; i++)
	{
		ist >> chal_x8->at(i);
		// cout << chal_x8->at(i) << " ";
	}
	// cout << endl;

	int basis_chal_x8_size, basis_chal_x8_s_size;
	ist >> basis_chal_x8_size;
	// cout << basis_chal_x8_size << "\n\n";
	ist >> basis_chal_x8_s_size;
	// cout << basis_chal_x8_s_size << "\n\n";
	for (i = 0; i < basis_chal_x8_size; i++)
	{
		vector<long> *x8;
		x8 = new vector<long>(basis_chal_x8_s_size);
		for (int j = 0; j < basis_chal_x8_s_size; j++)
		{
			long x8_temp;
			ist >> x8_temp;
			x8->at(j) = x8_temp;
			// cout << x8->at(j) << " ";
			// cout << x8_temp << " "<<flush;
		}
		// cout << endl;
		basis_chal_x8->at(i) = x8;
		// cout << "\n";
	}

	int mul_chal_x8_size;
	ist >> mul_chal_x8_size;
	// cout << mul_chal_x8_size << "\n\n";

	for (i = 0; i < mul_chal_x8_size; i++)
	{
		ist >> mul_chal_x8->at(i);
		// cout<<"mul_chal_x8: " << mul_chal_x8->at(i) << " ";
	}
	// cout << endl;
	ist.close();
	
	vector<vector<Cipher_elg> *> *c = new vector<vector<Cipher_elg> *>(m);
	Functions::inputCipher(c, num);

	vector<vector<Cipher_elg> *> *C = new vector<vector<Cipher_elg> *>(m);
	in_name = "cipher_out.txt";
	ist.open(in_name.c_str(), ios::in);
	if (!ist)
		cout << "Can't open " << in_name;

	vector<Cipher_elg> *r = 0;
	string pattern2 = ",";
	string line;
	for (i = 0; i < m; i++)
	{
		r = new vector<Cipher_elg>(n);
		for (int j = 0; j < n; j++)
		{
			getline(ist, line);
			char *strc = new char[strlen(line.c_str()) + 1];
			strcpy(strc, line.c_str()); //string转换成C-string
			char *str_u_t = strtok(strc, pattern2.c_str());
			char *str_v = strtok(NULL, pattern2.c_str());
			char str_u[strlen(str_u_t)] = {'\0'};
			memcpy(str_u, str_u_t + 1, strlen(str_u_t));
			str_u[strlen(str_u_t) - 1] = '\0';
			str_v[strlen(str_v) - 1] = '\0';
			ZZ u, v;
			conv(u, str_u);
			conv(v, str_v);
			Cipher_elg temp = Cipher_elg(u, v, H.get_mod());
			r->at(j) = temp;
		}
		//	ost<<endl;
		C->at(i) = r;
	}
	ist.close();

	array<ZZ, 6> hashChk; //hash验证
	for (int i = 0; i < 6; i++)
	{
		ZZ hashValueZZ;
		conv(hashValueZZ, hashStr[i].c_str());
		Mod_p hashValueModP = Mod_p(hashValueZZ, H.get_mod());
		while (hashValueModP.get_val() > ord)
			hashValueModP.set_val(hashValueModP.get_val() - ord);
		hashChk[i] = hashValueModP.get_val();
	}

	int flag = 0;
	//Check that the D_hi's are constructed correctly
	// cout<<"omega_LL: "<<omega_LL<<endl;
	b = func_ver::check_Dh_op(c_Dh, mul_chal_x8, D_h_bar, r_Dh_bar, omega_LL);
	if (b == 1)
	{
		//Check that matrix D is constructed correctly
		b = func_ver::check_D_op(c_D0, c_z, c_A, c_B, chal_x8, chal_y4, A_bar, r_A_bar, n);
		if (b == 1)
		{
			//Check that D_s is constructed correctly
			b = func_ver::check_Ds_op(c_Ds, c_Dh, c_Dm, chal_x6, chal_x8, Ds_bar, r_Ds_bar);
			if (b == 1)
			{
				//Check that the Dl's are correct
				b = func_ver::check_Dl_op(c_Dl, chal_x8, A_bar, Ds_bar, chal_y6, r_Dl_bar);
				if (b == 1)
				{
					//Check that vector d was constructed correctly
					b = func_ver::check_d_op(c_Dh, c_d, chal_x8, d_bar, r_d_bar);
					if (b == 1)
					{
						//Check that Deltas are constructed correctly
						b = func_ver::check_Delta_op(c_dh, c_Delta, chal_x8, Delta_bar, d_bar, r_Delta_bar, chal_x2, chal_z4, chal_y4);
						if (b == 1)
						{
							//Check that the commitments a_T contain the right values
							b = check_B();
							if (b == 1)
							{
								//Check that the reecncryption was done correctly
								b = check_a();
								if (b == 1)
								{
									//Check that E_c->at(mu-1) contains c and D->at(4) = C
									b = check_c(c); //Both commitments shoud be com(0,0)
									if (b == 1 & c_a->at(4) == c_a_c->at(3))
									{
										//Check correctness of the chiphertexts
										b = check_E(C);
										if (b == 1)
										{
											//Check the the reencryption of the E_c is correct
											b = check_ac();
											if (b == 1)
											{
												//Check the the hash
												b = check_hash(hashChk);
												if (b == 0)
												{
													flag = 1;
												}
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
	}
	time_t tstop = clock();
	double ttime = (tstop - tstart) / (double)CLOCKS_PER_SEC * 1000;
	cout << "To verify the proof took " << ttime << " ms." << endl;
	cout << "Validation results: " << flush;
	if (flag)
		cout << "PASS" << endl;
	else
		cout << "FAIL" << endl;
	return flag;
}

void Verifier_toom::calculate_c(Cipher_elg &c, vector<vector<Cipher_elg> *> *enc)
{
	long i, j;
	Cipher_elg temp;
	ZZ chal_temp;
	ZZ ord = H.get_ord();
	vector<ZZ> *v_chal = 0;

	chal_temp = to_ZZ(1);
	c = Cipher_elg(1, 1, H.get_mod());
	v_chal = new vector<ZZ>(n);
	for (i = 0; i < m; i++)
	{
		for (j = 0; j < n; j++)
		{
			MulMod(chal_temp, chal_temp, chal_x2, ord);
			v_chal->at(j) = chal_temp;
		}
		multi_expo::expo_mult(temp, enc->at(i), v_chal, omega);
		Cipher_elg::mult(c, c, temp);
	}

	delete v_chal;
}

void Verifier_toom::calculate_ac(Mod_p &com)
{
	long i;
	Mod_p temp;

	com = c_a_c->at(0);
	for (i = 1; i < mu_h; i++)
	{
		Mod_p::expo(temp, c_a_c->at(i), x->at(i - 1));
		Mod_p::mult(com, com, temp);
	}
}

void Verifier_toom::reduce_c_B()
{
	long i, j;
	Mod_p temp, temp_1;

	for (i = 0; i < 4 * m_r; i++)
	{
		temp = c_B->at(4 * i);
		for (j = 1; j < mu; j++)
		{
			Mod_p::expo(temp_1, c_B->at(4 * i + j), x->at(j - 1));
			Mod_p::mult(temp, temp, temp_1);
		}
		c_B_small->at(i) = temp;
	}
}

void Verifier_toom::calculate_C(Cipher_elg &C, vector<Cipher_elg> *C_c, vector<ZZ> *x)
{
	long i;
	ZZ t_1;
	ZZ ord = H.get_ord();
	Mod_p temp;
	Mod_p gen = H.get_gen();
	Cipher_elg temp_1;

	NegateMod(t_1, a_c_bar, ord);
	Mod_p::expo(temp, gen, t_1);
	C = El.encrypt(temp, to_ZZ(0));
	Cipher_elg::mult(C, C, C_c->at(0));
	for (i = 1; i < mu_h; i++)
	{
		Cipher_elg::expo(temp_1, C_c->at(i), x->at(i - 1));
		Cipher_elg::mult(C, C, temp_1);
	}
}

int Verifier_toom::check_B()
{
	long i, j;
	Mod_p temp, temp_1, t_B, co_B;
	ZZ mod = G.get_mod();
	vector<Mod_p> *c_B_small = new vector<Mod_p>(5);
	vector<Mod_p> *c_B_temp = new vector<Mod_p>(4);

	c_B_small->at(0) = c_B0;
	for (i = 0; i < m_r; i++)
	{
		temp = c_B->at(4 * i);
		for (j = 1; j < 4; j++)
		{
			Mod_p::expo(temp_1, c_B->at(4 * i + j), chal_x6->at(j - 1));
			Mod_p::mult(temp, temp, temp_1);
		}
		c_B_small->at(i + 1) = temp;
	}
	t_B = c_B_small->at(0);
	for (i = 1; i < 5; i++)
	{
		Mod_p::expo(temp, c_B_small->at(i), chal_x8->at(i - 1));
		Mod_p::mult(t_B, t_B, temp);
	}

	delete c_B_temp;
	delete c_B_small;

	co_B = Ped.commit_opt(B_bar, r_B_bar);
	//	cout<<"B "<<t_B<<" "<<co_B<<endl;
	if (t_B == co_B)
	{
		return 1;
	}
	return 0;
}

int Verifier_toom::check_B_red()
{
	long i, j;
	Mod_p temp, temp_1, t_B, co_B;
	ZZ mod = G.get_mod();
	vector<Mod_p> *c_B_temp = new vector<Mod_p>(m_r + 1);

	c_B_temp->at(0) = c_B0;
	for (i = 0; i < m_r; i++)
	{
		temp = c_B_small->at(4 * i);
		for (j = 1; j < mu; j++)
		{
			Mod_p::expo(temp_1, c_B_small->at(4 * i + j), chal_x6->at(j - 1));
			Mod_p::mult(temp, temp, temp_1);
		}
		c_B_temp->at(i + 1) = temp;
	}
	t_B = c_B_temp->at(0);
	for (i = 1; i < m_r + 1; i++)
	{
		Mod_p::expo(temp, c_B_temp->at(i), chal_x8->at(i - 1));
		Mod_p::mult(t_B, t_B, temp);
	}
	delete c_B_temp;
	co_B = Ped.commit_opt(B_bar, r_B_bar);
	//	cout<<"B "<<t_B<<endl;
	//	cout<<"B "<<co_B<<endl;

	if (t_B == co_B)
	{
		return 1;
	}
	return 0;
}

int Verifier_toom::check_a()
{
	long i;
	Mod_p t_a, co_a;
	vector<ZZ> *chal_temp = new vector<ZZ>(8);

	chal_temp->at(0) = 1;
	for (i = 1; i < 8; i++)
	{
		chal_temp->at(i) = chal_x8->at(i - 1);
	}
	multi_expo::multi_expo_LL(t_a, c_a, chal_temp, omega_sw);
	co_a = Ped.commit_sw(a_bar, r_a_bar);

	//cout<<"a "<<t_a<<" "<<co_a<<" "<<c_a->at(4)<<endl;
	delete chal_temp;
	if (t_a == co_a)
	{
		return 1;
	}
	return 0;
}

int Verifier_toom::check_c(vector<vector<Cipher_elg> *> *enc)
{
	Cipher_elg c, C;

	calculate_c(c, enc);

	calculate_C(C, C_c, chal_x6);
	//	cout<<"C "<<C_c->at(mu-1)<<" "<<c<<endl;
	//	cout<<"C "<<E->at(4)<<" "<<C<<endl;
	if (C_c->at(mu - 1) == c & E->at(4) == C)
	{
		return 1;
	}
	return 0;
}

int Verifier_toom::check_c_red()
{
	Cipher_elg C;

	calculate_C(C, C_c, chal_x6);
	//	cout<<C<<endl;
	//	cout<<E->at(4)<<endl;
	if (E->at(4) == C)
	{
		return 1;
	}
	return 0;
}

int Verifier_toom::check_E(vector<vector<Cipher_elg> *> *C)
{
	long i, j;
	Mod_p temp;
	Mod_p gen = H.get_gen();
	Cipher_elg temp_1, temp_2, t_D, c_D;
	vector<ZZ> *chal_1_temp = new vector<ZZ>(4);
	vector<ZZ> *chal_2_temp = new vector<ZZ>(4);
	vector<Cipher_elg> *row_C;

	for (i = 0; i < 3; i++)
	{
		chal_1_temp->at(i) = chal_x6->at(2 - i);
	}
	chal_1_temp->at(3) = 1;

	for (i = 0; i < m_r; i++)
	{
		row_C = new vector<Cipher_elg>(n);
		for (j = 0; j < n; j++)
		{
			multi_expo::multi_expo_LL(row_C->at(j), C->at(4 * i)->at(j), C->at(4 * i + 1)->at(j), C->at(4 * i + 2)->at(j), C->at(4 * i + 3)->at(j), chal_1_temp, omega_sw);
		}
		C_small->at(i) = row_C;
	}

	for (i = 0; i < 3; i++)
	{
		chal_2_temp->at(i) = chal_x8->at(2 - i);
	}
	chal_2_temp->at(3) = to_ZZ(1);

	Mod_p::expo(temp, gen, a_bar);
	temp_1 = El.encrypt(temp, rho_bar);
	multi_expo::expo_mult(temp_2, C_small, chal_2_temp, B_bar, omega);
	Cipher_elg::mult(c_D, temp_1, temp_2);
	//c_D=temp_1*temp_2;

	multi_expo::expo_mult(t_D, E, basis_chal_x8, omega);

	/* cout << "\n";
	for (i = 0; i < basis_chal_x8->size(); i++)
	{
		for (int j = 0; j < basis_chal_x8->at(0)->size(); j++)
		{
			cout << basis_chal_x8->at(i)->at(j) << " ";
		} 
		cout << "\n";
	} 
	cout << "\n"; */

	delete chal_1_temp;
	delete chal_2_temp;
	Functions::delete_vector(C_small);
	// cout<<"E"<<t_D<<endl;
	// cout<<"E"<<c_D<<endl;
	if (t_D == c_D)
	{
		return 1;
	}
	return 0;
}

int Verifier_toom::check_E_red(vector<vector<Cipher_elg> *> *C)
{
	long i, j, l;
	Mod_p temp;
	Mod_p gen = H.get_gen();
	Cipher_elg temp_1, temp_2, t_D, c_D;
	vector<ZZ> *x_temp = new vector<ZZ>(4);
	vector<ZZ> *chal_1_temp = new vector<ZZ>(4);
	vector<ZZ> *chal_2_temp = new vector<ZZ>(4);
	vector<vector<Cipher_elg> *> *C_small_temp = 0;
	vector<Cipher_elg> *row_C;

	for (i = 0; i < 3; i++)
	{
		x_temp->at(i) = x->at(2 - i);
	}
	x_temp->at(3) = 1;

	l = mu * m_r;
	for (i = 0; i < l; i++)
	{
		row_C = new vector<Cipher_elg>(n);
		for (j = 0; j < n; j++)
		{
			multi_expo::multi_expo_LL(row_C->at(j), C->at(4 * i)->at(j), C->at(4 * i + 1)->at(j), C->at(4 * i + 2)->at(j), C->at(4 * i + 3)->at(j), x_temp, omega_sw);
		}
		C_small->at(i) = row_C;
	}

	for (i = 0; i < 3; i++)
	{
		chal_1_temp->at(i) = chal_x6->at(2 - i);
	}
	chal_1_temp->at(3) = 1;

	C_small_temp = new vector<vector<Cipher_elg> *>(m_r);
	for (i = 0; i < m_r; i++)
	{
		row_C = new vector<Cipher_elg>(n);
		for (j = 0; j < n; j++)
		{
			multi_expo::multi_expo_LL(row_C->at(j), C_small->at(4 * i)->at(j), C_small->at(4 * i + 1)->at(j), C_small->at(4 * i + 2)->at(j), C_small->at(4 * i + 3)->at(j), chal_1_temp, omega);
		}
		C_small_temp->at(i) = row_C;
	}

	for (i = 0; i < 3; i++)
	{
		chal_2_temp->at(i) = chal_x8->at(2 - i);
	}
	chal_2_temp->at(3) = to_ZZ(1);

	Mod_p::expo(temp, gen, a_bar);
	temp_2 = El.encrypt(temp, rho_bar);
	multi_expo::expo_mult(temp_1, C_small_temp, chal_2_temp, B_bar, omega);
	Cipher_elg::mult(c_D, temp_1, temp_2);
	//c_D=temp_2*temp_1;

	multi_expo::expo_mult(t_D, E, basis_chal_x8, omega);
	Functions::delete_vector(C_small);
	Functions::delete_vector(C_small_temp);
	delete chal_2_temp;
	delete chal_1_temp;
	delete x_temp;
	//cout<<"E"<<t_D<<endl;
	//cout<<"E"<<c_D<<endl;
	if (t_D == c_D)
	{
		return 1;
	}
	return 0;
}

int Verifier_toom::check_ac()
{
	Mod_p t_a_c, co_a_c, temp;
	int i;

	t_a_c = c_a_c->at(0);
	for (i = 1; i < 7; i++)
	{
		Mod_p::expo(temp, c_a_c->at(i), chal_x6->at(i - 1));
		Mod_p::mult(t_a_c, t_a_c, temp);
	}
	co_a_c = Ped.commit_sw(a_c_bar, r_ac_bar);
	//	cout<<"ac "<<t_a_c<<" "<<c_a_c;
	if (t_a_c == co_a_c)
	{
		return 1;
	}
	return 0;
}

int Verifier_toom::check_hash(array<ZZ, 6> hashChk)
{
	int a = (hashChk[0] == chal_x2) ? 0 : 1;
	int b = (hashChk[1] == chal_z4) ? 0 : 1;
	int c = (hashChk[2] == chal_y4) ? 0 : 1;
	int d = (hashChk[3] == chal_x6->at(0)) ? 0 : 1;
	int e = (hashChk[4] == chal_y6->at(0)) ? 0 : 1;
	int f = (hashChk[5] == chal_x8->at(0)) ? 0 : 1;
	return a+b+c+d+e+f;
}