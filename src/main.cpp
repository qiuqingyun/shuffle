/*
 * main.cpp
 *
 *  Created on: 26.10.2010
 *      Author: stephaniebayer
 */

#include <stdio.h>
#include <time.h>
#include <vector>
#include <fstream>

#include "G_q.h"
#include "Functions.h"
#include "ElGammal.h"
#include "Cipher_elg.h"
#include "Permutation.h"
#include "Prover.h"
#include "Prover_me.h"
#include "Prover_fft.h"
#include "Prover_toom.h"
#include "Verifier.h"
#include "Verifier_me.h"
#include "Verifier_toom.h"
#include <NTL/ZZ.h>
#include <NTL/mat_ZZ.h>

#include <NTL/matrix.h>
#include <NTL/vec_vec_ZZ.h>
NTL_CLIENT

G_q G = G_q();			   // group used for the Pedersen commitment
G_q H = G_q();			   // group used for the the encryption
ElGammal El = ElGammal();  //The class for encryption and decryption
Pedersen Ped = Pedersen(); //Object which calculates the commitments
double time_rw_p = 0;
double time_rw_v = 0;
double time_cm = 0;
long m_r = 0;  //number of rows after reduction
long mu = 0;   //number of rows after reduction
long mu_h = 0; //2*mu-1, number of extra elements in the reduction

int shuffle_w_toom(vector<vector<Cipher_elg> *> *e, vector<vector<Cipher_elg> *> *E, vector<vector<ZZ> *> *R, vector<vector<vector<long> *> *> *pi, vector<long> num, ZZ genq, int role);

#include <iostream>
#include <chrono>
#include <ctime>
#include "sha256.h"

int main(int argc, char **argv)
{
	int role = -1;
	if (argc < 2)
	{
		cout << "Input your role:\nProver   -> 0\nVerifier -> 1" << endl;
		;
		while (role != 0 && role != 1)
		{
			cout << "role(0/1): " << flush;
			cin >> role;
		}
	}
	else
	{
		role = argv[1][0] - '0';
		if (role != 0 && role != 1)
		{
			cout << "Input your role:\nProver   -> 0\nVerifier -> 1" << endl;
			while (role != 0 && role != 1)
			{
				cout << "role(0/1): " << flush;
				cin >> role;
			}
		}
	}
	cout << "You are " << (role ? "Verifier" : "Prover") << "." << endl;

	int i;
	vector<long> num;						  //包含8个参数
	vector<vector<Cipher_elg> *> *c = 0;	  //原始输入的密文
	vector<vector<Cipher_elg> *> *C = 0;	  //重加密的密文
	vector<vector<vector<long> *> *> *pi = 0; //Permutation，用于shuffle
	vector<vector<ZZ> *> *R = 0;			  //用于重加密的随机数
	ZZ genq;								  //generator of Z_q，用于验证的生成元
	long m, n;
	double tstart, tstop, ttime, time_p, time_v;
	string file_name;

	time_p = 0;
	time_v = 0;
	num = vector<long>(8);
	//读取config文件里的参数，读取ElGammal公钥（和私钥）
	Functions::read_config(num, genq);
	m = num[1]; //行数 m
	n = num[2]; //列数 n
	if (role == 0)
		Ped = Pedersen(n, G);
	else
	{
		ifstream ist;
		ist.open("Pedersen.txt", ios::in);
		vector<Mod_p> gen_in;
		ZZ gen_temp;
		for (int i = 0; i <= n; i++)
		{
			string gen_str;
			ist >> gen_str;
			conv(gen_temp, gen_str.c_str());
			gen_in.push_back(Mod_p(gen_temp, H.get_mod()));
		}
		Ped = Pedersen(n, G, gen_in);
		ist.close();
	}
	Ped.set_omega(num[3], num[7], num[4]);
	if (role == 0)
	{
		c = new vector<vector<Cipher_elg> *>(m); //输入的密文
		//从cipher_in.txt中读取mxn(16x5)个(u,v)密文组
		//u = g^r，v = m×y^r，其中r为随机数，y是公钥，m是明文消息
		Functions::inputCipher(c, num);

		//shuffle开始
		tstart = (double)clock() / CLOCKS_PER_SEC;
		pi = new vector<vector<vector<long> *> *>(m);
		//生成用于shuffle的向量pi，创建permu.txt，内容为m×n(16×5)个整数
		Permutation::perm_matrix(pi, n, m);

		R = new vector<vector<ZZ> *>(m);
		//生成用于重加密的随机数，创建random.txt，内容为m×n(16×5)个随机数
		Functions::randomEl(R, num);
		//输出的密文
		C = new vector<vector<Cipher_elg> *>(m);
		//使用换元pi和随机元素R对密文e进行重新加密，创建reencrypted_ciper.txt，内容为mxn(16x5)个二元重加密后的(u,v)密文组
		Functions::reencryptCipher(C, c, pi, R, num);
		// Functions::decryptCipher(c,num,0);
		// Functions::decryptCipher(C,num,1);

		//shuffle开始结束
		tstop = (double)clock() / CLOCKS_PER_SEC;
		ttime = (tstop - tstart) * 1000;
		cout << "To shuffle the ciphertexts took " << ttime << " ms." << endl;
	}
	//正确性证明
	shuffle_w_toom(c, C, R, pi, num, genq, role);

	if (role == 0)
	{
		Functions::delete_vector(c);
		Functions::delete_vector(C);
		Functions::delete_vector(R);
		Functions::delete_vector(pi);
	}
	return 0;
}

int shuffle_w_toom(vector<vector<Cipher_elg> *> *c, vector<vector<Cipher_elg> *> *C, vector<vector<ZZ> *> *R, vector<vector<vector<long> *> *> *pi, vector<long> num, ZZ gen, int role)
{

	Prover_toom *P = 0;
	Verifier_toom *V = 0;
	double tstart, tstart_t, tstop, tstop_t, ttime, time_p, time_v;
	ZZ chal_10, ans_12;
	string file_name, name;
	ofstream ost;
	mu = 4;
	mu_h = 2 * mu - 1;
	m_r = num[1] / mu;

	// array<string, 5> files;
	int ans = 0;

	if (role)
	{ //V
		V = new Verifier_toom(num);
		ans = V->round_10(c, C);
		delete V;
	}
	else
	{ //P
		P = new Prover_toom(C, R, pi, num, gen);
		P->round_9();
		delete P;
	}

	return ans;
}
