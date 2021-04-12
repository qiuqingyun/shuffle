#include <iostream>
#include <ctime>
#include <vector>
#include <fstream>
#include <chrono>
#include <ctime>
#include "sha256.h"
#include "G_q.h"
#include "Functions.h"
#include "ElGammal.h"
#include "Cipher_elg.h"
#include "Permutation.h"
#include "Prover_toom.h"
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

int shuffle_w_toom(vector<vector<Cipher_elg>*>* e, vector<vector<Cipher_elg>*>* E, vector<vector<ZZ>*>* R, vector<vector<vector<long>*>*>* pi, vector<long> num, ZZ genq, int role);



int main(int argc, char** argv)
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
		if (role != 0 && role != 1 && role != 2)
		{
			cout << "Input your role:\nProver   -> 0\nVerifier -> 1" << endl;
			while (role != 0 && role != 1)
			{
				cout << "role(0/1): " << flush;
				cin >> role;
			}
		}
	}
	if (role == 2) {
		long p=100, q=90;
		srand((unsigned)time(NULL));
		if (argc > 2)
		{
			p = atol(argv[2]);
			q = atol(argv[3]);
			cout << "s" << endl;
		}
		cout << "Parameters generating" << flush;
		Functions::pqGen(p, q);
		cout << "\nParameters have been generated\n" << endl;
		return 0;
	}
	cout << "You are " << (role ? "Verifier" : "Prover") << "." << endl;

	int i;
	vector<long> num;						  //包含8个参数

	vector<vector<vector<long>*>*>* pi = 0; //Permutation，用于shuffle
	vector<vector<ZZ>*>* R = 0;			  //用于重加密的随机数
	ZZ genq;								  //generator of Z_q，用于验证的生成元
	long m, n;
	double tstart, tstop, ttime, time_p, time_v;
	string file_name;

	time_p = 0;
	time_v = 0;
	num = vector<long>(8);
	//读取parameters文件里的参数，读取ElGammal公钥（和私钥）
	Functions::read_config(num, genq);
	m = num[1]; //行数 m
	c = new vector<vector<Cipher_elg>*>(m); //输入的密文
	C = new vector<vector<Cipher_elg>*>(m); //输出的密文
	Functions::inputCipher(c, num);
	n = num[2]; //列数 n
	if (role == 0)
		Ped = Pedersen(n, G);
	else
	{
		ifstream ist;
		ist.open("Pedersen.txt", ios::in);
		if (!ist)
		{
			cout << "Can't open Pedersen.txt" << endl;
			exit(1);
		}
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
		//shuffle开始
		tstart = (double)clock() / CLOCKS_PER_SEC;
		pi = new vector<vector<vector<long>*>*>(m);
		//生成用于shuffle的向量pi，创建permu.txt，内容为m×n(16×5)个整数
		Permutation::perm_matrix(pi, n, m);

		R = new vector<vector<ZZ>*>(m);
		//生成用于重加密的随机数，创建random.txt，内容为m×n(16×5)个随机数
		Functions::randomEl(R, num);
		//输出的密文

		//使用换元pi和随机元素R对密文e进行重新加密，创建reencrypted_ciper.txt，内容为mxn(16x5)个二元重加密后的(u,v)密文组
		Functions::reencryptCipher(C, c, pi, R, num);
		/*Functions::decryptCipher(c, num, 0);
		Functions::decryptCipher(C, num, 1);*/

		//shuffle开始结束
		tstop = (double)clock() / CLOCKS_PER_SEC;
		ttime = (tstop - tstart) * 1000;
		cout << "To shuffle the ciphertexts took " << ttime << " ms." << endl;
	}
	else {
		ifstream ist;
		string in_name = "cipher_out.txt";
		ist.open(in_name.c_str(), ios::in);
		if (!ist)
		{
			cout << "Can't open " << in_name;
			exit(1);
		}
		Functions::readCipher(C, ist, num);
		ist.close();
		/*Functions::decryptCipher(c, num, 0);
		Functions::decryptCipher(C, num, 1);*/
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
	/*cout << "Press any key to close this window..." << flush;
	getch();*/
	return 0;
}

int shuffle_w_toom(vector<vector<Cipher_elg>*>* c, vector<vector<Cipher_elg>*>* C, vector<vector<ZZ>*>* R, vector<vector<vector<long>*>*>* pi, vector<long> num, ZZ gen, int role)
{
	Prover_toom* P = 0;
	Verifier_toom* V = 0;
	time_t tstart = clock();
	string act;
	mu = 4;
	mu_h = 2 * mu - 1;
	m_r = num[1] / mu;
	int ans = 0;
	if (role)
	{ //V
		V = new Verifier_toom(num);
		ans = V->round_10(c, C);
		act = "verify";
		delete V;
	}
	else
	{ //P
		P = new Prover_toom(C, R, pi, num, gen);
		P->round_9();
		act = "generate";
		delete P;
	}
	time_t tstop = clock();
	double ttime = (tstop - tstart) / (double)CLOCKS_PER_SEC * 1000;
	cout << "To " + act + " the proof took " << ttime << " ms." << endl;
	return ans;
}
