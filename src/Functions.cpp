#include "Functions.h"
#include <NTL/ZZ.h>
NTL_CLIENT

#include <vector>
#include <iostream>
#include <time.h>
#include <fstream>
#include <sstream>
#include <stdlib.h>
using namespace std;

extern G_q G;
extern G_q H;
extern ElGammal El;
extern Pedersen Ped;
vector<vector<Cipher_elg>*>* c = 0;	  //原始输入的密文
vector<vector<Cipher_elg>*>* C = 0;	  //重加密的密文
int Threshold = 100;
int exitMax = 10;

#define DEBUG 1

Functions::Functions()
{
	// TODO Auto-generated constructor stub
}

Functions::~Functions()
{
	// TODO Auto-generated destructor stub
}

void Functions::pqGen(long lp, long lq) {
	int flag = 1, index = 0;
	vector<ZZ>* pq = new vector<ZZ>(6);
	while (flag || pq->at(0) != pq->at(4))
	{
		SetSeed(to_ZZ((unsigned int)time(0) + clock()));
		//cout << endl;
		flag = find_groups(pq, lq, lp, lp, 16);
		if (++index > exitMax)
			exit(1);
	}
}

void Functions::read_config(vector<long>& num, ZZ& genq)
{
	vector<long> para = { 32,16,2,7,6,3,0,5 };
	num = para;
	vector<ZZ>* pq = new vector<ZZ>(4);
	ifstream ist("parameters.txt", ios::in);
	if (!ist)
	{
		cout << "Can't open parameters.txt" << endl;
		exit(1);
	}
	for (int i = 0; i < 4; i++)
	{
		ist >> pq->at(i);
	}
	ist.close();
	// cout<<NumBits(pq->at(1))<<" "<<NumBits(pq->at(0))<<endl;
	G = G_q(pq->at(2), pq->at(1), pq->at(0)); //ElGammal参数：生成元h 阶数q 模数p
	H = G_q(pq->at(2), pq->at(1), pq->at(0));
	genq = pq->at(3);

	El.set_group(H);
	ist.open("ElGammal.txt", ios::in);
	if (!ist)
	{
		cout << "Can't open ElGammal.txt" << endl;
		exit(1);
	}
	string sk_str, pk_str;
	ZZ sk, pk;
	getline(ist, sk_str);
	getline(ist, pk_str);
	conv(sk, sk_str.c_str());
	conv(pk, pk_str.c_str());
	El.set_key(sk, pk);
	ist.close();

	delete pq;
}

long Functions::tolong(string s)
{
	//using namespace std;
	long n;
	stringstream ss(s); // Could of course also have done ss("1234") directly.

	if ((ss >> n).fail())
	{
		//error
	}

	return n;
}

string Functions::tostring(long n)
{

	stringstream ss;
	ss << n;
	return ss.str();
}

string Functions::tostring(ZZ n)
{

	stringstream ss;
	ss << n;
	return ss.str();
}

//Creates a matrix of N random elements, if N<n*m 1 is encrypted in the last elements
vector<vector<Cipher_elg>*>* Functions::createCipher(vector<long> num)
{
	long N = num[0];
	long m = num[1];
	long n = num[2];
	vector<vector<Cipher_elg>*>* C = new vector<vector<Cipher_elg>*>(m);
	vector<Cipher_elg>* r = 0;
	Cipher_elg temp;
	ofstream ost;
	ZZ ran_2, ord;
	Mod_p ran_1;
	long count;
	long i, j;

	count = 1;
	ord = H.get_ord();
	ost.open("cipher_c.txt");
	for (i = 0; i < m; i++)
	{
		r = new vector<Cipher_elg>(n);

		for (j = 0; j < n; j++)
		{
			if (count <= N)
			{
				ran_2 = RandomBnd(ord);
				ran_1 = H.random_el(0);
				temp = El.encrypt(ran_1, ran_2);
				r->at(j) = temp;
				ost << temp << endl;
				count++;
			}
			else
			{
				ran_2 = RandomBnd(ord);
				temp = El.encrypt(1, ran_2);
				r->at(j) = temp;
				count++;
			}
		}
		C->at(i) = r;
	}
	ost.close();

	return C;
}

void Functions::createCipher(vector<vector<Cipher_elg>*>* C, vector<long> num)
{
	long N = num[0];
	long m = num[1]; //行
	long n = num[2]; //列
	vector<Cipher_elg>* r = 0;
	Cipher_elg temp;
	ZZ ran_2, ord;
	Mod_p ran_1;
	long count;
	long i, j;
	ofstream ost, ost2;
	ifstream ist;

	count = 1;
	ord = H.get_ord(); //order of the group

	vector<vector<Mod_p>> plaintexts;
	for (int vi = 0; vi < m; vi++) {
		vector<Mod_p> v_temp;
		for (int vj = 0; vj < n; vj++) {
			Mod_p temp_p;
			v_temp.push_back(temp_p);
		}
		plaintexts.push_back(v_temp);
	}
	ist.open("plaintext.txt", ios::in);
	if (!ist)
	{
		cout << "\"plaintext.txt\" does not exist, will be generated randomly" << endl;
		ost2.open("plaintext.txt");
		for (i = 0; i < m; i++)
		{
			for (j = 0; j < n; j++)
			{
				if (count <= N)
				{
					ran_1 = H.random_el(0); //明文m
					plaintexts[i][j] = ran_1;
				}
				else
				{
					ran_1 = 1; //明文m
					plaintexts[i][j] = ran_1;
				}
				ost2 << ran_1 << " ";
			}
			ost2 << endl;
		}
		ost2.close();
	}
	else
	{
		for (i = 0; i < m; i++)
			for (j = 0; j < n; j++)
				ist >> plaintexts[i][j];
	}

	ost.open("cipher_in.txt");
	for (i = 0; i < m; i++)
	{
		r = new vector<Cipher_elg>(n);
		for (j = 0; j < n; j++)
		{
			ran_2 = RandomBnd(ord);			 //随机数r，也被称作临时密钥
			ran_1 = plaintexts[i][j];		 //明文m
			temp = El.encrypt(ran_1, ran_2); //得到(u,v)密文组，u = g^r，v = m×y^r，y为公钥
			r->at(j) = temp;
			count++;
			ost << temp << " ";
		}
		ost << endl;
		C->at(i) = r;
	}
}

void Functions::inputCipher(vector<vector<Cipher_elg>*>*& Cipher, vector<long> num)
{
	long m = num[1]; //行
	long n = num[2]; //列
	ifstream ist;

	ist.open("cipher_in.txt", ios::in);
	if (!ist)
	{
		cout << "Can't open cipher_in.txt" << endl;
		exit(1);
	}
	readCipher(Cipher, ist, num);
	ist.close();
}

void Functions::readCipher(vector<vector<Cipher_elg>*>*& Cipher, ifstream& ist, vector<long> num)
{
	int m, n, amount, index_m = 0, index_n = 0, index = 0;
	string in_temp, u_str, v_str;
	size_t pos_start, pos_mid, pos_end;
	vector<string> cipher_raw;
	while (ist >> in_temp)
		cipher_raw.push_back(in_temp);
	amount = cipher_raw.size();
	num[0] = amount;
	m = num[1];
	n = amount / 16 + ((amount % 16) ? 1 : 0);
	num[2] = n;
	Cipher = new vector<vector<Cipher_elg>*>(m);
	for (int i = 0; i < m; i++) {
		vector<Cipher_elg>* r = new vector<Cipher_elg>(n);
		for (int j = 0; j < n; j++) {
			Cipher_elg temp;
			r->at(j) = temp;
		}
		Cipher->at(i) = r;
	}
	for (string i : cipher_raw) {
		index_m = index / n;
		index_n = index % n;
		pos_start = i.find("(");
		pos_mid = i.find(",");
		pos_end = i.find(")");
		u_str = i.substr(pos_start + 1, pos_mid - 1);
		v_str = i.substr(pos_mid + 1, pos_end - pos_mid - 1);
		ZZ u, v;
		conv(u, u_str.c_str());
		conv(v, v_str.c_str());
		Cipher_elg temp = Cipher_elg(u, v, H.get_mod());
		Cipher->at(index_m)->at(index_n) = temp;
		index++;
	}
	return;
}

void Functions::decryptCipher(vector<vector<Cipher_elg>*>* C, vector<long> num, int flag)
{
	long m = num[1]; //行
	long n = num[2]; //列
	string name[2] = { "pOrigin.txt", "pShuffle.txt" };
	ofstream ost;
	ost.open(name[flag], ios::out);
	ZZ plaintext;
	for (int i = 0; i < m; i++)
	{
		for (int j = 0; j < n; j++)
		{
			plaintext = El.decrypt(C->at(i)->at(j), flag);
			ost << plaintext << " " << flush;
		}
		ost << endl;
	}
}

//Creates a matrix of random numbers
vector<vector<ZZ>*>* Functions::randomEl(vector<long> num)
{
	long m = num[1];
	long n = num[2];
	vector<vector<ZZ>*>* R = new vector<vector<ZZ>*>(m);
	vector<ZZ>* r = 0;
	ZZ ran, ord;
	long i, j;
	ord = H.get_ord();
	for (i = 0; i < m; i++)
	{
		r = new vector<ZZ>(n);

		for (j = 0; j < n; j++)
		{
			r->at(j) = RandomBnd(ord);
		}
		R->at(i) = r;
	}
	return R;
}

void Functions::randomEl(vector<vector<ZZ>*>* R, vector<long> num)
{
	long m = num[1];
	long n = num[2];
	vector<ZZ>* r = 0;
	ZZ ran, ord;
	long i, j;
	ord = H.get_ord();

	// string name = "random.txt";
	// ofstream ost;
	// ost.open(name.c_str());
	for (i = 0; i < m; i++)
	{
		r = new vector<ZZ>(n);
		for (j = 0; j < n; j++)
		{
			r->at(j) = RandomBnd(ord);
			// ost<<r->at(j)<<" ";
		}
		//		ost<<endl;
		R->at(i) = r;
	}
	// ost.close();
}

//reencrypts the ciphertexts e using the permutation pi and the random elements R
vector<vector<Cipher_elg>*>* Functions::reencryptCipher(vector<vector<Cipher_elg>*>* e, vector<vector<vector<long>*>*>* pi, vector<vector<ZZ>*>* R, vector<long> num)
{
	long n, m;
	m = num[1];
	n = num[2];
	vector<vector<Cipher_elg>*>* C = new vector<vector<Cipher_elg>*>(m);
	vector<Cipher_elg>* r = 0;
	Cipher_elg temp;
	ZZ ran;
	long i, j;
	long row, col;
	for (i = 0; i < m; i++)
	{
		r = new vector<Cipher_elg>(n);
		for (j = 0; j < n; j++)
		{
			temp = El.encrypt(1, R->at(i)->at(j));
			row = pi->at(i)->at(j)->at(0);
			col = pi->at(i)->at(j)->at(1);
			Cipher_elg::mult(r->at(j), temp, e->at(row)->at(col));
		}
		C->at(i) = r;
	}
	return C;
}

void Functions::reencryptCipher(vector<vector<Cipher_elg>*>* C, vector<vector<Cipher_elg>*>* e, vector<vector<vector<long>*>*>* pi, vector<vector<ZZ>*>* R, vector<long> num)
{
	long n, m;
	m = num[1]; //行
	n = num[2]; //列
	vector<Cipher_elg>* r = 0;
	Cipher_elg temp;
	ZZ ran;
	long i, j;
	long row, col;
	string name = "cipher_out.txt";
	ofstream ost;
	ost.open(name.c_str());
	for (i = 0; i < m; i++)
	{
		r = new vector<Cipher_elg>(n);
		for (j = 0; j < n; j++)
		{
			temp = El.encrypt(1, R->at(i)->at(j));				   //生成随机加密的密文1
			row = pi->at(i)->at(j)->at(0);						   //shuffle后需要移动的行
			col = pi->at(i)->at(j)->at(1);						   //shuffle后需要移动的列
			Cipher_elg::mult(r->at(j), temp, e->at(row)->at(col)); //同态乘法
			ost << r->at(j) << endl;
		}
		//	ost<<endl;
		C->at(i) = r;
	}
	ost.close();
}

//Returns the Hadamard product of x and y
void Functions::Hadamard(vector<ZZ>* ret, vector<ZZ>* x, vector<ZZ>* y)
{

	long n, m, i;
	ZZ ord = H.get_ord();
	n = x->size();
	m = y->size();

	if (m != n)
	{
		cout << "Not possible" << endl;
	}
	else
	{
		for (i = 0; i < n; i++)
		{
			MulMod(ret->at(i), x->at(i), y->at(i), ord);
		}
	}
}

//returns the bilinear map of x and y, defined as x(y¡t)^T
ZZ Functions::bilinearMap(vector<ZZ>* x, vector<ZZ>* y, vector<ZZ>* t)
{
	long i, l;
	ZZ result, ord, tem;

	vector<ZZ>* temp = new vector<ZZ>(x->size());

	ord = H.get_ord();
	Hadamard(temp, y, t);
	l = x->size();
	result = 0;
	for (i = 0; i < l; i++)
	{
		MulMod(tem, x->at(i), temp->at(i), ord);
		AddMod(result, result, tem, ord);
	}
	delete temp;
	return result;
}

//finds prime numbers q,p such that p = 2*a*q+1 using test provided by Mau94, lp,lq are the number of bits of q,p
int Functions::find_group(vector<ZZ>* pq, long lq, long lp, long m)
{
	long l, i, j, logl, index = 0;
	ZZ mod30;
	ZZ q, q1, q2, p, a, an, gcd, gcd_1, gcd_2, temp, temp_1, gen, gen2, genq;
	bool b, bo, bol;
	int count = 0;
	string name;
	//q-1 needs to be divisible by 2*m, such that we can find a 2m-root of unity
	//cout << "Expectation: p " << lp << " bit | q " << lq << " bit" << endl;
	if ((lp - lq) > 2)
	{
		bol = false;
		while (bol == false)
		{
			l = lq - NumBits(2 * m);
			//generates q as 2*2*m*q1*q2+1 and tests if q can be prime
			b = false;
			bol = true;
			while (b == false)
			{
				b = new_q(q, q1, q2, m, l);
				cout << "." << flush;
			}
			b = false;
			while (b == false)
			{
				b = check_q(a, q, q1, q2, m, l);
				cout << "." << flush;
			}
			genq = a;

			l = lp - lq;
			bo = false;
			//Generate p as 2*q*q1+1 and test if p is possible prime
			while (bo == false)
			{
				bo = new_p(p, q1, q, l);
				//bo=new_p(p,q1, q2,q,l);
				cout << "." << flush;
				if (index++ > Threshold)
					return 1;
			}
			logl = 20 * log(l);
			j = 0;
			b = false;
			//If after log tries no p=2*q*q1+1 is prime a new q is picked
			while (j < logl && b == false)
			{
				b = true;

				if (q1 * q2 > q)
				{
					b = check_p(a, p, q1, q, l, j);
					//b=check_p(a, p, q1, q2,q,l,j);
				}
				else
				{
					b = check_p(a, p, q, q1, l, j);
				}
			}
			if (j == logl)
			{
				bol = false;
			}
			//cout << "." << flush;
		}

		//Generator of G_q in Z_p
		gen = PowerMod(a, 2 * q1, p);
	}
	else
	{ //Sophie Germain prime p=2*q+1
		bol = false;
		count = 0;
		while (bol == false)
		{
			l = lq - NumBits(2 * m);
			b = false;
			count++;
			while (b == false)
			{
				//Generate q as 2*2*m*q1*q2+1
				b = new_q(q, q1, q2, m, l);

				//q has to be 11,23,39 mod 30 to be part of a Sophie Germain prime
				mod30 = q % 30;
				if (mod30 == to_ZZ(11))
				{
					b = true;
				}
				if (mod30 == to_ZZ(23))
				{
					b = true;
				}
				if (mod30 == to_ZZ(29))
				{
					b = true;
				}
				cout << "." << flush;
			}
			b = false;
			while (b == false)
			{
				b = check_q(a, q, q1, q2, m, l);
				cout << "." << flush;
			}
			genq = a;

			p = 2 * q + 1;
			bol = probPrime(p);
			if (bol == true)
			{
				//Checks for random a, if a is a generator
				for (i = 0; i < 100; i++)
				{
					a = RandomBnd(p);
					an = PowerMod(a, p - 1, p);
					if (a != 1 && an == 1)
					{
						temp = PowerMod(a, q, p);
						if (temp != 1)
						{
							break;
						}
					}
				}
				if (i == 100)
				{
					bol = false;
				}
			}
			//cout << "." << flush;
		}

		//Generator of G_q in Z_p
		gen = PowerMod(a, 2, p);
	}
	pq->at(0) = p;
	pq->at(1) = q;
	pq->at(2) = gen;
	//Generator of Z_q
	pq->at(3) = genq;
	//cout << "Actuality  : p " << NumBits(pq->at(0)) << " bit | q " << NumBits(pq->at(1)) << " bit" << endl;
	//cout << NumBits(pq->at(1)) << " " << NumBits(pq->at(0)) << endl;
	ofstream ost;

	name = "parameters.txt";
	ost.open(name.c_str());
	ost << p << endl;
	ost << q << endl;
	ost << gen << endl;
	ost << genq << endl;
	ost.close();
	return 0;
}

//finds prime numbers q,p, p1 such that p = 2*a*q+1 and p1=2*b*q+1 using test provided by Mau94, lp,lq are the number of bits of q,p
int Functions::find_groups(vector<ZZ>* pq, long lq, long lp, long lp1, long m)
{
	ZZ q, q1, p1, a, gen;
	bool b, bo, bol;
	long logl, l, j;
	string name;
	int flag = 0, index = 0;

	bol = false;
	while (bol == false)
	{
		bol = true;
		flag = find_group(pq, lq, lp, m);
		if (flag)
			return flag;

		q = pq->at(1);
		l = lp1 - lq;
		if (l <= 1)
			exit(1);
		//Generate p1 as 2*q*q1+1 and test if p1 is possible prime
		bo = false;
		while (bo == false)
		{
			bo = new_p(p1, q1, q, l);
			cout << "." << flush;
			if (index++ > Threshold)
				return 1;
		}
		logl = log(l);
		j = 0;
		b = false;
		//If after log tries no p=2*q*q1+1 is prime a new q and p is picked
		while (j < logl && b == false)
		{
			b = true;

			if (q1 > q)
			{
				b = check_p(a, p1, q1, q, l, j);
			}
			else
			{
				b = check_p(a, p1, q, q1, l, j);
			}
			cout << "." << flush;
		}
		if (j == logl)
		{
			bol = false;
		}
		//cout << "." << flush;
	}

	//Generator of G_q in Z_p1
	gen = PowerMod(a, 2 * q1, p1);

	pq->at(4) = p1;
	pq->at(5) = gen;

	ofstream ost;
	//cout << NumBits(pq->at(1)) << " " << NumBits(pq->at(0)) << " " << NumBits(pq->at(4)) << endl;
	name = "pqhg.txt";
	ost.open(name.c_str());
	ost << pq->at(0) << endl;
	ost << pq->at(1) << endl;
	ost << pq->at(2) << endl;
	//ost << pq->at(3) << endl;
	//ost << p1 << endl;
	ost << gen;
	ost.close();
	return 0;
}

//Checks if a integer q is probably prime, calls the MillerRabin Test only with 1 witness
bool Functions::probPrime(ZZ q)
{
	bool b;

	b = false;
	if (q % 3 == 0)
	{
	}
	else if (q % 5 == 0)
	{
	}
	else if (q % 7 == 0)
	{
	}
	else if (q % 11 == 0)
	{
	}
	else if (q % 13 == 0)
	{
	}
	else if (q % 17 == 0)
	{
	}
	else if (q % 19 == 0)
	{
	}
	else if (ProbPrime(q, 1) == 0)
	{
	}
	else
		b = true;

	return b;
}

bool Functions::checkGCD(ZZ a, ZZ q1, ZZ q)
{
	bool b;
	ZZ temp, gcd;

	b = false;

	temp = PowerMod(a, (q - 1) / q1, q);
	gcd = GCD(temp - 1, q);
	if (gcd == 1)
	{
		b = true;
	}
	return b;
}

bool Functions::checkPow(ZZ a, ZZ q1, ZZ q)
{
	bool b;
	ZZ temp;

	b = true;
	temp = PowerMod(a, (q - 1) / q1, q);
	if (temp == 1)
	{
		b = false;
	}
	return b;
}

long Functions::checkL1(ZZ& a, ZZ q, ZZ q1)
{
	long i;
	ZZ an;

	for (i = 0; i < 100; i++)
	{
		a = RandomBnd(q);
		an = PowerMod(a, q - 1, q);
		if (a != 1 && an == 1 && checkGCD(a, q1, q) && checkGCD(a, to_ZZ(2), q))
		{
			break;
		}
	}

	return i;
}

long Functions::checkL1(ZZ& a, ZZ q, ZZ q1, ZZ q2)
{
	long i;
	ZZ an;

	for (i = 0; i < 100; i++)
	{
		a = RandomBnd(q);
		an = PowerMod(a, q - 1, q);
		if (a != 1 && an == 1 && checkGCD(a, q1, q) && checkGCD(a, q2, q) && checkGCD(a, to_ZZ(2), q))
		{
			break;
		}
	}

	return i;
}

bool Functions::new_q(ZZ& q, ZZ& q1, ZZ& q2, long m, long l)
{
	bool b;

	//Generate q as 2*2*m*q1*q2+1
	q1 = GenPrime_ZZ(l / 2 + 1);
	q2 = GenPrime_ZZ(l / 2 - 1);
	q = 2 * 2 * m * q1 * q2 + 1;

	b = probPrime(q);
	return b;
}

bool Functions::check_q(ZZ& a, ZZ& q, ZZ& q1, ZZ& q2, long m, long l)
{
	bool b, bo;
	long i;

	b = true;
	//Test condition of Lemma 1 of Mau94 with F=2*m*q1 and R = q2, F>sqrt(q) with different random integers a
	i = checkL1(a, q, q1);
	//If no a satisfies condition of Lemma 1, new values for q1, q2 are picked
	if (i == 100)
	{
		bo = false;
		while (bo == false)
		{
			bo = new_q(q, q1, q2, m, l);
		}
		b = false;
	}
	else
	{
		//checks if a is primitive (p.143 Mau94)
		b = checkPow(a, q2, q);
	}
	return b;
}

bool Functions::new_p(ZZ& p, ZZ& q1, ZZ q, long l)
{
	bool b;
	q1 = GenPrime_ZZ(l);
	p = 2 * q * q1 + 1;
	//cout<<" in new p: ";
	b = probPrime(p);
	return b;
}

bool Functions::new_p(ZZ& p, ZZ& q1, ZZ& q2, ZZ q, long l)
{
	bool b;
	long len;
	len = 0;
	while (len == 0 or len == 1 or len == l or len == l - 1)
	{
		len = RandomBnd(l);
	}
	//cout<<len<<" ";
	q1 = GenPrime_ZZ(len);
	q1 = GenPrime_ZZ(l - len);
	p = 2 * q * q1 * q2 + 1;
	//cout<<" in new p: ";
	b = probPrime(p);
	return b;
}

bool Functions::check_p(ZZ& a, ZZ& p, ZZ& q1, ZZ q, long l, long& j)
{
	bool b, bo;
	long i;

	b = true;
	//cout<<" in check";
	i = checkL1(a, p, q1);
	//If no a satisfies the condition, pick new prime q1
	if (i == 100)
	{
		bo = false;
		while (bo == false)
		{
			bo = new_p(p, q1, q, l);
		}
		b = false;
		j++;
	}
	else
	{ //Test if a is primitive, following Mau94 p.143
		b = checkPow(a, q, p);
	}
	return b;
}

bool Functions::check_p(ZZ& a, ZZ& p, ZZ& q1, ZZ& q2, ZZ q, long l, long& j)
{
	bool b, bo;
	long i;

	b = true;

	i = checkL1(a, p, q1, q2);
	//If no a satisfies the condition, pick new prime q1 und q2
	if (i == 100)
	{
		bo = false;
		while (bo == false)
		{
			bo = new_p(p, q1, q2, q, l);
		}
		b = false;
		j++;
	}
	else
	{ //Test if a is primitive, following Mau94 p.143
		b = checkPow(a, q, p);
	}
	return b;
}

//help functions to delete matrices
void Functions::delete_vector(vector<vector<ZZ>*>* v)
{
	long i;
	long l = v->size();

	for (i = 0; i < l; i++)
	{
		delete v->at(i);
		v->at(i) = 0;
	}
	delete v;
}

void Functions::delete_vector(vector<vector<long>*>* v)
{
	long i;
	long l = v->size();

	for (i = 0; i < l; i++)
	{
		delete v->at(i);
		v->at(i) = 0;
	}
	delete v;
}
void Functions::delete_vector(vector<vector<Cipher_elg>*>* v)
{
	long i;
	long l = v->size();

	for (i = 0; i < l; i++)
	{
		delete v->at(i);
		v->at(i) = 0;
	}
	delete v;
}

void Functions::delete_vector(vector<vector<vector<long>*>*>* v)
{
	long i;
	long l = v->size();

	for (i = 0; i < l; i++)
	{
		delete_vector(v->at(i));
	}
	delete v;
}

void Functions::delete_vector(vector<vector<vector<ZZ>*>*>* v)
{
	long i;
	long l = v->size();

	for (i = 0; i < l; i++)
	{
		delete_vector(v->at(i));
	}
	delete v;
}

// help functions, which pick random values and commit to a vector/matrix
//picks random value r and commits to the vector a,
void Functions::commit(vector<ZZ>* a, ZZ& r, Mod_p& com)
{
	ZZ ord = H.get_ord();

	r = RandomBnd(ord);
	com = Ped.commit(a, r);
	/*string name = "example.txt";
	ofstream ost;
	ost.open(name.c_str(),ios::app);
	ost<<r<<" "<<com<<endl;*/
}

//picks random values r and commits to the rows of the matrix a, a,r,com are variables of Prover
void Functions::commit(vector<vector<ZZ>*>* a_in, vector<ZZ>* r, vector<Mod_p>* com)
{
	long i, l;
	ZZ ord = H.get_ord();

	l = a_in->size();

	/*	string name = "example.txt";
	ofstream ost;
	ost.open(name.c_str(),ios::app);*/
	for (i = 0; i < l; i++)
	{
		r->at(i) = RandomBnd(ord);
		//		ost<<r->at(i)<<" ";
	}
	//	ost<<endl;
	for (i = 0; i < l; i++)
	{
		com->at(i) = Ped.commit(a_in->at(i), r->at(i));
		//	ost<<com->at(i)<<" ";
	}
	//	ost<<endl;
}

//picks random value r and commits to the vector a,
void Functions::commit_op(vector<ZZ>* a, ZZ& r, Mod_p& com)
{
	ZZ ord = H.get_ord();

	r = RandomBnd(ord);
	com = Ped.commit_opt(a, r);
}

//picks random values r and commits to the rows of the matrix a, a,r,com are variables of Prover
void Functions::commit_op(vector<vector<ZZ>*>* a_in, vector<ZZ>* r, vector<Mod_p>* com)
{
	long i, l;
	ZZ ord = H.get_ord();

	l = a_in->size();

	for (i = 0; i < l; i++)
	{
		r->at(i) = RandomBnd(ord);
	}
	for (i = 0; i < l; i++)
	{
		com->at(i) = Ped.commit_opt(a_in->at(i), r->at(i));
	}
}
