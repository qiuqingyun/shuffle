#include "ElGammal.h"
#include "G_q.h"

#include <NTL/ZZ.h>
NTL_CLIENT

#include "Mod_p.h"
#include <stdio.h>
#include <time.h>
#include <vector>
#include <fstream>


ElGammal::ElGammal() {
	// TODO Auto-generated constructor stub

}

//Creates ElGammal with secret key s, public key p and group H
ElGammal::ElGammal(long s, Mod_p p, G_q H) {
	G = H;
	sk = to_ZZ(s);
	pk = p;

}

//Creates ElGammal with secret key s, public key p and group H
ElGammal::ElGammal(ZZ s, Mod_p p, G_q H) {
	G = H;
	sk = s;
	pk = p;

}

//Creates ElGammal with secret key s and group H, the public key is pk = gen^s , gen generator of H
ElGammal::ElGammal(long s, G_q H) {
	Mod_p temp;
	G = H;
	sk = to_ZZ(s);
	temp = Mod_p(G.get_gen().get_val(), G.get_mod());
	pk = temp.expo(s);
}

//Creates ElGammal with secret key s and group H, the public key is pk = gen^s , gen generator of H
ElGammal::ElGammal(ZZ s, G_q H) {
	Mod_p temp;
	G = H;
	sk = s;
	temp = Mod_p(G.get_gen().get_val(), G.get_mod());
	pk = temp.expo(s);
}

//Set the group to G_q with order o, G_q subset of G_mod_p and generator gen, secret key is s and pk = gen^s
ElGammal::ElGammal(Mod_p gen, long o, long  mod, long s) {

	G = G_q(gen, o, mod);
	sk = to_ZZ(s);
	Mod_p temp;
	temp = Mod_p(gen.get_val(), mod);
	pk = temp.expo(s);
}

//Set the group to G_q with order o, G_q subset of G_mod_p and generator gen, secret key is s and pk = gen^s
ElGammal::ElGammal(Mod_p gen, long o, ZZ  mod, long s) {

	G = G_q(gen, o, mod);
	sk = to_ZZ(s);
	Mod_p temp;
	temp = Mod_p(gen.get_val(), mod);
	pk = temp.expo(s);
}

//Set the group to G_q with order o, G_q subset of G_mod_p and generator gen, secret key is s and pk = gen^s
ElGammal::ElGammal(Mod_p gen, long o, ZZ  mod, ZZ s) {

	G = G_q(gen, o, mod);
	sk = s;
	Mod_p temp;
	temp = Mod_p(gen.get_val(), mod);
	pk = temp.expo(s);
}

//Set the group to G_q with order o, G_q subset of G_mod_p and generator gen, secret key is s and pk = gen^s
ElGammal::ElGammal(Mod_p gen, ZZ o, ZZ  mod, long s) {

	G = G_q(gen, o, mod);
	sk = to_ZZ(s);
	Mod_p temp;
	temp = Mod_p(gen.get_val(), mod);
	pk = temp.expo(s);
}

//Set the group to G_q with order o, G_q subset of G_mod_p and generator gen, secret key is s and pk = gen^s
ElGammal::ElGammal(Mod_p gen, ZZ o, ZZ  mod, ZZ s) {

	G = G_q(gen, o, mod);
	sk = s;
	Mod_p temp;
	temp = Mod_p(gen.get_val(), mod);
	pk = temp.expo(s);
}

//Set the group to G_q with order o, G_q subset of G_mod_p and generator gen, secret key is s and public key p
ElGammal::ElGammal(Mod_p gen, long o, long  mod, long s, Mod_p p) {

	G = G_q(gen, o, mod);
	sk = to_ZZ(s);
	pk = p;
}

//Set the group to G_q with order o, G_q subset of G_mod_p and generator gen, secret key is s and public key p
ElGammal::ElGammal(Mod_p gen, long o, ZZ  mod, long s, Mod_p p) {

	G = G_q(gen, o, mod);
	sk = to_ZZ(s);
	pk = p;
}

//Set the group to G_q with order o, G_q subset of G_mod_p and generator gen, secret key is s and public key p
ElGammal::ElGammal(Mod_p gen, long o, ZZ  mod, ZZ s, Mod_p p) {

	G = G_q(gen, o, mod);
	sk = s;
	pk = p;
}

//Set the group to G_q with order o, G_q subset of G_mod_p and generator gen, secret key is s and public key p
ElGammal::ElGammal(Mod_p gen, ZZ o, ZZ  mod, long s, Mod_p p) {

	G = G_q(gen, o, mod);
	sk = to_ZZ(s);
	pk = p;
}

//Set the group to G_q with order o, G_q subset of G_mod_p and generator gen, secret key is s and public key p
ElGammal::ElGammal(Mod_p gen, ZZ o, ZZ  mod, ZZ s, Mod_p p) {

	G = G_q(gen, o, mod);
	sk = s;
	pk = p;
}

//Set the group to G_q with order o, G_q subset of G_mod_p and generator gen, secret key is s and public key p
ElGammal::ElGammal(long o, long  mod, long s, Mod_p p) {

	G = G_q(o, mod);
	sk = to_ZZ(s);
	pk = p;
}

//Set the group to G_q with order o and modular value mod, secret key is s and public key p
ElGammal::ElGammal(long o, ZZ  mod, long s, Mod_p p) {

	G = G_q(o, mod);
	sk = to_ZZ(s);
	pk = p;
}

//Set the group to G_q with order o and modular value mod, secret key is s and public key p
ElGammal::ElGammal(long o, ZZ  mod, ZZ s, Mod_p p) {

	G = G_q(o, mod);
	sk = s;
	pk = p;
}

//Set the group to G_q with order o and modular value mod, secret key is s and public key p
ElGammal::ElGammal(ZZ o, ZZ  mod, long s, Mod_p p) {

	G = G_q(o, mod);
	sk = to_ZZ(s);
	pk = p;
}

//Set the group to G_q with order o and modular value mod, secret key is s and public key p
ElGammal::ElGammal(ZZ o, ZZ  mod, ZZ s, Mod_p p) {

	G = G_q(o, mod);
	sk = to_ZZ(s);
	pk = p;
}

//Set the group to G_q with order o and modular value mod, secret key is s and public key pk = gen^s
ElGammal::ElGammal(long o, long  mod, long s) {

	G = G_q(o, mod);
	sk = to_ZZ(s);
	Mod_p temp;
	temp = Mod_p(G.get_gen().get_val(), mod);
	pk = temp.expo(s);
}

//Set the group to G_q with order o and modular value mod, secret key is s and public key pk = gen^s
ElGammal::ElGammal(long o, ZZ  mod, long s) {

	G = G_q(o, mod);
	sk = to_ZZ(s);
	Mod_p temp;
	temp = Mod_p(G.get_gen().get_val(), mod);
	pk = temp.expo(s);
}

//Set the group to G_q with order o and modular value mod, secret key is s and public key pk = gen^s
ElGammal::ElGammal(long o, ZZ  mod, ZZ s) {

	G = G_q(o, mod);
	sk = s;
	Mod_p temp;
	temp = Mod_p(G.get_gen().get_val(), mod);
	pk = temp.expo(s);
}

//Set the group to G_q with order o and modular value mod, secret key is s and public key pk = gen^s
ElGammal::ElGammal(ZZ o, ZZ  mod, long s) {

	G = G_q(o, mod);
	sk = to_ZZ(s);
	Mod_p temp;
	temp = Mod_p(G.get_gen().get_val(), mod);
	pk = temp.expo(s);
}

//Set the group to G_q with order o and modular value mod, secret key is s and public key pk = gen^s
ElGammal::ElGammal(ZZ o, ZZ  mod, ZZ s) {

	G = G_q(o, mod);
	sk = s;
	Mod_p temp;
	temp = Mod_p(G.get_gen().get_val(), mod);
	pk = temp.expo(s);
}


ElGammal::~ElGammal() {
	// TODO Auto-generated destructor stub
}

//Access to the parameters
G_q ElGammal::get_group()const {
	return G;
}

Mod_p ElGammal::get_pk() const {

	return pk;
}

ZZ ElGammal::get_sk()const {

	return sk;
}

//functions to change parameters
void ElGammal::set_group(G_q H) {

	G = H;
}

void ElGammal::set_sk(long s) {

	sk = to_ZZ(s);
	pk = G.get_gen().expo(s);
}

void ElGammal::set_sk(ZZ s) {

	sk = s;//????x
	pk = G.get_gen().expo(s);//??????????y=g^x
	string name = "ElGammal.txt";
	ofstream ost;
	ost.open(name.c_str(), ios::app);
	ost << sk << "\n" << pk << endl;//??????????
	ost.close();
}
void ElGammal::keyGen() {
	ZZ sk1 = RandomBnd(this->G.get_ord());
	ZZ sk2 = RandomBnd(this->G.get_ord());
	sk = AddMod(sk1, sk2, this->G.get_mod());
	pk = G.get_gen().expo(sk);//??????????y=g^x
	string name = "ElGammal.txt";
	ofstream ost;
	ost.open(name.c_str(), ios::out);
	ost << pk << "\n" << sk1 << "\n" << sk2 << endl;//??????????
	ost.close();
}
void ElGammal::set_key(ZZ s, ZZ p) {
	sk = s;//????
	pk = Mod_p(G.get_mod());
	pk.set_val(p);//????
}

//functions to encrypt value/element
Cipher_elg ElGammal::encrypt(Mod_p el) {
	Cipher_elg c;
	Mod_p temp_1, temp_2;
	ZZ ran;
	SetSeed(to_ZZ((unsigned int)time(0)));
	ran = RandomBnd(G.get_ord());
	temp_1 = G.get_gen().expo(ran);
	temp_2 = pk.expo(ran) * el;
	c = Cipher_elg(temp_1, temp_2);
	return c;

}

Cipher_elg ElGammal::encrypt(ZZ m) {
	Cipher_elg c;
	Mod_p temp_1, temp_2;
	ZZ ran;
	SetSeed(to_ZZ((unsigned int)time(0)));
	ran = RandomBnd(G.get_ord());
	cout << ran << endl;
	temp_1 = G.get_gen().expo(ran);
	temp_2 = pk.expo(ran) * Mod_p(m, G.get_mod());
	c = Cipher_elg(temp_1, temp_2);
	return c;
}

Cipher_elg ElGammal::encrypt(long m) {
	Cipher_elg c;
	Mod_p temp_1, temp_2;
	ZZ ran;
	SetSeed(to_ZZ((unsigned int)time(0)));
	ran = RandomBnd(G.get_ord());
	temp_1 = G.get_gen().expo(ran);
	temp_2 = pk.expo(ran) * Mod_p(m, G.get_mod());
	c = Cipher_elg(temp_1, temp_2);
	return c;
}

Cipher_elg ElGammal::encrypt(Mod_p el, long ran) {
	Cipher_elg c;
	Mod_p temp_1, temp_2;
	temp_1 = G.get_gen().expo(ran);
	temp_2 = pk.expo(ran) * el;
	c = Cipher_elg(temp_1, temp_2);
	return c;
}

//TODO:????????????
Cipher_elg ElGammal::encrypt(Mod_p el, ZZ ran) {
	Cipher_elg c;
	Mod_p temp_1, temp_2;
	temp_1 = G.get_gen().expo(ran);//h^r
	temp_2 = pk.expo(ran) * el;//m??y^r
	// temp_2 = pk.expo(ran)*el;//g^m??y^r
	c = Cipher_elg(temp_1, temp_2);//????(u,v)????????u = h^r??v = m??y^r
	return c;
}

//TODO:????????????
Cipher_elg ElGammal::encrypt(long m, ZZ ran) {
	Cipher_elg c;
	Mod_p temp_1, temp_2;
	temp_1 = G.get_gen().expo(ran);//h^r
	temp_2 = pk.expo(ran) * Mod_p(m, G.get_mod());//m??y^r
	c = Cipher_elg(temp_1, temp_2);
	return c;
}


Cipher_elg ElGammal::encrypt(ZZ m, long ran) {
	Cipher_elg c;
	Mod_p temp_1, temp_2;
	temp_1 = G.get_gen().expo(ran);
	temp_2 = pk.expo(ran) * Mod_p(m, G.get_mod());
	c = Cipher_elg(temp_1, temp_2);
	return c;
}

Cipher_elg ElGammal::encrypt(ZZ m, ZZ ran) {
	Cipher_elg c;
	Mod_p temp_1, temp_2;
	temp_1 = G.get_gen().expo(ran);
	temp_2 = pk.expo(ran) * Mod_p(m, G.get_mod());
	c = Cipher_elg(temp_1, temp_2);
	return c;
}

Cipher_elg ElGammal::encrypt(long m, long ran) {
	Cipher_elg c;
	Mod_p temp_1, temp_2;
	temp_1 = G.get_gen().expo(ran);
	temp_2 = pk.expo(ran) * Mod_p(m, G.get_mod());
	c = Cipher_elg(temp_1, temp_2);
	return c;
}

//Decrypts the ciphertext c
Mod_p ElGammal::decrypt(Cipher_elg c) {
	if (sk == 0)
		cout << "can not decrypt, need secret key" << endl;
	ZZ temp;
	Mod_p ans;
	ZZ mod = G.get_mod();
	temp = InvMod(c.get_u(), mod);
	temp = PowerMod(temp, sk, mod);
	temp = MulMod(temp, c.get_v(), mod);
	return temp;
}
ZZ ElGammal::decrypt(Cipher_elg c, int flag) {
	if (sk == 0)
		cout << "can not decrypt, need secret key" << endl;
	ZZ temp;
	ZZ mod = G.get_mod();
	temp = InvMod(c.get_u(), mod);
	temp = PowerMod(temp, sk, mod);
	temp = MulMod(temp, c.get_v(), mod);
	// cout<<temp<<" "<<flush;
	return temp;
}

//Assigment operator
void ElGammal::operator=(const ElGammal& el) {

	G = el.get_group();
	sk = el.get_sk();
	pk = el.get_pk();
}

