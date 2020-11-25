#ifndef RSA_H
#define RSA_H
#include <string>
#include <iostream>
#include <ctime>
using namespace std;
class RSA
{
public:
	string plaintext = "";
	string ciphertext = "";
	unsigned __int64 p;			//����p
	unsigned __int64 q;			//����q
	unsigned __int64 n;			//n=p*q
	unsigned __int64 b;			//a���ڦ�(n)��ģ��Ԫ��
	unsigned __int64 a = 65537;
	unsigned __int64 c;
	RSA(int nn, int ab) {
		n = nn;
		b = a = ab;
	}

	string Encrypt(string plaintext) {
		unsigned __int64 num;
		unsigned __int64 N;
		char cnum[7];
		string s;
		for (int i = 0; i < plaintext.size(); i += 2)
		{
			//��2��char��ASCII��ת����һ�𹹳�һ��6λ����
			num = plaintext[i] * 1000 + plaintext[i + 1];
			N = PowMod(num, a, n);
			sprintf_s(cnum, "%d", N);
			s = cnum;
			while (s.size() < 6)		//������6λ����ǰ�油0
			{
				s = "0" + s;
			}
			ciphertext += s;		//��6λ���ִ�������
		}
		return ciphertext;
	}

	string Decrypt(string ciphertext) {
		unsigned __int64 num;
		int aa;
		unsigned __int64 N;
		char cnum[7];
		string s = "";
		for (int i = 0; i < ciphertext.size(); i += 6)
		{
			//��������ÿ6λ�ó��������ܣ��õ�һ��6λ����ǰ3λΪһ��char����3λΪһ��char
			strcpy(cnum, ciphertext.substr(i, 6).c_str());
			sscanf(cnum, "%d", &aa);
			N = aa;
			num = PowMod(N, b, n);
			plaintext += char(num / 1000);
			plaintext += char(num % 1000);
		}
		return plaintext;
	}

	//����˽Կ�͹�Կ
	void generateKey() {
		//��Կ��(n,a)
		a = 65537;
		srand(time(0));
		p = prime[rand() % 90];
		q = prime[rand() % 90];
		n = p * q;
		b = mod_reverse(a, (p - 1) * (q - 1));
		//c = a^d mod n
		c = PowMod(a, b, n);

	}
	int pub() {
		return n;
	}
	int prikey() {
		return b;
	}
	int pubkey() {
		return a;
	}
	int sign() {
		return c;
	}

private:
	//��λ���� ��������ȡ
	int prime[90] = { 401, 409, 419, 421, 431, 433, 439,
		443, 449, 457, 461, 463, 467, 479, 487, 491, 499,
		503, 509, 521, 523, 541, 547, 557, 563, 569, 571,
		577, 587, 593, 599, 601, 607, 613, 617, 619, 631,
		641, 643, 647, 653, 659, 661, 673, 677, 683, 691,
		701, 709, 719, 727, 733, 739, 743, 751, 757, 761,
		769, 773, 787, 797, 809, 811, 821, 823, 827, 829,
		839, 853, 857, 859, 863, 877, 881, 883, 887, 907,
		911, 919, 929, 937, 941, 947, 953, 967, 971, 977,
		983, 991, 997 };

	//ģ�����㣬����ֵ x=a*b mod n
	inline unsigned __int64 MulMod(unsigned __int64 a, unsigned __int64 b, unsigned __int64 n)
	{
		return a * b % n;
	}
	//ģ�����㣬����ֵ x=base^pow mod n
	unsigned __int64 PowMod(unsigned __int64& base, unsigned __int64& pow, unsigned __int64& n)
	{
		unsigned __int64    a = base, b = pow, c = 1;
		while (b)
		{
			while (!(b & 1))
			{
				b >>= 1;            //a=a * a % n;    //�������������Դ���64λ������������������a*a��a>=2^32ʱ�Ѿ��������������ʵ�ʴ���Χû��64λ
				a = MulMod(a, a, n);
			}        b--;        //c=a * c % n;        //����Ҳ�����������64λ������Ϊ����32λ������֪�Ƿ���Խ��������⡣
			c = MulMod(a, c, n);
		}    return c;
	}
	//����d=gcd(a,b);�Ͷ�Ӧ�ڵ�ʽax+by=d�е�x,y
	long long extend_gcd(long long a, long long b, long long& x, long long& y) {
		if (a == 0 && b == 0) return -1;//�����Լ��
		if (b == 0) {
			x = 1; y = 0; return a;
		}
		long long d = extend_gcd(b, a % b, y, x);
		y -= a / b * x;
		return d;
	}
	//lx = 1(mod n) ��X
	long long mod_reverse(long long a, long long n) {
		long long x, y;
		long long d = extend_gcd(a, n, x, y);
		if (d == 1)
			return (x % n + n) % n;
		else return -1;
	}
};
#endif