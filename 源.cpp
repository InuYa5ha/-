#include<iostream>
#include<string>
#include<ctime>
#include"picosha2.h"
#include<json.h>
#include<fstream>
#include<random>
#include"RSA.h"
#include"ripemd160.h"
using namespace std;
typedef string str;

static const char* pszBase58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
std::string EncodeBase58(const unsigned char* pbegin, const unsigned char* pend)
{
	int zeroes = 0;
	int length = 0;
	while (pbegin != pend && *pbegin == 0) {
		pbegin++;
		zeroes++;
	}
	int size = (pend - pbegin) * 138 / 100 + 1; 
	std::vector<unsigned char> b58(size);
	while (pbegin != pend) {
		int carry = *pbegin;
		int i = 0;
		for (std::vector<unsigned char>::reverse_iterator it = b58.rbegin(); (carry != 0 || i < length) && (it != b58.rend()); it++, i++) {
			carry += 256 * (*it);
			*it = carry % 58;
			carry /= 58;
		}

		assert(carry == 0);
		length = i;
		pbegin++;
	}
	std::vector<unsigned char>::iterator it = b58.begin() + (size - length);
	while (it != b58.end() && *it == 0)
		it++;
	std::string str;
	str.reserve(zeroes + (b58.end() - it));
	str.assign(zeroes, '1');
	while (it != b58.end())
		str += pszBase58[*(it++)];
	return str;
}
bool DecodeBase58(const char* psz, std::vector<unsigned char>& vch)
{
	while (*psz && isspace(*psz))
		psz++;
	int zeroes = 0;
	int length = 0;
	while (*psz == '1') {
		zeroes++;
		psz++;
	}
	int size = strlen(psz) * 733 / 1000 + 1;
	std::vector<unsigned char> b256(size);
	while (*psz && !isspace(*psz)) {
		const char* ch = strchr(pszBase58, *psz);
		if (ch == nullptr)
			return false;
		int carry = ch - pszBase58;
		int i = 0;
		for (std::vector<unsigned char>::reverse_iterator it = b256.rbegin(); (carry != 0 || i < length) && (it != b256.rend()); ++it, ++i) {
			carry += 58 * (*it);
			*it = carry % 256;
			carry /= 256;
		}
		assert(carry == 0);
		length = i;
		psz++;
	}
	while (isspace(*psz))
		psz++;
	if (*psz != 0)
		return false;
	std::vector<unsigned char>::iterator it = b256.begin() + (size - length);
	while (it != b256.end() && *it == 0)
		it++;
	vch.reserve(zeroes + (b256.end() - it));
	vch.assign(zeroes, 0x00);
	while (it != b256.end())
		vch.push_back(*(it++));
	return true;
}
std::string EncodeBase58(const std::vector<unsigned char>& vch)
{
	return EncodeBase58(vch.data(), vch.data() + vch.size());
}
bool DecodeBase58(const std::string& str, std::vector<unsigned char>& vchRet)
{
	return DecodeBase58(str.c_str(), vchRet);
}
int hex2int(unsigned char x) {
	if (x >= '0' && x <= '9') {
		return (x - '0');
	}
	if (x >= 'A' && x <= 'F') {
		return (x - 'A' + 10);
	}
	if (x >= 'a' && x <= 'f') {
		return (x - 'a' + 10);
	}
}
unsigned __int64 MulMod(unsigned __int64 a, unsigned __int64 b, unsigned __int64 n){
	return a * b % n;
}
unsigned __int64 PowMod(unsigned __int64& base, unsigned __int64& pow, unsigned __int64& n){
	unsigned __int64    a = base, b = pow, c = 1;
	while (b){
		while (!(b & 1)){
			b >>= 1;
			a = MulMod(a, a, n);
		}        b--;
		c = MulMod(a, c, n);
	}    return c;
}
string Encrypt(string plaintext, unsigned __int64 m, unsigned __int64 n) {
	unsigned __int64 num;
	unsigned __int64 N;
	char cnum[7];
	string s;
	str ciphertext;
	for (int i = 0; i < plaintext.size(); i += 2){
		num = plaintext[i] * 1000 + plaintext[i + 1];
		N = PowMod(num, m, n);
		sprintf_s(cnum, "%d", N);
		s = cnum;
		while (s.size() < 6){
			s = "0" + s;
		}
		ciphertext += s;
	}
	return ciphertext;
}
double stringToDouble(string num){
	bool minus = false;
	string real = num; 
	if (num.at(0) == '-'){
		minus = true;
		real = num.substr(1, num.size() - 1);
	}
	char c;
	int i = 0;
	double result = 0.0, dec = 10.0;
	bool isDec = false;
	unsigned long size = real.size();
	while (i < size){
		c = real.at(i);
		if (c == '.'){
			isDec = true;
			i++;
			continue;
		}
		if (!isDec){
			result = result * 10 + c - '0';
		}
		else{
			result = result + (c - '0') / dec;
			dec *= 10;
		}
		i++;
	}
	if (minus == true) {
		result = -result;
	}
	return result;
}

#define RMDsize 160

byte* RMD(byte* message){
	dword         MDbuf[RMDsize / 32];
	static byte   hashcode[RMDsize / 8];
	dword         X[16];
	unsigned int  i;
	dword         length;
	dword         nbytes;

	MDinit(MDbuf);
	length = (dword)strlen((char*)message);

	for (nbytes = length; nbytes > 63; nbytes -= 64) {
		for (i = 0; i < 16; i++) {
			X[i] = BYTES_TO_DWORD(message);
			message += 4;
		}
		compress(MDbuf, X);
	}

	MDfinish(MDbuf, message, length, 0);

	for (i = 0; i < RMDsize / 8; i += 4) {
		hashcode[i] = MDbuf[i >> 2];
		hashcode[i + 1] = (MDbuf[i >> 2] >> 8);
		hashcode[i + 2] = (MDbuf[i >> 2] >> 16);
		hashcode[i + 3] = (MDbuf[i >> 2] >> 24);
	}

	return (byte*)hashcode;
}

str RIPEMD160(str hash) {
	char* data;
	int len = hash.length();
	data = (char*)malloc((len + 1) * sizeof(char));
	hash.copy(data, len, 0);
	byte* b = (byte*)data;
	byte* hashcode = RMD(b);
	char ret[41] = {};
	for (int j = 0; j < RMDsize / 8; j++) {
		char c[5];
		sprintf_s(c, "%02x", hashcode[j]);
		strcat_s(ret, c);
	}
	return ret;
}

str SHA256(str password) {
	str hash_hex_str;
	str new_hash = password;
	vector<unsigned char> hash(picosha2::k_digest_size);
	picosha2::hash256(new_hash.begin(), new_hash.end(), hash.begin(), hash.end());
	hash_hex_str = picosha2::bytes_to_hex_string(hash.begin(), hash.end());
	return hash_hex_str;
}

str BASE58(str hash) {
	unsigned char hexstr[30];
	memcpy(hexstr, &hash[0], 30);
	unsigned char udat[sizeof(hexstr) / 2];
	for (int i = 0; i < sizeof(hexstr); i += 2) {
		udat[i / 2] = hex2int(hexstr[i]) * 16 + hex2int(hexstr[i + 1]);
	}
	vector<unsigned char>vdat(udat, udat + sizeof(udat));
	str encode;
	encode = EncodeBase58(vdat);
	return encode;
}

double value() {
	default_random_engine e(time(0));
	uniform_real_distribution<double> u(0.00001, 0.5);
	return u(e);
}

typedef struct Datetime {
	str date;
	str time;
}datetime;

typedef struct Transaction {
	str ID;
	str Vin;
	str Vout;
}tra;

typedef struct key {
	str n;
	str m;
}key;

typedef struct Input {
	str Wallet;
	str txid;
	int vout;
	str signature;
	key pubkey;
}input;

typedef struct Output {
	str Wallet;
	double value;
	key pubkey;
}output;

typedef struct BLOCKS {
	str datetime;
	tra Transactions;
	str PrevBlockHash;
	str Hash;
	int Nonce;
	int Height;
}BLOCKS;

class Block {
public:
	datetime Timestamp;
	str datetime;
	tra Transactions;
	str PrevBlockHash;
	str Hash;
	int Nonce;
	int Height;
	BLOCKS block;

	void init();
	void new_block(tra Transactions, str prev_hash, int height);
	str set_hash();
	int nonce();
	void post(str name);
};

class BlockChain {
public:
	BLOCKS block[50];
	str current_hash;
	int height;

	void init();
	void add_block(BLOCKS block);
	void get_block(str block_hash);
	void save_blockchain();
	//void read_blockchain();   //不知道读出来的格式怎么输出
	void post(str name);
};

class Wallet {
public:
	key public_key;
	key private_key;
	str address;
	double balance;

	void new_address(str password);
	void load_from_file(str name);
	void save_to_file(str name);
	void update_to_file(str name);
};

class transaction {
public:
	str Hash;
	input vin;
	output vout;
	void init();
	int verify(str vinwallet);
	void sign(str message, key priv_key, key pub_key);
	void hash(str txid, str vinwallet, str voutwallet);
};



void Block::init() {
	Timestamp.date = "00000000";
	Timestamp.time = "00000000";
	datetime = "0000000000000000";
	Transactions.ID = "";
	Transactions.Vin = "";
	Transactions.Vout = "";
	PrevBlockHash = "0000000000000000000000000000000000000000000000000000000000000000";
	Hash = "0000000000000000000000000000000000000000000000000000000000000000";
	Nonce = NULL;
}

void BlockChain::init() {
	current_hash = "0000000000000000000000000000000000000000000000000000000000000000";
	height = 0;
}

void Block::new_block(tra Transactions, str prev_hash, int height) {
	block.Transactions.ID = Transactions.ID;
	block.Transactions.Vin = Transactions.Vin;
	block.Transactions.Vout = Transactions.Vout;
	block.PrevBlockHash = prev_hash;
	block.Hash = set_hash();
	block.Nonce = nonce();
	block.Height = height;
	block.datetime = datetime;
}

int Block::nonce() {
	return rand();
}

str Block::set_hash() {
	time_t nowtime;
	struct tm p;
	time(&nowtime);
	localtime_s(&p, &nowtime);
	str year, mon, mday, hour, min, sec;
	p.tm_year = p.tm_year + 1900;
	p.tm_mon = p.tm_mon + 1;
	year = to_string(p.tm_year);
	mon = to_string(p.tm_mon);
	mday = to_string(p.tm_mday);
	hour = to_string(p.tm_hour);
	min = to_string(p.tm_min);
	sec = to_string(p.tm_sec);
	Timestamp.date = year + mon + mday;
	Timestamp.time = hour + min + sec;
	datetime = Timestamp.date + Timestamp.time;
	str hash_hex_str;
	str new_hash = PrevBlockHash + datetime;
	vector<unsigned char> hash(picosha2::k_digest_size);
	picosha2::hash256(new_hash.begin(), new_hash.end(), hash.begin(), hash.end());
	hash_hex_str = picosha2::bytes_to_hex_string(hash.begin(), hash.end());
	return hash_hex_str;
}

void BlockChain::add_block(BLOCKS block1) {
	block[height].datetime = block1.datetime;
	block[height].Hash = block1.Hash;
	block[height].Height = block1.Height;
	block[height].Nonce = block1.Nonce;
	block[height].PrevBlockHash = block1.PrevBlockHash;
	block[height].Transactions.ID = block1.Transactions.ID;
	block[height].Transactions.Vin = block1.Transactions.Vin;
	block[height].Transactions.Vout = block1.Transactions.Vout;
	height++;
	current_hash = block1.Hash;
}

void BlockChain::save_blockchain() {
	Json::Value Transactions1;
	Transactions1["ID"] = Json::Value(block[height - 1].Transactions.ID);
	Transactions1["Vin"] = Json::Value(block[height - 1].Transactions.Vin);
	Transactions1["Vout"] = Json::Value(block[height - 1].Transactions.Vout);

	Json::Value block1;
	block1["Timestamp"] =Json::Value(block[height - 1].datetime);
	block1["Transactions"] = Json::Value(Transactions1);
	block1["PrevBlockHash"] = Json::Value(block[height - 1].PrevBlockHash);
	block1["Hash"] = Json::Value(block[height - 1].Hash);
	block1["Nonce"] = Json::Value(block[height - 1].Nonce);
	block1["Height"] = Json::Value(block[height - 1].Height);

	Json::Value block;
	block["block"] = Json::Value(block1);

	Json::Value blockchain;
	blockchain["block"].append(block1);

	Json::StyledWriter sw;
	cout << sw.write(blockchain) << endl;

	ofstream os;
	os.open("demo.json", std::ios::out | std::ios::app);
	if (!os.is_open())
		cout << "error: can not find or create the file which named \"demo.json\"." << endl;
	os << sw.write(blockchain);
	os.close();
}

string strRand(int length) {		
	char tmp;							
	string buffer;					
	random_device rd;				
	default_random_engine random(rd());

	for (int i = 0; i < length; i++) {
		tmp = random() % 36;
		if (tmp < 10) {		
			tmp += '0';
		}
		else {		
			tmp -= 10;
			tmp += 'A';
		}
		buffer += tmp;
	}
	return buffer;
}

void BlockChain::get_block(str block_hash) {
	for(int i = 0; i < height; i++) {
		if (block[i].Hash == block_hash) {
			Json::Value Transactions1;
			Transactions1["ID"] = Json::Value(block[i].Transactions.ID);
			Transactions1["Vin"] = Json::Value(block[i].Transactions.Vin);
			Transactions1["Vout"] = Json::Value(block[i].Transactions.Vout);

			Json::Value block1;
			block1["Timestamp"] = Json::Value(block[i].datetime);
			block1["Transactions"] = Json::Value(Transactions1);
			block1["PrevBlockHash"] = Json::Value(block[i].PrevBlockHash);
			block1["Hash"] = Json::Value(block[i].Hash);
			block1["Nonce"] = Json::Value(block[i].Nonce);
			block1["Height"] = Json::Value(block[i].Height);

			Json::Value block;
			block["block"] = Json::Value(block1);

			Json::Value blockchain;
			blockchain["block"].append(block1);

			Json::StyledWriter sw;
			cout << sw.write(blockchain) << endl;
		}
	}
}

void BlockChain::post(str name) {
	Json::Value Transactions1;
	Transactions1["ID"] = Json::Value(block[height - 1].Transactions.ID);
	Transactions1["Vin"] = Json::Value(block[height - 1].Transactions.Vin);
	Transactions1["Vout"] = Json::Value(block[height - 1].Transactions.Vout);

	Json::Value block1;
	block1["Timestamp"] = Json::Value(block[height - 1].datetime);
	block1["Transactions"] = Json::Value(Transactions1);
	block1["PrevBlockHash"] = Json::Value(block[height - 1].PrevBlockHash);
	block1["Hash"] = Json::Value(block[height - 1].Hash);
	block1["Nonce"] = Json::Value(block[height - 1].Nonce);
	block1["Height"] = Json::Value(block[height - 1].Height);

	Json::Value block;
	block["block"] = Json::Value(block1);

	Json::Value blockchain;
	blockchain["block"].append(block1);

	Json::StyledWriter sw;
	cout << sw.write(blockchain) << endl;

	ofstream os;
	str name1 = name + ".json";
	os.open(name1, std::ios::out | std::ios::app);
	if (!os.is_open())
		cout << "error: can not find or create the file which named \"demo.json\"." << endl;
	os << sw.write(blockchain);
	os.close();
}

void Wallet::new_address(str password) {
	RSA r(1, 1);
	r.generateKey();
	private_key.n = to_string(r.n);
	private_key.m = to_string(r.b);
	public_key.n = to_string(r.n);
	public_key.m = to_string(r.a);
	address = "00" + RIPEMD160(SHA256(public_key.n + public_key.m));
	address = BASE58(address + SHA256(SHA256(address)).substr(0, 8));
}

void Wallet::save_to_file(str name) {
	Json::Value Wallet1;
	Wallet1["private_key"] = Json::Value(private_key.n + "," + private_key.m);
	Wallet1["public_key"] = Json::Value(public_key.n + "," + public_key.m);
	Wallet1["address"] = Json::Value(address);
	Wallet1["balance"] = Json::Value(balance);

	/*Json::Value account;
	account["Wallet"].append(Wallet1);*/

	Json::StyledWriter sw;
	cout << sw.write(Wallet1) << endl;

	ofstream os;
	str name1 = name + ".json";
	os.open(name1, std::ios::out | std::ios::app);
	if (!os.is_open())
		cout << "error: can not find or create the file which named " + name1 << endl;
	os << sw.write(Wallet1);
	os.close();
}

void Wallet::update_to_file(str name) {
	Json::Value Wallet1;
	Wallet1["private_key"] = Json::Value(private_key.n + "," + private_key.m);
	Wallet1["public_key"] = Json::Value(public_key.n + "," + public_key.m);
	Wallet1["address"] = Json::Value(address);
	Wallet1["balance"] = Json::Value(balance);

	/*Json::Value account;
	account["Wallet"].append(Wallet1);*/

	Json::StyledWriter sw;
	cout << sw.write(Wallet1) << endl;

	ofstream os;
	str name1 = name + ".json";
	os.open(name1, std::ios::out | std::ios::in);
	if (!os.is_open())
		cout << "error: can not find or create the file which named " + name1 << endl;
	os << sw.write(Wallet1);
	os.close();
}

void Wallet::load_from_file(str name) {
	Json::Reader reader;
	Json::Value root;
	str name1 = name + ".json";
	ifstream in(name1, ios::binary);
	if (!in.is_open()) {
		cout << "Error opening file\n";
		return;
	}
	if (reader.parse(in, root)) {
		//const Json::Value arrayObj = root["Wallet"];
		str pri_key = root["private_key"].asString();
		str pub_key = root["public_key"].asString();
		str add = root["address"].asString();
		str bal = root["balance"].asString();
		int index = pri_key.find(",", 0);
		private_key.n = pri_key.substr(0, index);
		private_key.m = pri_key.substr(index + 1, pri_key.length());
		index = pub_key.find(",", 0);
		public_key.n = pub_key.substr(0, index);
		public_key.m = pub_key.substr(index + 1, pub_key.length());
		address = add;
		balance = stringToDouble(bal);
	}
}

void transaction::init() {
	Hash = "0000000000000000000000000000000000000000000000000000000000000000";
}

int transaction::verify(str vinwallet) {
	Wallet W;
	int i = 0;
	vout.value = value();
	W.load_from_file(vinwallet);
	if (W.address.length() == 0) {
		cout << "ERROR!" << endl;
		return i;
	}
	if (W.balance - vout.value < 0){
		cout << "No Enough Balance" << endl;
		return i;
	}
	return i + 1;
}

void transaction::sign(str message, key priv_key, key pub_key) {
	long long int n = atoi(priv_key.n.c_str());
	long long int m = atoi(priv_key.m.c_str());
	vin.signature = to_string(n) + "，" + Encrypt(message, m, n);
}

void transaction::hash(str txid, str vinwallet, str voutwallet) {
		Wallet W;
		W.load_from_file(vinwallet);
		vin.Wallet = vinwallet;
		vin.pubkey = W.public_key;
		/*if (vin.vout == 0) {
			vin.txid = SHA256(vin.Wallet);
		}*/
		W.load_from_file(voutwallet);
		vout.Wallet = voutwallet;
		vout.pubkey = W.public_key;
		str jsonstr = vin.Wallet + vin.txid + vin.signature + vin.pubkey.n + "," + vin.pubkey.m + vout.Wallet + to_string(vout.value) + vout.pubkey.n + "," + vout.pubkey.m;
		Hash = SHA256(jsonstr);
}

int main() {
	/*BlockChain BC;
	Block B;
	B.init();
	BC.init();
	char string1[10];
	BLOCKS genblock;
	B.new_block(B.Transactions, "", 0);
	genblock = B.block;
	BC.add_block(genblock);
	Json::Value Transactions1;
	Transactions1["ID"] = Json::Value(BC.block[0].Transactions.ID);
	Transactions1["Vin"] = Json::Value(BC.block[0].Transactions.Vin);
	Transactions1["Vout"] = Json::Value(BC.block[0].Transactions.Vout);

	Json::Value block1;
	block1["Timestamp"] = Json::Value(BC.block[0].datetime);
	block1["Transactions"] = Json::Value(Transactions1);
	block1["PrevBlockHash"] = Json::Value(BC.block[0].PrevBlockHash);
	block1["Hash"] = Json::Value(BC.block[0].Hash);
	block1["Nonce"] = Json::Value(BC.block[0].Nonce);
	block1["Height"] = Json::Value(BC.block[0].Height);

	Json::Value block;
	block["block"] = Json::Value(block1);

	Json::Value blockchain;
	blockchain["genblock"].append(block1);

	Json::StyledWriter sw;
	cout << sw.write(blockchain) << endl;

	ofstream os;
	os.open("demo.json", std::ios::out | std::ios::app);
	if (!os.is_open())
		cout << "error: can not find or create the file which named \"demo.json\"." << endl;
	os << sw.write(blockchain);
	os.close();

	for (int i = 0; i < 3; i++) {
		tra Transaction;
		Transaction.ID = strRand(3);
		_sleep(1 * 1000);
		Transaction.Vin = strRand(5);
		_sleep(1 * 1000);
		Transaction.Vout = strRand(5);
		str prev_hash = BC.current_hash;
		int height = BC.height;
		B.new_block(Transaction, prev_hash, height);
		BC.add_block(B.block);
		BC.save_blockchain();
		_sleep(1 * 1000);
	}
	cout << "current_hash:  " << BC.block[1].Hash << endl;
	BC.get_block(BC.block[1].Hash);*/
	str name[10];
	str txid[10];
	int vin_vout[10] = { 0 };
	Wallet W;
	srand(time(0));
	int n = 5;
	for (int i = 0; i < 5; i++) {
		name[i] = strRand(8);
		W.balance = 10;
		W.new_address(name[i]);
		W.save_to_file(name[i]);
		txid[i] = SHA256(name[i]);
		_sleep(1 * 1000);
	}
	transaction T;
	Block B;
	BlockChain BC;
	B.init();
	BC.init();
	for (int i = 0; i < 50; i++) {
		int vin = rand() % 5;
		vin_vout[vin]++;
		int vout = vin;
		while(vin == vout) {
			_sleep(1 * 1234);
			vout = rand() % 5;
		}
		if (T.verify(name[vin]) == 1) {
			W.load_from_file(name[vin]);
			str message = strRand(6);
			T.sign(message, W.private_key, W.public_key);
			if (vin_vout[vin] - 1 == 0)
				T.hash(txid[vin], name[vin], name[vout]);
			tra trans;
			trans.ID = W.address;
			trans.Vin = name[vin];
			trans.Vout = name[vout];
			str prev_hash = BC.current_hash;
			B.new_block(trans, prev_hash, i + 1);
			BC.add_block(B.block);
			int in = vin;
			while(1) {
				in = in + 1;
				in = in % 5;
				if (in == vin)
					break;
				BC.post(name[in]);
			}
 			BC.save_blockchain();
			W.load_from_file(name[vin]);
			W.balance = W.balance - T.vout.value;
			W.update_to_file(name[vin]);
			W.load_from_file(name[vout]);
			W.balance = W.balance + T.vout.value;
			W.update_to_file(name[vout]);
		}
	}
	return 0;
}