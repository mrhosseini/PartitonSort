#include <vector>
#include <iostream>
#include <vector>
#include <algorithm>
#include <set>
#include <string>
#include <fstream>
#include <sstream>
#include <iterator>
#include <functional>
#include "InputReader.h"
#include <regex>

using namespace std;

int InputReader::dim = 5;
int InputReader::reps = 1;

int_t inline InputReader::atoui(const string& in) {
	std::istringstream reader(in);
    int_t val;
	reader >> val;
	return val;
}
//CREDITS: http://stackoverflow.com/questions/236129/split-a-string-in-c
std::vector<std::string> & InputReader::split(const std::string &s, char delim, std::vector<std::string> &elems) {
	std::stringstream ss(s);
	std::string item;
	while (std::getline(ss, item, delim)) {
		elems.push_back(item);
	}
	return elems;
}

std::vector<std::string> InputReader::split(const std::string &s, char delim) {
	std::vector<std::string> elems;
	split(s, delim, elems);
	return elems;
}

std::vector<std::vector<int_t> > InputReader::ReadPackets(const string& filename) {
    vector<vector<int_t>> packets;
	ifstream input_file(filename);
	if (!input_file.is_open())
	{
		printf("Couldnt open packet set file \n");
		exit(1);
	} else {
		printf("Reading packet file %s\n", filename.c_str());
	}
	int line_number = 1;
	string content;
	while (getline(input_file, content)) {
		istringstream iss(content);
		vector<string> tokens{ istream_iterator < string > {iss}, istream_iterator < string > {} };
        vector<int_t> one_packet;
		for (int i = 0; i < dim; i++) {
			one_packet.push_back(atoui(tokens[i]));
		}
		packets.push_back(one_packet);
		line_number++;

	}
	return packets;
}

void InputReader::ReadIPRange(std::array<int_t,2>& IPrange,  unsigned int& prefix_length, const string& token)
{
	//cout << token << endl;
	//split slash
	vector<string> split_slash = split(token, '/');
	vector<string> split_ip = split(split_slash[0], '.');
	/*asindmemacces IPv4 prefixes*/
	/*temporary variables to store IP range */
	unsigned int mask;
	int masklit1;
	unsigned int masklit2, masklit3;
	unsigned int ptrange[4];
	for (int i = 0; i < 4; i++)
		ptrange[i] = atoui(split_ip[i]);
	mask = atoui(split_slash[1]);
	
	prefix_length = mask;

	mask = 32 - mask;
	masklit1 = mask / 8;
	masklit2 = mask % 8;

	/*count the start IP */
	for (int i = 3; i>3 - masklit1; i--)
		ptrange[i] = 0;
	if (masklit2 != 0){
		masklit3 = 1;
		masklit3 <<= masklit2;
		masklit3 -= 1;
		masklit3 = ~masklit3;
		ptrange[3 - masklit1] &= masklit3;
	}
	/*store start IP */
	IPrange[FieldSA] = ptrange[0];
	IPrange[FieldSA] <<= 8;
	IPrange[FieldSA] += ptrange[1];
	IPrange[FieldSA] <<= 8;
	IPrange[FieldSA] += ptrange[2];
	IPrange[FieldSA] <<= 8;
	IPrange[FieldSA] += ptrange[3];

	//key += std::bitset<32>(IPrange[0] >> prefix_length).to_string().substr(32 - prefix_length);
	/*count the end IP*/
	for (int i = 3; i>3 - masklit1; i--)
		ptrange[i] = 255;
	if (masklit2 != 0){
		masklit3 = 1;
		masklit3 <<= masklit2;
		masklit3 -= 1;
		ptrange[3 - masklit1] |= masklit3;
	}
	/*store end IP*/
	IPrange[FieldDA] = ptrange[0];
	IPrange[FieldDA] <<= 8;
	IPrange[FieldDA] += ptrange[1];
	IPrange[FieldDA] <<= 8;
	IPrange[FieldDA] += ptrange[2];
	IPrange[FieldDA] <<= 8;
	IPrange[FieldDA] += ptrange[3];
}
void InputReader::ReadPort(std::array<int_t,2>& Portrange, const string& from, const string& to)
{
	Portrange[LOW] = atoui(from);
	Portrange[HIGH] = atoui(to);
}

void InputReader::ReadProtocol(std::array<int_t,2>& Protocol, const string& last_token)
{
	// Example : 0x06/0xFF
	vector<string> split_slash = split(last_token, '/');

	if (split_slash[1] != "0xFF") {
		Protocol[LOW] = 0;
		Protocol[HIGH] = 255;
	} else {
		Protocol[LOW] = Protocol[HIGH] = std::stoul(split_slash[0], nullptr, 16);
	}
}


int InputReader::ReadFilter(vector<string>& tokens, vector<Rule>& ruleset, unsigned int cost)
{
	// 5 fields: sip, dip, sport, dport, proto = 0 (with@), 1, 2 : 4, 5 : 7, 8

	/*allocate a few more bytes just to be on the safe side to avoid overflow etc*/
	Rule temp_rule(dim);
	string key;
	if (tokens[0].at(0) != '@')  {
		/* each rule should begin with an '@' */
		printf("ERROR: NOT A VALID RULE FORMAT\n");
		exit(1);
	}

	int index_token = 0;
	int i = 0;
	for (int rep = 0; rep < reps; rep++)
	{
		/* reading SIP range */
		if (i == 0) {

			ReadIPRange(temp_rule.range[i], temp_rule.prefix_length[i], tokens[index_token++].substr(1));
			i++;
		} else {
			ReadIPRange(temp_rule.range[i], temp_rule.prefix_length[i], tokens[index_token++]);
			i++;
		}
		/* reading DIP range */
		ReadIPRange(temp_rule.range[i], temp_rule.prefix_length[i], tokens[index_token++]);
		i++;
		ReadPort(temp_rule.range[i++], tokens[index_token], tokens[index_token + 2]);
		index_token += 3;
		ReadPort(temp_rule.range[i++], tokens[index_token], tokens[index_token + 2]);
		index_token += 3;
		ReadProtocol(temp_rule.range[i++], tokens[index_token++]);
	}

	temp_rule.priority = cost;

	ruleset.push_back(temp_rule);

	return 0;
}
void InputReader::LoadFilters(ifstream& fp, vector<Rule>& ruleset)
{
	int line_number = 0;
	string content;
	while (getline(fp, content)) {
		istringstream iss(content);
		vector<string> tokens{ istream_iterator < string > {iss}, istream_iterator < string > {} };
		ReadFilter(tokens, ruleset, line_number++);
	}
}
vector<Rule> InputReader::ReadFilterFileClassBench(const string&  filename)
{
	//assume 5*rep fields

	vector<Rule> rules;
	ifstream column_counter(filename);
	ifstream input_file(filename);
	if (!input_file.is_open() || !column_counter.is_open())
	{
		printf("Couldnt open filter set file \n");
		exit(1);
	}


	LoadFilters(input_file, rules);
	input_file.close();
	column_counter.close();

	//need to rearrange the priority

	int max_pri = rules.size() - 1;
	for (size_t i = 0; i < rules.size(); i++) {
		rules[i].priority = max_pri - i; 
	}
	/*for (int i = 0; i < 5; i++) {
	set<interval> iv;
	for (rule& r : ruleset) {
	iv.insert(interval(r.range[i][0], r.range[i][1], 0));
	}
	cout << "field " << i << " has " << iv.size() << " unique intervals" << endl;
	}*/
	/*for (auto& r : rules) {
	for (auto &p : r.range) {
	cout << p[0] << ":" << p[1] << " ";
	}
	cout << endl;
	}
	exit(0);*/

	return	rules;
}

bool IsPower2(unsigned int x) {
	return ((x - 1) & x) == 0;
}

bool IsPrefix(unsigned int low, unsigned int high) {
	unsigned int diff = high - low;

	return ((low & high) == low) && IsPower2(diff + 1);
}

unsigned int PrefixLength(unsigned int low, unsigned int high) {
	unsigned int x = high - low;
	int lg = 0;
	for (; x; x >>= 1) lg++;
	return 32 - lg;
}

void InputReader::ParseRange(std::array<int_t, 2>& range, const string& text) {
	vector<string> split_colon = split(text, ':');
	// to obtain interval
	range[LOW] = atoui(split_colon[LOW]);
	range[HIGH] = atoui(split_colon[HIGH]);
	if (range[LOW] > range[HIGH]) {
        printf("Problematic range: %lu-%lu\n", range[LOW], range[HIGH]);
	}
}

vector<Rule> InputReader::ReadFilterFileMSU(const string&  filename)
{
	vector<Rule> rules;
	ifstream input_file(filename);
	if (!input_file.is_open())
	{
		printf("Couldnt open filter set file \n");
		exit(1);
	}
	string content;
	getline(input_file, content);
	getline(input_file, content);
	vector<string> split_comma = split(content, ',');
	dim = split_comma.size();

	int priority = 0;
	getline(input_file, content);
	vector<string> parts = split(content, ',');
    vector<array<int_t, 2>> bounds(parts.size());
	for (size_t i = 0; i < parts.size(); i++) {
		ParseRange(bounds[i], parts[i]);
		//printf("[%u:%u] %d\n", bounds[i][LOW], bounds[i][HIGH], PrefixLength(bounds[i][LOW], bounds[i][HIGH]));
	}

	while (getline(input_file, content)) {
		// 5 fields: sip, dip, sport, dport, proto = 0 (with@), 1, 2 : 4, 5 : 7, 8
		Rule temp_rule(dim);
		vector<string> split_comma = split(content, ',');
		// ignore priority at the end
		for (size_t i = 0; i < split_comma.size() - 1; i++)
		{
			ParseRange(temp_rule.range[i], split_comma[i]);
			if (IsPrefix(temp_rule.range[i][LOW], temp_rule.range[i][HIGH])) {
				temp_rule.prefix_length[i] = PrefixLength(temp_rule.range[i][LOW], temp_rule.range[i][HIGH]);
			}
			//if ((i == FieldSA || i == FieldDA) & !IsPrefix(temp_rule.range[i][LOW], temp_rule.range[i][HIGH])) {
			//	printf("Field is not a prefix!\n");
			//}
			if (temp_rule.range[i][LOW] < bounds[i][LOW] || temp_rule.range[i][HIGH] > bounds[i][HIGH]) {
				printf("rule out of bounds!\n");
			}
		}
		temp_rule.priority = priority++;
		temp_rule.tag = atoi(split_comma[split_comma.size() - 1].c_str());
		rules.push_back(temp_rule);
	}
	for (auto & r : rules) {
		r.priority = rules.size() - r.priority;
	}

	/*for (auto& r : rules) {
	for (auto &p : r.range) {
	cout << p[0] << ":" << p[1] << " ";
	}
	cout << endl;
	}
	exit(0);*/
    return rules;
}

#define MAC_ADDR_LEN 6
#define MIN_NG_LINE_LEN 8
#define NG_NW_SRC      "nw_src"
#define NG_NW_DST      "nw_dst"
#define NG_TP_SRC      "tp_src"
#define NG_TP_DST      "tp_dst"
#define NG_NW_PROTO    "nw_proto"
#define NG_DL_SRC      "dl_src"
#define NG_DL_DST      "dl_dst"
#define NG_ETH_TYPE    "eth_type"
#define NG_IN_PORT     "in_port"
enum SIMPLE_FIELD_NG_INDEX {
    NGI_NW_SRC = 0,
    NGI_NW_DST,
    NGI_TP_SRC,
    NGI_TP_DST,
    NGI_NW_PROTO,
    NGI_DL_SRC,
    NGI_DL_DST,
    NGI_ETH_TYPE,
    NGI_IN_PORT,
    NGI_FIELD_COUNT
};
std::vector<Rule> InputReader::ReadFilterFileClassBenchNg(const string &filename)
{
    const char *ng_fieldnames[] = {NG_NW_SRC, NG_NW_DST, NG_TP_SRC, NG_TP_DST, NG_NW_PROTO, NG_DL_SRC, NG_DL_DST, NG_ETH_TYPE, NG_IN_PORT};

    std::map<std::string, uint64_t> ng_max_values = {
        {NG_NW_SRC, 0xFFFFFFFF},
        {NG_NW_DST, 0xFFFFFFFF},
        {NG_TP_SRC, 0xFFFF},
        {NG_TP_DST, 0xFFFF},
        {NG_NW_PROTO, 0xFF},
        {NG_DL_SRC, 0xFFFFFFFFFFFF},
        {NG_DL_DST, 0xFFFFFFFFFFFF},
        {NG_ETH_TYPE, 0xFFFF},
        {NG_IN_PORT, 0xFFFF}
    };

    vector<Rule> rules;
    FILE *fp = fopen(filename.c_str(), "r");
    if (!fp) {
        perror("RuleSet::readNgFile::fopen");
        return rules;
    }

    char line[1000] = {};

    int id = 0;
    dim = 9;
    while (fgets(line, 999, fp) != 0) {

        if (strlen(line) < MIN_NG_LINE_LEN || !strchr(line, '=')) {
            printf("\nInvalid line in file: {%s}", line);
            continue;
        }
        //SimpleRule *rule = new SimpleRule();
        Rule rule(dim);
        for (uint32_t i = 0; i < 9; i++) {
            bool isPrefix = (i <= 1) ? true : false;
            char *sub = strstr(line, ng_fieldnames[i]);
            if (sub) {
                sub += strlen(ng_fieldnames[i]) + 1; // +1 for =
                ReadNgField(rule, i, isPrefix, ng_fieldnames[i], sub);
            } else {
                rule.range[i][LOW] = 0;
                rule.range[i][HIGH] = ng_max_values[ng_fieldnames[i]];
            }
        }

        rule.id = id;
        id++;
        rules.push_back(rule);
    }

    int max_pri = rules.size() - 1;
    for (size_t i = 0; i < rules.size(); i++) {
        rules[i].priority = max_pri - i;
    }

    return rules;
}

void InputReader::ReadNgField(Rule &rule, int fieldIndex, bool isPrefix, const char *name, const char *fieldstr)
{
    //this->type = type;
    uint64_t first = 0;
    uint64_t second = 0;
    //int wildcard = 0;
    uint8_t addr[MAC_ADDR_LEN];
    memset(addr, 0, MAC_ADDR_LEN);
    //this->name = name;

    if (isPrefix) {
        uint8_t chunks[4];
        int l = 0;
        sscanf(fieldstr, "%d.%d.%d.%d/%d", (int *) &chunks[0], (int *) &chunks[1], (int *) &chunks[2], (int *) &chunks[3], &l);

        //memcpy(&this->prefix, chunks, 4);
        uint8_t *p = (uint8_t*) &first;
        for (int i = 0; i < 4; i++)
            p[i] = chunks[3 - i];

        uint32_t msk = 0x80000000;
        uint32_t mask = 0;
        for (int i = 0; i < l; i++, msk = msk >> 1) {
            mask = mask | msk;
        }
        rule.range[fieldIndex][LOW] = ((uint32_t) mask) & first;
        rule.range[fieldIndex][HIGH] = (~ (uint32_t) mask) | first;
        rule.prefix_length[fieldIndex] = l;

    } else {
        if (!strncmp(name, "eth_type", std::min(strlen(name), strlen("eth_type")))) {
            uint64_t value = 0;
            sscanf(&fieldstr[2], "%lx", &value);
            first = value;
            second = value;
        } else if (!strncmp(name, "dl_src", std::min(strlen(name), strlen("dl_src"))) ||
                   !strncmp(name, "dl_dst", std::min(strlen(name), strlen("dl_dst")))) {
            int32_t chunk[MAC_ADDR_LEN] = {};
            sscanf(fieldstr, "%2x:%2x:%2x:%2x:%2x:%2x", &chunk[0], &chunk[1], &chunk[2], &chunk[3], &chunk[4], &chunk[5]);
            first = 0;
            for (int i = 0; i < MAC_ADDR_LEN; i++) {
                addr[i] = (chunk[i] & 0xFF);
                if (sizeof(uint64_t) >= 6) {
                    uint64_t tmp = chunk[i];
                    first = first | (tmp << (8 * i));
                }
                second = first;
            }
        } else {
            uint64_t value = 0;
            sscanf(fieldstr, "%lu", &value);
            first = value;
            second = value;
        }
        rule.range[fieldIndex][LOW] = first;
        rule.range[fieldIndex][HIGH] = second;
    }
}

vector<Rule> InputReader::ReadFilterFile(const string&  filename) {


	ifstream in(filename);
	if (!in.is_open())
	{
		printf("Couldnt open filter set file \n");
		printf("%s\n", filename.c_str());
		exit(1);
	} else {
		printf("Reading filter file %s\n", filename.c_str());
	}
	//cout << filename << " ";
	string content;
	getline(in, content);
	istringstream iss(content);
	vector<string> tokens{ istream_iterator < string > {iss}, istream_iterator < string > {} };
	if (content[0] == '!') {
		// MSU FORMAT
		vector<string> split_semi = split(tokens.back(), ';');
		reps = (atoi(split_semi.back().c_str()) + 1) / 5;
		dim = reps * 5;

		return ReadFilterFileMSU(filename);

	} else if (content[0] == '@') {
		// CLassBench Format
		/* COUNT COLUMN */

		if (tokens.size() % 9 == 0) {
			reps = tokens.size() / 9;
		}
		
	    dim = reps * 5;
		return ReadFilterFileClassBench(filename);
	} else {
//		cout << "ERROR: unknown input format please use either MSU format or ClassBench format" << endl;
//		exit(1);
        return ReadFilterFileClassBenchNg(filename);
	}
	in.close();
}
