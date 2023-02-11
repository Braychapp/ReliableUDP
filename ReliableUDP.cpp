/*
* FILE : ReliableUDP.cpp
* PROJECT : Reliable UDP
* PROGRAMMER : Brayden Chapple, Evan O'Hara
* FIRST VERSION : 2023-02-10
* DESCRIPTION :
* This program is used to open a server and a client then send files between them using UDP
*/



/*
	Reliability and Flow Control Example
	From "Networking for Game Programmers" - http://www.gaffer.org/networking-for-game-programmers
	Author: Glenn Fiedler <gaffer@gaffer.org>
*/
/*
What we need to do for the assignment
parse command line for a file name 
figure out size of file
calculate number of required packets to send the file
create packets and assign them a number
send packets to the server
loop for each packet
read the next packet from the file
send the packet to server
close file
*/
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <filesystem>
#include<chrono>

#include "Net.h"
#pragma warning(disable : 4996)

using namespace std;

//#define SHOW_ACKS

using namespace std;
using namespace net;

const int ServerPort = 30000;
const int ClientPort = 30001;
const int ProtocolId = 0x11223344;
const float DeltaTime = 1.0f / 30.0f;
const float SendRate = 1.0f / 30.0f;
const float TimeOut = 10.0f;
const int PacketSize = 256;
int packetsRecieved = 0;
char filenameO[50];




// added functions for MD5 hashing taken from https://www.programmingalgorithms.com/algorithm/md5/cpp/
// sorry I had to add it to the cpp file and not a header file
// when I tried to add it to a header file, it broke the rest
// of the code in Net.h

typedef union uwb {
	unsigned w;
	unsigned char b[4];
} MD5union;

typedef unsigned DigestArray[4];

static unsigned func0(unsigned abcd[]) {
	return (abcd[1] & abcd[2]) | (~abcd[1] & abcd[3]);
}

static unsigned func1(unsigned abcd[]) {
	return (abcd[3] & abcd[1]) | (~abcd[3] & abcd[2]);
}

static unsigned func2(unsigned abcd[]) {
	return  abcd[1] ^ abcd[2] ^ abcd[3];
}

static unsigned func3(unsigned abcd[]) {
	return abcd[2] ^ (abcd[1] | ~abcd[3]);
}

typedef unsigned(*DgstFctn)(unsigned a[]);

static unsigned* calctable(unsigned* k)
{
	double s, pwr;
	int i;

	pwr = pow(2.0, 32);
	for (i = 0; i < 64; i++) {
		s = fabs(sin(1.0 + i));
		k[i] = (unsigned)(s * pwr);
	}
	return k;
}

static unsigned rol(unsigned r, short N)
{
	unsigned  mask1 = (1 << N) - 1;
	return ((r >> (32 - N)) & mask1) | ((r << N) & ~mask1);
}

static unsigned* MD5Hash(string msg)
{
	int mlen = msg.length();
	static DigestArray h0 = { 0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476 };
	static DgstFctn ff[] = { &func0, &func1, &func2, &func3 };
	static short M[] = { 1, 5, 3, 7 };
	static short O[] = { 0, 1, 5, 0 };
	static short rot0[] = { 7, 12, 17, 22 };
	static short rot1[] = { 5, 9, 14, 20 };
	static short rot2[] = { 4, 11, 16, 23 };
	static short rot3[] = { 6, 10, 15, 21 };
	static short* rots[] = { rot0, rot1, rot2, rot3 };
	static unsigned kspace[64];
	static unsigned* k;

	static DigestArray h;
	DigestArray abcd;
	DgstFctn fctn;
	short m, o, g;
	unsigned f;
	short* rotn;
	union {
		unsigned w[16];
		char     b[64];
	}mm;
	int os = 0;
	int grp, grps, q, p;
	unsigned char* msg2;

	if (k == NULL) k = calctable(kspace);

	for (q = 0; q < 4; q++) h[q] = h0[q];

	{
		grps = 1 + (mlen + 8) / 64;
		msg2 = (unsigned char*)malloc(64 * grps);
		memcpy(msg2, msg.c_str(), mlen);
		msg2[mlen] = (unsigned char)0x80;
		q = mlen + 1;
		while (q < 64 * grps) { msg2[q] = 0; q++; }
		{
			MD5union u;
			u.w = 8 * mlen;
			q -= 8;
			memcpy(msg2 + q, &u.w, 4);
		}
	}

	for (grp = 0; grp < grps; grp++)
	{
		memcpy(mm.b, msg2 + os, 64);
		for (q = 0; q < 4; q++) abcd[q] = h[q];
		for (p = 0; p < 4; p++) {
			fctn = ff[p];
			rotn = rots[p];
			m = M[p]; o = O[p];
			for (q = 0; q < 16; q++) {
				g = (m * q + o) % 16;
				f = abcd[1] + rol(abcd[0] + fctn(abcd) + k[q + 16 * p] + mm.w[g], rotn[q % 4]);

				abcd[0] = abcd[3];
				abcd[3] = abcd[2];
				abcd[2] = abcd[1];
				abcd[1] = f;
			}
		}
		for (p = 0; p < 4; p++)
			h[p] += abcd[p];
		os += 64;
	}

	return h;
}

static string GetMD5String(string msg) {
	string str;
	int j, k;
	unsigned* d = MD5Hash(msg);
	MD5union u;
	for (j = 0; j < 4; j++) {
		u.w = d[j];
		char s[9];
		sprintf(s, "%02x%02x%02x%02x", u.b[0], u.b[1], u.b[2], u.b[3]);
		str += s;
	}

	return str;
}

//
// END OF MD5 Hashing stuff
//

class FlowControl
{
public:

	FlowControl()
	{
		printf("flow control initialized\n");
		Reset();
	}

	void Reset()
	{
		mode = Bad;
		penalty_time = 4.0f;
		good_conditions_time = 0.0f;
		penalty_reduction_accumulator = 0.0f;
	}

	void Update(float deltaTime, float rtt)
	{
		const float RTT_Threshold = 250.0f;

		if (mode == Good)
		{
			if (rtt > RTT_Threshold)
			{
				printf("*** dropping to bad mode ***\n");
				mode = Bad;
				if (good_conditions_time < 10.0f && penalty_time < 60.0f)
				{
					penalty_time *= 2.0f;
					if (penalty_time > 60.0f)
						penalty_time = 60.0f;
					printf("penalty time increased to %.1f\n", penalty_time);
				}
				good_conditions_time = 0.0f;
				penalty_reduction_accumulator = 0.0f;
				return;
			}

			good_conditions_time += deltaTime;
			penalty_reduction_accumulator += deltaTime;

			if (penalty_reduction_accumulator > 10.0f && penalty_time > 1.0f)
			{
				penalty_time /= 2.0f;
				if (penalty_time < 1.0f)
					penalty_time = 1.0f;
				printf("penalty time reduced to %.1f\n", penalty_time);
				penalty_reduction_accumulator = 0.0f;
			}
		}

		if (mode == Bad)
		{
			if (rtt <= RTT_Threshold)
				good_conditions_time += deltaTime;
			else
				good_conditions_time = 0.0f;

			if (good_conditions_time > penalty_time)
			{
				printf("*** upgrading to good mode ***\n");
				good_conditions_time = 0.0f;
				penalty_reduction_accumulator = 0.0f;
				mode = Good;
				return;
			}
		}
	}

	float GetSendRate()
	{
		return mode == Good ? 30.0f : 10.0f;
	}

private:

	enum Mode
	{
		Good,
		Bad
	};

	Mode mode;
	float penalty_time;
	float good_conditions_time;
	float penalty_reduction_accumulator;
};

// ----------------------------------------------

int main(int argc, char* argv[])
{
	// deletes the buffer file that holds the data
	//remove("buffer_file.bin");
	
	enum Mode
	{
		Client,
		Server
	};

	Mode mode = Server;
	Address address;
	vector <char> fdata;
	vector <char> filename;
	if (argc >= 2)
	{
		int a, b, c, d;
		#pragma warning (suppress : 4996)
		if (sscanf(argv[1], "%d.%d.%d.%d", &a, &b, &c, &d))
		{
			mode = Client;
			address = Address(a, b, c, d, ServerPort);

			if (strstr(argv[2], ".txt") != nullptr)
			{
				//we know its a text file
				ifstream file(argv[2]);
				if (!file.is_open())
				{
					cerr << "Failed to open a ASCII file";
					return 0;
				}
				else
				{
					fdata.assign((istreambuf_iterator<char>(file)), istreambuf_iterator<char>());
					file.close();

					string str = argv[2];
					str = str + " ";
					filename.assign(str.begin(), str.end());
					fdata.insert(fdata.begin(), 1);
					fdata.insert(fdata.begin() + 1, filename.begin(), filename.end());
				}
			}
			else if (strstr(argv[2], ".bin") != nullptr)
			{
				//we know its a binary file
				ifstream file(argv[2]);
				if (!file.is_open())
				{
					cerr << "Failed to open binary file";
				}
				else
				{
					fdata.assign((istreambuf_iterator<char>(file)), istreambuf_iterator<char>());
					file.close();

					string str = argv[2];
					str = str + " ";
					filename.assign(str.begin(), str.end());
					fdata.insert(fdata.begin(), 1);
					fdata.insert(fdata.begin() + 1, filename.begin(), filename.end());

				}
			}
			else
			{
				//no file found
				cerr << "No accepted file extension specified";
				return 0;
			}

		}
	}

	// initialize

	if (!InitializeSockets())
	{
		printf("failed to initialize sockets\n");
		return 1;
	}

	ReliableConnection connection(ProtocolId, TimeOut);

	const int port = mode == Server ? ServerPort : ClientPort;

	if (!connection.Start(port))
	{
		printf("could not start connection on port %d\n", port);
		return 1;
	}

	if (mode == Client)
		connection.Connect(address);
	else
		connection.Listen();

	bool connected = false;
	float sendAccumulator = 0.0f;
	float statsAccumulator = 0.0f;

	FlowControl flowControl;

	int i = 0;
	char hello[] = "Hello World";
	char message[15];
		
	int offset = 0;
	int size = fdata.size();

	
	while (true)
	{
		// update flow control

		if (connection.IsConnected())
			flowControl.Update(DeltaTime, connection.GetReliabilitySystem().GetRoundTripTime() * 1000.0f);

		const float sendRate = flowControl.GetSendRate();

		// detect changes in connection state

		if (mode == Server && connected && !connection.IsConnected())
		{
			flowControl.Reset();
			printf("reset flow control\n");
			connected = false;
			packetsRecieved = 0;
			for (int i = 0; i < 50; i++) {
				filenameO[i] = '\0';
			}
		}

		if (!connected && connection.IsConnected())
		{
			printf("client connected to server\n");
			connected = true;
		}

		if (!connected && connection.ConnectFailed())
		{
			printf("connection failed\n");
			break;
		}

		// send and receive packets

		if (mode == Client)
		{

			// Get the vector data into a string
			string md5Buffer;
			for (char c : fdata)
			{
				md5Buffer.push_back(c);
			}
			md5Buffer = GetMD5String(md5Buffer); // Get the MD5 String value


			sendAccumulator += DeltaTime;
			
			auto start = chrono::steady_clock::now();

			while (sendAccumulator > 1.0f / sendRate)
			{			
				unsigned char packet[PacketSize];

				if (fdata.size() <= 0)
				{
					// send the last 32 bit hashing
					memcpy(packet, &md5Buffer[offset], md5Buffer.size());
					connection.SendPacket(packet, md5Buffer.size());
					auto end = chrono::steady_clock::now();
					chrono::duration<double> elapsed_seconds = end - start;
					cout << "elapsed file transfer time: " << elapsed_seconds.count() << "s or: " << elapsed_seconds.count() * 1000 << "ms\n";
					return 1;

				}

				// the remaing size of fdata is greater than the PacketSize (>256)
				if (fdata.size() > sizeof(packet))
				{
					memset(packet, 0, sizeof(packet));
					memcpy(packet, &fdata[offset], sizeof(packet));

					connection.SendPacket(packet, sizeof(packet));
				}

				// the remaining data in fsize is less than PacketSize (<256), last send of file data, not including hash number
				else if (fdata.size() <= sizeof(packet))
				{
					memset(packet, 0, fdata.size());
					memcpy(packet, &fdata[offset], fdata.size());

					connection.SendPacket(packet, fdata.size());
				}

				sendAccumulator -= 1.0f / sendRate;
				

				// remove packet we just sent from fdata
				if (fdata.size() >= sizeof(packet))
				{
					// removes the last remaining amount of fdata, that is less
					// than or equal to the packet amount (<256)
					fdata.erase(fdata.begin(), fdata.begin() + sizeof(packet));
				}
				else
				{
					// usually happens for most of the file transfer, except the last transfer of packets
					// removes the packet that was just sent from fdata
					fdata.erase(fdata.begin(), fdata.begin() + fdata.size());
				}
				
				printf("Packet Sent: %s\n", packet);

			}
		}

		if (mode == Server)
		{

			char hashCodeFromClient[33] = {NULL};

			while (true)
			{
				unsigned char packet[256];
				vector<char> filenameVec;
				int bytes_read = connection.ReceivePacket(packet, sizeof(packet));

				if (bytes_read == 0)
				{
					
					break;
				}

				//this is used for getting the filename and extension
				if (packetsRecieved == 0)
				{
					packet[0] = '1';
					packetsRecieved++;
				}

				printf("Packet Recieved: %s\n", packet);
				//below deals with the first packet that is recieved because it contains the filename and extension
				if (packetsRecieved == 1)
				{
					int length = sizeof(packet) / sizeof(packet[0]);
					int space_index = -1;
					vector<char> data;

					for (int i = 0; i < length; i++) {
						if (packet[i] == ' ') {
							space_index = i;
							break;
						}
						if (space_index == -1)
						{
							filenameVec.push_back(packet[i]);
						}
						else
						{
							break;
						}
						
					}

					for (int i = 0; i < filenameVec.size(); i++) {
						filenameO[i - 1] = filenameVec[i];
					}
					if (space_index != -1) {
						for (int i = space_index + 1; i < length; i++) {
							data.push_back(packet[i]);
						}
						//putting the data back into the packet after removing what was necessary
						for (int i = 0; i < data.size(); i++)
						{
							packet[i] = data[i];
							if (data[i] == '\0')
								break;
						}
					}
					packetsRecieved++;
					
				}


				// Open the buffer_file that the packets will be written to
				
				const char* fileN = filenameO;
				ofstream file;
				file.open(fileN, std::ios_base::binary | std::ios::app);
				if (file.is_open())
				{
					file.write((const char*)packet, bytes_read);
					file.close();
				}
				else
				{
					cerr << "error opening file for writing.";
					return 0;
				}


				// now open the buffer file after it has been written to
				// and extract the hash code from the last 32 bytes
				
				/*ifstream inputFile;
				
				inputFile.open(fileN, ios::binary | ios::ate);
				if (inputFile.is_open())
				{
					inputFile.seekg(-32, std::ios::end);
					inputFile.read(hashCodeFromClient, 32);
					hashCodeFromClient[32] = 0;

					inputFile.close();
					printf("HERE IS THE SERVER HASH CODE: %s\n\n", hashCodeFromClient);
				}*/

			}

			//// we have the hash code after the file has been fully transfered
			//// problem is that it breaks above while loop, for small moments between
			//// sending packets
			//if (hashCodeFromClient != NULL)
			//{
			//	

			//}
			
		}
		// show packets that were acked this frame

#ifdef SHOW_ACKS
		unsigned int* acks = NULL;
		int ack_count = 0;
		connection.GetReliabilitySystem().GetAcks(&acks, ack_count);
		if (ack_count > 0)
		{
			printf("acks: %d", acks[0]);
			for (int i = 1; i < ack_count; ++i)
				printf(",%d", acks[i]);
			printf("\n");
		}
#endif

		// update connection

		connection.Update(DeltaTime);

		// show connection stats

		statsAccumulator += DeltaTime;

		while (statsAccumulator >= 0.25f && connection.IsConnected())
		{
			float rtt = connection.GetReliabilitySystem().GetRoundTripTime();

			unsigned int sent_packets = connection.GetReliabilitySystem().GetSentPackets();
			unsigned int acked_packets = connection.GetReliabilitySystem().GetAckedPackets();
			unsigned int lost_packets = connection.GetReliabilitySystem().GetLostPackets();

			float sent_bandwidth = connection.GetReliabilitySystem().GetSentBandwidth();
			float acked_bandwidth = connection.GetReliabilitySystem().GetAckedBandwidth();

			printf("rtt %.1fms, sent %d, acked %d, lost %d (%.1f%%), sent bandwidth = %.1fkbps, acked bandwidth = %.1fkbps\n",
				rtt * 1000.0f, sent_packets, acked_packets, lost_packets,
				sent_packets > 0.0f ? (float)lost_packets / (float)sent_packets * 100.0f : 0.0f,
				sent_bandwidth, acked_bandwidth);

			statsAccumulator -= 0.25f;
		}

		net::wait(DeltaTime);
	}

	ShutdownSockets();

	return 0;
}
