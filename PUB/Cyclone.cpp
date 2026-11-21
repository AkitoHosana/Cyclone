#include <immintrin.h>
#include <iostream>
#include <iomanip>
#include <string>
#include <cstring>
#include <chrono>
#include <vector>
#include <sstream>
#include <stdexcept>
#include <algorithm>
#include <fstream>
#include <omp.h>
#include <random>
#include <array>
#include <mutex>
#include <cmath>

#ifdef _WIN32
    #include <windows.h>
#endif

#include "SECP256K1.h"
#include "Point.h"
#include "Int.h"
#include "IntGroup.h"
#include "tee_stream.h"

void initConsole() {
#ifdef _WIN32
    HANDLE hConsole = GetStdHandle(STD_OUTPUT_HANDLE);
    DWORD mode = 0;
    GetConsoleMode(hConsole, &mode);
    SetConsoleMode(hConsole, mode | ENABLE_VIRTUAL_TERMINAL_PROCESSING);
#endif
}

void clearTerminal() {
#ifdef _WIN32
    HANDLE hStdOut = GetStdHandle(STD_OUTPUT_HANDLE);
    COORD coord = {0, 0};
    DWORD count;
    CONSOLE_SCREEN_BUFFER_INFO csbi;
    GetConsoleScreenBufferInfo(hStdOut, &csbi);
    FillConsoleOutputCharacter(hStdOut, ' ', csbi.dwSize.X * csbi.dwSize.Y, coord, &count);
    SetConsoleCursorPosition(hStdOut, coord);
#else
    std::cout << "\033[2J\033[H";
#endif
    std::cout.flush();
}

void moveCursorTo(int x, int y) {
#ifdef _WIN32
    HANDLE hStdOut = GetStdHandle(STD_OUTPUT_HANDLE);
    COORD coord = {(SHORT)x, (SHORT)y};
    SetConsoleCursorPosition(hStdOut, coord);
#else
    std::cout << "\033[" << y << ";" << x << "H";
#endif
    std::cout.flush();
}

void clearLine() {
#ifdef _WIN32
    HANDLE hStdOut = GetStdHandle(STD_OUTPUT_HANDLE);
    CONSOLE_SCREEN_BUFFER_INFO csbi;
    GetConsoleScreenBufferInfo(hStdOut, &csbi);
    COORD coord = {0, csbi.dwCursorPosition.Y};
    DWORD count;
    FillConsoleOutputCharacter(hStdOut, ' ', csbi.dwSize.X, coord, &count);
    SetConsoleCursorPosition(hStdOut, coord);
#else
    std::cout << "\033[K";
#endif
    std::cout.flush();
}

#define BISIZE 256
#if BISIZE == 256
#define NB64BLOCK 5
#define NB32BLOCK 10
#else
#error Unsupported size
#endif

static constexpr int POINTS_BATCH_SIZE = 256;
static constexpr int HASH_BATCH_SIZE = 8;
int g_prefixLength = 4; 

static constexpr double statusIntervalSec = 5.0;
std::mutex coutMutex;

std::vector<uint64_t> hexToBigNum(const std::string& hex) {
    std::vector<uint64_t> bigNum;
    const size_t len = hex.size();
    bigNum.reserve((len + 15) / 16);
    for (size_t i = 0; i < len; i += 16) {
        size_t start = (len >= 16 + i) ? len - 16 - i : 0;
        size_t partLen = (len >= 16 + i) ? 16 : (len - i);
        uint64_t value = std::stoull(hex.substr(start, partLen), nullptr, 16);
        bigNum.push_back(value);
    }
    return bigNum;
}

std::string bigNumToHex(const std::vector<uint64_t>& num) {
    std::ostringstream oss;
    for (auto it = num.rbegin(); it != num.rend(); ++it) {
        if (it != num.rbegin())
            oss << std::setw(16) << std::setfill('0');
        oss << std::hex << *it;
    }
    return oss.str();
}

std::vector<uint64_t> singleElementVector(uint64_t val) {
    return { val };
}

std::vector<uint64_t> bigNumAdd(const std::vector<uint64_t>& a, const std::vector<uint64_t>& b) {
    std::vector<uint64_t> sum;
    sum.reserve(std::max(a.size(), b.size()) + 1);
    uint64_t carry = 0;
    for (size_t i = 0, sz = std::max(a.size(), b.size()); i < sz; ++i) {
        uint64_t x = (i < a.size()) ? a[i] : 0ULL;
        uint64_t y = (i < b.size()) ? b[i] : 0ULL;
        __uint128_t s = (__uint128_t)x + (__uint128_t)y + carry;
        carry = (uint64_t)(s >> 64);
        sum.push_back((uint64_t)s);
    }
    if (carry) sum.push_back(carry);
    return sum;
}

std::vector<uint64_t> bigNumSubtract(const std::vector<uint64_t>& a, const std::vector<uint64_t>& b) {
    std::vector<uint64_t> diff = a;
    uint64_t borrow = 0;
    for (size_t i = 0; i < b.size(); ++i) {
        uint64_t subtrahend = b[i];
        if (diff[i] < subtrahend + borrow) {
            diff[i] = diff[i] + (~0ULL) - subtrahend - borrow + 1ULL;
            borrow = 1ULL;
        } else {
            diff[i] -= (subtrahend + borrow);
            borrow = 0ULL;
        }
    }

    for (size_t i = b.size(); i < diff.size() && borrow; ++i) {
        if (diff[i] == 0ULL) {
            diff[i] = ~0ULL;
        } else {
            diff[i] -= 1ULL;
            borrow = 0ULL;
        }
    }
    while (!diff.empty() && diff.back() == 0ULL)
        diff.pop_back();
    return diff;
}

std::pair<std::vector<uint64_t>, uint64_t> bigNumDivide(const std::vector<uint64_t>& a, uint64_t divisor) {
    std::vector<uint64_t> quotient(a.size(), 0ULL);
    uint64_t remainder = 0ULL;
    for (int i = (int)a.size() - 1; i >= 0; --i) {
        __uint128_t temp = ((__uint128_t)remainder << 64) | a[i];
        uint64_t q = (uint64_t)(temp / divisor);
        uint64_t r = (uint64_t)(temp % divisor);
        quotient[i] = q;
        remainder   = r;
    }
    while (!quotient.empty() && quotient.back() == 0ULL)
        quotient.pop_back();
    return { quotient, remainder };
}

long double hexStrToLongDouble(const std::string &hex) {
    long double result = 0.0L;
    for (char c : hex) {
        result *= 16.0L;
        if (c >= '0' && c <= '9')
            result += (c - '0');
        else if (c >= 'a' && c <= 'f')
            result += (c - 'a' + 10);
        else if (c >= 'A' && c <= 'F')
            result += (c - 'A' + 10);
    }
    return result;
}

int calculatePuzzleSize(const std::string& startHex, const std::string& endHex) {
    auto start = hexToBigNum(startHex);
    auto end = hexToBigNum(endHex);
    auto rangeSize = bigNumSubtract(end, start);
    rangeSize = bigNumAdd(rangeSize, singleElementVector(1ULL));
    long double rangeSizeLD = hexStrToLongDouble(bigNumToHex(rangeSize));
    int puzzleSize = static_cast<int>(std::log2(rangeSizeLD)) + 1;
    return puzzleSize;
}

std::string padHexTo64(const std::string &hex) {
    return (hex.size() >= 64) ? hex : std::string(64 - hex.size(), '0') + hex;
}

Int hexToInt(const std::string &hex) {
    Int number;
    char buf[65] = {0};
    std::strncpy(buf, hex.c_str(), 64);
    number.SetBase16(buf);
    return number;
}

std::string intToHex(const Int &value) {
    Int temp;
    temp.Set((Int*)&value);
    return temp.GetBase16();
}

bool intGreater(const Int &a, const Int &b) {
    std::string ha = ((Int&)a).GetBase16();
    std::string hb = ((Int&)b).GetBase16();
    if (ha.size() != hb.size()) return (ha.size() > hb.size());
    return (ha > hb);
}

bool isEven(const Int &number) {
    return ((Int&)number).IsEven();
}

std::string intXToHex64(const Int &x) {
    Int temp;
    temp.Set((Int*)&x);
    std::string hex = temp.GetBase16();
    if (hex.size() < 64)
        hex.insert(0, 64 - hex.size(), '0');
    return hex;
}

std::string pointToCompressedHex(const Point &point) {
    return (isEven(point.y) ? "02" : "03") + intXToHex64(point.x);
}

void intToXBin(const Int &x, uint8_t outX[32]) {
    Int temp;
    temp.Set((Int*)&x);
    for (int i = 0; i < 32; i++) {
        outX[i] = (uint8_t)temp.GetByte(31 - i);
    }
}

void printUsage(const char *programName) {
    std::cerr << "Usage: " << programName << " -k <compressed_public_key_hex> [-p <puzzle> | -r <startHex:endHex>] -b <x_prefix_bytes> [-t <threads>]\n";
    std::cerr << "  -k : Target compressed public key (66 hex chars); matching uses its x coordinate\n";
    std::cerr << "  -b : Number of x-coordinate prefix bytes to compare (1-32)\n";
    std::cerr << "  -t : Number of CPU threads to use (default: all available cores)\n";
}

std::string formatElapsedTime(double seconds) {
    int hrs = (int)seconds / 3600;
    int mins = ((int)seconds % 3600) / 60;
    int secs = (int)seconds % 60;
    std::ostringstream oss;
    oss << std::setw(2) << std::setfill('0') << hrs << ":"
        << std::setw(2) << std::setfill('0') << mins << ":"
        << std::setw(2) << std::setfill('0') << secs;
    return oss.str();
}

struct ThreadRange {
    std::string startHex;
    std::string endHex;
};

static std::vector<ThreadRange> g_threadRanges;

class Xoshiro256plus {
public:
    Xoshiro256plus(uint64_t seed = 0) {

        state[0] = splitmix64(seed);
        for (int i = 1; i < 4; ++i) {
            state[i] = splitmix64(state[i - 1]);
        }
    }

    inline uint64_t next() __attribute__((hot)) {
        const uint64_t s0 = state[0];
        const uint64_t s1 = state[1];
        const uint64_t s2 = state[2];
        const uint64_t s3 = state[3];

        const uint64_t result = s0 + s3;
        const uint64_t t = s1 << 17;

        state[2] = s2 ^ s0;
        state[3] = s3 ^ s1;
        state[1] = s1 ^ state[2];
        state[0] = s0 ^ state[3];
        state[2] ^= t;

        state[3] = rotl(state[3], 45);

        return result;
    }

private:

    inline uint64_t splitmix64(uint64_t x) __attribute__((always_inline)) {
        uint64_t z = (x += 0x9e3779b97f4a7c15);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9;
        z = (z ^ (z >> 27)) * 0x94d049bb133111eb;
        return z ^ (z >> 31);
    }

    inline uint64_t rotl(const uint64_t x, int k) __attribute__((always_inline)) {
        return (x << k) | (x >> (64 - k));
    }

    alignas(32) std::array<uint64_t, 4> state;
};

Int generateRandomPrivateKey(Int minKey, Int maxKey, Xoshiro256plus &rng) {
    Int rangeSize = maxKey; Int one; one.SetInt32(1);
    rangeSize.Sub(&minKey);
    rangeSize.Add(&one);

    size_t nBytes = rangeSize.GetBase16().size() / 2 + 1;
    std::vector<uint64_t> randWords((nBytes + 7) / 8);
    for (auto &w : randWords) {
        w = rng.next();  
    }

    Int offset = hexToInt(bigNumToHex(randWords));
    offset.Mod(&rangeSize);

    Int result = minKey;
    result.Add(&offset);
    return result;
}

void printStatsBlock(int numCPUs, const std::string &targetPublicKeyHex,
                    const std::string &rangeStr, double mkeysPerSec,
                    unsigned long long totalChecked, double elapsedTime,
                    int puzzle)
{
    std::lock_guard<std::mutex> lock(coutMutex);
    static bool firstPrint = true;

    if (!firstPrint) {
        moveCursorTo(1, 1);
        for (int i = 0; i < 7; i++) {
            clearLine();
            moveCursorTo(1, 1 + i + 1);
        }
    } else {
        firstPrint = false;
    }

    moveCursorTo(1, 1);
    std::cout << "================= WORK IN PROGRESS =================\n";
    std::cout << "Puzzle/Bits   : " << puzzle << "\n";
    std::cout << "Target PubKey : " << targetPublicKeyHex.substr(0, 16) << "..." << targetPublicKeyHex.substr(58) << "\n";
    std::cout << "X prefix length: " << g_prefixLength << " bytes" << "\n";
    std::cout << "Mode          : Random\n";
    std::cout << "CPU Threads   : " << numCPUs << "\n";
    std::cout << "Mkeys/s       : " << std::fixed << std::setprecision(2) << mkeysPerSec << "\n";
    std::cout << "Total Checked : " << totalChecked << "\n";
    std::cout << "Elapsed Time  : " << formatElapsedTime(elapsedTime) << "\n"; 
    std::cout << "Range         : " << rangeStr << "\n";
    std::cout.flush();
}

int main(int argc, char *argv[]) {
    initConsole();
    clearTerminal();
    bool publicKeyProvided = false, rangeProvided = false, puzzleProvided = false;
    std::string targetPublicKeyHex;
    std::vector<uint8_t> targetPublicKey;
    int puzzle = 0;
    std::string rangeStartHex, rangeEndHex;
    int numCPUs = omp_get_num_procs();
    Int minKey, maxKey; 

    for (int i = 1; i < argc; i++) {
        if (!std::strcmp(argv[i], "-k") && i + 1 < argc) {
            targetPublicKeyHex = argv[++i];
            if (targetPublicKeyHex.size() != 66) {
                std::cerr << "Invalid public key length. Must be 66 hex chars (33 bytes compressed).\n";
                return 1;
            }
            publicKeyProvided = true;
            targetPublicKey.resize(33);
            for (size_t j = 0; j < 33; j++) {
                targetPublicKey[j] = std::stoul(targetPublicKeyHex.substr(j * 2, 2), nullptr, 16);
            }
        } else if (!std::strcmp(argv[i], "-p") && i + 1 < argc) {
            puzzle = std::stoi(argv[++i]);
            if (puzzle <= 0) {
                std::cerr << "Invalid puzzle value. Must be greater than 0.\n";
                return 1;
            }
            puzzleProvided = true;
        } else if (!std::strcmp(argv[i], "-r") && i + 1 < argc) {
            std::string range = argv[++i];
            size_t colonPos = range.find(':');
            if (colonPos == std::string::npos) {
                std::cerr << "Invalid range format. Expected startHex:endHex.\n";
                return 1;
            }
            rangeStartHex = range.substr(0, colonPos);
            rangeEndHex = range.substr(colonPos + 1);
            rangeProvided = true;
            puzzle = calculatePuzzleSize(rangeStartHex, rangeEndHex);
        } else if (!std::strcmp(argv[i], "-b") && i + 1 < argc) {
            g_prefixLength = std::stoi(argv[++i]);
            if (g_prefixLength <= 0 || g_prefixLength > 32) {
                std::cerr << "Invalid x-coordinate prefix length. Must be between 1 and 32.\n";
                return 1;
            }
        } else if (!std::strcmp(argv[i], "-t") && i + 1 < argc) {
            numCPUs = std::stoi(argv[++i]);
            if (numCPUs <= 0) {
                std::cerr << "Invalid number of threads. Must be greater than 0.\n";
                return 1;
            }
        } else {
            std::cerr << "Unknown parameter: " << argv[i] << "\n";
            printUsage(argv[0]);
            return 1;
        }
    }

    if (!publicKeyProvided || (!rangeProvided && !puzzleProvided)) {
        std::cerr << "Both -k and (-p or -r) are required!\n";
        printUsage(argv[0]);
        return 1;
    }

    if (puzzleProvided) {
        Int one;
        one.SetBase10(const_cast<char *>("1"));
        minKey = one;
        minKey.ShiftL(puzzle - 1);
        maxKey = one;
        maxKey.ShiftL(puzzle);
        maxKey.Sub(&one);

        rangeStartHex = intToHex(minKey);
        rangeEndHex = intToHex(maxKey);
    } else if (rangeProvided) {
        minKey = hexToInt(rangeStartHex);
        maxKey = hexToInt(rangeEndHex);
    }

    bool matchFound = false;

    auto rangeStart = hexToBigNum(rangeStartHex);
    auto rangeEnd = hexToBigNum(rangeEndHex);

    bool validRange = false;
    if (rangeStart.size() < rangeEnd.size()) {
        validRange = true;
    } else if (rangeStart.size() > rangeEnd.size()) {
        validRange = false;
    } else {
        validRange = true;
        for (int i = (int)rangeStart.size() - 1; i >= 0; --i) {
            if (rangeStart[i] < rangeEnd[i]) {
                break;
            } else if (rangeStart[i] > rangeEnd[i]) {
                validRange = false;
                break;
            }
        }
    }
    if (!validRange) {
        std::cerr << "Range start must be less than range end.\n";
        return 1;
    }

    puzzle = calculatePuzzleSize(rangeStartHex, rangeEndHex);

    auto rangeSize = bigNumSubtract(rangeEnd, rangeStart);
    rangeSize = bigNumAdd(rangeSize, singleElementVector(1ULL));

    const std::string rangeSizeHex = bigNumToHex(rangeSize);
    const long double totalRangeLD = hexStrToLongDouble(rangeSizeHex);

    auto [chunkSize, remainder] = bigNumDivide(rangeSize, (uint64_t)numCPUs);
    g_threadRanges.resize(numCPUs);

    std::vector<uint64_t> currentStart = rangeStart;
    for (int t = 0; t < numCPUs; t++) {
        auto currentEnd = bigNumAdd(currentStart, chunkSize);
        if (t < (int)remainder) {
            currentEnd = bigNumAdd(currentEnd, singleElementVector(1ULL));
        }
        currentEnd = bigNumSubtract(currentEnd, singleElementVector(1ULL));

        g_threadRanges[t].startHex = bigNumToHex(currentStart);
        g_threadRanges[t].endHex = bigNumToHex(currentEnd);

        currentStart = bigNumAdd(currentEnd, singleElementVector(1ULL));
    }
    const std::string displayRange = g_threadRanges.front().startHex + ":" + g_threadRanges.back().endHex;

    unsigned long long globalComparedCount = 0ULL;
    double globalElapsedTime = 0.0;
    double mkeysPerSec = 0.0;

    const auto tStart = std::chrono::high_resolution_clock::now();
    auto lastStatusTime = tStart;

    std::string foundPrivateKeyHex;
    std::string foundPublicKeyHex;

    Int one;
    one.SetBase10(const_cast<char *>("1"));
    Int rangeSizeInt = maxKey;
    rangeSizeInt.Sub(&minKey);

    Secp256K1 secp;
    secp.Init();

#pragma omp parallel num_threads(numCPUs) \
    shared(globalComparedCount, globalElapsedTime, mkeysPerSec, matchFound, \
           foundPrivateKeyHex, foundPublicKeyHex, lastStatusTime)
{
        const int threadId = omp_get_thread_num();
        Xoshiro256plus rng(std::random_device{}() + threadId);
        Int privateKey = hexToInt(g_threadRanges[threadId].startHex);
        const Int threadRangeEnd = hexToInt(g_threadRanges[threadId].endHex);

        std::vector<Point> plusPoints(POINTS_BATCH_SIZE);
        std::vector<Point> minusPoints(POINTS_BATCH_SIZE);
        for (int i = 0; i < POINTS_BATCH_SIZE; i++) {
            Int tmp; tmp.SetInt32(i);
            Point p = secp.ComputePublicKey(&tmp); 
            plusPoints[i] = p;
            p.y.ModNeg();
            minusPoints[i] = p;
        }

        std::vector<Int> deltaX(POINTS_BATCH_SIZE);
        IntGroup modGroup(POINTS_BATCH_SIZE);

        const int fullBatchSize = 2 * POINTS_BATCH_SIZE;
        std::vector<Int> pointBatchX(fullBatchSize);
        std::vector<Int> pointBatchY(fullBatchSize);

        alignas(32) uint8_t localXCoords[fullBatchSize][32];
        int localBatchCount = 0;
        int pointIndices[fullBatchSize];

        unsigned long long localComparedCount = 0ULL;

        while (true) {
            privateKey = generateRandomPrivateKey(minKey, maxKey, rng);

            Int currentBatchKey;
            currentBatchKey.Set(&privateKey);
            Point startPoint = secp.ComputePublicKey(&currentBatchKey);

            Int startPointX, startPointY, startPointXNeg;
            startPointX.Set(&startPoint.x);
            startPointY.Set(&startPoint.y);
            startPointXNeg.Set(&startPointX);
            startPointXNeg.ModNeg();

            for (int i = 0; i < POINTS_BATCH_SIZE; i += 4) {
                deltaX[i].ModSub(&plusPoints[i].x, &startPointX);
                deltaX[i+1].ModSub(&plusPoints[i+1].x, &startPointX);
                deltaX[i+2].ModSub(&plusPoints[i+2].x, &startPointX);
                deltaX[i+3].ModSub(&plusPoints[i+3].x, &startPointX);
            }
            modGroup.Set(deltaX.data());
            modGroup.ModInv();

            for (int i = 0; i < POINTS_BATCH_SIZE; i++) {
                Int deltaY;
                deltaY.ModSub(&plusPoints[i].y, &startPointY);

                Int slope;
                slope.ModMulK1(&deltaY, &deltaX[i]);

                Int slopeSq;
                slopeSq.ModSquareK1(&slope);

                pointBatchX[i].Set(&startPointXNeg);
                pointBatchX[i].ModAdd(&slopeSq);
                pointBatchX[i].ModSub(&plusPoints[i].x);

                Int diffX;
                diffX.Set(&startPointX);
                diffX.ModSub(&pointBatchX[i]);
                diffX.ModMulK1(&slope);

                pointBatchY[i].Set(&startPointY);
                pointBatchY[i].ModNeg();
                pointBatchY[i].ModAdd(&diffX);
            }

            for (int i = 0; i < POINTS_BATCH_SIZE; i++) {
                Int deltaY;
                deltaY.ModSub(&minusPoints[i].y, &startPointY);

                Int slope;
                slope.ModMulK1(&deltaY, &deltaX[i]);

                Int slopeSq;
                slopeSq.ModSquareK1(&slope);

                pointBatchX[POINTS_BATCH_SIZE + i].Set(&startPointXNeg);
                pointBatchX[POINTS_BATCH_SIZE + i].ModAdd(&slopeSq);
                pointBatchX[POINTS_BATCH_SIZE + i].ModSub(&minusPoints[i].x);

                Int diffX;
                diffX.Set(&startPointX);
                diffX.ModSub(&pointBatchX[POINTS_BATCH_SIZE + i]);
                diffX.ModMulK1(&slope);

                pointBatchY[POINTS_BATCH_SIZE + i].Set(&startPointY);
                pointBatchY[POINTS_BATCH_SIZE + i].ModNeg();
                pointBatchY[POINTS_BATCH_SIZE + i].ModAdd(&diffX);
            }

            for (int i = 0; i < fullBatchSize; i++) {
                // The search target is x-only; avoid serializing y parity for every point.
                intToXBin(pointBatchX[i], localXCoords[localBatchCount]);
                pointIndices[localBatchCount] = i;
                localBatchCount++;

                if (localBatchCount == fullBatchSize) {
                    for (int j = 0; j < fullBatchSize; j++) {
                        bool match = true;
                        for (int b = 0; b < g_prefixLength; b++) {
                            if (localXCoords[j][b] != targetPublicKey[b + 1]) {
                                match = false;
                                break;
                            }
                        }

                    if (match) {
                        bool fullXMatch = false;
                        #pragma omp critical
                        {
                            if (!matchFound) {
                                auto tEndTime = std::chrono::high_resolution_clock::now();
                                globalElapsedTime = std::chrono::duration<double>(tEndTime - tStart).count();
                                mkeysPerSec = (double)(globalComparedCount + localComparedCount) / globalElapsedTime / 1e6;

                                Int matchingPrivateKey;
                                matchingPrivateKey.Set(&currentBatchKey);
                                int idx = pointIndices[j];
                                if (idx < 256) {
                                    Int offset; offset.SetInt32(idx);
                                    matchingPrivateKey.Add(&offset);
                                } else {
                                    Int offset; offset.SetInt32(idx - 256);
                                    matchingPrivateKey.Sub(&offset);
                                }
                                foundPrivateKeyHex = padHexTo64(intToHex(matchingPrivateKey));
                                Point matchedPoint;
                                matchedPoint.x.Set(&pointBatchX[idx]);
                                matchedPoint.y.Set(&pointBatchY[idx]);
                                foundPublicKeyHex = pointToCompressedHex(matchedPoint);

                                fullXMatch = std::memcmp(
                                    localXCoords[j], targetPublicKey.data() + 1, 32) == 0;

                                if (fullXMatch) {
                                    matchFound = true;
                                } else {
                                    std::lock_guard<std::mutex> lock(coutMutex);
                                    moveCursorTo(1, 14);
                                    clearLine();
                                    std::cout << "================== PARTIAL MATCH FOUND! ============\n";
                                    std::cout << "Prefix length : " << g_prefixLength << " bytes" << "\n";
                                    std::cout << "Private Key   : " << foundPrivateKeyHex << "\n";
                                    std::cout << "Public Key    : " << foundPublicKeyHex << "\n";
                                    std::cout << "Found PubKey  : " << foundPublicKeyHex << "\n";
                                    std::cout << "Target PubKey : " << targetPublicKeyHex << "\n";
                                    std::cout << "Matched bytes : ";
                                    for (int b = 0; b < g_prefixLength; b++) {
                                        printf("%02x", targetPublicKey[b + 1]);
                                    }
                                    std::cout << std::endl;

                                    std::ofstream partialFile("MATCH.txt", std::ios::app);
                                    if (partialFile) {
                                        partialFile << "================== PARTIAL MATCH FOUND! ============\n";
                                        partialFile << "Prefix length : " << g_prefixLength << " bytes" << "\n";
                                        partialFile << "Private Key   : " << foundPrivateKeyHex << "\n";
                                        partialFile << "Public Key    : " << foundPublicKeyHex << "\n";
                                        partialFile << "Found PubKey  : " << foundPublicKeyHex << "\n";
                                        partialFile << "Target PubKey : " << targetPublicKeyHex << "\n";
                                        partialFile << "Matched bytes : ";
                                        for (int b = 0; b < g_prefixLength; b++) {
                                            partialFile << std::setw(2) << std::setfill('0') << std::hex 
                                                        << static_cast<unsigned int>(targetPublicKey[b + 1]);
                                        }
                                        partialFile << std::endl;
                                    }
                                }
                            }
                        }
                        if (fullXMatch) {
                            #pragma omp cancel parallel
                        }
                    }
                    localComparedCount++;
                }
                localBatchCount = 0;
            }
        }

            auto now = std::chrono::high_resolution_clock::now();
            double secondsSinceStatus = std::chrono::duration<double>(now - lastStatusTime).count();
            if (secondsSinceStatus >= statusIntervalSec) {
                #pragma omp critical
                {
                    globalComparedCount += localComparedCount;
                    localComparedCount = 0ULL;
                    globalElapsedTime = std::chrono::duration<double>(now - tStart).count();
                    mkeysPerSec = (double)globalComparedCount / globalElapsedTime / 1e6;

                    printStatsBlock(numCPUs, targetPublicKeyHex, displayRange,
                                   mkeysPerSec, globalComparedCount,
                                   globalElapsedTime, puzzle);
                    lastStatusTime = now;
                }
            }

            if (matchFound) {
                break;
            }
        }

        #pragma omp atomic
        globalComparedCount += localComparedCount;
}

    auto tEnd = std::chrono::high_resolution_clock::now();
    globalElapsedTime = std::chrono::duration<double>(tEnd - tStart).count();

        if (!matchFound) {
            std::cout << "\033[14;1H";
            std::cout << "\033[K";
            std::cout << "================= NO MATCH FOUND =================";               
            mkeysPerSec = (double)globalComparedCount / globalElapsedTime / 1e6;
            std::cout << "\nNo match found in range: " << rangeStartHex << ":" << rangeEndHex << "\n";
            std::cout << "Total Checked : " << globalComparedCount << "\n";
            std::cout << "Elapsed Time  : " << formatElapsedTime(globalElapsedTime) << "\n";
            std::cout << "Speed         : " << mkeysPerSec << " Mkeys/s\n";
            std::cout.flush();
        } else {

            std::ofstream file("KEYFOUND.txt");
            if (file.is_open()) {
                TeeBuf teeBuf(std::cout.rdbuf(), file.rdbuf());
                std::ostream teeStream(&teeBuf);
                teeStream << "================== FOUND MATCH! ====================\n";
                teeStream << "Private Key   : " << foundPrivateKeyHex << "\n";
                teeStream << "Public Key    : " << foundPublicKeyHex << "\n";
                teeStream << "Total Checked : " << globalComparedCount << "\n";
                teeStream << "Elapsed Time  : " << formatElapsedTime(globalElapsedTime) << "\n";
                teeStream << "Speed         : " << mkeysPerSec << " Mkeys/s\n";
                file.close();
            } else {
                std::cerr << "Cannot open KEYFOUND.txt for writing\n";
            }
            return 0;
    }

    return 0;
}