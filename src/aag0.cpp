#ifndef __PROGTEST__
#include <cstring>
#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <sstream>
#include <iomanip>
#endif


const int aag_state_machine[15][5] =
{
        {0, 0, 1, -1, 0},
        {0, 7, 8, 0, 0},
        {4, -1, 5, 4, 1},
        {6, 2, 3, 12, 1},
        {-1, 2, 3, 0, 0},
        {-1, 6, -1, 2, 0},
        {6, -1, -1, 5, 1},
        {1, 0, 9, 4, 1},
        {10, 7, 8, 12, 1},
        {0, 14, 8, 7, 0},
        {10, 0, 1, 5, 1},
        {3, -1, 5, 13, 1},
        {0, 10, 1, 2, 0},
        {-1, 11, 3, 7, 0},
        {8, 0, 9, 13, 1},
};

const int aag_start_state = 0;


bool checkString(const char * inputString) {
    auto state = aag_start_state;
    while(*inputString && state != -1) {
        if(*inputString < 'a' || 'd' < *inputString)
            return false;
        state = aag_state_machine[state][*inputString++ - 'a'];
    }
    return state != -1 && aag_state_machine[state][4];
}

#ifndef __PROGTEST__
#include <string>
int main() {
    std::string str;
    while(std::cin >> str)
        std::cout << (checkString(str.c_str()) ? "OK" : "WRONG") << std::endl;
    return 0;
}
#endif