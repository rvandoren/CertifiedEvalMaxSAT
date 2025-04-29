#include "proof_checker.h"
#include <iostream>

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "Usage: ./proof_check <proof_file>" << std::endl;
        return 1;
    }

    std::string filename = argv[1];
    if (!checkProofFile(filename)) {
        std::cerr << "Proof check failed" << std::endl;
        return 1;
    }

    std::cout << "Proof check successful" << std::endl;
    return 0;
}
