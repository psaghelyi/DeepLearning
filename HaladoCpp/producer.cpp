#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <cstdlib> // std::rand, std::srand
#include <ctime>   // std::time


#include "date.hpp"
#include "stopper.hpp"

#define MEASURE_EXECUTION_TIME 1


int main(int argc, char* argv[]) {
    if (argc < 3 || argc > 4) {
        std::cerr << "Helytelen számú argumentum. Használat: <program> N K [fájlnév/-]" << std::endl;
        return 1; // Hiba státusz
    }

    int N = std::stoi(argv[1]);
    int K = std::stoi(argv[2]);
    std::ostream* output;
    std::ofstream file;
    if (argc == 4 && std::string(argv[3]) != "-") {
        file.open(argv[3]);
        if (!file) {
            std::cerr << "Nem sikerült megnyitni a fájlt írásra: " << argv[3] << std::endl;
            return 1;
        }
        output = &file;
    } else {
        output = &std::cout;
    }

    std::srand(std::time(nullptr)); // Véletlenszám-generátor inicializálása
    static const Date start(1976, 6, 4);
    static const Date end(2023, 4, 16);

    try {
        *output << N << '\n' << K << '\n';
        // gondoltam kipróbálom az időmérési függvényemet is
        measureExecutionTime("Véletlen dátumok generálása", [N, K, &output]() 
        {
            for (int i = 0; i < N + K; ++i) {
                Date date = Date::randomDate(start, end);
                *output << date << std::endl;
            }
        });
    } catch (const terrible_random& e) {
        std::cerr << "Hiba: " << e.what() << std::endl;
        return 1;
    }

    // close the file handle if it was a physical file
    if (output == &file) {
        file.close();
    }

    return 0;
}
