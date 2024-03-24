#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <cassert>

#define MEASURE_EXECUTION_TIME 1

#include "avl_tree.hpp"
#include "consumer.hpp"
#include "stopper.hpp"


// Dátumlita betöltése fájlból
// Első két sor: N és K beolvasása
// A következő N+K dátumok beolvasása (N+K sorban)
// Az első N dátumot AVL fába szúrjuk, a maradék K-t pedig egy vektorba
void loadDatesFromFile(const std::string& filename, AVLTree<Date>& nDates, std::vector<Date>& kDates) {
    std::ifstream file(filename);

    if (!file) {
        std::cerr << "Nem sikerült megnyitni a fájlt olvasásra: " << filename << std::endl;
        return;
    }

    int N, K;
    file >> N >> K;

    kDates.reserve(K);

    for (int i = 0; i < N; ++i) {
        int year, month, day;
        file >> year >> month >> day;
        nDates.root = nDates.insertNode(nDates.root, Date(year, month, day));
    }

    for (int i = 0; i < K; ++i) {
        int year, month, day;
        file >> year >> month >> day;
        kDates.push_back(Date(year, month, day));
    }

    file.close();

    std::cout << "Fájl beolvasva: " << filename << std::endl;
}


int main(int argc, char* argv[]) {
    AVLTree<Date> nDates;
    std::vector<Date> kDates;

    measureExecutionTime("Dátumok betöltése", [&nDates, &kDates]() {
        loadDatesFromFile("dates.txt", nDates, kDates);
    });

    // C container típus hatékonyságának mérőszáma a fa magassága
    std::cout << "N max: " << pow(2, nDates.height(nDates.root)) << " (" << nDates.height(nDates.root) << ")" << std::endl;
    std::cout << "K: " << kDates.size() << std::endl;

    measureExecutionTime("Feldolgozás", [&nDates, &kDates]() {
        std::vector<Date>::const_iterator it = kDates.begin();
        do {
            // 1. keressük a legkissebb dátumot
            AVLNode<Date>* smallest = nDates.minValueNode(nDates.root);
            // 2. feldolgozzuk
            consumer(smallest->key);
            // 3. töröljük a legkissebb dátumot
            nDates.root = nDates.deleteNode(nDates.root, smallest->key);
            // 4. beszúrunk egyet a kDates-ből, amíg van
            if (it != kDates.end()) {
                nDates.root = nDates.insertNode(nDates.root, *it);
                ++it;
            }
        } while (nDates.root != nullptr);
    });

    return 0;
};

