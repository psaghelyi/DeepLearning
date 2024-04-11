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

void processDatesV1(AVLTree<Date>& nDates, const std::vector<Date>& kDates) {
    std::vector<Date>::const_iterator it = kDates.begin();
        do {
            // 1. keressük a legkissebb dátumot
            Date const *nDateElem = &nDates.minValueNode(nDates.root)->key;
            
#ifdef DEBUG
           std::cout << "N: " << nDateElem->getYear() << "-" << nDateElem->getMonth() << "-" << nDateElem->getDay() << std::endl;
#endif

            // 2. feldolgozzuk
            consumer(*nDateElem);
            // 3. töröljük a legkissebb dátumot
            nDates.root = nDates.deleteNode(nDates.root, *nDateElem);
            // 4. beszúrunk egyet a kDates-ből, amíg van
            if (it != kDates.end()) {
                nDates.root = nDates.insertNode(nDates.root, *it);
                ++it;
            }
        } while (nDates.root != nullptr);
}


// kiserleti verzio (nem mukodik)
void processDatesV2(AVLTree<Date>& nDates, const std::vector<Date>& kDates) {
    // ha a kDates-bol olyan elem jon, ami kisebb mint a nDates-ben levo legkisebb elem, 
    // akkor azt fel is hasznaljuk.
    // Kar lenne betenni az nDates-be es onnan megint kivenni ugyanazt.
    Date const *nDateElem = &nDates.minValueNode(nDates.root)->key;
    std::vector<Date>::const_iterator it = kDates.begin();
    Date const *kDateElem = nullptr;
    
    for(;;) {
        // ha van kDateElem, es kisebb mint a nDateElem, akkor felhasznaljuk
        if (kDateElem != nullptr) {
#ifdef DEBUG
            std::cout << "K: " << kDateElem->getYear() << "-" << kDateElem->getMonth() << "-" << kDateElem->getDay() << std::endl;
#endif
            consumer(*kDateElem);
            ++it;
            kDateElem = (*it < *nDateElem ? &*it : nullptr);            
            continue;
        }

        // felhasnzlajuk a legkissebb nDateElem-et
#ifdef DEBUG
        std::cout << "N: " << nDateElem->getYear() << "-" << nDateElem->getMonth() << "-" << nDateElem->getDay() << std::endl;
#endif
        consumer(*nDateElem);
        
        // töröljük
        nDates.root = nDates.deleteNode(nDates.root, *nDateElem);

        if (nDates.root == nullptr && it == kDates.end()) {
            break;
        }

        if (nDates.root != nullptr) {
            nDateElem = &nDates.minValueNode(nDates.root)->key;
        }

        // teszunk a helyere egy ujat a kDates-bol (ha nem ures)
        if (it != kDates.end()) {
            nDates.root = nDates.insertNode(nDates.root, *it);
            ++it;
        }

        

        // vesszuk a kovetkezo legkisebb nDateElem-et
        
    }
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
        processDatesV1(nDates, kDates);
        //processDatesV2(nDates, kDates);
    });

    return 0;
};

