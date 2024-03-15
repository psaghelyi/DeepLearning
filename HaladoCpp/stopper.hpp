#ifndef STOPPER_HPP
#define STOPPER_HPP

#include <functional>

/*
measureExecutionTime("Példa feladat", []() {
    // Itt implementálható a tényleges feladat, pl. egy ciklus vagy bármilyen számítás
    for(int i = 0; i < 1000000; ++i) {
        // Tegyük fel, hogy ez a feladatunk
    }
*/

template<typename Func>
void measureExecutionTime(const std::string& taskName, Func task) {
    using namespace std::chrono;

    // Feladat kezdésének ideje
    std::cerr << "A(z) \"" << taskName << "\" nevű taszk végrehajtása elkezdődött." << std::endl;

    // Feladat végrehajtása
    auto start = high_resolution_clock::now();
    task();
    auto end = high_resolution_clock::now();
    
    // Feladat befejezésének ideje
    std::cerr << "A(z) \"" << taskName << "\" nevű taszk végrehajtása befejeződött." << std::endl;

    // Eltöltött idő számítása
    auto duration = duration_cast<microseconds>(end - start).count();
    std::cerr << "A végrehajtásra eltöltött idő: " << duration << " mikroszekundum." << std::endl;
}

#endif
