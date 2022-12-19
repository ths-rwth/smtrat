#include <random>
namespace smtrat::fmplex {

class Random {
    static constexpr int seed = 0;

    static std::mt19937& generator() {
        static std::mt19937 generator(seed);
        return generator;
    }

    static int from_range(int min, int max) {
        std::uniform_int_distribution<> d(min, max);
        return d(generator());
    }

    static bool boolean() {
        return from_range(0,1) == 1;
    }

    template<typename T>
    static void shuffle (std::vector<T>& elems) {
        std::shuffle(std::begin(elems), std::end(elems), generator());
    }


};

}