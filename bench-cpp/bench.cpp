#include <iostream>
#include <set>
#include <random>
#include <chrono>
#include <cassert>
#include <string>

// Park Miller LCG
inline uint32_t rand(uint32_t x) {
    uint64_t product = static_cast<uint64_t>(x) * 48271;
    uint32_t next = static_cast<uint32_t>((product & 0x7FFFFFFF) + (product >> 31));
    return (next & 0x7FFFFFFF) + (next >> 31);
}

auto now() {
    return std::chrono::high_resolution_clock::now();
}

std::set<uint32_t> buildRandomTree(uint32_t seed, uint32_t count) {
    auto t1 = now();
    std::set<uint32_t> tree;

    while (count != 0) {
        seed = rand(seed);
        tree.insert(seed);
        count--;
    }

    auto t2 = now();
    std::cout << "random-insert "
              << std::chrono::duration_cast<std::chrono::nanoseconds>(t2 - t1).count()
              << std::endl;
    return tree;
}

void searchRandomTree(const std::set<uint32_t>& tree, uint32_t seed, uint32_t count) {
    auto t1 = now();
    uint32_t found = 0;

    uint32_t i = count;
    while (i != 0) {
        seed = rand(seed);
        if (tree.find(seed) != tree.end()) {
            found++;
        }
        i--;
    }

    auto t2 = now();
    assert(found == count);
    std::cout << "random-search "
              << std::chrono::duration_cast<std::chrono::nanoseconds>(t2 - t1).count()
              << std::endl;
}

void benchRandomTree(uint32_t seed, uint32_t count) {
    auto tree = buildRandomTree(seed, count);
    searchRandomTree(tree, seed, count);
}

std::set<uint32_t> buildSequentialTree(uint32_t count) {
    auto t1 = now();
    std::set<uint32_t> tree;

    while (count != 0) {
        tree.insert(count);
        count--;
    }

    auto t2 = now();
    std::cout << "sequential-insert "
              << std::chrono::duration_cast<std::chrono::nanoseconds>(t2 - t1).count()
              << std::endl;
    return tree;
}

void searchSequentialTree(const std::set<uint32_t>& tree, uint32_t count) {
    auto t1 = now();
    uint32_t found = 0;

    uint32_t i = count;
    while (i != 0) {
        if (tree.find(count) != tree.end()) {
            found++;
        }
        i--;
    }

    auto t2 = now();
    assert(found == count);
    std::cout << "sequential-search "
              << std::chrono::duration_cast<std::chrono::nanoseconds>(t2 - t1).count()
              << std::endl;
}

void benchSequentialTree(uint32_t count) {
    auto tree = buildSequentialTree(count);
    searchSequentialTree(tree, count);
}

int main(int argc, char* argv[]) {
    if (argc < 3) {
        std::cerr << "Please provide more arguments" << std::endl;
        return 1;
    }

    uint32_t seed = std::stoul(argv[1]);
    uint32_t count = std::stoul(argv[2]);

    benchRandomTree(seed, count);
    benchSequentialTree(count);

    return 0;
}
