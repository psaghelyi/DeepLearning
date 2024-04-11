#include <iostream>
#include <assert.h>
#include "avl_tree.hpp"
#include "date.hpp"

int main() {
    AVLTree<Date> tree;

    uint64_t counter = 0;
    
    for (int i = 0; i < 1000000; ++i) {
        tree.root = tree.insertNode(tree.root, Date::randomDate(Date::create(2000, 1, 1), Date::create(2002, 12, 31)));
        ++counter;
    }

    // get the smallest date until the tree gets empty
    while (tree.root != nullptr) {
        auto node = tree.minValueNode(tree.root);
        //std::cout << node->key << " [" << node->count << "]" << std::endl;
        tree.root = tree.deleteNode(tree.root, node->key);
        --counter;
    }

    assert(counter == 0);

    return 0;
}
