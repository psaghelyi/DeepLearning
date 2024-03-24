#include <iostream>
#include <fstream>
#include <string>
#include <vector>

#include "avl_tree.hpp"

int main(int argc, char* argv[]) {
    AVLTree<int> tree;

    // Insert elements
    tree.root = tree.insert(tree.root, 10);
    tree.root = tree.insert(tree.root, 20);
    tree.root = tree.insert(tree.root, 5);
    tree.root = tree.insert(tree.root, 4);
    tree.root = tree.insert(tree.root, 6);

    // Traverse the teree by always getting the smallest element
    while (tree.root != nullptr) {
        AVLNode<int>* smallest = tree.minValueNode(tree.root);
        std::cout << "The smallest element is: " << smallest->key << std::endl;

        // "Soft delete" the smallest element
        tree.root = tree.deleteNode(tree.root, smallest->key);
        std::cout << "Smallest element removed." << std::endl;
    }

    return 0;
};