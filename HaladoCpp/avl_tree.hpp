#ifndef AVL_TREE_HPP
#define AVL_TREE_HPP

template <typename T>
class AVLNode {
public:
    T key;
    int height;
    AVLNode *left, *right;

    AVLNode(T d) : key(d), height(1), left(nullptr), right(nullptr) {}
};

template <typename T>
class AVLTree {
public:
    AVLNode<T>* root = nullptr;

    int height(AVLNode<T> *N) {
        if (N == nullptr)
            return 0;
        return N->height;
    }

    int max(int a, int b) {
        return (a > b) ? a : b;
    }

    AVLNode<T>* rightRotate(AVLNode<T> *y) {
        AVLNode<T> *x = y->left;
        AVLNode<T> *T2 = x->right;

        // forgatás
        x->right = y;
        y->left = T2;

        // magasságok frissítése
        y->height = max(height(y->left), height(y->right)) + 1;
        x->height = max(height(x->left), height(x->right)) + 1;

        // új gyökér visszaadása
        return x;
    }

    AVLNode<T>* leftRotate(AVLNode<T> *x) {
        AVLNode<T> *y = x->right;
        AVLNode<T> *T2 = y->left;

        // forgatás
        y->left = x;
        x->right = T2;

        // magasságok frissítése
        x->height = max(height(x->left), height(x->right)) + 1;
        y->height = max(height(y->left), height(y->right)) + 1;

        // új gyökér visszaadása
        return y;
    }

    int getBalance(AVLNode<T> *N) {
        if (N == nullptr)
            return 0;
        return height(N->left) - height(N->right);
    }

    AVLNode<T>* maintainBalance(AVLNode<T>* node, T key) {
        /* Magasság frissítése az ősben */
        node->height = 1 + max(height(node->left), height(node->right));

        /* Ellenőrizzük, hogy szükséges-e kiegyensúlyozni */
        int balance = getBalance(node);

        // Ha igen, akkor 4 eset lehetséges 

        // Bal Bal eset
        if (balance > 1 && key < node->left->key)
            return rightRotate(node);

        // Jobb Jobb eset
        if (balance < -1 && key > node->right->key)
            return leftRotate(node);

        // Bal Jobb eset
        if (balance > 1 && key > node->left->key) {
            node->left = leftRotate(node->left);
            return rightRotate(node);
        }

        // Jobb Bal eset
        if (balance < -1 && key < node->right->key) {
            node->right = rightRotate(node->right);
            return leftRotate(node);
        }

        // ha már kiegyensúlyozott, akkor csak visszaadjuk az eredeti gyökért
        return node;
    }

    AVLNode<T>* insert(AVLNode<T>* node, T key) {
        /* 1. nulladik elem az üres fában */
        if (node == nullptr)
            return(new AVLNode<T>(key));

        if (key < node->key)
            node->left = insert(node->left, key);
        else if (key > node->key)
            node->right = insert(node->right, key);
        else // nem lehet két egyforma elem egy BST-ben
            return node;

        /* 2. Ha szükséges, akkor kiegyensúlyozunk */
        return maintainBalance(node, key);
    }

    // Helper function to delete a node with a given key
    AVLNode<T>* deleteNode(AVLNode<T>* node, T key) {
        /* 1. Üres fa esetén visszatérünk */
        if (node == nullptr)
            return node;

        if (key < node->key)
            node->left = deleteNode(node->left, key);
        else if (key > node->key)
            node->right = deleteNode(node->right, key);
        else {
            // egy vagy nulla gyerek
            if ((node->left == nullptr) || (node->right == nullptr)) {
                AVLNode<T>* temp = node->left ? node->left : node->right;

                // nulla gyerek
                if (temp == nullptr) {
                    temp = node;
                    node = nullptr;
                }
                else // egy gyerek
                    *node = *temp; // másoljuk a nem üres gyerek tartalmát
                delete temp;
            }
            else {
                // két gyerek: keressük az utódot (a jobb részfában a legkisebb)
                AVLNode<T>* temp = minValueNode(node->right);

                // másoljuk az utód adatait erre a csúcsra
                node->key = temp->key;

                // töröljük az inorder utódot
                node->right = deleteNode(node->right, temp->key);
            }
        }

        // ha csak egy csúcs volt a fában akkor visszatérünk
        if (node == nullptr)
            return node;

        /* 2. Ha szükséges, akkor kiegyensúlyozunk */
        return maintainBalance(node, key);
    }


    // Utility function to get the node with
    // the smallest key value found in that tree
    AVLNode<T>* minValueNode(AVLNode<T>* node) {
        AVLNode<T>* current = node;

        /* loop down to find the leftmost leaf */
        while (current->left != nullptr)
            current = current->left;

        return current;
    }

};

#endif
