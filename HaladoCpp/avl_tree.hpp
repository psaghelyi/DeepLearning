#ifndef AVL_TREE_HPP
#define AVL_TREE_HPP

template <typename T>
class AVLNode {
public:
    T key;
    int height;
    uint64_t count;
    AVLNode *left, *right;

    AVLNode(T d) : key(d), height(1), count(1), left(nullptr), right(nullptr) {}
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


    AVLNode<T>* insertNode(AVLNode<T>* node, T key) {
        /* 1. nulladik elem az üres fában */
        if (node == nullptr)
            return(new AVLNode<T>(key));

        if (key < node->key)
            node->left = insertNode(node->left, key);
        else if (key > node->key)
            node->right = insertNode(node->right, key);
        else // nem lehet két egyforma elem egy BST-ben
        {
            node->count++;
            return node;
        }

        /* 2. Ha szükséges, akkor kiegyensúlyozunk */
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


    AVLNode<T>* deleteNode(AVLNode<T>* root, T key) {
        // Step 1: üres fa
        if (root == nullptr)
            return root;

        if (key < root->key)
            root->left = deleteNode(root->left, key);
        else if (key > root->key)
            root->right = deleteNode(root->right, key);
        else {
            // eloszor a szamlalot csokkantjuk, ha nulla, akkor torlunk
            if (root->count-- > 1) {
                return root;
            }
            
            // egy gyerek vagy semmi
            if ((root->left == nullptr) || (root->right == nullptr)) {
                AVLNode<T>* temp = root->left ? root->left : root->right;

                // nincs gyerek
                if (temp == nullptr) {
                    temp = root;
                    root = nullptr;
                }
                else
                    *root = *temp;
                delete temp;
            }
            else {
                // két gyerek: az utód megtalálása (a jobb részfában a legkisebb elem)
                AVLNode<T>* temp = minValueNode(root->right);

                root->key = temp->key;

                // az utód törlése
                root->right = deleteNode(root->right, temp->key);
            }
        }

        // ha csak egy elem volt a fában
        if (root == nullptr)
            return root;

        // Step 2: magasság frissítése
        root->height = 1 + max(height(root->left), height(root->right));

        // Step 3: kell-e kiegyensúlyozni?
        int balance = getBalance(root);

        // bal bal eset
        if (balance > 1 && getBalance(root->left) >= 0)
            return rightRotate(root);

        // bal jobb eset
        if (balance > 1 && getBalance(root->left) < 0) {
            root->left = leftRotate(root->left);
            return rightRotate(root);
        }

        // jobb jobb eset
        if (balance < -1 && getBalance(root->right) <= 0)
            return leftRotate(root);

        // jobb bal eset
        if (balance < -1 && getBalance(root->right) > 0) {
            root->right = rightRotate(root->right);
            return leftRotate(root);
        }

        return root;
    }


    AVLNode<T>* minValueNode(AVLNode<T>* node) {
        AVLNode<T>* current = node;

        /* loop down to find the leftmost leaf */
        while (current->left != nullptr)
            current = current->left;

        return current;
    }

};


#endif
