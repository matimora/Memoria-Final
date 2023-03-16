#include "lookup_tables.h"
#include "binary_trees.h"
#include "succinct_tree.h"
#include "bit_array.h"
#include "util.h"
#include "basic.h"
#include <stdio.h>
#include <vector>
#include <bits/stdc++.h>

using namespace std;

class Leaf;
class Block;

class Node
{

public:
  int t_min;
  int t_max;
  int t_excess;
  int t_ones;
  int t_zeros;
  int t_numchunk;
  int t_level;
  Node *parent;
  Node *left;
  Node *right;
  // Leaf *x;
  Block *y;

  Node();
  ~Node();
  Node *create_struct(BIT_ARRAY *, unsigned long);
  Node *navigate(Node *, int &);
  Node *navigate2(Node *, int);
  int open(Node *, int);
  int close(Node *, int);
  void insert_left(Node *&, int);
  void insert_right(Node *&, int);
  void insert_parent(Node *&, int);
  void delete_node(Node *&, int);
  void input_value(Node *);
  void update_value(Node *);
  void get_leaves(Node *, vector<Node *> &);
  void delete_internal_nodes(Node *);
  Node *reestruct(Node *);
  void update_tree(Node *);
  int forward_search(Node *, int);
  Node *fws_node(Node *, int);
  int backward_search(Node *, int);
  Node *bws_node(Node *, int);
  void invariant(Block *);
};

class Block : public Node
{

public:
  int eti;
  vector<bool> vect;
  Node *leaf;
  Block *next;
  Block *prev;

  Block(void);
  ~Block();
};

class rmMT : public Node
{
public:
  Node *root;

  rmMT(BIT_ARRAY *, unsigned long);
  Node &get_root();
  Node *init_struct(BIT_ARRAY *, unsigned long);
  void memory_of_struct();
  void insert_l(int);
  void insert_r(int);
  void insert_p(int);
  void erase(int);
  void find_open(int);
  void find_close(int);
  void match(int);
};