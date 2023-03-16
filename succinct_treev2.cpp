#include "lookup_tables.h"
#include "binary_trees.h"
#include "succinct_tree.h"
#include "class.h"
#include "bit_array.h"
#include "util.h"
#include "basic.h"
#include <vector>
#include <iostream>
#include <algorithm>
#include <iterator>
#include <stack>

using namespace std;

/* ASSUMPTIONS:
 * - s = 256 (8 bits) (Following the sdsl/libcds implementations)
 * - k = 2 (Min-max tree will be a binary tree)
 * - Each thread has to process at least one chunk with parentheses (Problem with n <= s)
 */

/**CONSTRUCTORES**/
Node::Node()
{
  t_min = 0;
  t_max = 0;
  t_excess = 0;
  t_ones = 0;
  t_numchunk = 0;
  // x = NULL;
  y = NULL;
  left = NULL;
  right = NULL;
  parent = NULL;
}
Node::~Node()
{
  // x = NULL;
  y = NULL;
  left = NULL;
  right = NULL;
  parent = NULL;
}
Block::Block()
{
  eti = 0;
  next = NULL;
  prev = NULL;
  leaf = NULL;
}
Block::~Block()
{
  next = NULL;
  prev = NULL;
  leaf = NULL;
  vect.clear();
}
rmMt *init_rmMt(unsigned long n)
{
  rmMt *st = (rmMt *)malloc(sizeof(rmMt));
  st->s = 256;                                                     // tamaño bloque
  st->c = st->s * 0.75;                                            // carga inicial del bloque
  st->k = 2;                                                       // numero de hijo
  st->n = n;                                                       // numero de parentesis
  st->num_chunks = ceil((double)n / st->c);                        //  es la cantidad de bloques
  st->height = ceil(log(st->num_chunks) / log(st->k));             // heigh = logk(num_chunks), Heigh of the min-max tree
  st->internal_nodes = (pow(st->k, st->height) - 1) / (st->k - 1); // Number of internal nodes;

  return st;
}

void print_rmMt(rmMt *st)
{
  fprintf(stderr, "Chunk size: %u\n", st->s);
  fprintf(stderr, "Arity: %u\n", st->k);
  fprintf(stderr, "Number of parentheses: %lu\n", st->n);
  fprintf(stderr, "Number of chunks (leaves): %u\n", st->num_chunks);
  fprintf(stderr, "Height: %u\n", st->height);
  fprintf(stderr, "Number of internal nodes: %u\n", st->internal_nodes);
}

/**FUNCIONES INTERNAS**/
Node *Node::create_struct(BIT_ARRAY *bit_array, unsigned long n)
{
  vector<bool> a;
  rmMt *st = init_rmMt(n);
  st->bit_array = bit_array;

  if (st->s >= n)
  {
    fprintf(stderr, "Error: Input size is smaller or equal than the chunk size (input size: %lu, chunk size: %u)\n", n, st->s);
    exit(0);
  }

  /*
   * STEP 2: Computation of arrays e', m', M' and n'
   */
  /*
  /*
   * STEP 2.1: Each thread computes the prefix computation in a range of the bit array
   */
  vector<Block *> bloques_aux;
  unsigned int chunk = 0;                // contador de bloques
  unsigned chunk_limit = st->num_chunks; // It is possible that the last thread process less chunks
  // Node *arrL[chunk_limit];               // ELIMINE UN *
  vector<Node *> arrL;
  for (chunk = 0; chunk < chunk_limit; chunk++)
  {
    Block *bloque = new Block();
    Node *leave = new Node(); // CAMBIE DE NODE A LEAF
    bloque->eti = chunk;
    depth_t min = 0, max = 0, partial_excess = 0, ones = 0, numchunk = 0, zeros = 0;
    unsigned int llimit = 0, ulimit = 0;
    unsigned int global_chunk = chunk; // se posiciona en el bloque que va ciclando

    if (st->num_chunks - 1 < global_chunk)
    {
      llimit = 0;
      ulimit = 0;
    }
    else
    {
      llimit = st->c * chunk;
      ulimit = llimit + st->c;
      if (st->n < st->c)
        ulimit = n;
      if (ulimit > st->n)
        ulimit = st->n;
    }
    for (int symbol = llimit; symbol < ulimit; symbol++)
    {
      bool aux1 = (bool)bit_array_get_bit(bit_array, symbol);

      a.push_back(aux1);

      ++numchunk;
      // Excess computation
      if (bit_array_get_bit(bit_array, symbol) == 0)
      {
        --partial_excess;
        ++zeros;
      }
      else
      {
        ++partial_excess;
        ++ones;
      }
      // Minimum computation
      if (symbol == llimit)
      {
        min = partial_excess; // By default the minimum value is the first excess value
        max = partial_excess; // By default the maximum value is the first excess value
      }
      else
      {
        if (partial_excess < min)
        {
          min = partial_excess;
        }
        if (partial_excess > max)
        {
          max = partial_excess;
        }
      }
    }
    copy(a.begin(), a.end(), back_inserter(bloque->vect));
    a.clear();
    bloques_aux.push_back(bloque);
    leave->y = bloque;
    bloque->leaf = leave;
    leave->parent = NULL;

    if (global_chunk < st->num_chunks)
    {
      leave->t_excess = partial_excess;
      leave->t_min = min;
      leave->t_max = max;
      leave->t_ones = ones;
      leave->t_numchunk = numchunk;
    }
    arrL.push_back(leave);
    arrL[chunk]->t_excess = partial_excess;
    arrL[chunk]->t_max = max;
    arrL[chunk]->t_min = min;
    arrL[chunk]->t_ones = ones;
    arrL[chunk]->t_zeros = zeros;
    arrL[chunk]->t_numchunk = numchunk;
    arrL[chunk]->y = bloque;
  }
  /**ENLAZA LOS BLOQUES**/
  int z = arrL.size();
  for (int i = 0; i < bloques_aux.size(); i++)
  {
    if (i == 0)
    {
      bloques_aux[i]->prev = NULL;
      bloques_aux[i]->next = bloques_aux[i + 1];
    }
    if (i > 0 && i < (bloques_aux.size() - 1))
    {
      bloques_aux[i]->prev = bloques_aux[i - 1];
      bloques_aux[i]->next = bloques_aux[i + 1];
    }

    if ((i + 1) == bloques_aux.size())
    {
      bloques_aux[i]->next = NULL;
      bloques_aux[i]->prev = bloques_aux[i - 1];
    }
    if (bloques_aux[i]->vect.size() < 128)
    {
      invariant(bloques_aux[i]);
    }
  }
  vector<Node *> arr;
  for (int i = 0; i < (2 * chunk_limit - 1); i++)
  {
    if (i < (chunk_limit - 1))
    {
      Node *aux = new Node();
      arr.push_back(aux);
      arr[i]->t_excess = 0;
      arr[i]->t_max = 0;
      arr[i]->t_min = 0;
      arr[i]->t_ones = 0;
      arr[i]->t_zeros = 0;
      arr[i]->t_numchunk = 0;
      if (i == 0 && arr[0] != NULL)
      {
        arr[0]->left = NULL;
        arr[0]->right = NULL;
        arr[0]->parent = NULL;
        arr[0]->t_level = i;
      }
      else if (arr[i] != NULL)
      {
        if (arr[(i - 1) / 2] != NULL)
        {
          arr[i]->parent = arr[(i - 1) / 2];
          arr[i]->t_level = arr[(i - 1) / 2]->t_level + 1;
          arr[i]->left = NULL;
          arr[i]->right = NULL;
          if (i % 2 == 1)
          {
            arr[(i - 1) / 2]->left = arr[i];
          }
          else
          {
            arr[(i - 1) / 2]->right = arr[i];
          }
        }
      }
    }
  }
  vector<Node *> last_internal;
  get_leaves(arr[0], last_internal);
  Node *impar = new Node();
  int node_size = 0;
  int internal_size = 0;
  /**actualizar valores del ultimo nivel de los nodos internos del arbol**/
  while (node_size < arrL.size() && internal_size < last_internal.size())
  {
    last_internal[internal_size]->left = arrL[node_size];
    last_internal[internal_size]->right = arrL[node_size + 1];
    arrL[node_size]->parent = last_internal[internal_size];
    arrL[node_size + 1]->parent = last_internal[internal_size];
    arrL[node_size]->t_level = last_internal[internal_size]->t_level + 1;
    arrL[node_size + 1]->t_level = last_internal[internal_size]->t_level + 1;
    if (arrL[node_size]->t_min < arrL[node_size + 1]->t_min + arrL[node_size]->t_excess)
    {
      last_internal[internal_size]->t_min = arrL[node_size]->t_min;
    }
    else
    {
      last_internal[internal_size]->t_min = arrL[node_size + 1]->t_min + arrL[node_size]->t_excess;
    }
    if (arrL[node_size]->t_max > arrL[node_size + 1]->t_max + arrL[node_size]->t_excess)
    {
      last_internal[internal_size]->t_max = arrL[node_size]->t_max;
    }
    else
    {
      last_internal[internal_size]->t_max = arrL[node_size + 1]->t_max + arrL[node_size]->t_excess;
    }
    last_internal[internal_size]->t_excess = arrL[node_size]->t_excess + arrL[node_size + 1]->t_excess;
    last_internal[internal_size]->t_ones = arrL[node_size]->t_ones + arrL[node_size + 1]->t_ones;
    last_internal[internal_size]->t_zeros = arrL[node_size]->t_zeros + arrL[node_size + 1]->t_zeros;
    last_internal[internal_size]->t_numchunk = arrL[node_size]->t_numchunk + arrL[node_size + 1]->t_numchunk;
    /**añadir imparidad**/
    if (last_internal[internal_size]->parent->right == NULL)
    {
      impar = last_internal[internal_size]->parent;
      impar->right = arrL[node_size + 2];
      arrL[node_size + 2]->parent = impar;
      arrL[node_size + 2]->t_level = impar->t_level + 1;
      arr.push_back(arrL[node_size + 2]);
      node_size++;
    }
    node_size = node_size + 2;
    internal_size++;
  }

  /**actulizar los demas niveles del arbol**/
  for (int i = arr.size() - 1; i > 0; i = i - 2)
  {
    if (arr[i - 1]->t_min < arr[i]->t_min + arr[i - 1]->t_excess)
    {

      arr[(i - 1) / 2]->t_min = arr[i - 1]->t_min;
    }
    else
    {
      arr[(i - 1) / 2]->t_min = arr[i]->t_min + arr[i - 1]->t_excess;
    }
    if (arr[i - 1]->t_max > arr[i]->t_max + arr[i - 1]->t_excess)
    {
      arr[(i - 1) / 2]->t_max = arr[i - 1]->t_max;
    }
    else
    {
      arr[(i - 1) / 2]->t_max = arr[i]->t_max + arr[i - 1]->t_excess;
    }
    arr[(i - 1) / 2]->t_ones = arr[i - 1]->t_ones + arr[i]->t_ones;
    arr[(i - 1) / 2]->t_zeros = arr[i - 1]->t_zeros + arr[i]->t_zeros;
    arr[(i - 1) / 2]->t_excess = arr[i - 1]->t_excess + arr[i]->t_excess;
    arr[(i - 1) / 2]->t_numchunk = arr[i - 1]->t_numchunk + arr[i]->t_numchunk;
  }
  /*
   * STEP 3: Computation of all universal tables
   */

  T = create_lookup_tables();
  return arr[0];
}
/**Busqueda del nodo que contiene el i parentesis de apertura**/
Node *Node::navigate(Node *node, int &a)
{
  int aux = 0;
  Node *aux_node = node;
  while (aux_node->y == NULL)
  {
    if (aux_node->left != NULL && aux_node->left->t_ones >= a)
    {
      aux_node = aux_node->left;
    }
    else
    {
      if (aux_node->left == NULL)
      {
        aux_node = aux_node->right;
      }
      else
      {
        a = a - aux_node->left->t_ones;
        aux_node = aux_node->right;
      }
    }
  }

  return aux_node;
}
/**Busqueda del nodo que contiene el i parentesis de cierre**/
Node *Node::navigate2(Node *node, int a)
{
  Node *aux_node = node;
  while (aux_node->y == NULL)
  {
    if (aux_node->left->t_zeros >= a)
    {
      aux_node = aux_node->left;
    }
    else
    {
      a = a - aux_node->left->t_zeros;
      aux_node = aux_node->right;
    }
  }
  return aux_node;
}
/**Busqueda que encuentra la posicion exacta del parentesis de cierre en el bloque**/
int Node::close(Node *node, int a)
{
  int aux = 0;
  Node *aux_node = node;
  while (aux_node->y == NULL)
  {
    if (aux_node->left->t_zeros >= a)
    {
      aux_node = aux_node->left;
    }
    else
    {
      a = a - aux_node->left->t_zeros;
      aux_node = aux_node->right;
    }
  }
  for (int i = 0; i < aux_node->y->vect.size(); i++)
  {

    if (aux_node->y->vect[i] == 0)
    {
      aux++;
    }
    if (aux == a)
    {
      return i;
    }
  }
  return -1;
}
Node *Node::bws_node(Node *node, int a)
{
  return NULL;
}
/**Busqueda que encuentra la posicion del parentesis de apertura apartir de un parentesis de cierre**/
int Node::backward_search(Node *node, int pos)
{
  Block *search = node->y;
  int p_e = 0;
  int d_prime = 0;
  Node *aux = node;
  /**for busca en el bloque el parentesis de apertura**/
  for (int i = pos; i >= 0; i--)
  {
    if (search->vect[i] == 0)
    {
      d_prime++;
    }
    else
    {
      d_prime--;
    }
    if (p_e == d_prime)
    {
      return i;
    }
  }
  /**bucle que sube**/
  while (aux != NULL)
  {
    if (aux->parent == NULL)
    {
      break;
    }
    /**Vengo de un nodo derecho**/
    if (aux == aux->parent->right)
    {
      aux = aux->parent->left;
      if (d_prime - aux->t_excess + aux->t_min <= 1)
      {
        if (aux->y != NULL)
        {
          for (int i = aux->y->vect.size() - 1; i >= 0; i--)
          {
            if (aux->y->vect[i] == 0)
            {
              d_prime++;
            }
            else
            {
              d_prime--;
            }
            if (p_e == d_prime)
            {
              return i;
            }
          }
        }
        /**encuentra pero no es hoja**/
        else
        {
          break;
        }
      }
      else
      {
        d_prime = d_prime - aux->t_excess;
      }
    }
    else
    {
      aux = aux->parent;
    }
  }
  /**bucle que baja**/
  while (aux->y == NULL)
  {
    /**caso esta en hijo derecho**/
    if (d_prime + aux->right->t_min - aux->right->t_excess <= 0)
    {
      aux = aux->right;
      if (aux->y != NULL)
      {
        for (int i = aux->y->vect.size() - 1; i >= 0; i--)
        {
          if (aux->y->vect[i] == 0)
          {
            d_prime++;
          }
          else
          {
            d_prime--;
          }
          if (p_e == d_prime)
          {
            return i;
          }
        }
      }
    }
    else
    {
      d_prime = d_prime - aux->right->t_excess;
      aux = aux->left;
      if (aux->y != NULL)
      {
        for (int i = aux->y->vect.size() - 1; i >= 0; i--)
        {
          if (aux->y->vect[i] == 0)
          {
            d_prime++;
          }
          else
          {
            d_prime--;
          }
          if (p_e == d_prime)
          {
            return i;
          }
        }
      }
    }
  }
  return -1;
}
/**Busqueda que encuentra la posicion exacta del parentesis de apertura en el bloque**/
int Node::open(Node *node, int a)
{
  int aux = 0;
  Node *aux_node = node;
  /*while (aux_node->y == NULL)
  {
    if (aux_node->left != NULL && aux_node->left->t_ones >= a)
    {
      aux_node = aux_node->left;
    }
    else
    {
      if (aux_node->left == NULL)
      {
        aux_node = aux_node->right;
      }
      else
      {
        if (aux_node->t_numchunk == aux_node->right->t_numchunk)
        {
          aux_node = aux_node->right;
        }
        else
        {
          a = a - aux_node->left->t_ones;
          aux_node = aux_node->right;
        }
      }
    }
  }
*/
  for (int i = 0; i < aux_node->y->vect.size(); i++)
  {
    if (aux == a && aux_node->y->vect[i] == 1)
    {
      return i;
    }
    if (aux_node->y->vect[i] == 1)
    {
      aux++;
    }
    if (aux == a && aux_node->y->vect[i] == 1 && i != 0)
    {
      return i;
    }
  }
  return -1;
}
/**Inserción de un nodo hijo izquierdo**/
void Node::insert_left(Node *&p, int a)
{
  Node *leaf = leaf->navigate(p, a);
  int pos = open(leaf, a);
  Block *aux = leaf->y;

  if (aux->vect.size() < 256) // 256 == tamaño del bloque.
  {

    aux->vect.insert(aux->vect.begin() + (pos + 1), 1);
    aux->vect.insert(aux->vect.begin() + (pos + 2), 0);
    input_value(leaf);
    update_value(leaf);
  }
  else
  {
    Node *nleft = new Node();
    Node *nright = new Node();
    Block *lblock = new Block();
    Block *rblock = new Block();
    // ENLACES NODO LEAF CON SUS NUEVOS HIJOS
    leaf->left = nleft;
    leaf->right = nright;
    // enlace hijo izquierdo con su padre
    nleft->parent = leaf;
    nleft->t_level = leaf->t_level + 1;
    // enlace hijo derecho con su padre
    nright->parent = leaf;
    nright->t_level = leaf->t_level + 1;
    // enlace de los nodos hacia sus bloques bloques
    nleft->y = lblock;
    nright->y = rblock;
    // enlace de los bloques hacia sus nodos
    lblock->leaf = nleft;
    rblock->leaf = nright;
    // enlaace entre los bloques
    lblock->next = rblock;
    rblock->prev = lblock;
    vector<bool> a;
    vector<bool> b;
    for (int i = 0; i < leaf->y->vect.size(); i++)
    {
      if (i < (leaf->y->vect.size()) / 2)
      {
        a.push_back(leaf->y->vect[i]);
      }
      else
      {
        b.push_back(leaf->y->vect[i]);
      }
    }
    copy(a.begin(), a.end(), back_inserter(lblock->vect));
    copy(b.begin(), b.end(), back_inserter(rblock->vect));
    a.clear();
    b.clear();
    Block *auxl = leaf->y->prev;
    Block *auxr = leaf->y->next;
    leaf->y = NULL;
    delete aux;

    // enlazo con los bloques creados
    lblock->prev = auxl;
    rblock->next = auxr;
    if (pos < lblock->vect.size())
    {
      lblock->vect.insert(lblock->vect.begin() + (pos + 1), 1);
      lblock->vect.insert(lblock->vect.begin() + (pos + 2), 0);
      input_value(nleft);
      input_value(nright);
      update_value(nleft);
      update_value(nright);
      int height = nleft->t_level;
      Node *balanced = nleft;
      int i = 0; // check  tree balanced
      while (i < 3)
      {
        if (balanced == balanced->parent->left)
        {
          balanced = balanced->parent->right;
          if (height - balanced->t_level >= 2 && balanced->y != NULL)
          {
            p = reestruct(*&p);
            i++;
          }
          else
          {
            balanced = balanced->parent;
            i++;
          }
        }
        else
        {
          balanced = balanced->parent->left;
          if (height - balanced->t_level >= 2 && balanced->y != NULL)
          {
            p = reestruct(*&p);
            i++;
          }
          else
          {
            balanced = balanced->parent;
            i++;
          }
        }
      }
    }
    else
    {
      rblock->vect.insert(rblock->vect.begin() + ((pos - lblock->vect.size()) + 1), 1);
      rblock->vect.insert(rblock->vect.begin() + ((pos - lblock->vect.size()) + 2), 0);
      input_value(nleft);
      input_value(nright);
      update_value(nleft);
      update_value(nright);
      int height = nright->t_level;
      Node *balanced = nright->parent;
      int i = 0; // check  tree balanced
      while (i < 3)
      {
        if (balanced == balanced->parent->left)
        {
          balanced = balanced->parent->right;
          if (height - balanced->t_level >= 2 && balanced->y != NULL)
          {
            p = reestruct(*&p);
            i++;
          }
          else
          {
            balanced = balanced->parent;
            i++;
          }
        }
        else
        {
          balanced = balanced->parent->left;
          if (height - balanced->t_level >= 2 && balanced->y != NULL)
          {
            p = reestruct(*&p);
            i++;
          }
          else
          {
            balanced = balanced->parent;
            i++;
          }
        }
      }
    }
  }
}
/**Inserción de un nodo hijo derecho**/
void Node::insert_right(Node *&p, int a)

{
  Node *leaf = leaf->navigate(p, a);
  int pos = leaf->open(leaf, a);
  Node *leaf_right = leaf_right->fws_node(leaf, pos);
  int close = leaf_right->forward_search(leaf, pos);
  Node *leaf_aux = leaf_right;
  Block *aux = leaf_right->y;

  if (aux->vect.size() < 256) // 256 == tamaño del bloque.
  {
    if (close == 0)
    {
      aux->vect.insert(aux->vect.begin(), 0);
      aux->vect.insert(aux->vect.begin(), 1);
      input_value(leaf_aux);
      update_value(leaf_aux);
    }
    else if (close == 1)
    {
      aux->vect.insert(aux->vect.begin() + 1, 0);
      aux->vect.insert(aux->vect.begin() + 1, 1);
      input_value(leaf_aux);
      update_value(leaf_aux);
    }
    else
    {
      aux->vect.insert(aux->vect.begin() + (close - 1), 0);
      aux->vect.insert(aux->vect.begin() + (close - 2), 1);
      input_value(leaf_aux);
      update_value(leaf_aux);
    }
  }
  else
  {
    Node *nleft = new Node();
    Node *nright = new Node();
    Block *lblock = new Block();
    Block *rblock = new Block();
    // ENLACES NODO LEAF CON SUS NUEVOS HIJOS
    leaf_aux->left = nleft;
    leaf_aux->right = nright;
    // enlace hijo izquierdo con su padre
    nleft->parent = leaf_aux;
    // enlace hijo derecho con su padre
    nright->parent = leaf_aux;
    // enlace de los nodos hacia sus bloques bloques
    nleft->y = lblock;
    nright->y = rblock;
    // enlace de los bloques hacia sus nodos
    lblock->leaf = nleft;
    rblock->leaf = nright;
    // enlaace entre los bloques
    lblock->next = rblock;
    rblock->prev = lblock;
    vector<bool> a;
    vector<bool> b;
    for (int i = 0; i < leaf_aux->y->vect.size(); i++)
    {
      if (i < (leaf_aux->y->vect.size()) / 2)
      {
        a.push_back(leaf_aux->y->vect[i]);
      }
      else
      {
        b.push_back(leaf_aux->y->vect[i]);
      }
    }
    copy(a.begin(), a.end(), back_inserter(lblock->vect));
    copy(b.begin(), b.end(), back_inserter(rblock->vect));
    a.clear();
    b.clear();
    Block *auxl = leaf_aux->y->prev;
    Block *auxr = leaf_aux->y->next;
    leaf_aux->y = NULL;

    // enlazo con los bloques creados
    if (auxr != NULL)
    {
      auxr->prev = rblock;
    }
    rblock->next = auxr;
    delete aux;
    if (close < lblock->vect.size())
    {
      if (close == 0)
      {
        lblock->vect.insert(lblock->vect.begin(), 0);
        lblock->vect.insert(lblock->vect.begin(), 1);
        nleft->input_value(nleft);
        nright->input_value(nright);
        nleft->update_value(nleft);
        nright->update_value(nright);
      }
      else if (close == 1)
      {
        lblock->vect.insert(lblock->vect.begin() + 1, 0);
        lblock->vect.insert(lblock->vect.begin() + 1, 1);
        nleft->input_value(nleft);
        nright->input_value(nright);
        nleft->update_value(nleft);
        nright->update_value(nright);
      }
      else
      {
        lblock->vect.insert(lblock->vect.begin() + (close - 1), 0);
        lblock->vect.insert(lblock->vect.begin() + (close - 2), 1);
        nleft->input_value(nleft);
        nright->input_value(nright);
        nleft->update_value(nleft);
        nright->update_value(nright);
      }
      int height = nleft->t_level;
      Node *balanced = nleft;
      int i = 0; // check  tree balanced
      while (i < 3)
      {
        if (balanced == balanced->parent->left)
        {
          balanced = balanced->parent->right;
          if (height - balanced->t_level >= 2 && balanced->y != NULL)
          {
            p = reestruct(*&p);
            i++;
          }
          else
          {
            balanced = balanced->parent;
            i++;
          }
        }
        else
        {
          balanced = balanced->parent->left;
          if (height - balanced->t_level >= 2 && balanced->y != NULL)
          {
            p = reestruct(*&p);
            i++;
          }
          else
          {
            balanced = balanced->parent;
            i++;
          }
        }
      }
    }
    else
    {
      if (close - lblock->vect.size() == 0)
      {
        rblock->vect.insert(rblock->vect.begin(), 0);
        rblock->vect.insert(rblock->vect.begin(), 1);
        nleft->input_value(nleft);
        nright->input_value(nright);
        nleft->update_value(nleft);
        nright->update_value(nright);
      }
      else if (close - lblock->vect.size() == 1)
      {
        rblock->vect.insert(rblock->vect.begin() + 1, 0);
        rblock->vect.insert(rblock->vect.begin() + 1, 1);
        nleft->input_value(nleft);
        nright->input_value(nright);
        nleft->update_value(nleft);
        nright->update_value(nright);
      }
      else
      {
        rblock->vect.insert(rblock->vect.begin() + ((close - lblock->vect.size()) - 1), 0);
        rblock->vect.insert(rblock->vect.begin() + ((close - lblock->vect.size()) - 2), 1);
        nleft->input_value(nleft);
        nright->input_value(nright);
        nleft->update_value(nleft);
        nright->update_value(nright);
      }
      int height = nleft->t_level;
      Node *balanced = nleft;
      int i = 0; // check  tree balanced
      while (i < 3)
      {
        if (balanced == balanced->parent->left)
        {
          balanced = balanced->parent->right;
          if (height - balanced->t_level >= 2 && balanced->y != NULL)
          {
            p = reestruct(*&p);
            i++;
          }
          else
          {
            balanced = balanced->parent;
            i++;
          }
        }
        else
        {
          balanced = balanced->parent->left;
          if (height - balanced->t_level >= 2 && balanced->y != NULL)
          {
            p = reestruct(*&p);
            i++;
          }
          else
          {
            balanced = balanced->parent;
            i++;
          }
        }
      }
    }
  }
}
/**Inserción de un nodo padre**/
void Node::insert_parent(Node *&p, int a)
{
  Node *leaf = leaf->navigate(p, a);
  Node *leaf_left = leaf;
  Block *aux_leaf = leaf->y;
  int pos = leaf->open(leaf, a);
  Node *leaf_right = leaf_right->fws_node(leaf, pos);
  int close = leaf_right->forward_search(leaf, pos);
  Node *leaf_aux = leaf_right;
  Block *aux = leaf_right->y;
  /**BLOQUES IGUALES**/
  if (aux_leaf == aux)
  {
    if (aux_leaf->vect.size() < 256)
    {
      if (pos == 0)
      {
        aux_leaf->vect.insert(aux_leaf->vect.begin() + pos, 1);
        aux_leaf->vect.insert(aux_leaf->vect.begin() + (close + 2), 0);
        input_value(leaf);
        update_value(leaf);
      }
      else
      {
        aux_leaf->vect.insert(aux_leaf->vect.begin() + (pos - 1), 1);
        aux_leaf->vect.insert(aux_leaf->vect.begin() + (close + 2), 0);
        input_value(leaf);
        update_value(leaf);
      }
    }
    else
    {
      Node *nleft = new Node();
      Node *nright = new Node();
      Block *lblock = new Block();
      Block *rblock = new Block();
      // ENLACES NODO LEAF CON SUS NUEVOS HIJOS
      leaf->left = nleft;
      leaf->right = nright;
      // enlace hijo izquierdo con su padre
      nleft->parent = leaf;
      // enlace hijo derecho con su padre
      nright->parent = leaf;
      // enlace de los nodos hacia sus bloques bloques
      nleft->y = lblock;
      nright->y = rblock;
      // enlace de los bloques hacia sus nodos
      lblock->leaf = nleft;
      rblock->leaf = nright;
      // enlaace entre los bloques
      lblock->next = rblock;
      rblock->prev = lblock;
      vector<bool> a;
      vector<bool> b;
      for (int i = 0; i < leaf->y->vect.size(); i++)
      {
        if (i < (leaf->y->vect.size()) / 2)
        {
          a.push_back(leaf->y->vect[i]);
        }
        else
        {
          b.push_back(leaf->y->vect[i]);
        }
      }
      copy(a.begin(), a.end(), back_inserter(lblock->vect));
      copy(b.begin(), b.end(), back_inserter(rblock->vect));
      a.clear();
      b.clear();
      Block *auxl = leaf->y->prev;
      Block *auxr = leaf->y->next;
      leaf->y = NULL;
      // enlazo con los bloques creados
      lblock->prev = auxl;
      rblock->next = auxr;
      delete aux_leaf;
      /**cuando ambas posiciones se encuentran en el bloque izquierdo**/
      if (pos < lblock->vect.size() && close < lblock->vect.size())
      {
        if (pos == 0)
        {
          lblock->vect.insert(lblock->vect.begin() + pos, 1);
          lblock->vect.insert(lblock->vect.begin() + (close + 2), 0);
          input_value(nleft);
          input_value(nright);
          update_value(nleft);
          update_value(nright);
        }
        else
        {
          lblock->vect.insert(lblock->vect.begin() + (pos - 1), 1);
          lblock->vect.insert(lblock->vect.begin() + (close + 2), 0);
          input_value(nleft);
          input_value(nright);
          update_value(nleft);
          update_value(nright);
        }
        int height = nleft->t_level;
        Node *balanced = nleft->parent;
        int i = 0; // check  tree balanced
        while (i < 3)
        {
          if (balanced == balanced->parent->left)
          {
            balanced = balanced->parent->right;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
          else
          {
            balanced = balanced->parent->left;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
        }
      }
      /**cuando open se encuentra en el bloque izquierdo y close en el bloque derecho**/
      else if (pos < lblock->vect.size() && close > lblock->vect.size())
      {
        if (pos == 0)
        {
          lblock->vect.insert(lblock->vect.begin() + pos, 1);
          rblock->vect.insert(rblock->vect.begin() + (close - lblock->vect.size() + 2), 0);
          input_value(nleft);
          input_value(nright);
          update_value(nleft);
          update_value(nright);
        }
        else
        {
          lblock->vect.insert(lblock->vect.begin() + (pos - 1), 1);
          rblock->vect.insert(rblock->vect.begin() + (close - lblock->vect.size() + 2), 0);
          input_value(nleft);
          input_value(nright);
          update_value(nleft);
          update_value(nright);
        }
        int height = nleft->t_level;
        Node *balanced = nleft->parent;
        int i = 0; // check  tree balanced
        while (i < 3)
        {
          if (balanced == balanced->parent->left)
          {
            balanced = balanced->parent->right;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
          else
          {
            balanced = balanced->parent->left;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
        }
      }
      /**mismo bloque pero en la derecha**/
      else
      {
        if (lblock->vect.size() - pos == 0)
        {
          rblock->vect.insert(rblock->vect.begin() + pos, 1);
          rblock->vect.insert(rblock->vect.begin() + (close - lblock->vect.size() + 2), 0);
          input_value(nleft);
          input_value(nright);
          update_value(nleft);
          update_value(nright);
        }
        else
        {
          rblock->vect.insert(rblock->vect.begin() + (pos - 1), 1);
          rblock->vect.insert(rblock->vect.begin() + (close - lblock->vect.size() + 2), 0);
          input_value(nleft);
          input_value(nright);
          update_value(nleft);
          update_value(nright);
        }
        int height = nright->t_level;
        Node *balanced = nright->parent;
        int i = 0; // check  tree balanced
        while (i < 3)
        {
          if (balanced == balanced->parent->left)
          {
            balanced = balanced->parent->right;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
          else
          {
            balanced = balanced->parent->left;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
        }
      }
    }
  }
  /**BLOQUES DISTINTOS**/
  else
  {
    if (aux_leaf->vect.size() < 256) // 256 == tamaño del bloque.
    {
      if (pos == 0)
      {
        aux_leaf->vect.insert(aux_leaf->vect.begin() + pos, 1);
        input_value(leaf);
        update_value(leaf);
      }
      else
      {
        aux_leaf->vect.insert(aux_leaf->vect.begin() + (pos - 1), 1);
        input_value(leaf);
        update_value(leaf);
      }
    }
    else
    {
      Node *nleft = new Node();
      Node *nright = new Node();
      Block *lblock = new Block();
      Block *rblock = new Block();
      // ENLACES NODO LEAF CON SUS NUEVOS HIJOS
      leaf->left = nleft;
      leaf->right = nright;
      // enlace hijo izquierdo con su padre
      nleft->parent = leaf;
      // enlace hijo derecho con su padre
      nright->parent = leaf;
      // enlace de los nodos hacia sus bloques bloques
      nleft->y = lblock;
      nright->y = rblock;
      // enlace de los bloques hacia sus nodos
      lblock->leaf = nleft;
      rblock->leaf = nright;
      // enlaace entre los bloques
      lblock->next = rblock;
      rblock->prev = lblock;
      vector<bool> a;
      vector<bool> b;
      for (int i = 0; i < leaf->y->vect.size(); i++)
      {
        if (i < (leaf->y->vect.size()) / 2)
        {
          a.push_back(leaf->y->vect[i]);
        }
        else
        {
          b.push_back(leaf->y->vect[i]);
        }
      }
      copy(a.begin(), a.end(), back_inserter(lblock->vect));
      copy(b.begin(), b.end(), back_inserter(rblock->vect));
      a.clear();
      b.clear();
      Block *auxl = leaf->y->prev;
      Block *auxr = leaf->y->next;
      leaf->y = NULL;
      // enlazo con los bloques creados
      lblock->prev = auxl;
      rblock->next = auxr;
      delete aux_leaf;
      if (pos < lblock->vect.size())
      {
        if (pos == 0)
        {
          lblock->vect.insert(lblock->vect.begin() + pos, 1);
          input_value(nleft);
          input_value(nright);
          update_value(nleft);
          update_value(nright);
        }
        else
        {
          lblock->vect.insert(lblock->vect.begin() + (pos - 1), 1);
          input_value(nleft);
          input_value(nright);
          update_value(nleft);
          update_value(nright);
        }
        int height = nleft->t_level;
        Node *balanced = nleft->parent;
        int i = 0; // check  tree balanced
        while (i < 3)
        {
          if (balanced == balanced->parent->left)
          {
            balanced = balanced->parent->right;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
          else
          {
            balanced = balanced->parent->left;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
        }
      }
      else
      {
        if (pos - lblock->vect.size() == 0)
        {
          rblock->vect.insert(rblock->vect.begin(), 1);
          input_value(nleft);
          input_value(nright);
          update_value(nleft);
          update_value(nright);
        }
        else
        {
          rblock->vect.insert(rblock->vect.begin() + ((pos - lblock->vect.size()) - 1), 1);
          nleft->input_value(nleft);
          nright->input_value(nright);
          nleft->update_value(nleft);
          nright->update_value(nright);
        }
        int height = nright->t_level;
        Node *balanced = nright->parent;
        int i = 0; // check  tree balanced
        while (i < 3)
        {
          if (balanced == balanced->parent->left)
          {
            balanced = balanced->parent->right;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
          else
          {
            balanced = balanced->parent->left;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
        }
      }
    }
    if (aux->vect.size() < 256) // 256 == tamaño del bloque.
    {

      aux->vect.insert(aux->vect.begin() + (close + 1), 0);
      input_value(leaf_aux);
      update_value(leaf_aux);
    }
    else
    {
      Node *nnleft = new Node();
      Node *nnright = new Node();
      Block *llblock = new Block();
      Block *rrblock = new Block();
      // ENLACES NODO LEAF CON SUS NUEVOS HIJOS
      leaf_aux->left = nnleft;
      leaf_aux->right = nnright;
      // enlace hijo izquierdo con su padre
      nnleft->parent = leaf_aux;
      // enlace hijo derecho con su padre
      nnright->parent = leaf_aux;
      // enlace de los nodos hacia sus bloques bloques
      nnleft->y = llblock;
      nnright->y = rrblock;
      // enlace de los bloques hacia sus nodos
      llblock->leaf = nnleft;
      rrblock->leaf = nnright;
      // enlaace entre los bloques
      llblock->next = rrblock;
      rrblock->prev = llblock;
      vector<bool> aa;
      vector<bool> bb;
      for (int i = 0; i < leaf_aux->y->vect.size(); i++)
      {
        if (i < (leaf_aux->y->vect.size()) / 2)
        {
          aa.push_back(leaf_aux->y->vect[i]);
        }
        else
        {
          bb.push_back(leaf_aux->y->vect[i]);
        }
      }
      copy(aa.begin(), aa.end(), back_inserter(llblock->vect));
      copy(bb.begin(), bb.end(), back_inserter(rrblock->vect));
      aa.clear();
      bb.clear();
      Block *auxl = leaf_aux->y->prev;
      Block *auxr = leaf_aux->y->next;
      leaf_aux->y = NULL;
      delete aux;
      // enlazo con los bloques creados

      if (close < llblock->vect.size())
      {
        llblock->vect.insert(llblock->vect.begin() + (close + 1), 0);
        input_value(nnleft);
        input_value(nnright);
        update_value(nnleft);
        update_value(nnright);
        int height = nnleft->t_level;
        Node *balanced = nnleft->parent;
        int i = 0; // check  tree balanced
        while (i < 3)
        {
          if (balanced == balanced->parent->left)
          {
            balanced = balanced->parent->right;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
          else
          {
            balanced = balanced->parent->left;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
        }
      }
      else
      {
        rrblock->vect.insert(rrblock->vect.begin() + ((close - llblock->vect.size()) + 1), 0);
        input_value(nnleft);
        input_value(nnright);
        update_value(nnleft);
        update_value(nnright);
        int height = nnright->t_level;
        Node *balanced = nnright->parent;
        int i = 0; // check  tree balanced
        while (i < 3)
        {
          if (balanced == balanced->parent->left)
          {
            balanced = balanced->parent->right;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
          else
          {
            balanced = balanced->parent->left;
            if (height - balanced->t_level >= 2 && balanced->y != NULL)
            {
              p = reestruct(*&p);
              i++;
            }
            else
            {
              balanced = balanced->parent;
              i++;
            }
          }
        }
      }
    }
  }
}
/**eliminación de un nodo**/
void Node::delete_node(Node *&p, int a)
{
  Node *leaf = leaf->navigate(p, a);
  Node *leaf_open = leaf;
  Block *aux_leaf = leaf->y;
  int pos = p->open(leaf, a);
  Node *leaf_right = leaf_right->fws_node(leaf, pos);
  int close = leaf_right->forward_search(leaf, pos);
  Node *leaf_close = leaf_right;
  Block *aux_close = leaf_right->y;
  if (leaf_open == leaf_close)
  {
    aux_leaf->vect.erase(aux_leaf->vect.begin() + pos);
    aux_leaf->vect.erase(aux_leaf->vect.begin() + (close - 1));
    /**caso bloque cumple con la invariante**/
    if (aux_leaf->vect.size() >= 128)
    {
      input_value(leaf_open);
      update_value(leaf_open);
    }
    /**consulto bloque anterior**/
    else if (aux_leaf->prev != NULL)
    {
      Node *preview = aux_leaf->prev->leaf;
      Node *aux_parent = preview->parent;
      Block *b_preview = aux_leaf->prev;
      /**fusionar con el bloque**/
      if (aux_leaf->vect.size() + b_preview->vect.size() <= 256)
      {
        vector<bool> aux;
        for (int i = 0; i < b_preview->vect.size(); i++)
        {
          aux.push_back(b_preview->vect[i]);
        }
        for (int i = 0; i < aux_leaf->vect.size(); i++)
        {
          aux.push_back(aux_leaf->vect[i]);
        }
        /**elimino informacion repetida**/
        aux_leaf->vect.clear();
        b_preview->vect.clear();
        /**actualizo info**/
        for (int i = 0; i < aux.size(); i++)
        {
          aux_leaf->vect.push_back(aux[i]);
        }
        input_value(leaf_open);
        input_value(preview);
        update_value(leaf_open);
        update_value(preview);
        /**ENLACES NUEVOS**/
        Block *neighbour = b_preview->prev;
        neighbour->next = aux_leaf;
        aux_leaf->prev = neighbour;
        int v;
        if (preview == aux_parent->left)
        {
          aux_parent->left = NULL;
        }
        else
        {
          aux_parent->right = NULL;
        }
        delete b_preview; // elimino bloque anterior
        delete preview;   // elimino nodo anterior
        if (aux_parent->left == NULL && aux_parent->right == NULL)
        {
          p = reestruct(*&p);
        }
      }
      else
      {
        int request = 128 - aux_leaf->vect.size();
        vector<bool> aux;
        /**obtengo la info de mi vecino**/
        for (int i = b_preview->vect.size() - request; i < b_preview->vect.size(); i++)
        {
          aux.push_back(b_preview->vect[i]);
        }
        /**elimino en mi vecino lo que pedi**/
        for (int i = 0; i < request; i++)
        {
          b_preview->vect.pop_back();
        }
        /**fusionar la informacion**/
        for (int i = 0; i < aux_leaf->vect.size(); i++)
        {
          aux.push_back(aux_leaf->vect[i]);
        }
        /**actualizo**/
        aux_leaf->vect.clear();
        for (int i = 0; i < aux.size(); i++)
        {
          aux_leaf->vect.push_back(aux[i]);
        }
        aux.clear();
        input_value(leaf_open);
        input_value(preview);
        update_value(leaf_open);
        update_value(preview);
      }
    }
    /**bloque siguiente**/
    else
    {
      Node *leaf_next = aux_leaf->next->leaf;
      Node *aux_parent = leaf_next->parent;
      Block *b_next = aux_leaf->next;
      /**fusionar con el bloque**/
      if (aux_leaf->vect.size() + b_next->vect.size() <= 256)
      {
        vector<bool> aux;
        for (int i = 0; i < aux_leaf->vect.size(); i++)
        {
          aux.push_back(aux_leaf->vect[i]);
        }
        for (int i = 0; i < b_next->vect.size(); i++)
        {
          aux.push_back(b_next->vect[i]);
        }
        /**elimino informacion repetida**/
        aux_leaf->vect.clear();
        b_next->vect.clear();
        /**actualizo info**/
        for (int i = 0; i < aux.size(); i++)
        {
          aux_leaf->vect.push_back(aux[i]);
        }
        input_value(leaf_open);
        input_value(leaf_next);
        update_value(leaf_open);
        update_value(leaf_next);
        /**enlazo **/
        Block *neighbour = b_next->next;
        neighbour->prev = aux_leaf;
        aux_leaf->next = neighbour;
        if (leaf_next == aux_parent->left)
        {
          aux_parent->left = NULL;
        }
        else
        {
          aux_parent->right = NULL;
        }
        delete b_next;    // elimino bloque anterior
        delete leaf_next; // elimino nodo anterior
        if (aux_parent->left == NULL && aux_parent->right == NULL)
        {
          p = reestruct(*&p);
        }
      }
      else
      {
        int request = 128 - aux_leaf->vect.size();
        vector<bool> aux;
        /**fusionar la informacion**/
        for (int i = 0; i < aux_leaf->vect.size(); i++)
        {
          aux.push_back(aux_leaf->vect[i]);
        }
        /**obtengo la info de mi vecino**/
        for (int i = 0; i < request; i++)
        {
          aux.push_back(b_next->vect[i]);
        }
        /**elimino en mi vecino lo que pedi**/
        for (int i = 0; i < request; i++)
        {
          b_next->vect.erase(b_next->vect.begin());
        }
        /**actualizo**/
        aux_leaf->vect.clear();
        for (int i = 0; i < aux.size(); i++)
        {
          aux_leaf->vect.push_back(aux[i]);
        }
        aux.clear();
        input_value(leaf_open);
        input_value(leaf_next);
        update_value(leaf_open);
        update_value(leaf_next);
      }
    }
  }
  else
  {
    aux_leaf->vect.erase(aux_leaf->vect.begin() + pos);
    aux_close->vect.erase(aux_close->vect.begin() + close);
    if (aux_leaf->vect.size() >= 128)
    {
      input_value(leaf_open);
      update_value(leaf_open);
    }
    else
    {
      if (aux_leaf->prev != NULL)
      {
        Node *preview = aux_leaf->prev->leaf;
        Node *aux_parent = preview->parent;
        Block *b_preview = aux_leaf->prev;
        /**fusionar con el bloque**/
        if (aux_leaf->vect.size() + b_preview->vect.size() <= 256)
        {
          vector<bool> aux;
          for (int i = 0; i < b_preview->vect.size(); i++)
          {
            aux.push_back(b_preview->vect[i]);
          }
          for (int i = 0; i < aux_leaf->vect.size(); i++)
          {
            aux.push_back(aux_leaf->vect[i]);
          }
          /**elimino informacion repetida**/
          aux_leaf->vect.clear();
          b_preview->vect.clear();
          /**actualizo info**/
          for (int i = 0; i < aux.size(); i++)
          {
            aux_leaf->vect.push_back(aux[i]);
          }
          input_value(leaf_open);
          input_value(preview);
          update_value(leaf_open);
          update_value(preview);
          /**ENLACES NUEVOS**/
          Block *neighbour = b_preview->prev;
          neighbour->next = aux_leaf;
          aux_leaf->prev = neighbour;
          if (preview == aux_parent->left)
          {
            aux_parent->left = NULL;
          }
          else
          {
            aux_parent->right = NULL;
          }
          delete b_preview; // elimino bloque anterior
          delete preview;   // elimino nodo anterior
          if (aux_parent->left == NULL && aux_parent->right == NULL)
          {
            p = reestruct(*&p);
          }
        }
        else
        {
          int request = 128 - aux_leaf->vect.size();
          vector<bool> aux;
          /**obtengo la info de mi vecino**/
          for (int i = b_preview->vect.size() - request; i < b_preview->vect.size(); i++)
          {
            aux.push_back(b_preview->vect[i]);
          }
          /**elimino en mi vecino lo que pedi**/
          for (int i = 0; i < request; i++)
          {
            b_preview->vect.pop_back();
          }
          /**fusionar la informacion**/
          for (int i = 0; i < aux_leaf->vect.size(); i++)
          {
            aux.push_back(aux_leaf->vect[i]);
          }
          /**actualizo**/
          aux_leaf->vect.clear();
          for (int i = 0; i < aux.size(); i++)
          {
            aux_leaf->vect.push_back(aux[i]);
          }
          aux.clear();
          input_value(leaf_open);
          input_value(preview);
          update_value(leaf_open);
          update_value(preview);
        }
      }
      else
      {
        Node *leaf_next = aux_leaf->next->leaf;
        Node *aux_parent = leaf_next->parent;
        Block *b_next = aux_leaf->next;
        /**fusionar con el bloque**/
        if (aux_leaf->vect.size() + b_next->vect.size() <= 256)
        {
          vector<bool> aux;
          for (int i = 0; i < aux_leaf->vect.size(); i++)
          {
            aux.push_back(aux_leaf->vect[i]);
          }
          for (int i = 0; i < b_next->vect.size(); i++)
          {
            aux.push_back(b_next->vect[i]);
          }
          /**elimino informacion repetida**/
          aux_leaf->vect.clear();
          b_next->vect.clear();
          /**actualizo info**/
          for (int i = 0; i < aux.size(); i++)
          {
            aux_leaf->vect.push_back(aux[i]);
          }
          input_value(leaf_open);
          input_value(leaf_next);
          update_value(leaf_open);
          update_value(leaf_next);
          /**enlazo **/
          Block *neighbour = b_next->next;
          neighbour->prev = aux_leaf;
          aux_leaf->next = neighbour;
          if (leaf_next == aux_parent->left)
          {
            aux_parent->left = NULL;
          }
          else
          {
            aux_parent->right = NULL;
          }
          if (b_next == aux_close)
          {
            aux_close = NULL;
          }
          else
          {
            delete b_next; // elimino bloque anterior
          }
          delete leaf_next; // elimino nodo anterior
          if (aux_parent->left == NULL && aux_parent->right == NULL)
          {
            p = reestruct(*&p);
          }
        }
        else
        {
          int request = 128 - aux_leaf->vect.size();
          vector<bool> aux;
          /**fusionar la informacion**/
          for (int i = 0; i < aux_leaf->vect.size(); i++)
          {
            aux.push_back(aux_leaf->vect[i]);
          }
          /**obtengo la info de mi vecino**/
          for (int i = 0; i < request; i++)
          {
            aux.push_back(b_next->vect[i]);
          }
          /**elimino en mi vecino lo que pedi**/
          for (int i = 0; i < request; i++)
          {
            b_next->vect.erase(b_next->vect.begin());
          }
          /**actualizo**/
          aux_leaf->vect.clear();
          for (int i = 0; i < aux.size(); i++)
          {
            aux_leaf->vect.push_back(aux[i]);
          }
          aux.clear();
          input_value(leaf_open);
          input_value(leaf_next);
          update_value(leaf_open);
          update_value(leaf_next);
        }
      }
    }
    if (aux_close != NULL)
    {
      if (aux_close->vect.size() >= 128)
      {
        input_value(leaf_close);
        update_value(leaf_close);
      }
      else
      {
        if (aux_close->prev != NULL)
        {
          Node *preview = aux_close->prev->leaf;
          Node *aux_parent = preview->parent;
          Block *b_preview = aux_close->prev;
          /**fusionar con el bloque**/
          if (aux_close->vect.size() + b_preview->vect.size() <= 256)
          {
            vector<bool> aux;
            for (int i = 0; i < b_preview->vect.size(); i++)
            {
              aux.push_back(b_preview->vect[i]);
            }
            for (int i = 0; i < aux_close->vect.size(); i++)
            {
              aux.push_back(aux_close->vect[i]);
            }
            /**elimino informacion repetida**/
            aux_close->vect.clear();
            b_preview->vect.clear();
            /**actualizo info**/
            for (int i = 0; i < aux.size(); i++)
            {
              aux_close->vect.push_back(aux[i]);
            }
            input_value(leaf_open);
            input_value(preview);
            update_value(leaf_open);
            update_value(preview);
            /**ENLACES NUEVOS**/
            Block *neighbour = b_preview->prev;
            neighbour->next = aux_close;
            aux_close->prev = neighbour;
            if (preview == aux_parent->left)
            {
              aux_parent->left = NULL;
            }
            else
            {
              aux_parent->right = NULL;
            }
            delete b_preview; // elimino bloque anterior
            delete preview;   // elimino nodo anterior
            if (aux_parent->left == NULL && aux_parent->right == NULL)
            {
              p = reestruct(*&p);
            }
          }
          else
          {
            int request = 128 - aux_close->vect.size();
            vector<bool> aux;
            /**obtengo la info de mi vecino**/
            for (int i = b_preview->vect.size() - request; i < b_preview->vect.size(); i++)
            {
              aux.push_back(b_preview->vect[i]);
            }
            /**elimino en mi vecino lo que pedi**/
            for (int i = 0; i < request; i++)
            {
              b_preview->vect.pop_back();
            }
            /**fusionar la informacion**/
            for (int i = 0; i < aux_close->vect.size(); i++)
            {
              aux.push_back(aux_close->vect[i]);
            }
            /**actualizo**/
            aux_close->vect.clear();
            for (int i = 0; i < aux.size(); i++)
            {
              aux_close->vect.push_back(aux[i]);
            }
            aux.clear();
            input_value(leaf_close);
            input_value(preview);
            update_value(leaf_close);
            update_value(preview);
          }
        }
        else
        {
          Node *leaf_next = aux_close->next->leaf;
          Node *aux_parent = leaf_next->parent;
          Block *b_next = aux_close->next;
          /**fusionar con el bloque**/
          if (aux_close->vect.size() + b_next->vect.size() <= 256)
          {
            vector<bool> aux;
            for (int i = 0; i < aux_close->vect.size(); i++)
            {
              aux.push_back(aux_close->vect[i]);
            }
            for (int i = 0; i < b_next->vect.size(); i++)
            {
              aux.push_back(b_next->vect[i]);
            }
            /**elimino informacion repetida**/
            aux_close->vect.clear();
            b_next->vect.clear();
            /**actualizo info**/
            for (int i = 0; i < aux.size(); i++)
            {
              aux_close->vect.push_back(aux[i]);
            }
            input_value(leaf_close);
            input_value(leaf_next);
            update_value(leaf_close);
            update_value(leaf_next);
            /**enlazo **/
            Block *neighbour = b_next->next;
            neighbour->prev = aux_close;
            aux_close->next = neighbour;
            if (leaf_next == aux_parent->left)
            {
              aux_parent->left = NULL;
            }
            else
            {
              aux_parent->right = NULL;
            }
            delete b_next;    // elimino bloque anterior
            delete leaf_next; // elimino nodo anterior
            if (aux_parent->left == NULL && aux_parent->right == NULL)
            {
              p = reestruct(*&p);
            }
          }
          else
          {
            int request = 128 - aux_close->vect.size();
            vector<bool> aux;
            /**fusionar la informacion**/
            for (int i = 0; i < aux_close->vect.size(); i++)
            {
              aux.push_back(aux_close->vect[i]);
            }
            /**obtengo la info de mi vecino**/
            for (int i = 0; i < request; i++)
            {
              aux.push_back(b_next->vect[i]);
            }
            /**elimino en mi vecino lo que pedi**/
            for (int i = 0; i < request; i++)
            {
              b_next->vect.erase(b_next->vect.begin());
            }
            /**actualizo**/
            aux_close->vect.clear();
            for (int i = 0; i < aux.size(); i++)
            {
              aux_close->vect.push_back(aux[i]);
            }
            aux.clear();
            input_value(leaf_close);
            input_value(leaf_next);
            update_value(leaf_close);
            update_value(leaf_next);
          }
        }
      }
    }
  }
}
/**Computacion de valores en el nodo hoja**/
void Node::input_value(Node *node)
{
  int aux_ones = 0;
  int aux_zeros = 0;
  int aux_min = 0;
  int aux_max = 0;
  int aux_num = 0;
  int aux_excess = 0;
  for (int i = 0; i < node->y->vect.size(); i++)
  {
    if (node->y->vect[i] == 1)
    {
      aux_excess++;
      aux_ones++;
    }
    else
    {
      aux_excess--;
      aux_zeros++;
    }
    aux_num++;
    if (i == 0)
    {
      aux_min = aux_excess;
      aux_max = aux_excess;
    }

    if (aux_excess < aux_min)
    {
      aux_min = aux_excess;
    }
    if (aux_excess > aux_max)
    {
      aux_max = aux_excess;
    }
  }
  node->t_excess = aux_excess;
  node->t_max = aux_max;
  node->t_min = aux_min;
  node->t_ones = aux_ones;
  node->t_zeros = aux_zeros;
  node->t_numchunk = aux_num;
}
/**Actualización de la rama**/
void Node::update_value(Node *node)
{
  Node *father = node->parent;
  while (father != NULL)
  {
    if (father->left == NULL)
    {
      father->t_excess = father->right->t_excess;
      father->t_max = father->right->t_max;
      father->t_min = father->right->t_min;
      father->t_numchunk = father->right->t_numchunk;
      father->t_ones = father->right->t_ones;
      father->t_zeros = father->right->t_zeros;
      father = father->parent;
    }
    else if (father->right == NULL)
    {
      father->t_excess = father->left->t_excess;
      father->t_max = father->left->t_max;
      father->t_min = father->left->t_min;
      father->t_numchunk = father->left->t_numchunk;
      father->t_ones = father->left->t_ones;
      father->t_zeros = father->left->t_zeros;
      father = father->parent;
    }
    else
    {
      if (father->left->t_min < father->right->t_min + father->left->t_excess)
      {
        father->t_min = father->left->t_min;
      }
      else
      {
        father->t_min = father->right->t_min + father->left->t_excess;
      }
      if (father->left->t_max > father->right->t_max + father->left->t_excess)
      {
        father->t_max = father->left->t_max;
      }
      else
      {
        father->t_max = father->right->t_max + father->left->t_excess;
      }
      father->t_excess = father->left->t_excess + father->right->t_excess;
      father->t_ones = father->left->t_ones + father->right->t_ones;
      father->t_zeros = father->left->t_zeros + father->right->t_zeros;
      father->t_numchunk = father->left->t_numchunk + father->right->t_numchunk;
      father = father->parent;
    }
  }
}
/**Forward Search**/
int Node::forward_search(Node *node, int pos)
{
  Block *search = node->y;
  int p_e = 0;
  int d_prime = 0;
  Node *aux = node;
  if (pos + 1 >= search->vect.size())
  {
    d_prime = d_prime + 0;
  }
  else
  {
    for (int i = pos + 1; i < search->vect.size(); i++)
    {
      if (search->vect[i] == 1)
      {
        d_prime++;
      }
      else
      {
        d_prime--;
      }

      if (p_e == d_prime + 1)
      {
        return i;
      }
    }
  }
  // d_prime = d_prime + aux->t_excess - 1;
  //  bucle para subir hasta encontrar un nodo padre que contenga el parentesis de cierre
  while (aux != NULL)
  {
    if (aux->parent == NULL)
    {
      break;
    }
    /**VENGO DE UN HIJO IZQUIERDO**/
    if (aux == aux->parent->left)
    {
      if (aux->parent->right != NULL)
      {
        aux = aux->parent->right;
        if (d_prime + aux->t_min <= -1)
        {
          if (aux->y != NULL)
          {
            for (int i = 0; i < aux->y->vect.size(); i++)
            {
              if (aux->y->vect[i] == 1)
              {
                d_prime++;
              }
              if (aux->y->vect[i] == 0)
              {
                d_prime--;
              }
              if (p_e == d_prime + 1)
              {
                return i;
              }
            }
          }
          /**ELSE ENCUENTRA EN NODO DERECHO PERO NO ES HOJA**/
          else
          {
            break;
          }
        }
        else
        {
          d_prime = d_prime + aux->t_excess;
        }
      }
      else
      {
        aux = aux->parent;
      }
    }
    /** ELSE CASO HIJO DERECHO**/
    else
    {
      aux = aux->parent;
    }
  }

  // bucle que va bajando hasta encontrar un  nodo hoja que contenga el parentesis de cierre

  while (aux->y == NULL)
  {
    if (aux->left != NULL)
    {
      if (aux->left->t_min + d_prime <= -1)
      {
        aux = aux->left;
        if (aux->y != NULL)
        {
          for (int i = 0; i < aux->y->vect.size(); i++)
          {
            if (aux->y->vect[i] == 1)
            {
              d_prime++;
            }
            if (aux->y->vect[i] == 0)
            {
              d_prime--;
            }

            if (p_e == d_prime + 1)
            {
              return i;
            }
          }
        }
      }
      else
      {
        d_prime = d_prime + aux->left->t_excess;
        aux = aux->right;
        if (aux->y != NULL)
        {
          for (int i = 0; i < aux->y->vect.size(); i++)
          {
            if (aux->y->vect[i] == 1)
            {
              d_prime++;
            }
            if (aux->y->vect[i] == 0)
            {
              d_prime--;
            }
            if (p_e == d_prime + 1)
            {
              return i;
            }
          }
        }
      }
    }
    else
    {
      aux = aux->right;
      if (aux->y != NULL)
      {
        for (int i = 0; i < aux->y->vect.size(); i++)
        {
          if (aux->y->vect[i] == 1)
          {
            d_prime++;
          }
          if (aux->y->vect[i] == 0)
          {
            d_prime--;
          }
          if (p_e == d_prime + 1)
          {
            return i;
          }
        }
      }
    }
  }
  return -1;
}
/**Encontra nodo hoja parentesis de cierre**/
Node *Node::fws_node(Node *node, int pos)
{
  Block *search = node->y;
  int p_e = 0;
  int d_prime = 0;
  Node *aux = node;
  if (pos + 1 >= search->vect.size())
  {
    d_prime = d_prime + 0;
  }
  else
  {
    for (int i = pos + 1; i < search->vect.size(); i++)
    {
      if (search->vect[i] == 1)
      {
        d_prime++;
      }
      else
      {
        d_prime--;
      }

      if (p_e == d_prime + 1)
      {
        return aux;
      }
    }
  }
  // d_prime = d_prime + aux->t_excess - 1;
  //  bucle para subir hasta encontrar un nodo padre que contenga el parentesis de cierre
  while (aux != NULL)
  {
    if (aux->parent == NULL)
    {
      break;
    }
    /**VENGO DE UN HIJO IZQUIERDO**/
    if (aux == aux->parent->left)
    {
      if (aux->parent->right != NULL)
      {
        aux = aux->parent->right;
        if (d_prime + aux->t_min <= -1)
        {
          if (aux->y != NULL)
          {
            return aux;
          }
          /**ELSE ENCUENTRA EN NODO DERECHO PERO NO ES HOJA**/
          else
          {
            break;
          }
        }
        else
        {
          d_prime = d_prime + aux->t_excess;
        }
      }
      else
      {
        aux = aux->parent;
      }
    }
    /** ELSE CASO HIJO DERECHO**/
    else
    {
      aux = aux->parent;
    }
  }

  // bucle que va bajando hasta encontrar un  nodo hoja que contenga el parentesis de cierre

  while (aux->y == NULL)
  {
    if (aux->left != NULL)
    {
      if (aux->left->t_min + d_prime <= -1)
      {
        aux = aux->left;
        if (aux->y != NULL)
        {
          return aux;
        }
      }
      else
      {
        d_prime = d_prime + aux->left->t_excess;
        aux = aux->right;
        if (aux->y != NULL)
        {
          return aux;
        }
      }
    }
    else
    {
      aux = aux->right;
      if (aux->y != NULL)
      {
        return aux;
      }
    }
  }
  return NULL;
}
/**obtener el ultimo nivel de la estructura**/
void Node::get_leaves(Node *p, vector<Node *> &vector)
{
  if (p == NULL)
  {
    return;
  }
  if (p->left == NULL && p->right == NULL)
  {
    vector.push_back(p);
  }
  p->get_leaves(p->left, vector);
  p->get_leaves(p->right, vector);
}
/**eliminar los nodos internos**/
void Node::delete_internal_nodes(Node *p)
{
  if (p == NULL)
  {
    return;
  }
  delete_internal_nodes(p->left);
  delete_internal_nodes(p->right);
  if (p->y == NULL)
  {
    delete p;
  }
}
/**reestructuracion**/
Node *Node::reestruct(Node *p)
{
  vector<Node *> leaves;
  get_leaves(p, leaves);
  for (int i = 0; i < leaves.size(); i++)
  {
    if (leaves[i]->y == NULL)
    {
      leaves.erase(leaves.begin() + i);
    }
  }
  delete_internal_nodes(p);
  int size = leaves.size();
  vector<Node *> arr;
  for (int i = 0; i < (2 * size - 1); i++)
  {
    if (i < (size - 1))
    {
      Node *aux = new Node();
      arr.push_back(aux);
      arr[i]->t_excess = 0;
      arr[i]->t_max = 0;
      arr[i]->t_min = 0;
      arr[i]->t_ones = 0;
      arr[i]->t_zeros = 0;
      arr[i]->t_numchunk = 0;
      if (i == 0 && arr[0] != NULL)
      {
        arr[0]->left = NULL;
        arr[0]->right = NULL;
        arr[0]->parent = NULL;
        arr[0]->t_level = i;
      }
      else if (arr[i] != NULL)
      {
        if (arr[(i - 1) / 2] != NULL)
        {
          arr[i]->parent = arr[(i - 1) / 2];
          arr[i]->t_level = arr[(i - 1) / 2]->t_level + 1;
          arr[i]->left = NULL;
          arr[i]->right = NULL;
          if (i % 2 == 1)
          {
            arr[(i - 1) / 2]->left = arr[i];
          }
          else
          {
            arr[(i - 1) / 2]->right = arr[i];
          }
        }
      }
    }
  }
  vector<Node *> last_internal;
  get_leaves(arr[0], last_internal);
  int node_size = 0;
  int internal_size = 0;
  Node *impar = new Node();
  while (node_size < leaves.size() && internal_size < last_internal.size())
  {
    last_internal[internal_size]->left = leaves[node_size];
    last_internal[internal_size]->right = leaves[node_size + 1];
    leaves[node_size]->parent = last_internal[internal_size];
    leaves[node_size + 1]->parent = last_internal[internal_size];
    leaves[node_size]->t_level = last_internal[internal_size]->t_level;
    leaves[node_size + 1]->t_level = last_internal[internal_size]->t_level;
    if (leaves[node_size]->t_min < leaves[node_size + 1]->t_min + leaves[node_size]->t_excess)
    {
      last_internal[internal_size]->t_min = leaves[node_size]->t_min;
    }
    else
    {
      last_internal[internal_size]->t_min = leaves[node_size + 1]->t_min + leaves[node_size]->t_excess;
    }
    if (leaves[node_size]->t_max > leaves[node_size + 1]->t_max + leaves[node_size]->t_excess)
    {
      last_internal[internal_size]->t_max = leaves[node_size]->t_max;
    }
    else
    {
      last_internal[internal_size]->t_max = leaves[node_size + 1]->t_max + leaves[node_size]->t_excess;
    }
    last_internal[internal_size]->t_excess = leaves[node_size]->t_excess + leaves[node_size + 1]->t_excess;
    last_internal[internal_size]->t_ones = leaves[node_size]->t_ones + leaves[node_size + 1]->t_ones;
    last_internal[internal_size]->t_zeros = leaves[node_size]->t_zeros + leaves[node_size + 1]->t_zeros;
    last_internal[internal_size]->t_numchunk = leaves[node_size]->t_numchunk + leaves[node_size + 1]->t_numchunk;
    if (last_internal[internal_size]->parent->right == NULL)
    {
      impar = last_internal[internal_size]->parent;
      impar->right = leaves[node_size + 2];
      leaves[node_size + 2]->parent = impar;
      leaves[node_size + 2]->t_level = impar->t_level + 1;
      arr.push_back(leaves[node_size + 2]);
      node_size++;
    }
    node_size = node_size + 2;
    internal_size++;
  }
  for (int i = arr.size() - 1; i > 0; i = i - 2)
  {
    if (arr[i - 1]->t_min < arr[i]->t_min + arr[i - 1]->t_excess)
    {

      arr[(i - 1) / 2]->t_min = arr[i - 1]->t_min;
    }
    else
    {
      arr[(i - 1) / 2]->t_min = arr[i]->t_min + arr[i - 1]->t_excess;
    }
    if (arr[i - 1]->t_max > arr[i]->t_max + arr[i - 1]->t_excess)
    {
      arr[(i - 1) / 2]->t_max = arr[i - 1]->t_max;
    }
    else
    {
      arr[(i - 1) / 2]->t_max = arr[i]->t_max + arr[i - 1]->t_excess;
    }
    arr[(i - 1) / 2]->t_ones = arr[i - 1]->t_ones + arr[i]->t_ones;
    arr[(i - 1) / 2]->t_zeros = arr[i - 1]->t_zeros + arr[i]->t_zeros;
    arr[(i - 1) / 2]->t_excess = arr[i - 1]->t_excess + arr[i]->t_excess;
    arr[(i - 1) / 2]->t_numchunk = arr[i - 1]->t_numchunk + arr[i]->t_numchunk;
  }
  /*
   * STEP 3: Computation of all universal tables
   */

  T = create_lookup_tables();
  return arr[0];
}

/**corregir invariante**/
void Node::invariant(Block *a)
{
  if (a->vect.size() < 128)
  {
    int need = 130 - a->vect.size();       // lo que necesito para llegar a la invariante
    int pos = a->prev->vect.size() - need; // posicionarme desde donde pedire los parentesis a mi vecino
    vector<bool> aux;                      // vector aux para el bloque que reviso
    vector<bool> ant;                      // vector aux para el bloque anterior
    Node *node_prev = a->prev->leaf;       // Nodo anterior
    Node *node_aux = a->leaf;              // Nodo actual
    /**for para almacenar lo nuevo del bloque anterior**/
    for (int i = 0; i < pos; i++)
    {
      ant.push_back(a->prev->vect[i]);
    }
    /**for pasar los parentesis**/
    for (int j = pos; j < a->prev->vect.size(); j++)
    {
      aux.push_back(a->prev->vect[j]);
    }
    /**añadir al vector los parentesis del bloque que necesita parentesis**/
    for (int k = 0; k < a->vect.size(); k++)
    {
      aux.push_back(a->vect[k]);
    }
    a->prev->vect.clear();
    a->vect.clear();
    copy(aux.begin(), aux.end(), back_inserter(a->vect));
    copy(ant.begin(), ant.end(), back_inserter(a->prev->vect));
    aux.clear();
    ant.clear();
    input_value(node_aux);
    input_value(node_prev);
    a->invariant(a->prev);
  }
}
/**FUNCIONES DE LA ESTRUCTURA**/

/**Construccion**/
rmMT::rmMT(BIT_ARRAY *bit_array, unsigned long n)
{
  root = new Node();
  root = create_struct(bit_array, n);
}
/**Obtener el nodo raiz**/
Node &rmMT::get_root()
{
  return *root;
}
/**Obtener memoria de la estructura**/
void rmMT::memory_of_struct()
{
  vector<Node *> leaves;
  get_leaves(root, leaves);
  double total_leaves = leaves.size();
  int total_parenthesis = 0;
  Block *aux = leaves[leaves.size() - 1]->y;
  for (int i = 0; i < leaves.size(); i++)
  {
    total_parenthesis = total_parenthesis + leaves[i]->t_numchunk;
  }
  double total_node = 2 * leaves.size() - 1;
  double size_of_total_block = total_leaves * sizeof(aux);
  double size_of_total_node = total_node * sizeof(root);
  double size_of_total_struct = size_of_total_block + size_of_total_node;
  if (size_of_total_struct > 1000000)
  {
    size_of_total_struct = size_of_total_struct / 1000000;
  }
  int max_capacity = 256 * leaves.size();
  double capacity_total = ((100 * total_parenthesis) / max_capacity);
  double free_capacity = 100 - capacity_total;
  cout << max_capacity << "," << total_parenthesis << "," << leaves.size() << endl;
}
/**insercion en la estructura nodo hijo izquierdo**/
void rmMT::insert_l(int a)
{

  insert_left(root, a);
}
/**insercion en la estructura nodo hijo derecho **/
void rmMT::insert_r(int a)
{
  insert_right(root, a);
}
/**Insercion en la estructura nodo padre**/
void rmMT::insert_p(int a)
{
  insert_parent(root, a);
}
/**Eliminacion de un nodo**/
void rmMT::erase(int a)
{
  delete_node(root, a);
}
void rmMT::find_open(int a)
{
  Node *node_close = navigate2(root, a);
  int pos_close = close(root, a);
  int pos_open = backward_search(node_close, pos_close);
  // cout << pos_open << endl;
  if (pos_open == -1)
  {
    cout << "MALO" << endl;
  }
}
void rmMT::find_close(int a)
{
  Node *node_open = node_open->navigate(root, a);
  int pos_open = node_open->open(root, a);
  Node *node_close = node_close->fws_node(node_open, pos_open);
  int pos_close = node_close->forward_search(node_open, pos_open);
}
/**Funcion que realiza forward y backward search**/
void rmMT::match(int a)
{
  /**parentesis de cierre a partir de un parentesis de apertura**/
  Node *node_open = node_open->navigate(root, a);
  int pos_open = node_open->open(root, a);
  Node *node_close = node_close->fws_node(node_open, pos_open);
  int pos_close = node_close->forward_search(node_open, pos_open);
  int pos_openv2 = backward_search(node_close, pos_close);
}