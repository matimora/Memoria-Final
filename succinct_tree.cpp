
/******************************************************************************
 * succinct_tree.c
 *
 * Parallel construction of succinct trees
 * For more information: http://www.inf.udec.cl/~josefuentes/sea2015/
 *
 ******************************************************************************
 * Copyright (C) 2015 José Fuentes Sepúlveda <jfuentess@udec.cl>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 *****************************************************************************/

#include "lookup_tables.h"
#include "binary_trees.h"
#include "succinct_tree.h"
#include "class.h"
#include "bit_array.h"
#include "util.h"
#include "basic.h"
#include <stdio.h>
#include <vector>
#include <bits/stdc++.h>


using namespace std;

/* ASSUMPTIONS:
 * - s = 256 (8 bits) (Following the sdsl/libcds implementations)
 * - k = 2 (Min-max tree will be a binary tree)
 * - Each thread has to process at least one chunk with parentheses (Problem with n <= s)
 */

Node::Node(){
      t_min=0;
      t_max=0;
      t_excess=0;
      t_ones=0;
      t_numchunk=0;
      left=NULL;
      right=NULL;
      parent=NULL;

} 
InternalNode::InternalNode(){

      t_min=0;
      t_max=0;
      t_excess=0;
      t_ones=0;
      t_numchunk=0;
      left=NULL;
      right=NULL;
      parent=NULL;


}

Leaf::Leaf(){

    t_min=0;
    t_max=0;
    t_excess=0;
    t_ones=0;
    t_numchunk=0;
    parent=NULL;
    block=NULL;
}
Block::Block(){

      vect.resize(256);
      eti = 0;  
      next=NULL;
      prev=NULL;
      leaf=NULL;
}
LinkedList::LinkedList(){

      head=NULL;
      tail=NULL;
}
void LinkedList::InsertBlock(Block* bl){

    Block* aux  =   new Block(); 
    aux->vect   =   bl->vect;
    aux->next   =   bl-> next;
    bl->next    =   aux;
    aux -> prev =   bl;
    if(tail != NULL){
      tail -> next -> prev = aux;
    }
    if(head == NULL){
      head=aux;
    }
    tail=aux;

}
rmMt* init_rmMt(unsigned long n) {
  rmMt* st = (rmMt*)malloc(sizeof(rmMt));
  st->s = 256; // tamaño bloque
  st->c = st->s*0.75; // carga inicial del bloque
  st->k = 2; // numero de hijo
  st->n = n; // numero de parentesis
  st->num_chunks = ceil((double)n/st->c); //  es la cantidad de bloques
  st->height = ceil(log(st->num_chunks)/log(st->k)); // heigh = logk(num_chunks), Heigh of the min-max tree
  st->internal_nodes = (pow(st->k,st->height)-1)/(st->k-1); // Number of internal nodes;
  
  return st;
}


void print_rmMt(rmMt* st) {
  fprintf(stderr, "Chunk size: %u\n", st->s);
  fprintf(stderr, "Arity: %u\n", st->k);
  fprintf(stderr, "Number of parentheses: %lu\n", st->n);
  fprintf(stderr, "Number of chunks (leaves): %u\n", st->num_chunks);
  fprintf(stderr, "Height: %u\n", st->height);
  fprintf(stderr, "Number of internal nodes: %u\n", st->internal_nodes);
}

rmMt* st_create(BIT_ARRAY* bit_array, unsigned long n) {
  rmMt* st = init_rmMt(n);
  /* print_rmMt(st); */
  st->bit_array = bit_array;

  if(st->s >= n){
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

 // for(unsigned int thread = 0; thread < num_threads; thread++) {
     
    unsigned int chunk = 0; // contador de bloques
    unsigned chunk_limit= st->num_chunks; // It is possible that the last thread process less chunks
    Node* arrL[chunk_limit*sizeof(Node)];
    for(chunk = 0; chunk < chunk_limit; chunk++) {
      Block* bloque = new Block();
      Node* leave = new Leaf();
      LinkedList* aux = new LinkedList();
      bloque->eti = chunk;

      depth_t min = 0, max = 0, partial_excess = 0, ones = 0, numchunk = 0;
      unsigned int llimit = 0, ulimit = 0;
      unsigned int global_chunk = chunk; // se posiciona en el bloque que va ciclando
      
      if(st->num_chunks-1 < global_chunk) {
	      llimit = 0;
	      ulimit = 0;
      }
      else {
	        llimit = st->c*chunk;
          // mismo caso que el else if
	        ulimit = llimit + st->c; 
	        if(st->n < st->c)
	           ulimit = n;
	        if(ulimit > st->n)
	          ulimit = st->n;
        
      }
      unsigned int symbol=0;
      for(symbol=llimit ; symbol<ulimit  ;symbol++ ) {
        bool aux = (bool)bit_array_get_bit(bit_array, symbol);
        bloque->vect.push_back(aux);
        
        ++numchunk;
	// Excess computation
	      if(bit_array_get_bit(bit_array, symbol) == 0){
	        --partial_excess;
      
        }
	      else{
	        ++partial_excess;
          ++ones;
          
        }

	// Minimum computation
        if(symbol==llimit) {
          min = partial_excess; // By default the minimum value is the first excess value
          max = partial_excess; // By default the maximum value is the first excess value
         ///num_mins = 1;
        }
        else {
          if(partial_excess < min) {
          min = partial_excess;
         // num_mins = 1;
          } 
          if(partial_excess > max){
            max = partial_excess;
            }	  
          }
      }
      aux->InsertBlock(bloque);
      if(bloque->vect.size() < (st->s/2) ){
        int h = bloque -> vect.size();
        int i =(st->c);
        for(int h; h < ((st->s)/2)+1;h++){
          swap(bloque -> prev-> vect[i],bloque -> vect[h]);
          i--;
        }
         
        }
      leave  -> left  = bloque;
      leave  -> right = bloque;
      bloque -> leaf  = leave;
      if(global_chunk < st->num_chunks) {
	      leave -> t_excess = partial_excess;
	      leave -> t_min = min;
	      leave -> t_max = max;
        leave -> t_ones = ones;
        leave -> t_numchunk = numchunk;
      }  
      arrL[i] = leave;
      
      // este if calcula los valores de exceso minimo y maximo del bloque
      // considerar que se elimina todo lo relacionado con hebras
      /*if(global_chunk < st->num_chunks) {
	      leave -> t_excess = partial_excess;
	      leave -> t_min = min;
	      leave -> t_max = max;
        leave -> t_ones = ones;
        leave -> t_numchunk = numchunk;
      }*/
      /*printf("bloque %d con valores ="
                  "%d,%d,%d,%d,%d\n",
                  bloque->eti,
                  leave->t_excess,
                  leave->t_min,
                  leave->t_max,
                  leave->t_ones,
                  leave->t_numchunk
              );*/
    }
  /*
   * STEP 2.2: Completing the internal nodes of the min-max tree
   */
  // Connect Internal Nodes
  InternalNode* arr[(2*num_chunks-1)*sizeof(InternalNode + Node)]; 
  for (int i = 0 ; i<(2*num_chunks-1);i++){
    if(i<(2*num_chunks-1)){
      InternalNode* aux = new InternalNode();
      arr[i] = aux;
      if(i==0 && arr[0]!= NULL){
        aux = is_root();
        aux -> left   = NULL;
        aux -> right  = NULL;
        aux -> parent = NULL;
      }
      else if(arr[i]!=NULL){
        if(arr[(2*i)+1]==NULL){
         aux -> left = NULL;
        }
        else if(arr[(2*i)+2]==NULL){
          aux->right = NULL
        }
        else if( i%2 !=0){
         arr[(i-1)/2]-> left =arr[i];
        }
        else if(i%2 == 0){
          arr[(i-1)/2]-> right = arr[i];
        }
      aux -> parent  = arr[(i-1)/2];
      }
    }
    else{
      arr[i] = arrL[i-((2*num_chunks -1)/2)];
      if( arr[i]!=NULL){
        if (i%2 !=0){
          arr[(i-1)/2] -> left = arr[i];
        }
        else if(i%2 == 0){
          arr[(i-1)/2] -> right = arr[i];
        }
      arr[i] -> parent = arr[(i-1)/2];
      }
    }

    
  }
  // computational the 1° leave of internal Node
   for(int i = 0 ; i<(2*num_chunks-1);i=i+2){
    if(arr[i]->t_min < arr[i+1]-> t_min + arr[i]->t_excess){
      arr[(i-1)/2]->t_min = arr[i] -> t_min;
    }
    else{
      arr[(i-1)/2]-> t_min = arr[i+1]-> t_min + arr[i]->t_excess;
    }
    if(arr[i]-> t_max > arr[i+1]-> t_max + arr[i] -> t_excess){
      arr[(i-1)/2] -> t_max = arr[i] -> t_max;
    }
    else{
      arr[(i-1)/2]-> t_max = arr[i+1]-> t_max + arr[i]->t_excess;
    }
    arr[(i-1)/2] -> t_ones = arr[i] -> t_ones + arr[i+1] -> t_ones;
    arr[(i-1)/2] -> t_excess = arr[i] -> t_excess + arr[i+1] -> t_excess;
    arr[(i-1)/2] -> t_numchunk = arr[i] -> t_numchunk + arr[i+1] -> t_numchunk;

   }
   // computational of internal node
   for(int i=((2*num_chunks -1)/2)-1; i>=0;i=i-2){
    if(arr[i-1]->t_min < arr[i]-> t_min + arr[i-1]->t_excess){
      arr[(i-1)/2]->t_min = arr[i-1] -> t_min;
    }
    else{
      arr[(i-1)/2]-> t_min = arr[i]-> t_min + arr[i-1]->t_excess;
    }
    if(arr[i-1]-> t_max > arr[i]-> t_max + arr[i-1] -> t_excess){
      arr[(i-1)/2] -> t_max = arr[i-1] -> t_max;
    }
    else{
      arr[(i-1)/2]-> t_max = arr[i]-> t_max + arr[i-1]->t_excess;
    }
    arr[(i-1)/2] -> t_ones = arr[i-1] -> t_ones + arr[i] -> t_ones;
    arr[(i-1)/2] -> t_excess = arr[i-1] -> t_excess + arr[i] -> t_excess;
    arr[(i-1)/2] -> t_numchunk = arr[i-1] -> t_numchunk + arr[i] -> t_numchunk;
  
   }
  /*
   * STEP 3: Computation of all universal tables
   */

  T = create_lookup_tables();

  return st;
}
void insert_left(rmMT* st, int a){
  Node* navigate = new Node();
  Node* aux_n;
  Block* aux;
  navigate = is_root(); // start navigate in root
  //int aux= a; // position of node 
  aux_n = navigate(navigate,a);
  int open = open(aux_n, a);
  aux = aux_n -> left ->bloque;
 
  if(aux-> vec.size() < st->s){  
    aux->vec.insert(aux->vec.begin()+(open+1),1);
    aux->vec.insert(aux->vec.begin()+(open+2),0);
    int num = 0;
    for(int i=0;i<aux->vec.size();i++){
          num++;
         aux_n -> t_numchunk = num;
      }
    Node* paux = new Node();
    paux = nleft -> parent -> node;
    while (paux -> parent != NULL){
        paux -> t_numchunk = paux -> left -> node -> t_numchunk + paux -> right -> node -> t_numchunk;
        paux -> parent = node;
      }
  }
        
  else{
    Node* nleft   = new Node();
    Node* nright  = new Node();
    Block* lblock = new Block();
    Block* rblock = new Block();
    aux_n -> left -> nleft;
    aux_n -> right -> nright;
    nleft -> parent -> aux_n;
    nright -> parent -> aux_n;
    nleft -> left -> lblock;
    nleft -> right -> lblock;
    lblock -> prev -> bloque;
    bloque -> next -> lblock;
    lblock -> next -> rblock;
    lblock -> leaf -> nleft;
    nright -> left -> rblock;
    nright -> right -> rblock;
    rblock -> leaf -> nright;
    rblock -> prev -> lblock;
    rblock -> next -> bloque;
    bloque -> prev -> rblock;
    for(int i=0;i<bloque->vec.size();i++){
      if(i<(bloque->vec.size())/2){
        lblock->vec[i]=bloque->vec[i];
      }
      else{
        rblock->vec[i]= bloque->vec[i];
      } 
    }
    lblock->vec.insert(aux->vec.begin()+(a+1),1);
    lblock->vec.insert(aux->vec.begin()+(a+2),0);
    int ex = 0;
    int min = INT_MIN;
    int max = INT_MAX;
    int ones = 0;
    int num = 0;
    for(int i=0;i<lblock->vec.size();i++){
      if(lblock->vec[i]==1){
        ex++;
        ones++;
      }
      else{
        ex--;
      }
      num++;
      min = ex; 
      max = ex; 
      if(ex < min) {
        min = ex;
      
      } 
      if(ex > max){
        max = ex;
      }
    }
      nleft -> t_excess   = ex;
      nleft -> t_max      = max;
      nleft -> t_min      = min;
      nleft -> t_ones     = ones;
      nleft -> t_numchunk = num;
      int exx = 0;
      int minn = 0, maxx = 0 , oness = 0, numm = 0;
      for(int i=0;i<rblock->vec.size();i++){
      if(rblock->vec[i]==1){
        exx++;
        oness++;
      }
      else{
        exx--;
      }
      numm++;
      minn = exx; 
      maxx = exx; 
      if(exx < minn) {
        minn = exx;
      
      } 
      if(exx > maxx){
        maxx = exx;
      }
    }
      rleft -> t_excess   = exx;
      rleft -> t_max      = maxx;
      rleft -> t_min      = minn;
      rleft -> t_ones     = oness;
      rleft -> t_numchunk = numm;
        
      Node* paux = new Node();
      paux = nleft -> parent -> node;
      while (paux -> parent != NULL){
        if(paux-> left -> node -> t_min < paux -> left -> node -> t_excess + paux -> right -> node -> t_min){
          paux -> t_min =paux -> left -> node -> t_min;
        }
        else if (paux-> left -> node -> t_min > paux -> left-> node -> t_excess + paux -> right -> node -> t_min){
          paux -> t_min = paux -> left-> node -> t_excess + paux -> right -> node -> t_min;
        }
        if(paux -> left -> node -> t_max > paux -> left -> node -> t_excess + paux -> right -> node -> t_max){
           paux -> t_max = paux -> left -> node -> t_max;
        }
        else if (paux -> left -> node -> t_max < paux -> left -> node -> t_excess + paux -> right -> node -> t_max){
          paux -> t_max = paux -> left -> node -> t_excess + paux -> right -> node -> t_max;
        }
        paux -> t_ones = paux -> left -> node -> t_ones + paux -> right -> node -> t_ones;
        paux -> t_numchunk = paux -> left -> node -> t_numchunk + paux -> right -> node -> t_numchunk;
        paux -> t_excess = paux -> left -> node -> t_excess + paux -> right -> node -> t_excess; 
        paux -> parent -> node;
      }

    }
    

  }


void insert_right(rmMT* st, int a){
  Node* navigate = new Node();
  Node* aux_n;
  Block* aux;
  int close;
  navigate = is_root(); // start navigate in root
  aux_n = navigate2(navigate,a); 
  close = fws(st,-1,c);
  aux = aux_n -> left ->bloque;
  if(bloque-> vec.size() < st->s){  
          bloque->vec.insert(aux->vec.begin()+(close-1),0);
          bloque->vec.insert(aux->vec.begin()+(close-2),1);
          int num = 0;
    for(int i=0;i<aux->vec.size();i++){
          num++;
         aux_n -> t_numchunk = num;
      }
    Node* paux = new Node();
    paux = nleft -> parent -> node;
    while (paux -> parent != NULL){
        paux -> t_numchunk = paux -> left -> node -> t_numchunk + paux -> right -> node -> t_numchunk;
        paux -> parent = node;
      }
  }
  else{
    Node* nleft   = new Node();
    Node* nright  = new Node();
    Block* lblock = new Block();
    Block* rblock = new Block();
    aux_n -> left -> nleft;
    aux_n -> right -> nright;
    nleft -> parent -> aux_n;
    nright -> parent -> aux_n;
    nleft -> left -> lblock;
    nleft -> right -> lblock;
    lblock -> prev -> bloque;
    bloque -> next -> lblock;
    lblock -> next -> rblock;
    lblock -> leaf -> nleft;
    nright -> left -> rblock;
    nright -> right -> rblock;
    rblock -> leaf -> nright;
    rblock -> prev -> lblock;
    rblock -> next -> bloque;
    bloque -> prev -> rblock;
    for(int i=0;i<aux->vec.size();i++){
      if(i<(aux->vec.size())/2){
        lblock->vec[i]=bloque->vec[i];
      }
      else{
        rblock->vec[i]= bloque->vec[i];
      } 
    }
    rblock->vec.insert(aux->vec.begin()+(close-1),0);
    rblock->vec.insert(aux->vec.begin()+(close-2),1);
    int ex = 0;
    int min = INT_MIN;
    int max = INT_MAX;
    int ones = 0;
    int num = 0;
    for(int i=0;i<lblock->vec.size();i++){
      if(lblock->vec[i]==1){
        ex++;
        ones++;
      }
      else{
        ex--;
      }
      num++;
      min = ex; 
      max = ex; 
      if(ex < min) {
        min = ex;
      
      } 
      if(ex > max){
        max = ex;
      }
      nleft -> t_excess   = ex;
      nleft -> t_max      = max;
      nleft -> t_min      = min;
      nleft -> t_ones     = ones;
      nleft -> t_numchunk = num;
      int exx = 0;
      int minn = 0, maxx = 0 , oness = 0, numm = 0;
      for(int i=0;i<rblock->vec.size();i++){
      if(rblock->vec[i]==1){
        exx++;
        oness++;
      }
      else{
        exx--;
      }
      numm++;
      minn = exx; 
      maxx = exx; 
      if(exx < minn) {
        minn = exx;
      
      } 
      if(exx > maxx){
        maxx = exx;
      }
      rleft -> t_excess   = exx;
      rleft -> t_max      = maxx;
      rleft -> t_min      = minn;
      rleft -> t_ones     = oness;
      rleft -> t_numchunk = numm;
      }   
      Node* paux = new Node();
      paux = rleft -> parent -> node;
      while (paux -> parent != NULL){
        if(paux-> left -> node -> t_min < paux -> left -> node -> t_excess + paux -> right -> node -> t_min){
          paux -> t_min =paux -> left -> node -> t_min;
        }
        else if (paux-> left -> node -> t_min > paux -> left-> node -> t_excess + paux -> right -> node -> t_min){
          paux -> t_min = paux -> left-> node -> t_excess + paux -> right -> node -> t_min;
        }
        if(paux -> left -> node -> t_max > paux -> left -> node -> t_excess + paux -> right -> node -> t_max){
           paux -> t_max = paux -> left -> node -> t_max;
        }
        else if (paux -> left -> node -> t_max < paux -> left -> node -> t_excess + paux -> right -> node -> t_max){
          paux -> t_max = paux -> left -> node -> t_excess + paux -> right -> node -> t_max;
        }
        paux -> t_ones = paux -> left -> node -> t_ones + paux -> right -> node -> t_ones;
        paux -> t_numchunk = paux -> left -> node -> t_numchunk + paux -> right -> node -> t_numchunk;
        paux -> t_excess = paux -> left -> node -> t_excess + paux -> right -> node -> t_excess; 
        paux -> parent -> node;
      }

  }
  
}
void insert_parent(rmMT* st,int a){
  Node* navigate = new Node();
  Node* aux_n,aux_m;
  Block* l,r;
  navigate = is_root(); // start navigate in root
  //int aux= a; // position of node 
  aux_n = navigate(navigate,a);
  aux_m = navigate2(navigate,a)
  int open = open(aux_n, a);
  int close = fws(st,-1,a);
  l = aux_n -> left -> bloque;
  r = aux_m -> left -> bloque;
  if(l->vec-size()< st-> s){
    if(open-1 < 0){
      l->vec.insert(l->vec.begin()+0,1);
    }
    else{
      l->vec.insert(l->vec.begin()+(open-1),1);
    }
    for(int i=0;i<aux->vec.size();i++){
          num++;
         aux_n -> t_numchunk = num;
      }
    Node* paux = new Node();
    paux = nleft -> parent -> node;
    while (paux -> parent != NULL){
        paux -> t_numchunk = paux -> left -> node -> t_numchunk + paux -> right -> node -> t_numchunk;
        paux -> parent = node;
      }
  }
  else{
    Node* nleft   = new Node();
    Node* nright  = new Node();
    Block* lblock = new Block();
    Block* rblock = new Block();
    aux_n -> left -> nleft;
    aux_n -> right -> nright;
    nleft -> parent -> aux_n;
    nright -> parent -> aux_n;
    nleft -> left -> lblock;
    nleft -> right -> lblock;
    lblock -> prev -> bloque;
    bloque -> next -> lblock;
    lblock -> next -> rblock;
    lblock -> leaf -> nleft;
    nright -> left -> rblock;
    nright -> right -> rblock;
    rblock -> leaf -> nright;
    rblock -> prev -> lblock;
    rblock -> next -> bloque;
    bloque -> prev -> rblock;
    for(int i=0;i<l->vec.size();i++){
      if(i<(l->vec.size())/2){
        lblock->vec[i]=bloque->vec[i];
      }
      else{
        rblock->vec[i]= bloque->vec[i];
      } 
    }
    if(open < l->vec.size()/2){
      if(open-1 < 0){
        lblock->vec.insert(l->vec.begin()+0,1);
      }
      else{
        lblock->vec.insert(lblock->vec.begin()+(open-1),1);
      }
    }
    else{
      if(open-1 < 0){
        lblock->vec.insert(l->vec.begin()+0,1);
      }
      else{
        lblock->vec.insert(lblock->vec.begin()+(open-1),1);
      }
    }
    int ex = 0;
    int min = INT_MIN;
    int max = INT_MAX;
    int ones = 0;
    int num = 0;
    for(int i=0;i<lblock->vec.size();i++){
      if(lblock->vec[i]==1){
        ex++;
        ones++;
      }
      else{
        ex--;
      }
      num++;
      min = ex; 
      max = ex; 
      if(ex < min) {
        min = ex;
      
      } 
      if(ex > max){
        max = ex;
      }
    }
      nleft -> t_excess   = ex;
      nleft -> t_max      = max;
      nleft -> t_min      = min;
      nleft -> t_ones     = ones;
      nleft -> t_numchunk = num;
    int exx = 0;
    int minn = 0, maxx = 0 , oness = 0, numm = 0;
    for(int i=0;i<rblock->vec.size();i++){
    if(rblock->vec[i]==1){
        exx++;
        oness++;
      }
      else{
        exx--;
      }
      numm++;
      minn = exx; 
      maxx = exx; 
      if(exx < minn) {
        minn = exx;
      
      } 
      if(exx > maxx){
        maxx = exx;
      }
    }
      rleft -> t_excess   = exx;
      rleft -> t_max      = maxx;
      rleft -> t_min      = minn;
      rleft -> t_ones     = oness;
      rleft -> t_numchunk = numm;
        
      Node* paux = new Node();
      paux = nleft -> parent -> node;
      while (paux -> parent != NULL){
        if(paux-> left -> node -> t_min < paux -> left -> node -> t_excess + paux -> right -> node -> t_min){
          paux -> t_min =paux -> left -> node -> t_min;
        }
        else if (paux-> left -> node -> t_min > paux -> left-> node -> t_excess + paux -> right -> node -> t_min){
          paux -> t_min = paux -> left-> node -> t_excess + paux -> right -> node -> t_min;
        }
        if(paux -> left -> node -> t_max > paux -> left -> node -> t_excess + paux -> right -> node -> t_max){
           paux -> t_max = paux -> left -> node -> t_max;
        }
        else if (paux -> left -> node -> t_max < paux -> left -> node -> t_excess + paux -> right -> node -> t_max){
          paux -> t_max = paux -> left -> node -> t_excess + paux -> right -> node -> t_max;
        }
        paux -> t_ones = paux -> left -> node -> t_ones + paux -> right -> node -> t_ones;
        paux -> t_numchunk = paux -> left -> node -> t_numchunk + paux -> right -> node -> t_numchunk;
        paux -> t_excess = paux -> left -> node -> t_excess + paux -> right -> node -> t_excess; 
        paux -> parent -> node;
      }
  }
    
  }
  if(r->vec.size() < st->s){
    r->vec.insert(r->vec.begin()+(close+1),0);
  }
  else{
    Node* nleft1   = new Node();
    Node* nright1  = new Node();
    Block* lblock1 = new Block();
    Block* rblock1 = new Block();
    aux_m -> left -> nleft1;
    aux_m -> right -> nright1;
    nleft1 -> parent -> aux_m;
    nright1 -> parent -> aux_m;
    nleft1 -> left -> lblock1;
    nleft1 -> right -> lblock1;
    lblock1 -> prev -> bloque;
    bloque -> next -> lblock1;
    lblock1 -> next -> rblock1;
    lblock1 -> leaf -> nleft1;
    nright1 -> left -> rblock1;
    nright1 -> right -> rblock1;
    rblock1 -> leaf -> nright1;
    rblock1 -> prev -> lblock1;
    rblock1 -> next -> bloque;
    bloque -> prev -> rblock1;
    for(int i=0;i<r->vec.size();i++){
      if(i<(r->vec.size())/2){
        lblock1->vec[i]=r->vec[i];
      }
      else{
        rblock1->vec[i]= r->vec[i];
      } 
    }
    if(open < r->vec.size()/2){
      if(open-1 < 0){
        lblock1->vec.insert(lblock1->vec.begin()+0,1);
      }
      else{
        lblock1->vec.insert(lblock1->vec.begin()+(open-1),1);
      }
    }
    else{
      if(open-1 < 0){
        lblock1->vec.insert(lblock1->vec.begin()+0,1);
      }
      else{
        lblock1->vec.insert(lblock1->vec.begin()+(open-1),1);
      }
    }
    int ex1 = 0;
    int min1 = INT_MIN;
    int max1 = INT_MAX;
    int ones1 = 0;
    int num1 = 0;
    for(int i=0;i<lblock1->vec.size();i++){
      if(lblock1->vec[i]==1){
        ex1++;
        ones1++;
      }
      else{
        ex1--;
      }
      num1++;
      min1 = ex1; 
      max1 = ex1; 
      if(ex1 < min1) {
        min1 = ex1;
      
      } 
      if(ex1 > max1){
        max1 = ex1;
      }
    }
      nleft1 -> t_excess   = ex;
      nleft1 -> t_max      = max;
      nleft1 -> t_min      = min;
      nleft1 -> t_ones     = ones;
      nleft1 -> t_numchunk = num;
    int exx1 = 0;
    int minn 1= 0, maxx1 = 0 , oness1 = 0, numm1 = 0;
    for(int i=0;i<rblock1->vec.size();i++){
    if(rblock1->vec[i]==1){
        exx1++;
        oness1++;
      }
      else{
        exx1--;
      }
      numm1++;
      minn1 = exx1; 
      maxx1 = exx1; 
      if(exx1 < minn1) {
        minn1 = exx1;
      
      } 
      if(exx1 > maxx1){
        maxx1 = exx1;
      }
    }
      rleft1 -> t_excess   = exx;
      rleft1 -> t_max      = maxx;
      rleft1 -> t_min      = minn;
      rleft1 -> t_ones     = oness;
      rleft1 -> t_numchunk = numm;
        
      Node* paux1 = new Node();
      paux1 = nleft1 -> parent -> node;
      while (paux1 -> parent != NULL){
        if(paux1-> left -> node -> t_min < paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_min){
          paux1 -> t_min =paux1 -> left -> node -> t_min;
        }
        else if (paux1-> left -> node -> t_min > paux1 -> left-> node -> t_excess + paux1 -> right -> node -> t_min){
          paux1 -> t_min = paux1 -> left-> node -> t_excess + paux1 -> right -> node -> t_min;
        }
        if(paux1 -> left -> node -> t_max > paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_max){
           paux1 -> t_max = paux1 -> left -> node -> t_max;
        }
        else if (paux1 -> left -> node -> t_max < paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_max){
          paux1 -> t_max = paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_max;
        }
        paux1 -> t_ones = paux1 -> left -> node -> t_ones + paux1 -> right -> node -> t_ones;
        paux1 -> t_numchunk = paux1 -> left -> node -> t_numchunk + paux1 -> right -> node -> t_numchunk;
        paux1 -> t_excess = paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_excess; 
        paux1 -> parent -> node;
      }

  }
  

}
void erase(rmMT* st, int a){
  Node* navigate = new Node();
  int b = a;
  int close = fws(st,-1,b);
  int open = open(navigate,b);
  Node* aux = navigate(navigate,b);
  Block* baux = aux -> left -> bloque;
  Node* aux1 = navigate2(navigate,b);
  Block* baux1 = aux1 -> left -> bloque;
  if(baux-> vec.size() > (st->s)/2){
    baux -> vec.erase(baux -> vec.begin()+open);
  }
  else{
    Block* ant = baux -> prev -> bloque;
    Node* after = ant -> leaf -> node;
    Block* desp = baux -> next -> bloque;
    Node* before = desp -> leaf -> node;
    if(ant-> vec.size() > (st->s)*0.6){
      int size = st -> s - baux-> vec.size();
      Block* free = new Block();
      int t=0;
      for (int i = ant ->vec.size()-size; i < ant -> vec.size();i++){
        free -> vec.push_back(ant->vec[i]);
        ant -> vec.erase(ant ->vec.begin()+i);
        t++;
      }
      for (int i=t; i < baux ->vec.size();i++){
        free -> vec.push_back(baux->vec[i]);
      }
      baux->vec.clear();
      for(int i=0;i< free->vec.size();i++){
        baux-> vec.push_back(free->vec[i]);
      }
      free(free);
      baux -> vec.erase(baux -> vec.begin()+open);
      /*Calculo block ant*/
      int ex = 0;
      int exx = 0;
      int min = INT_MIN;
      int minn = INT_MIN;
      int max = INT_MAX;
      int maxx = INT_MAX;
      int ones = 0;
      int oness = 0;
      int num = 0;
      int numm = 0;
      for(int i=0;i<baux->vec.size();i++){
        if(baux->vec[i]==1){
          ex++;
          exx++
          ones++;
          oness++;
        }
        else{
          ex--;
          exx--;
        }
        num++;
        numm++;
        min = ex;
        minn = exx; 
        max = ex; 
        maxx = exx;
        if(ex < min) {
          min = ex;
      
        }
        if(exx < minn){
          minn = exx;
        } 
        if(ex > max){
          max = ex;
        }
        if(exx > maxx){
          maxx = exx;
        }
      }
      baux -> t_excess   = ex;
      baux -> t_max      = max;
      baux -> t_min      = min;
      baux -> t_ones     = ones;
      baux -> t_numchunk = num;
      after  -> t_excess   = exx;
      after  -> t_max      = maxx;
      after  -> t_min      = minn;
      after  -> t_ones     = oness;
      after  -> t_numchunk = numm;
      Node* paux = new Node();
      paux = baux -> parent -> node; 
      while (paux -> parent != NULL){
      if(paux-> left -> node -> t_min < paux -> left -> node -> t_excess + paux -> right -> node -> t_min){
        paux -> t_min =paux1 -> left -> node -> t_min;
      }
      else if (paux-> left -> node -> t_min > paux -> left-> node -> t_excess + paux -> right -> node -> t_min){
        paux -> t_min = paux -> left-> node -> t_excess + paux -> right -> node -> t_min;
      }
      if(paux -> left -> node -> t_max > paux -> left -> node -> t_excess + paux -> right -> node -> t_max){
         paux -> t_max = paux -> left -> node -> t_max;
      }
      else if (paux -> left -> node -> t_max < paux -> left -> node -> t_excess + paux -> right -> node -> t_max){
       paux -> t_max = paux -> left -> node -> t_excess + paux -> right -> node -> t_max;
      }
      paux -> t_ones = paux -> left -> node -> t_ones + paux -> right -> node -> t_ones;
      paux -> t_numchunk = paux -> left -> node -> t_numchunk + paux -> right -> node -> t_numchunk;
      paux -> t_excess = paux -> left -> node -> t_excess + paux -> right -> node -> t_excess; 
      paux -> parent -> node;
      }
      Node* paux1 = new Node();
      paux1 = after -> parent -> node; 
      while (paux -> parent != NULL){
      if(paux1-> left -> node -> t_min < paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_min){
        paux1 -> t_min =paux1 -> left -> node -> t_min;
      }
      else if (paux1-> left -> node -> t_min > paux1 -> left-> node -> t_excess + paux1 -> right -> node -> t_min){
        paux1 -> t_min = paux1 -> left-> node -> t_excess + paux1 -> right -> node -> t_min;
      }
      if(paux1 -> left -> node -> t_max > paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_max){
         paux1 -> t_max = paux1 -> left -> node -> t_max;
      }
      else if (paux1 -> left -> node -> t_max < paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_max){
       paux1 -> t_max = paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_max;
      }
      paux1 -> t_ones = paux1 -> left -> node -> t_ones + paux1 -> right -> node -> t_ones;
      paux1 -> t_numchunk = paux1 -> left -> node -> t_numchunk + paux1 -> right -> node -> t_numchunk;
      paux1 -> t_excess = paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_excess; 
      paux1 -> parent -> node;
      }

    }
    if(desp -> vec.size() > (st->s)*0.6 &&){
      int size1 = st -> s - baux -> vec.size();
      Block* free1 = new Block();
      for (int  i = 0; i </*condicion*/; i++){
        free1 -> vec.push_back(desp -> vec[i]);
        desp -> vec.erase(desp -> vec.begin()+i);
      }
      for(int j = size1; j<baux -> vec.size();j++){
        free1-> vec.push_back(baux -> vec[j]);
      }
      baux -> vec.clear();
      for (int k=0; k< free1-> vec.size();k++){
        baux -> vec.push_back(free1->vec[i]);
      }
      free(free1);
      baux -> vec.erase(baux -> vec.begin()+open);
      /*Calculo block despues*/
      int ex1 = 0;
      int exx1 = 0;
      int min1 = INT_MIN;
      int minn1 = INT_MIN;
      int max1 = INT_MAX;
      int maxx1 = INT_MAX;
      int ones1 = 0;
      int oness1 = 0;
      int num1 = 0;
      int numm1 = 0;
      for(int i=0;i<baux->vec.size();i++){
        if(baux->vec[i]==1){
          ex1++;
          exx1++
          ones1++;
          oness1++;
        }
        else{
          ex1--;
          exx1--;
        }
        num1++;
        numm1++;
        min1 = ex1;
        minn1 = exx1; 
        max1 = ex1; 
        maxx1 = exx1;
        if(ex1 < min1) {
          min1 = ex1;
      
        }
        if(exx1 < minn1){
          minn1 = exx1;
        } 
        if(ex1 > max1){
          max1 = ex1;
        }
        if(exx1 > maxx1){
          maxx1 = exx1;
        }
      }
      baux -> t_excess   = ex1;
      baux -> t_max      = max1;
      baux -> t_min      = min1;
      baux -> t_ones     = ones1;
      baux -> t_numchunk = num1;
      before  -> t_excess   = exx1;
      before  -> t_max      = maxx1;
      before  -> t_min      = minn1;
      before  -> t_ones     = oness1;
      before  -> t_numchunk = numm1;
      Node* paux2 = new Node();
      paux2 = baux -> parent -> node; 
      while (paux2 -> parent != NULL){
      if(paux2-> left -> node -> t_min < paux2 -> left -> node -> t_excess + paux2 -> right -> node -> t_min){
        paux2 -> t_min =paux2 -> left -> node -> t_min;
      }
      else if (paux2-> left -> node -> t_min > paux2 -> left-> node -> t_excess + paux2 -> right -> node -> t_min){
        paux2 -> t_min = paux2 -> left-> node -> t_excess + paux2 -> right -> node -> t_min;
      }
      if(paux2 -> left -> node -> t_max > paux2 -> left -> node -> t_excess + paux2 -> right -> node -> t_max){
         paux2 -> t_max = paux2 -> left -> node -> t_max;
      }
      else if (paux2 -> left -> node -> t_max < paux2 -> left -> node -> t_excess + paux2 -> right -> node -> t_max){
       paux2 -> t_max = paux2 -> left -> node -> t_excess + paux2 -> right -> node -> t_max;
      }
      paux2 -> t_ones = paux2 -> left -> node -> t_ones + paux2 -> right -> node -> t_ones;
      paux2 -> t_numchunk = paux2 -> left -> node -> t_numchunk + paux2 -> right -> node -> t_numchunk;
      paux2 -> t_excess = paux2 -> left -> node -> t_excess + paux2 -> right -> node -> t_excess; 
      paux2 -> parent -> node;
      }
      Node* paux3 = new Node();
      paux3 = before -> parent -> node; 
      while (paux -> parent != NULL){
      if(paux3-> left -> node -> t_min < paux3 -> left -> node -> t_excess + paux3 -> right -> node -> t_min){
        paux3 -> t_min =paux3 -> left -> node -> t_min;
      }
      else if (paux3-> left -> node -> t_min > paux3 -> left-> node -> t_excess + paux3 -> right -> node -> t_min){
        paux3 -> t_min = paux3 -> left-> node -> t_excess + paux3 -> right -> node -> t_min;
      }
      if(paux3 -> left -> node -> t_max > paux3 -> left -> node -> t_excess + paux3 -> right -> node -> t_max){
         paux3 -> t_max = paux3 -> left -> node -> t_max;
      }
      else if (paux3 -> left -> node -> t_max < paux3 -> left -> node -> t_excess + paux3 -> right -> node -> t_max){
       paux3 -> t_max = paux3 -> left -> node -> t_excess + paux3 -> right -> node -> t_max;
      }
      paux3 -> t_ones = paux3 -> left -> node -> t_ones + paux3 -> right -> node -> t_ones;
      paux3 -> t_numchunk = paux3 -> left -> node -> t_numchunk + paux3 -> right -> node -> t_numchunk;
      paux3 -> t_excess = paux3 -> left -> node -> t_excess + paux3 -> right -> node -> t_excess; 
      paux3 -> parent -> node;
      }

    }
  }
  /*PARENTESIS DE CIERRE*/
  if(baux1-> vec.size() > (st->s)/2){
    baux1 -> vec.erase(baux1 -> vec.begin()+open);
  }
  else{
    Block* ant = baux -> prev -> bloque;
    Node* after = ant -> leaf -> node;
    Block* desp = baux -> next -> bloque;
    Node* before = desp -> leaf -> node;
    if(ant-> vec.size() > (st->s)*0.6){
      int size = st -> s - baux-> vec.size();
      Block* free = new Block();
      int t=0;
      for (int i = ant ->vec.size()-size; i < ant -> vec.size();i++){
        free -> vec.push_back(ant->vec[i]);
        ant -> vec.erase(ant ->vec.begin()+i);
        t++;
      }
      for (int i=t; i < baux ->vec.size();i++){
        free -> vec.push_back(baux->vec[i]);
      }
      baux->vec.clear();
      for(int i=0;i< free->vec.size();i++){
        baux-> vec.push_back(free->vec[i]);
      }
      free(free);
      baux -> vec.erase(baux -> vec.begin()+open);
      /*Calculo block ant*/
      int ex = 0;
      int exx = 0;
      int min = INT_MIN;
      int minn = INT_MIN;
      int max = INT_MAX;
      int maxx = INT_MAX;
      int ones = 0;
      int oness = 0;
      int num = 0;
      int numm = 0;
      for(int i=0;i<baux->vec.size();i++){
        if(baux->vec[i]==1){
          ex++;
          exx++
          ones++;
          oness++;
        }
        else{
          ex--;
          exx--;
        }
        num++;
        numm++;
        min = ex;
        minn = exx; 
        max = ex; 
        maxx = exx;
        if(ex < min) {
          min = ex;
      
        }
        if(exx < minn){
          minn = exx;
        } 
        if(ex > max){
          max = ex;
        }
        if(exx > maxx){
          maxx = exx;
        }
      }
      baux -> t_excess   = ex;
      baux -> t_max      = max;
      baux -> t_min      = min;
      baux -> t_ones     = ones;
      baux -> t_numchunk = num;
      after  -> t_excess   = exx;
      after  -> t_max      = maxx;
      after  -> t_min      = minn;
      after  -> t_ones     = oness;
      after  -> t_numchunk = numm;
      Node* paux = new Node();
      paux = baux -> parent -> node; 
      while (paux -> parent != NULL){
      if(paux-> left -> node -> t_min < paux -> left -> node -> t_excess + paux -> right -> node -> t_min){
        paux -> t_min =paux1 -> left -> node -> t_min;
      }
      else if (paux-> left -> node -> t_min > paux -> left-> node -> t_excess + paux -> right -> node -> t_min){
        paux -> t_min = paux -> left-> node -> t_excess + paux -> right -> node -> t_min;
      }
      if(paux -> left -> node -> t_max > paux -> left -> node -> t_excess + paux -> right -> node -> t_max){
         paux -> t_max = paux -> left -> node -> t_max;
      }
      else if (paux -> left -> node -> t_max < paux -> left -> node -> t_excess + paux -> right -> node -> t_max){
       paux -> t_max = paux -> left -> node -> t_excess + paux -> right -> node -> t_max;
      }
      paux -> t_ones = paux -> left -> node -> t_ones + paux -> right -> node -> t_ones;
      paux -> t_numchunk = paux -> left -> node -> t_numchunk + paux -> right -> node -> t_numchunk;
      paux -> t_excess = paux -> left -> node -> t_excess + paux -> right -> node -> t_excess; 
      paux -> parent -> node;
      }
      Node* paux1 = new Node();
      paux1 = after -> parent -> node; 
      while (paux -> parent != NULL){
      if(paux1-> left -> node -> t_min < paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_min){
        paux1 -> t_min =paux1 -> left -> node -> t_min;
      }
      else if (paux1-> left -> node -> t_min > paux1 -> left-> node -> t_excess + paux1 -> right -> node -> t_min){
        paux1 -> t_min = paux1 -> left-> node -> t_excess + paux1 -> right -> node -> t_min;
      }
      if(paux1 -> left -> node -> t_max > paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_max){
         paux1 -> t_max = paux1 -> left -> node -> t_max;
      }
      else if (paux1 -> left -> node -> t_max < paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_max){
       paux1 -> t_max = paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_max;
      }
      paux1 -> t_ones = paux1 -> left -> node -> t_ones + paux1 -> right -> node -> t_ones;
      paux1 -> t_numchunk = paux1 -> left -> node -> t_numchunk + paux1 -> right -> node -> t_numchunk;
      paux1 -> t_excess = paux1 -> left -> node -> t_excess + paux1 -> right -> node -> t_excess; 
      paux1 -> parent -> node;
      }

    }
    if(desp -> vec.size() > (st->s)*0.6 &&){
      int size1 = st -> s - baux -> vec.size();
      Block* free1 = new Block();
      for (int  i = 0; i </*condicion*/; i++){
        free1 -> vec.push_back(desp -> vec[i]);
        desp -> vec.erase(desp -> vec.begin()+i);
      }
      for(int j = size1; j<baux -> vec.size();j++){
        free1-> vec.push_back(baux -> vec[j]);
      }
      baux -> vec.clear();
      for (int k=0; k< free1-> vec.size();k++){
        baux -> vec.push_back(free1->vec[i]);
      }
      free(free1);
      baux -> vec.erase(baux -> vec.begin()+open);
      /*Calculo block despues*/
      int ex1 = 0;
      int exx1 = 0;
      int min1 = INT_MIN;
      int minn1 = INT_MIN;
      int max1 = INT_MAX;
      int maxx1 = INT_MAX;
      int ones1 = 0;
      int oness1 = 0;
      int num1 = 0;
      int numm1 = 0;
      for(int i=0;i<baux->vec.size();i++){
        if(baux->vec[i]==1){
          ex1++;
          exx1++
          ones1++;
          oness1++;
        }
        else{
          ex1--;
          exx1--;
        }
        num1++;
        numm1++;
        min1 = ex1;
        minn1 = exx1; 
        max1 = ex1; 
        maxx1 = exx1;
        if(ex1 < min1) {
          min1 = ex1;
      
        }
        if(exx1 < minn1){
          minn1 = exx1;
        } 
        if(ex1 > max1){
          max1 = ex1;
        }
        if(exx1 > maxx1){
          maxx1 = exx1;
        }
      }
      baux -> t_excess   = ex1;
      baux -> t_max      = max1;
      baux -> t_min      = min1;
      baux -> t_ones     = ones1;
      baux -> t_numchunk = num1;
      before  -> t_excess   = exx1;
      before  -> t_max      = maxx1;
      before  -> t_min      = minn1;
      before  -> t_ones     = oness1;
      before  -> t_numchunk = numm1;
      Node* paux2 = new Node();
      paux2 = baux -> parent -> node; 
      while (paux2 -> parent != NULL){
      if(paux2-> left -> node -> t_min < paux2 -> left -> node -> t_excess + paux2 -> right -> node -> t_min){
        paux2 -> t_min =paux2 -> left -> node -> t_min;
      }
      else if (paux2-> left -> node -> t_min > paux2 -> left-> node -> t_excess + paux2 -> right -> node -> t_min){
        paux2 -> t_min = paux2 -> left-> node -> t_excess + paux2 -> right -> node -> t_min;
      }
      if(paux2 -> left -> node -> t_max > paux2 -> left -> node -> t_excess + paux2 -> right -> node -> t_max){
         paux2 -> t_max = paux2 -> left -> node -> t_max;
      }
      else if (paux2 -> left -> node -> t_max < paux2 -> left -> node -> t_excess + paux2 -> right -> node -> t_max){
       paux2 -> t_max = paux2 -> left -> node -> t_excess + paux2 -> right -> node -> t_max;
      }
      paux2 -> t_ones = paux2 -> left -> node -> t_ones + paux2 -> right -> node -> t_ones;
      paux2 -> t_numchunk = paux2 -> left -> node -> t_numchunk + paux2 -> right -> node -> t_numchunk;
      paux2 -> t_excess = paux2 -> left -> node -> t_excess + paux2 -> right -> node -> t_excess; 
      paux2 -> parent -> node;
      }
      Node* paux3 = new Node();
      paux3 = before -> parent -> node; 
      while (paux -> parent != NULL){
      if(paux3-> left -> node -> t_min < paux3 -> left -> node -> t_excess + paux3 -> right -> node -> t_min){
        paux3 -> t_min =paux3 -> left -> node -> t_min;
      }
      else if (paux3-> left -> node -> t_min > paux3 -> left-> node -> t_excess + paux3 -> right -> node -> t_min){
        paux3 -> t_min = paux3 -> left-> node -> t_excess + paux3 -> right -> node -> t_min;
      }
      if(paux3 -> left -> node -> t_max > paux3 -> left -> node -> t_excess + paux3 -> right -> node -> t_max){
         paux3 -> t_max = paux3 -> left -> node -> t_max;
      }
      else if (paux3 -> left -> node -> t_max < paux3 -> left -> node -> t_excess + paux3 -> right -> node -> t_max){
       paux3 -> t_max = paux3 -> left -> node -> t_excess + paux3 -> right -> node -> t_max;
      }
      paux3 -> t_ones = paux3 -> left -> node -> t_ones + paux3 -> right -> node -> t_ones;
      paux3 -> t_numchunk = paux3 -> left -> node -> t_numchunk + paux3 -> right -> node -> t_numchunk;
      paux3 -> t_excess = paux3 -> left -> node -> t_excess + paux3 -> right -> node -> t_excess; 
      paux3 -> parent -> node;
      }

    }
    
  }
  
}
int fws(rmMT* st,int d,int a){
  int d = -1;
  int d_prime;
  Node* aux = navigate(aux,a);
  int open_aux = open(aux,a);
  Block* baux = aux ->left -> bloque;
  int aux_excess=0;
  int value = 0;
  for(int i=0;i<baux ->vec[a];i++){
    if (baux -> vec[i]==1){
      value++;
    }
    else(baux -> vec[i]==0){
      value--;
    }

  }
  for(int i=open_aux;i<baux->vec.size();i++){
      if(baux->vec[i]==1){
        aux_excess++;
      }
      else if(baux->vec[i]==0){
        aux_excess--;
      }
      else if(baux->vec[a]+d == baux->vec[i]){
        int 
        return i;
      }    
  }
  int d_prime = aux_excess;
  while(true){
    if(aux -> left -> node -> t_min  + d_prime =< d){
      if(aux -> left == aux -> right){
         aux -> left -> node;
        Block* rec = aux -> left -> bloque;
        for(int i=0;i< rec->vec.size();i++){
          if( value =rec->vec[i] + d){
            return i;
          }
        }
      }
      d_prime = d_prime + aux -> t_excess; 
    }
    else if(aux -> right -> node -> t_min  + d_prime =< d){
      aux -> left -> node;
      Block* rec = aux -> left -> bloque;
      for(int i=0;i< rec->vec.size();i++){
        if( value =rec->vec[i] + d){
          return i;
        }
      }

    }
    else{
      d_prime = d_prime + aux -> t_excess;
      aux = aux -> parent -> node;
    }
  }
}

Node* navigate (Node* node,int a){
  Node* aux;
  int aux_ones;
  if(node -> t_ones < a && node->left != node->right){
    aux_ones=a;
   if(node->left ->node -> t_ones < aux_ones){
    aux = node ->left -> node;
    aux_ones = node -> left -> node -> t_ones;
    navigate(aux,aux_ones);
   } 
   else{
    aux = node -> right -> node;
    aux_ones = node -> right -> node -> t_ones;
    navigate(aux,aux_ones);
   }
  }
  return node;



}
int open(Node* node, int a){
  Node* aux = node;
  int aux_ones = 0;
  while (aux -> left != aux -> right){
    if( aux ->  left -> aux -> t_ones < a){
        aux -> left -> node;
    }
    else{
      aux_ones = aux_ones + a;
      aux -> right -> node; 
    }
  }
  Block* baux;
  baux = aux -> left -> bloque;
  for (int i=0; i< buax -> vec.size();i++){
      if(baux ->vec[i]==1){
        aux_ones++;
      }
      if(aux_ones == a){
        return i;
      }
  }
}
int32_t sum(rmMt* st, int32_t idx){

  if(idx >= st->n)
    return -1;
  
  int32_t chk = idx/st->s;
  int32_t excess = 0;

  // Previous chunk
  if(chk)
    excess += st->e_prime[chk-1];
  
  int llimit = chk*st->s;
  int rlimit = (idx/8)*8;

  word_t j=0;
  for(j=llimit; j<rlimit; j+=8) {
#ifdef ARCH64
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFFL<<(j&(word_size-1)))) >> (j&(word_size-1));
#else
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFF<<(j&(word_size-1)))) >> (j&(word_size-1));
#endif

    excess += T->word_sum[sum_idx];
  }

  for(uint i=j; i<=idx; i++)
    excess += 2*bit_array_get_bit(st->bit_array,i)-1;

  return excess;
}

int32_t check_leaf(rmMt* st, int32_t i, int32_t d) {
  int end = (i/st->s+1)*st->s;
  int llimit = (((i)+8)/8)*8;
  int rlimit = (end/8)*8;
  int32_t excess = d;
  int32_t output;
  int32_t j = 0;

  for(j=i+1; j< min(end, llimit); j++){
    excess += 2*bit_array_get_bit(st->bit_array,j)-1;
    if(excess == d-1)
      return j;
  }

  for(j=llimit; j<rlimit; j+=8) {
    int32_t desired = d - 1 - excess; // desired value must belongs to the range [-8,8]
    
#ifdef ARCH64
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFFL<<(j&(word_size-1)))) >> (j&(word_size-1));
#else
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFF<<(j&(word_size-1)))) >> (j&(word_size-1));
#endif
    
    if (desired >= -8 && desired <= 8) {
    uint16_t ii = (desired+8<<8) + sum_idx;
        
    int8_t x = T->near_fwd_pos[ii];
    if(x < 8)
      return j+x;
  }
    excess += T->word_sum[sum_idx];
  }
  
  for (j=max(llimit,rlimit); j < end; ++j) {
    excess += 2*bit_array_get_bit(st->bit_array,j)-1;
    if (excess == d-1) {
      return j;
    }
  }
  
  return i-1;
}


int32_t check_sibling(rmMt* st, int32_t i, int32_t d) {
  int llimit = i;
  int rlimit = i+st->s;
  int32_t output;
  int32_t excess = st->e_prime[(i-1)/st->s];
  int32_t j = 0;

  for(j=llimit; j<rlimit; j+=8) {
    int32_t desired = d - 1 - excess; // desired value must belongs to the range [-8,8]  
    
#ifdef ARCH64
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFFL<<(j&(word_size-1)))) >> (j&(word_size-1));
#else
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFF<<(j&(word_size-1)))) >> (j&(word_size-1));
#endif
    
    if (desired >= -8 && desired <= 8) {
    uint16_t ii = (desired+8<<8) + sum_idx;
    
    int8_t x = T->near_fwd_pos[ii];
    if(x < 8)
      return j+x;
  }
    excess += T->word_sum[sum_idx];
  }
    
  return i-1;
}
// Funciones 
int32_t fwd_search2(rmMt* st, int32_t i) {
    // Excess value up to the ith position 
    int32_t d = sum(st, i);
    
    int chunk = i / st->s;
    int32_t output;
    long j;
    
    // Case 1: Check if the chunk of i contains fwd_search(B, i, d)
    
    output = check_leaf(st, i, d);
    if(output > i)
      return output;
    
    // Case 2: The answer is not in the chunk of i, but it is in its sibling
    // (assuming a binary tree, if i%2==0, then its right sibling is at position
    // i+1)
    
    if(chunk%2 == 0) { // The current chunk has a right sibling
      // The answer is in the right sibling of the current node
      if(st->m_prime[chunk+1] <= d && d <= st->M_prime[chunk+1]) { 
	output = check_sibling(st, st->s*(chunk+1), d);
	if(output >= st->s*(chunk+1))
	  return output;
      }
    }
  
    // Case 3: It is necessary up and then down in the min-max tree
    
    long node = parent(st->internal_nodes + chunk); // Initial node
    // Go up the tree
    while (!is_root(node)) {
      if (is_left_child(node)) { // if the node is a left child
	node = right_sibling(node); // choose right sibling
	
	if (st->m_prime[node] <= d-1 && d-1 <= st->M_prime[node])
	  break;
      }
      node = parent(node); // choose parent
    }

    // Go down the tree
    if (!is_root(node)) { // found solution for the query
      while (!is_leaf(node, st)) {
	node = left_child(node); // choose left child
	if (!(st->m_prime[node] <= d-1 && d-1 <= st->M_prime[node])) {
	  node = right_sibling(node); // choose right child == right sibling of the left child
	  if(st->m_prime[node] > d-1 || d-1 > st->M_prime[node]) {
	    return -1;
	  }
	}
      }

      chunk = node - st->internal_nodes;
      return check_sibling(st, st->s*chunk, d);
    }
    return -1;
}

// Check a leaf from left to right
int32_t check_leaf_r(rmMt* st, int32_t i, int32_t d) {
  int end = (i/st->c+1)*st->c;
  int llimit = (((i)+8)/8)*8;
  int rlimit = (end/8)*8;
  int32_t excess = d;
  int32_t output;
  int32_t j = 0;
  
  for(j=i+1; j< min(end, llimit); j++){
    excess += 2*bit_array_get_bit(st->bit_array,j)-1;
    if(excess == d-1)
      return j;
  }

  for(j=llimit; j<rlimit; j+=8) {
    int32_t desired = d - 1 - excess; // desired value must belongs to the range [-8,8]
    
#ifdef ARCH64
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFFL<<(j&(word_size-1)))) >> (j&(word_size-1));
#else
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFF<<(j&(word_size-1)))) >> (j&(word_size-1));
#endif
    
    if (desired >= -8 && desired <= 8) {
    uint16_t ii = (desired+8<<8) + sum_idx;
        
    int8_t x = T->near_fwd_pos[ii];
    if(x < 8)
      return j+x;
  }
    excess += T->word_sum[sum_idx];
  }
  
  for (j=max(llimit,rlimit); j < end; ++j) {
    excess += 2*bit_array_get_bit(st->bit_array,j)-1;
    if (excess == d-1) {
      return j;
    }
  }
  
  return i-1;
}

// Check siblings from left to right
int32_t check_sibling_r(rmMt* st, int32_t i, int32_t d) {
  int llimit = i;
  int rlimit = i+st->s;
  int32_t output;
  int32_t excess = st->e_prime[(i-1)/st->s];
  int32_t j = 0;

  for(j=llimit; j<rlimit; j+=8) {
    int32_t desired = d - excess; // desired value must belongs to the range [-8,8]  
    
#ifdef ARCH64
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFFL<<(j&(word_size-1)))) >> (j&(word_size-1));
#else
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFF<<(j&(word_size-1)))) >> (j&(word_size-1));
#endif
    
    if (desired >= -8 && desired <= 8) {
      uint16_t ii = (desired+8<<8) + sum_idx;
      
      int8_t x = T->near_fwd_pos[ii];
      
      if(x < 8)
	return j+x;
    }
    excess += T->word_sum[sum_idx];
  }
    
  return i-1;
}

int32_t fwd_search(rmMt* st, int32_t i, int32_t d) {
    // Excess value up to the ith position 
    int32_t target = sum(st, i) + d - 1;
    
    int chunk = i / st->c;
    int32_t output;
    long j;
    
    // Case 1: Check if the chunk of i contains fwd_search(bit_array, i, target)
    output = check_leaf_r(st, i, target);
    if(output > i)
      return output;
    
    // Case 2: The answer is not in the chunk of i, but it is in its sibling
    // (assuming a binary tree, if i%2==0, then its right sibling is at position i+1)
    if(chunk%2 == 0) { // The current chunk has a right sibling
      // The answer is in the right sibling of the current node
      if(st->m_prime[st->internal_nodes + chunk+1] <= target && target <=
	 st->M_prime[st->internal_nodes+ chunk+1]) {

	output = check_sibling_r(st, st->c*(chunk+1), target);
	if(output >= st->s*(chunk+1))
	  return output;
      }
    }
  
    // Case 3: It is necessary up and then down in the min-max tree
    long node = parent(chunk + st->internal_nodes); // Initial node
    // Go up the tree
    while (!is_root(node)) {
      if (is_left_child(node)) { // if the node is a left child
	node = right_sibling(node); // choose right sibling
	
	if (st->m_prime[node] <= target && target <= st->M_prime[node])
	  break;
      }
      node = parent(node); // choose parent
    }

    // Go down the tree
    if (!is_root(node)) { // found solution for the query
      while (!is_leaf(node, st)) {
	node = left_child(node); // choose left child
	if (!(st->m_prime[node] <= target && target <= st->M_prime[node])) {
	  node = right_sibling(node); // choose right child == right sibling of the left child
	  if(st->m_prime[node] > target || target > st->M_prime[node]) {
	    return i;
	  }
	}
      }
      
      chunk = node - st->internal_nodes;

      return check_sibling_r(st, st->s*chunk, target);
    }
    return i;
}

int32_t find_close(rmMt* st, int32_t i){
  if(bit_array_get_bit(st->bit_array,i) == 0)
    return i;

  return fwd_search(st, i, 0);
}

S
// Naive implementation of fwd_search
int32_t naive_fwd_search(rmMt* st, int32_t i, int32_t d) {
  int begin = i+1;
  int end = st->n;
  int32_t excess = sum(st, i);
  int32_t target = excess + d - 1;
  int32_t j = 0;

  for(j=begin; j < end; j++) {
    excess += 2*bit_array_get_bit(st->bit_array,j)-1;
    if(excess == target)
      return j;
  }

  return i;
}

// Semi naive implementation of fwd_search
int32_t semi_fwd_search(rmMt* st, int32_t i, int32_t d) {
  int32_t excess = sum(st, i);
  int32_t target = excess + d - 1;
  int32_t j = 0;
  int chunk = i/st->s;

  int begin = i+1;
  int end = (chunk+1)*st->s;
  for(j=begin; j < end; j++) {
    excess += 2*bit_array_get_bit(st->bit_array,j)-1;
    if(excess == target)
      return j;
  }

  begin = chunk+1;
  end = st->num_chunks;
  for(j=begin; j<end;j++) {
    uint idx = st->internal_nodes + j;
    if(st->m_prime[idx] <= target && st->M_prime[idx] >= target) {
      chunk = j;
      break;
    }
  }

  begin = chunk*st->s;
  end = (chunk+1)*st->s;
  excess = st->e_prime[chunk-1];

  for(j=begin; j < end; j++) {
    excess += 2*bit_array_get_bit(st->bit_array,j)-1;
    if(excess == target)
      return j;
  }
  return i;
}

int32_t find_close_naive(rmMt* st, int32_t i){
  if(bit_array_get_bit(st->bit_array,i) == 0)
    return i;

  return naive_fwd_search(st, i, 0);
}

int32_t find_close_semi(rmMt* st, int32_t i){
  if(bit_array_get_bit(st->bit_array,i) == 0)
    return i;

  return semi_fwd_search(st, i, 0);
}

int32_t rank_0(rmMt* st, int32_t i) {
  // Excess value up to the ith position
  if(i >= st->n)
    i = st->n-1;
    int32_t d = sum(st, i);
  
  return (i+1-d)/2;
}


// Naive implementation of bwd_search
int32_t naive_bwd_search(rmMt* st, int32_t i, int32_t d) {
  int begin = 0;
  int32_t excess = sum(st, i);
  int32_t target = excess + d;
  int32_t j = 0;

  for(j=i; j >= begin; j--) {
    excess += 2*bit_array_get_bit(st->bit_array,j)-1;
    if(excess == target) {
      return j;
    }
  }

  return i;
}

// Semi implementation of bwd_search
int32_t semi_bwd_search(rmMt* st, int32_t i, int32_t d) {
  int32_t excess = sum(st, i);
  int32_t target = excess + d;
  int32_t j = 0;

  if(target == 0 && i == st->n-1)
    return 0;
  
  int chunk = i/st->s;
  int begin = i;
  int end = chunk*st->s;

  for(j=begin; j >= end; j--) {
    excess += 1 - 2*bit_array_get_bit(st->bit_array,j);
    if(excess == target)
      return j;
  }

  begin = chunk-1;
  end = 0;

  for(j=begin; j >= end; j--) {
    int idx = st->internal_nodes + j;

    if(st->m_prime[idx] <= target && st->M_prime[idx] >= target) {
      chunk = j;
      break;
    }
  }

  begin = (chunk+1)*st->s-1;
  end = chunk*st->s;
  excess = st->e_prime[chunk];

  // Special case 2
  if(excess == target)
    return begin+1;

  for(j=begin; j >= end; j--) {
    excess += 1 - 2*bit_array_get_bit(st->bit_array,j);
    if(excess == target)
      return j;
  }

  return i;
}

// Check a leaf from right to left
int32_t check_leaf_l(rmMt* st, int32_t i, int32_t target, int32_t excess) {
  int rlimit = (i/8)*8;
  int begin = (i/st->s)*st->s;
  int llimit = ((begin+8)/8)*8;
  if(llimit > rlimit)
    llimit = rlimit;
  int32_t output;
  int32_t j = 0;

  for(j=i; j >= max(rlimit, llimit); j--){
    excess += 2*bit_array_get_bit(st->bit_array,j)-1;
    if(excess == target) {
      return j;
    }
  }
  for(j = rlimit-8; j >= llimit; j-=8) {
    int32_t desired = excess - target; // desired value must belongs to the range [-8,8]
    
#ifdef ARCH64
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFFL<<(j&(word_size-1)))) >> (j&(word_size-1));
#else
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFF<<(j&(word_size-1)))) >> (j&(word_size-1));
#endif
    if (desired >= -8 && desired <= 8) {
      uint16_t ii = (desired+8<<8) + sum_idx;
      
      int8_t x = T->near_bwd_pos[ii];
      if(x < 8)
	return j+x;
    }
    excess += T->word_sum[sum_idx];
  }

  for (j=min(llimit,rlimit)-1; j >= begin; j--) {
    excess += 2*bit_array_get_bit(st->bit_array,j)-1;
    if (excess == target) {
      return j;
    }
  }
  
  return i;
}

// Check a left sibling
int32_t check_sibling_l(rmMt* st, int32_t i, int32_t excess, int32_t d) {
  int llimit = i;
  int rlimit = i+st->s;

  int32_t e = st->e_prime[i/st->s];
  int32_t output;
  int32_t j = 0;

  for(j = rlimit-8; j >= llimit; j-=8) {
    int32_t desired =  excess - d - e; // desired value must belongs to the range [-8,8]
    
#ifdef ARCH64
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFFL<<(j&(word_size-1)))) >> (j&(word_size-1));
#else
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFF<<(j&(word_size-1)))) >> (j&(word_size-1));
#endif
    if (desired >= -8 && desired <= 8) {
      uint16_t ii = (desired+8<<8) + sum_idx;
      
      int8_t x = T->near_bwd_pos[ii];
      if(x < 8)
	return j+x;
    }
    e -= T->word_sum[sum_idx];
  }
  
  return i-1;
}

int32_t bwd_search(rmMt* st, int32_t i, int32_t d) {
  int32_t excess = sum(st, i);
  int32_t target = excess + d;

  int chunk = i / st->s;
  int32_t output = i;
  long j;

  // Case 1: Check if the chunk of i contains bwd_search(bit_array, i, target)
  output = check_leaf_l(st, i, target, excess);
  if(output < i)
    return output;
  
  // Case 2: The answer is not in the chunk of i, but it is in its sibling
  // (assuming a binary tree, if i%2==1, then its left sibling is at position i-1)
  if(chunk%2 == 1) { // The current chunk has a left sibling
    // The answer is in the left sibling of the current node
    if(st->m_prime[st->internal_nodes + chunk - 1] <= excess-d+1 && excess-d+1 <=
       st->M_prime[st->internal_nodes + chunk - 1]) {
      
      output = check_sibling_l(st, st->s*(chunk-1), excess, d);
      if(output >= st->s*(chunk-1))
  	return output;
    }
  }

  // Case 3: It is necessary up and then down in the min-max tree
  long node = parent(chunk + st->internal_nodes); // Initial node
  // Go up the tree
  while (!is_root(node)) {
    if (is_right_child(node)) { // if the node is a left child
      node = left_sibling(node); // choose right sibling
      
      //      if (st->m_prime[node] <= target && target <= st->M_prime[node])
      if (st->m_prime[node] <= excess-d && excess-d <= st->M_prime[node])
	break;      
    }
    node = parent(node); // choose parent
  }

  // Go down the tree
  if (!is_root(node)) { // found solution for the query
    while (!is_leaf(node, st)) {
      node = right_child(node); // choose right child

      if (!(st->m_prime[node] <= excess-d && excess-d <= st->M_prime[node])) {
	node = left_sibling(node); // choose left child == left sibling of the	right child
	
	if(st->m_prime[node] > excess-d || excess-d > st->M_prime[node]) {
	  return i;
	}
      }
    }

    chunk = node - st->internal_nodes;

    // Special case: if the result is at the beginning of chunk i, then,
    // the previous condition will select the chunk i-1
    //    if(st->e_prime[chunk] == target) { // If the last value (e') of chunk is equal
    if(st->e_prime[chunk] == excess-d) { // If the last value (e') of chunk is equal
    // to the target, then the answer is in the first position of the next chunk

      return (chunk+1)*st->s;
    }
    
    return check_sibling_l(st, st->s*chunk, excess, d);
  }
  else {// Special case: Pair of parentheses wrapping the parentheses sequence
        //(at positions 0 and n-1)
    if(i == st->n-1 && excess==0)
      output = 0;
  }

  return output;
}

int32_t find_open_naive(rmMt* st, int32_t i){
  if(bit_array_get_bit(st->bit_array,i) == 1)
    return i;

  return naive_bwd_search(st, i, 0);  
}

int32_t find_open(rmMt* st, int32_t i){
  if(bit_array_get_bit(st->bit_array,i) == 1)
    return i;

  return bwd_search(st, i, 0);  
}

int32_t find_open_semi(rmMt* st, int32_t i){
  if(bit_array_get_bit(st->bit_array,i) == 1)
    return i;

  return semi_bwd_search(st, i, 0);  
}

int32_t rank_1(rmMt* st, int32_t i) {
    // Excess value up to the ith position 
  if(i >= st->n)
    i = st->n-1;
  int32_t d = sum(st, i);
  
  return (i+1+d)/2;
}


int32_t check_chunk(rmMt* st, int32_t i, int32_t d) {
  int llimit = i;
  int rlimit = i+st->s;
  int32_t output;
  int32_t excess = st->e_prime[(i-1)/st->s];
  int32_t j = 0;

  for(j=llimit; j<rlimit; j+=8) {
    int32_t desired = d - 1 - excess; // desired value must belongs to the range [-8,8]  
    
#ifdef ARCH64
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFFL<<(j&(word_size-1)))) >> (j&(word_size-1));
#else
    int32_t sum_idx = (((st->bit_array)->words[j>>logW]) & (0xFF<<(j&(word_size-1)))) >> (j&(word_size-1));
#endif
    
    if (desired >= -8 && desired <= 8) {
      uint16_t ii = (desired+8<<8) + sum_idx;
      
      int8_t x = T->near_fwd_pos[ii];
      if(x < 8)
	return j+x;
    }
    excess += T->word_sum[sum_idx];
  } 
    
  return i-1;
}

// ToDo: Implement it more efficiently
int32_t select_0(rmMt* st, int32_t i){

  int32_t j = 0;

  // The answer is after the position 2*i-1
  int32_t excess = sum(st,2*i-1);

  // Note: The answer is not beyond the position 2*i-1+depth_max, where
  // depth_max is the maximal depth (excess) of the input tree
  int32_t llimit = 2*i-1;
  int32_t rlimit = llimit + st->M_prime[0];
  int32_t d = 0;

  for (j=llimit+1; j <=rlimit; ++j,++d) {
    if (excess == d)
      return j-1;
    excess += 2*bit_array_get_bit(st->bit_array,j)-1;
  }

    return -1;
}

// ToDo: Implement it more efficiently
int32_t select_1(rmMt* st, int32_t i){
  int32_t j = 0;

  // Note: The answer is in the range [0,2*i-1] not beyond the position 2*i-1
  int32_t excess = 0;
  int32_t llimit = 0;
  int32_t rlimit = 2*i-1;
  int32_t d = 2*i-1;

  for (j=llimit; j <=rlimit; ++j,--d) {
    excess += 2*bit_array_get_bit(st->bit_array,j)-1;
    if (excess == d)
      return j;
  }

    return -1;
}


int32_t match(rmMt* st, int32_t i) {
  if(bit_array_get_bit(st->bit_array,i))
    return find_close(st, i);
  else
    return find_open(st, i);
}

int32_t match_naive(rmMt* st, int32_t i) {
  if(bit_array_get_bit(st->bit_array,i))
    return find_close_naive(st, i);
  else
    return find_open_naive(st, i);
}

int32_t match_semi(rmMt* st, int32_t i) {
  if(bit_array_get_bit(st->bit_array,i))
    return find_close_semi(st, i);
  else
    return find_open_semi(st, i);
}


int32_t parent_t(rmMt* st, int32_t i) {
  if(!bit_array_get_bit(st->bit_array,i))
    i = find_open(st, i);
  
  return bwd_search(st, i, 2);
}

int32_t depth(rmMt* st, int32_t i) {
  return 2*rank_1(st, i)-i-1;
}

int32_t first_child(rmMt* st, int32_t i) {
  if(i >= st->n-1)
    return -1;

  if(!bit_array_get_bit(st->bit_array,i))
    return -1;
  
  if(bit_array_get_bit(st->bit_array,i+1))
    return i+1;
  else 
    return -1;
}

int32_t next_sibling(rmMt* st, int32_t i) {
  if(i >= st->n-1)
    return -1;
  
  if(!bit_array_get_bit(st->bit_array,i))
    return -1;

  i = find_close(st, i);  
  
  if(bit_array_get_bit(st->bit_array,i+1))
    return i+1;
  else 
    return -1;
}

int32_t is_leaf_t(rmMt* st, int32_t i) {
  if(i >= st->n-1)
    return 0;

  if(!bit_array_get_bit(st->bit_array,i))
    return 0;

  if(!bit_array_get_bit(st->bit_array,i+1))
    return 1;
  
  return 0;
}

ulong size_rmMt(rmMt *st) {
  ulong sizeRmMt = sizeof(rmMt);
  ulong sizeBitArray = st->bit_array->num_of_bits/8;
  ulong sizePrimes = 3*((st->num_chunks + st->internal_nodes)*sizeof(int16_t)) +
    st->num_chunks*sizeof(int16_t);

  return sizeRmMt + sizeBitArray + sizePrimes;
}
