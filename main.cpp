/******************************************************************************
 * main.c
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

#include <stdlib.h>
#include <stdio.h>
#include <sys/time.h>
#include <time.h>
#include <ctime>
#include <cstdlib>
#include "succinct_treev2.cpp"
#include "util.h"

int main(int argc, char **argv)
{

  struct timespec stime, etime;
  double time;

  if (argc < 2)
  {
    fprintf(stderr, "Usage: %s <input parentheses sequence>\n", argv[0]);
    exit(EXIT_FAILURE);
  }

  long n;

  BIT_ARRAY *B = parentheses_to_bits(argv[1], &n);

#ifdef MALLOC_COUNT
  size_t s_total_memory = malloc_count_total();
  size_t s_current_memory = malloc_count_current();
  malloc_reset_peak();
#else
  if (clock_gettime(CLOCK_THREAD_CPUTIME_ID, &stime))
  {
    fprintf(stderr, "clock_gettime failed");
    exit(-1);
  }
#endif
  /*

    PARA EXPERIMENTAR RECUERDA QUE LOS VALORES DE INSERCIONES TIENE QUE SER TAM DEL ARCHIVO DIVIDIDO EN 2 MENOS 1

  */
  /*clock_t start = clock();
  double time_construct;*/
  rmMT *tree = new rmMT(B, n);
  /*time_construct = ((double)clock() - start) / CLOCKS_PER_SEC;
  printf("%s,%.10f\n", argv[1], time_construct);*/
  /*int entry;
  sscanf(argv[2], "%d", &entry);
  clock_t start = clock();
  double time_insert_left;*/
  /* for (int i = 0; i <= entry; i++)
   {
     tree->match(i);
   }
   time_insert_left = ((double)clock() - start) / CLOCKS_PER_SEC;
   printf("%s,0,%d,%.10f\n", argv[1], entry, time_insert_left);*/
  int r;
  int nodo = tree->root->t_ones;
  int entry, function;
  sscanf(argv[2], "%d", &function);
  sscanf(argv[3], "%d", &entry);
  vector<int> random;
  for (int i = 0; i < entry; i++)
  {
    random.push_back(r = rand() % nodo / 1);
  }
  switch (function)
  {
  case 1:
  {
    clock_t start = clock();
    double time_insert_left;
    for (int i = 1; i < random.size(); i++)
    {
      tree->insert_l(random[i]);
    }
    time_insert_left = ((double)clock() - start) / CLOCKS_PER_SEC;
    printf("%s,%d,%d,%.10f\n", argv[1], function, entry, time_insert_left);
    break;
  }
  case 2:
  {
    clock_t start_1 = clock();
    double time_insert_right;
    for (int i = 1; i < random.size(); i++)
    {
      tree->insert_r(random[i]);
    }
    time_insert_right = ((double)clock() - start_1) / CLOCKS_PER_SEC;
    printf("%s,%d,%d,%.10f\n", argv[1], function, entry, time_insert_right);
    break;
  }
  case 3:
  {
    clock_t start_2 = clock();
    double time_insert_parent;
    for (int i = 1; i < random.size(); i++)
    {
      tree->insert_p(random[i]);
    }
    time_insert_parent = ((double)clock() - start_2) / CLOCKS_PER_SEC;
    printf("%s,%d,%d,%.10f\n", argv[1], function, entry, time_insert_parent);
    break;
  }
  case 4:
  {
    clock_t start_3 = clock();
    double time_delete;
    for (int i = 1; i < random.size(); i++)
    {
      tree->erase(random[i]);
    }
    time_delete = ((double)clock() - start_3) / CLOCKS_PER_SEC;
    printf("%s,%d,%d,%.10f\n", argv[1], function, entry, time_delete);
    break;
  }
  }
#ifdef MALLOC_COUNT
  size_t e_total_memory = malloc_count_total();
  size_t e_current_memory = malloc_count_current();
  printf("%s,%ld,%zu,%zu,%zu,%zu,%zu\n", argv[1], n, s_total_memory,
         e_total_memory, malloc_count_peak(), s_current_memory, e_current_memory);
  // total cantidad de memoria desde el inicio,sin descontar los free
  // current cuanta memoria, se lleva en el momento
  // Unidad bytes
#else
  if (clock_gettime(CLOCK_THREAD_CPUTIME_ID, &etime))
  {
    fprintf(stderr, "clock_gettime failed");
    exit(-1);
  }

  // time = (etime.tv_sec - stime.tv_sec) + (etime.tv_nsec - stime.tv_nsec) / 1000000000.0;
  // printf("%s,%lu,%lf\n", argv[1], n, time);
#endif

  return EXIT_SUCCESS;
}
