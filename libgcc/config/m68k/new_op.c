#include <stdlib.h>
#include <stdio.h>
extern void * malloc(unsigned);
void * _Znwj (unsigned sz)
{
  void *p = malloc(sz);
  if (p)
    return p;
  perror("std::bad_alloc");
  abort();
}
