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

void __cxa_pure_virtual() {
  perror("pure virtual method called");
  abort();
}

void __cxa_deleted_virtual() {
  perror("deletd virtual method called");
  abort();
}
