#include "stabs.h"

extern void __register_frame_info(void *, void *);
extern void * _EH_FRAME_OBJECTS__[];
extern void * _EH_FRAME_BEGINS__[];

void __init_eh() {
    void ** frame = _EH_FRAME_BEGINS__;
    void ** object = _EH_FRAME_OBJECTS__;
    
    int n = *(int *)frame++;
    int m = *(int *)object++;
    if (n != m)
	    return;
    
    while (n--) {
	    __register_frame_info(*frame++, *object++);
    }
}

ADD2INIT(__init_eh,-5);

