typedef void (*fptr)(int*);

void target(int* p) {

}

fptr gfp = target;

void callee(int* p) {
  gfp(p);
}
