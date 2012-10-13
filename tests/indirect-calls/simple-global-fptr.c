typedef void (*fptr)(int*);

fptr gfp;

void target(int* p) {

}

void setup() {
  gfp = target;
}

void callee(int* p) {
  gfp(p);
}
