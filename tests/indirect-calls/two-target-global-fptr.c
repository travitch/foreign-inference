typedef void (*fptr)(int*);

fptr gfp;

void target(int* p) {

}

void target2(int* p) {

}

void targe3(int* p) {

}

void setup2() {
  gfp = target2;
}

void setup() {
  gfp = target;
}

void callee(int* p) {
  gfp(p);
}
