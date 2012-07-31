struct S {
  int * p1;
  int * p2;
};

extern struct S * g;

void f(int * p){
  g->p2 = p;
}
