unsigned int my_add(unsigned int a, unsigned int b) {
  while (a > 0) {
    a = a - 1;
    b = b + 1;
  }
  return b;
}

unsigned int my_id(unsigned int a) {
  return my_add(a,0);
}

unsigned int my_add_rec(unsigned int a, unsigned int b) {
  if(a==0) return b;
  return my_add_rec(a-1,b+1);
}

unsigned int my_add_rec3(unsigned int a, unsigned int b) {
  if(a==0) return b;
  if(a>=3) return my_add_rec3(a-3,b+3);
  return my_add_rec3(a-1,b+1);
}

void my_add_ptr(unsigned int a, unsigned int *b) {
  *b = *b + a;
}

unsigned int factorial(unsigned int a) {
  unsigned int acc = 1;
  for(int i = 1; i <= a; i += 1)
    acc *= i;
  return acc;
}

unsigned int recfactorial(unsigned int a) {
  if (a <= 1) return 1;
  return a * recfactorial(a-1);
}

unsigned int factorial_rec_acc_impl(unsigned int a, unsigned int acc){
  if(a<=1) return acc;
  return factorial_rec_acc_impl(a-1,acc*a);
}

unsigned int factorial_rec_acc(unsigned int a){
  return factorial_rec_acc_impl(a,1);
}
