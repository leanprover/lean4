#include <iostream>
#include "runtime/init_module.h"
#include "runtime/object.h"
typedef lean::object obj;
/* Initialization function for the module `test.lean` */
void initialize_test();
/* C++ header for the function `foo` at `test.lean` */
obj* l_foo(obj*);

int main(int argc, char ** argv) {
    if (argc != 2) {
        std::cerr << "incorrect number of arguments\n";
        return 1;
    }
    /* Initialize Lean runtime */
    lean::initialize_runtime_module();
    /* Initialize module `test.lean` */
    initialize_test();
    /* Convert the first argument into a Lean `nat` object */
    unsigned n = std::atoi(argv[1]);
    obj * v = lean::mk_nat_obj(n);
    /* Invoke `foo` defined at `test.lean` */
    obj * r = l_foo(v);
    /* Result is a Lean string */
    std::cout << "Result: " << lean::string_cstr(r) << "\n";
    /* We use `lean::dec` to consume/dispose the result value. */
    lean::dec(r);
    return 0;
}
