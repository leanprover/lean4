#include <lean/lean.h>

void lean_initialize_runtime_module(void);

int main(void) {
    lean_initialize_runtime_module();
    lean_panic("boom", true);
    return 0;
}
