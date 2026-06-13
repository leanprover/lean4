#include <lean/lean.h>

int main(void) {
    lean_init_task_manager_using(1);
    lean_init_task_manager();
    return 0;
}
