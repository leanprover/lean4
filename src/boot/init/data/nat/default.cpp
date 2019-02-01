// Lean compiler output
// Module: init.data.nat.default
// Imports: init.data.nat.basic init.data.nat.div
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
void _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
void _l_initialize__l_s4_init_s4_data_s3_nat_s3_div();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s3_nat_s7_default() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
 _l_initialize__l_s4_init_s4_data_s3_nat_s3_div();
}
